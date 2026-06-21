import Chapter3_GraphTheory.Section3_3.SigmaSeparationSymmetric

/-!
# claim_3_27 — `lem:replace_walk` — Walk replacement preserves σ-openness

This file formalises *claim 3_27* of the lecture notes
(Forré & Mooij, `lecture-notes/lecture_notes/graphs.tex`,
`\label{lem:replace_walk}`): given a $C$-$\sigma$-open walk
$\pi = (v_0 \sim \dots \sim v_n)$ in a CDMG $G$ and two
positions $i < j$ with $v_i \in \Sc^G(v_j)$, there exists a
walk $\sigma_{ij}$ from $v_i$ to $v_j$ — directed in one of
the two orientations depending on the boundary configuration
of $\pi$ at position $j$ — entirely within $\Sc^G(v_j)$ whose
splice into $\pi$ (replacing the subwalk between positions
$i$ and $j$) is still $C$-$\sigma$-open.

The authoritative spec is the rewritten canonical tex
statement at
`leanification/Chapter3_GraphTheory/Section3_3/tex/`
`claim_3_27_statement_LabelRoman.tex`, which folds in the
"Addition to the LN" paragraph (length-$0$ trivial-replacement
admitted when $v_i = v_j$) and expands the LN's case-(i)/(ii)
discriminant explicitly.

## Side-aware predicates

The σ-openness hypothesis on $\pi$ and the σ-openness
conclusion on $\pi'$ both reference `Walk.IsSigmaOpenGiven`
(`SigmaBlockedWalks.lean`).  Its underlying `WalkStep`
predicates `HeadAtSource` and `HeadAtTarget` read each step's
arrowhead pattern off the constructor tag alone, so the
splice-boundary σ-openness analysis transports verbatim from
the LN's informal walk-diagram inspection.
-/

namespace Causality

namespace CDMG

-- ## Design choice — claim_3_27 section-wide statement context
--
-- *Polymorphic `Node : Type*` with `[DecidableEq Node]`.*  Matches the
--   chapter-wide convention used by every `CDMG`-opening file in
--   Sections 3.1, 3.2 and 3.3 — see
--   `Section3_3/SigmaSeparationSymmetric.lean:88` for the same block
--   in `claim_3_22`, and `Section3_3/SigmaBlockedWalks.lean` for the
--   same block in `def_3_17`.  The `CDMG`, `Walk`, `G.Sc`,
--   `IsSigmaOpenGiven`, `IsDirectedWalk`, and `Walk.reverse`
--   definitions used in the theorem signature are all parameterised
--   over this same implicit binder block, so the theorem signature
--   below auto-binds these binders into its type.
--
-- *Three-dash `--- start helper` / `--- end helper` markers.*  This
--   `variable` block is statement-typing infrastructure that the
--   wrapped theorem signature cannot compile without (the `G : CDMG
--   Node` premise pattern-matches against the implicit `Node`).
--   Chapter convention for that kind of declaration is the three-dash
--   helper flavour, distinct from the two-dash main-statement marker
--   used to wrap the theorem itself.
-- claim_3_27 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- claim_3_27 --- end helper

-- ## Design choice — `Walk.replaceWalkCaseI` (case-(i)/(ii) discriminant)
--
-- *Role.*  Captures the LN's case-(i)/case-(ii) discriminant of
--   `lem:replace_walk`: case (i) fires iff "$j = \pi.\text{length}$
--   OR the walk-step at position $j$ on $\pi$ is `.forwardE _` (the
--   directed E-edge $v_j \to v_{j+1}$)"; case (ii) fires otherwise.
--   The theorem signature uses this as the disjunctive switch on the
--   direction-witness of the replacement subwalk `σ_ij`: case (i) →
--   `σ_ij.IsDirectedWalk`; case (ii) → `σ_ij.reverse.IsDirectedWalk`.
--
-- *Why a dedicated helper predicate, not an inline disjunction in the
--   signature.*  Encoding the case-(i)/case-(ii) disjunction inline
--   would force two near-duplicate disjunction-of-WalkStep-
--   constructor patterns into the binder block (one positive for the
--   `σ_ij.IsDirectedWalk` direction-witness, one negated for the
--   `σ_ij.reverse.IsDirectedWalk` direction-witness).  Pulling out a
--   named helper consolidates the discriminant into a single Prop on
--   `(π, j)`, makes the signature readable, and gives the proof-phase
--   worker a clean `(h : π.replaceWalkCaseI j)` /
--   `(h : ¬ π.replaceWalkCaseI j)` hypothesis to case-split on.
--
-- *Why exclude `.bidir` from case (i).*  The LN's case-(i) trigger is
--   "$v_j \tuh v_{j+1}$ on $\pi$" — the `\tuh` macro encodes the
--   directed E-edge $(v_j, v_{j+1}) \in E$ (tail at $v_j$, head at
--   $v_{j+1}$).  A `.bidir` walk-step encodes a bidirected $L$-edge
--   $s(v_j, v_{j+1}) \in G.L$, which places arrowheads at BOTH $v_j$
--   and $v_{j+1}$ — this is `\huh` in the LN's symbol set, NOT
--   `\tuh`.  Bidirected steps therefore fall under case (ii) in the
--   LN.  The canonical rewritten tex statement
--   (`tex/claim_3_27_statement_LabelRoman.tex` case (i)) explicitly
--   writes "$a_j = (v_j, v_{j+1}) \in E$", which excludes bidirected
--   $L$-edges.
--
-- *Why structural recursion via nested constructor pattern-matching.*
--   Mirrors `Walk.IsDirectedWalk` (`Section3_1/Walks.lean:941`): the
--   recursion descends one cons-cell at every step `j + 1 → j` and
--   consumes one cons-cell of the walk simultaneously.  At `j = 0` on
--   a cons-cell, the constructor tag of the head WalkStep is the
--   case (i)/(ii) discriminant: `.forwardE` → case (i) (returns
--   `True`); `.backwardE` / `.bidir` → case (ii) (returns `False`).
--   At `j = 0` on a trivial walk `.nil _ _`, `j = π.length = 0`
--   holds, which puts us in the first disjunct of case (i) — so
--   `True`.  At `j ≥ 1` on a trivial walk, we are off-range (`j >
--   π.length`); the predicate returns `False` for totality, but this
--   branch is unreachable from the theorem's hypotheses (which
--   constrain `j ≤ π.length`).
--
-- *Three-dash helper marker.*  The theorem signature's
--   `π.replaceWalkCaseI j` and `¬ π.replaceWalkCaseI j` premises
--   cannot type-check without this helper, so the website builder
--   needs to extract it alongside the wrapped statement.  Same
--   discipline as the `variable {Node : Type*}` block above.
--
-- *Wording-check subtlety `case_i_fork_at_vj_blocking_criteria_-`
--   `overlooked` resolution.*  The working-phase wording-check
--   flagged the LN's case-(i) proof step "the same blocking
--   criteria apply to $v_j$ on $\pi'$" as doing significant
--   undeclared work: on $\pi$ a *fork* at $v_j$ has two outgoing
--   walk-neighbours $v_{j-1}, v_{j+1}$, but on $\pi'$ the left edge
--   becomes incoming, so $v_j$ degenerates from fork to right-chain
--   with only $v_{j+1}$ as an outgoing walk-neighbour.  Under an
--   outgoing-only $\sigma$-blocking convention the blocking criteria
--   are NOT pointwise the same, raising the question whether the
--   case-(i) replacement could spuriously block at $v_j$.  The
--   subtlety is benign under our chapter-wide blocking convention:
--   `BlockableAndUnblockable.lean`'s `HasBlockingLeftSlot` /
--   `HasBlockingRightSlot` (`def_3_16`) IS asymmetric (the criterion
--   queries outgoing walk-neighbours on each side separately), AND
--   the σ-open hypothesis on $\pi$ excludes the problematic corner:
--   if $v_j$ were a fork on $\pi$ with $v_j \in C$,
--   $v_j \in \Sc^G(v_{j-1})$, and $v_j \notin \Sc^G(v_{j+1})$
--   (the only configuration where the criteria genuinely differ
--   pre/post-replacement), then the right slot of the fork on $\pi$
--   would already be a blocking slot, contradicting $\pi$'s
--   σ-openness at position $j$.  So the LN's "same blocking
--   criteria" reduction is verified — the proof-phase worker can
--   discharge $v_j$'s σ-openness on $\pi'$ from $v_j$'s σ-openness
--   on $\pi$ without a separate fork-vs-right-chain bridge lemma,
--   and the case-(i)/(ii) discriminant captured by this helper does
--   not need a sub-case for forks.
-- claim_3_27 --- start helper
def Walk.replaceWalkCaseI {G : CDMG Node} :
    ∀ {u v : Node}, Walk G u v → ℕ → Prop
  | _, _, .nil _ _, 0 => True
  | _, _, .nil _ _, _ + 1 => False
  | _, _, .cons _ (.forwardE _) _, 0 => True
  | _, _, .cons _ (.backwardE _) _, 0 => False
  | _, _, .cons _ (.bidir _) _, 0 => False
  | _, _, .cons _ _ p, j + 1 => p.replaceWalkCaseI j
-- claim_3_27 --- end helper

/-! ### Private proof helpers for `replaceWalk`

The lemmas below support the proof of `replaceWalk` only; none of them
appear in the markered statement.  They are `private` to this file and
carry no markers per the chapter's litmus test (would removing this
helper cause the markered statement to fail to compile?  No → no
markers).  Organised top-down:

* `mem_*` lemmas — `Anc` / `Desc` / `Sc` reflexivity, transitivity, and
  SCC-equality on a shared component;
* `Walk.splitAt` — split a walk at a position into a prefix + suffix;
* `Walk.shortestDirectedWalk` — extract a minimum-length directed walk
  via classical `Nat.find`;
* `Walk.unblockable_imp_sigma_open_at` — the walk-level inline
  formulation of claim_3_21 (unblockable non-collider ⇒ σ-open at that
  position), needed to discharge the strictly-interior σ_{ij} verdict.
-/

-- ## Anc / Desc / Sc helper lemmas

lemma mem_Anc_refl {G : CDMG Node} {v : Node} (hv : v ∈ G) :
    v ∈ G.Anc v := ⟨hv, ⟨Walk.nil v hv, trivial⟩⟩

lemma mem_Desc_refl {G : CDMG Node} {v : Node} (hv : v ∈ G) :
    v ∈ G.Desc v := ⟨hv, ⟨Walk.nil v hv, trivial⟩⟩

lemma mem_Sc_refl {G : CDMG Node} {v : Node} (hv : v ∈ G) :
    v ∈ G.Sc v := ⟨mem_Anc_refl hv, mem_Desc_refl hv⟩

lemma mem_Anc_trans {G : CDMG Node} {u v w : Node}
    (huv : u ∈ G.Anc v) (hvw : v ∈ G.Anc w) : u ∈ G.Anc w := by
  obtain ⟨huG, p_uv, hp_uv⟩ := huv
  obtain ⟨_hvG, p_vw, hp_vw⟩ := hvw
  exact ⟨huG, p_uv.comp p_vw, Walk.isDirectedWalk_comp _ _ hp_uv hp_vw⟩

private lemma mem_Desc_trans {G : CDMG Node} {u v w : Node}
    (huv : u ∈ G.Desc v) (hvw : v ∈ G.Desc w) : u ∈ G.Desc w := by
  obtain ⟨huG, p_vu, hp_vu⟩ := huv
  obtain ⟨_hvG, p_wv, hp_wv⟩ := hvw
  exact ⟨huG, p_wv.comp p_vu, Walk.isDirectedWalk_comp _ _ hp_wv hp_vu⟩

private lemma mem_Sc_of_Sc {G : CDMG Node} {u v w : Node}
    (huv : u ∈ G.Sc v) (hvw : v ∈ G.Sc w) : u ∈ G.Sc w :=
  ⟨mem_Anc_trans huv.1 hvw.1, mem_Desc_trans huv.2 hvw.2⟩

lemma Walk.target_mem {G : CDMG Node} :
    ∀ {u v : Node}, Walk G u v → v ∈ G
  | _, _, .nil _ hv => hv
  | _, _, .cons _ _ p => Walk.target_mem p

private lemma mem_Sc_symm {G : CDMG Node} {u v : Node}
    (h : u ∈ G.Sc v) : v ∈ G.Sc u := by
  obtain ⟨⟨huG, p_uv, hp_uv⟩, ⟨_, p_vu, hp_vu⟩⟩ := h
  have hvG : v ∈ G := Walk.target_mem p_uv
  exact ⟨⟨hvG, p_vu, hp_vu⟩, ⟨hvG, p_uv, hp_uv⟩⟩

private lemma mem_G_of_mem_Sc {G : CDMG Node} {u v : Node}
    (h : u ∈ G.Sc v) : u ∈ G := h.1.1

private lemma Sc_eq_of_mem_Sc {G : CDMG Node} {u v : Node}
    (h : u ∈ G.Sc v) : G.Sc u = G.Sc v := by
  ext x
  constructor
  · intro hxu
    exact mem_Sc_of_Sc hxu h
  · intro hxv
    exact mem_Sc_of_Sc hxv (mem_Sc_symm h)

-- ## Walk splitting at a position
--
-- A walk-splitter at position `k`.  The shape `Σ' (mid : Node), …`
-- captures the midpoint vertex; the proof helpers `splitAt_length_left`
-- / `splitAt_length_right` / `splitAt_vertices_*` / `splitAt_comp`
-- characterise the two sub-walks against `Walk.length` and
-- `Walk.vertices`.

/-- Split `p : Walk G u w` at position `k ≤ p.length` into a prefix
    of length `k` and a suffix of length `p.length - k`. -/
def Walk.splitAt {G : CDMG Node} :
    ∀ {u w : Node} (p : Walk G u w) (k : ℕ), k ≤ p.length →
      Σ' (mid : Node), (Walk G u mid) × (Walk G mid w)
  | _, _, .nil v hv, 0, _ => ⟨v, .nil v hv, .nil v hv⟩
  | _, _, .nil _ _, _ + 1, hk =>
      absurd hk (by simp [Walk.length])
  | u, _, .cons mid s p, 0, _ =>
      ⟨u, .nil u (WalkStep.source_mem s), .cons mid s p⟩
  | _, _, .cons mid s p, k + 1, hk =>
      ⟨(p.splitAt k (Nat.le_of_succ_le_succ hk)).1,
        .cons mid s (p.splitAt k (Nat.le_of_succ_le_succ hk)).2.1,
        (p.splitAt k (Nat.le_of_succ_le_succ hk)).2.2⟩

lemma Walk.splitAt_length_left {G : CDMG Node} :
    ∀ {u w : Node} (p : Walk G u w) (k : ℕ) (hk : k ≤ p.length),
      (p.splitAt k hk).2.1.length = k
  | _, _, .nil _ _, 0, _ => rfl
  | _, _, .nil _ _, _ + 1, hk => absurd hk (by simp [Walk.length])
  | _, _, .cons _ _ _, 0, _ => rfl
  | _, _, .cons _ _ p, k + 1, hk => by
      show ((Walk.cons _ _ p).splitAt (k + 1) hk).2.1.length = k + 1
      change (Walk.cons _ _ (p.splitAt k _).2.1).length = k + 1
      change (p.splitAt k _).2.1.length + 1 = k + 1
      rw [Walk.splitAt_length_left p k]

lemma Walk.splitAt_length_right {G : CDMG Node} :
    ∀ {u w : Node} (p : Walk G u w) (k : ℕ) (hk : k ≤ p.length),
      (p.splitAt k hk).2.2.length = p.length - k
  | _, _, .nil _ _, 0, _ => rfl
  | _, _, .nil _ _, _ + 1, hk => absurd hk (by simp [Walk.length])
  | _, _, .cons _ _ p, 0, _ => by
      change (Walk.cons _ _ p).length = (Walk.cons _ _ p).length - 0
      rfl
  | _, _, .cons _ _ p, k + 1, hk => by
      change (p.splitAt k _).2.2.length = (Walk.cons _ _ p).length - (k + 1)
      rw [Walk.splitAt_length_right p k]
      change p.length - k = p.length + 1 - (k + 1)
      omega

lemma Walk.splitAt_comp {G : CDMG Node} :
    ∀ {u w : Node} (p : Walk G u w) (k : ℕ) (hk : k ≤ p.length),
      (p.splitAt k hk).2.1.comp (p.splitAt k hk).2.2 = p
  | _, _, .nil _ _, 0, _ => rfl
  | _, _, .nil _ _, _ + 1, hk => absurd hk (by simp [Walk.length])
  | _, _, .cons _ _ _, 0, _ => by
      show (Walk.nil _ _).comp _ = _
      rfl
  | _, _, .cons mid s p, k + 1, hk => by
      show (Walk.cons mid s (p.splitAt k _).2.1).comp (p.splitAt k _).2.2
            = Walk.cons mid s p
      change Walk.cons mid s ((p.splitAt k _).2.1.comp (p.splitAt k _).2.2)
            = Walk.cons mid s p
      rw [Walk.splitAt_comp p k]

lemma Walk.splitAt_vertices_left {G : CDMG Node} :
    ∀ {u w : Node} (p : Walk G u w) (k : ℕ) (hk : k ≤ p.length),
      (p.splitAt k hk).2.1.vertices = p.vertices.take (k + 1)
  | _, _, .nil _ _, 0, _ => by
      change [_] = (List.take 1 [_])
      rfl
  | _, _, .nil _ _, _ + 1, hk => absurd hk (by simp [Walk.length])
  | u, _, .cons _ _ _, 0, _ => by
      show [u] = ((u :: _).take 1)
      rfl
  | u, _, .cons _ _ p, k + 1, hk => by
      show (u :: (p.splitAt k _).2.1.vertices) = ((u :: p.vertices).take (k + 2))
      rw [Walk.splitAt_vertices_left p k]
      rfl

lemma Walk.splitAt_vertices_right {G : CDMG Node} :
    ∀ {u w : Node} (p : Walk G u w) (k : ℕ) (hk : k ≤ p.length),
      (p.splitAt k hk).2.2.vertices = p.vertices.drop k
  | _, _, .nil _ _, 0, _ => rfl
  | _, _, .nil _ _, _ + 1, hk => absurd hk (by simp [Walk.length])
  | u, _, .cons _ _ p, 0, _ => by
      show (u :: p.vertices) = ((u :: p.vertices).drop 0)
      rfl
  | _, _, .cons _ _ p, k + 1, hk => by
      show (p.splitAt k _).2.2.vertices = ((_ :: p.vertices).drop (k + 1))
      rw [Walk.splitAt_vertices_right p k]
      rfl

lemma Walk.splitAt_mid_get {G : CDMG Node} :
    ∀ {u w : Node} (p : Walk G u w) (k : ℕ) (hk : k ≤ p.length),
      p.vertices[k]? = some (p.splitAt k hk).1
  | _, _, .nil _ _, 0, _ => rfl
  | _, _, .nil _ _, _ + 1, hk => absurd hk (by simp [Walk.length])
  | _, _, .cons _ _ _, 0, _ => rfl
  | _, _, .cons _ _ p, k + 1, hk => by
      show (_ :: p.vertices)[k + 1]? = some (p.splitAt k _).1
      change p.vertices[k]? = some (p.splitAt k _).1
      exact Walk.splitAt_mid_get p k _

-- ## Shortest directed walk extraction

noncomputable def Walk.shortestDirectedWalk {G : CDMG Node}
    {u v : Node} (h : ∃ p : Walk G u v, p.IsDirectedWalk) :
    {p : Walk G u v //
      p.IsDirectedWalk ∧
      ∀ q : Walk G u v, q.IsDirectedWalk → p.length ≤ q.length} := by
  classical
  let S : ℕ → Prop := fun n =>
    ∃ p : Walk G u v, p.IsDirectedWalk ∧ p.length = n
  have hS_nonempty : ∃ n, S n := by
    obtain ⟨p, hp⟩ := h
    exact ⟨p.length, p, hp, rfl⟩
  let n_min : ℕ := Nat.find hS_nonempty
  have h_n_min : S n_min := Nat.find_spec hS_nonempty
  let p_min : Walk G u v := h_n_min.choose
  have h_min_spec := h_n_min.choose_spec
  refine ⟨p_min, h_min_spec.1, ?_⟩
  intro q hq
  have hq_in_S : S q.length := ⟨q, hq, rfl⟩
  have : n_min ≤ q.length := Nat.find_min' hS_nonempty hq_in_S
  rw [show p_min.length = n_min from h_min_spec.2]
  exact this

-- ## Reverse of a directed walk gives a backward walk

/-- A walk whose every step is `.backwardE` (i.e. `p.reverse.IsDirectedWalk`)
    has the same length as its reverse. -/
private lemma Walk.length_reverseDirected_eq {G : CDMG Node}
    {u v : Node} (p : Walk G u v) :
    p.reverse.length = p.length := by
  exact Walk.length_reverse p

-- ## Sc → Anc and Sc → Desc projection lemmas

private lemma mem_Anc_of_mem_Sc {G : CDMG Node} {u v : Node}
    (h : u ∈ G.Sc v) : u ∈ G.Anc v := h.1

private lemma mem_Desc_of_mem_Sc {G : CDMG Node} {u v : Node}
    (h : u ∈ G.Sc v) : u ∈ G.Desc v := h.2

-- ## Walk.reverse equals nil for nil walks

private lemma Walk.reverse_nil {G : CDMG Node} (v : Node) (hv : v ∈ G) :
    (Walk.nil v hv : Walk G v v).reverse = Walk.nil v hv := rfl

-- ## Directed-walk decomposition through composition

lemma Walk.IsDirectedWalk_of_comp_left {G : CDMG Node} :
    ∀ {u v w : Node} (p1 : Walk G u v) (p2 : Walk G v w),
      (p1.comp p2).IsDirectedWalk → p1.IsDirectedWalk
  | _, _, _, .nil _ _, _, _ => trivial
  | _, _, _, .cons _ s p1', p2, h => by
      cases s with
      | forwardE _ =>
        show p1'.IsDirectedWalk
        exact Walk.IsDirectedWalk_of_comp_left p1' p2 h
      | backwardE _ => exact h.elim
      | bidir _ => exact h.elim

lemma Walk.IsDirectedWalk_of_comp_right {G : CDMG Node} :
    ∀ {u v w : Node} (p1 : Walk G u v) (p2 : Walk G v w),
      (p1.comp p2).IsDirectedWalk → p2.IsDirectedWalk
  | _, _, _, .nil _ _, _, h => h
  | _, _, _, .cons _ s p1', p2, h => by
      cases s with
      | forwardE _ => exact Walk.IsDirectedWalk_of_comp_right p1' p2 h
      | backwardE _ => exact h.elim
      | bidir _ => exact h.elim

-- ## Every vertex on a directed walk is in `Desc` of the source and
-- `Anc` of the target.

lemma Walk.directed_vertex_mem_Desc {G : CDMG Node} :
    ∀ {u w : Node} (p : Walk G u w), p.IsDirectedWalk →
      ∀ {x : Node}, x ∈ p.vertices → x ∈ G.Desc u
  | _, _, .nil v hv, _, x, hx => by
      change x ∈ [v] at hx
      rw [List.mem_singleton] at hx
      subst hx
      exact mem_Desc_refl hv
  | u, _, .cons mid s p, h_dir, x, hx => by
      change x ∈ (u :: p.vertices) at hx
      rcases List.mem_cons.mp hx with rfl | h_in
      · exact mem_Desc_refl (WalkStep.source_mem s)
      · cases s with
        | forwardE h_E =>
          have h_p_dir : p.IsDirectedWalk := h_dir
          have h_x_desc_mid : x ∈ G.Desc mid :=
            Walk.directed_vertex_mem_Desc p h_p_dir h_in
          obtain ⟨hx_mem, p_mid_x, hp_dir⟩ := h_x_desc_mid
          refine ⟨hx_mem,
                  .cons mid (.forwardE h_E) p_mid_x,
                  ?_⟩
          show p_mid_x.IsDirectedWalk
          exact hp_dir
        | backwardE _ => exact h_dir.elim
        | bidir _ => exact h_dir.elim

lemma Walk.directed_vertex_mem_Anc {G : CDMG Node} :
    ∀ {u w : Node} (p : Walk G u w), p.IsDirectedWalk →
      ∀ {x : Node}, x ∈ p.vertices → x ∈ G.Anc w
  | _, _, .nil v hv, _, x, hx => by
      change x ∈ [v] at hx
      rw [List.mem_singleton] at hx
      subst hx
      exact mem_Anc_refl hv
  | u, _, .cons mid s p, h_dir, x, hx => by
      change x ∈ (u :: p.vertices) at hx
      rcases List.mem_cons.mp hx with rfl | h_in
      · cases s with
        | forwardE h_E =>
          have h_p_dir : p.IsDirectedWalk := h_dir
          have hwG : _ ∈ G := Walk.target_mem p
          refine ⟨WalkStep.source_mem (G := G) (.forwardE h_E),
                  .cons mid (.forwardE h_E) p, ?_⟩
          show p.IsDirectedWalk
          exact h_p_dir
        | backwardE _ => exact h_dir.elim
        | bidir _ => exact h_dir.elim
      · cases s with
        | forwardE _ =>
          have h_p_dir : p.IsDirectedWalk := h_dir
          exact Walk.directed_vertex_mem_Anc p h_p_dir h_in
        | backwardE _ => exact h_dir.elim
        | bidir _ => exact h_dir.elim

-- ## Cast lemmas: target-type rewrites are benign for vertex / length /
-- IsDirectedWalk computations.

lemma Walk.vertices_cast_target {G : CDMG Node} {u : Node}
    {v v' : Node} (h : v = v') (p : Walk G u v) :
    (h ▸ p).vertices = p.vertices := by
  subst h; rfl

lemma Walk.length_cast_target {G : CDMG Node} {u : Node}
    {v v' : Node} (h : v = v') (p : Walk G u v) :
    (h ▸ p).length = p.length := by
  subst h; rfl

lemma Walk.IsDirectedWalk_cast_target {G : CDMG Node} {u : Node}
    {v v' : Node} (h : v = v') (p : Walk G u v) :
    (h ▸ p).IsDirectedWalk ↔ p.IsDirectedWalk := by
  subst h; rfl

lemma Walk.vertices_cast_source {G : CDMG Node} {v : Node}
    {u u' : Node} (h : u = u') (p : Walk G u v) :
    (h ▸ p).vertices = p.vertices := by
  subst h; rfl

lemma Walk.length_cast_source {G : CDMG Node} {v : Node}
    {u u' : Node} (h : u = u') (p : Walk G u v) :
    (h ▸ p).length = p.length := by
  subst h; rfl

lemma Walk.IsDirectedWalk_cast_source {G : CDMG Node} {v : Node}
    {u u' : Node} (h : u = u') (p : Walk G u v) :
    (h ▸ p).IsDirectedWalk ↔ p.IsDirectedWalk := by
  subst h; rfl

-- ## Walk.vertices ends with the target — local copy under a different
-- name since `Walk.vertices_getLast` already exists in scope.

private lemma Walk.last_vertex_eq_target {G : CDMG Node} :
    ∀ {u v : Node} (p : Walk G u v),
      p.vertices.getLast (Walk.vertices_ne_nil p) = v
  | _, _, .nil _ _ => rfl
  | _, _, .cons _ _ p => by
      change (_ :: p.vertices).getLast _ = _
      rw [List.getLast_cons (Walk.vertices_ne_nil p)]
      exact Walk.last_vertex_eq_target p

-- ## Composition-aware lemmas — outer-left fragment
--
-- Each lemma is by `induction p1` with `k` and `p2` generalised inside,
-- so the outer match on `p1` aligns with `Walk.comp`'s unfolding and
-- the inner case-split on `k` aligns with each predicate's recursion.

lemma Walk.refactor_IsCollider_comp_left {G : CDMG Node}
    {u v w : Node} (p1 : Walk G u v) :
    ∀ (p2 : Walk G v w) (k : ℕ), k < p1.length →
      (p1.comp p2).IsCollider k = p1.IsCollider k := by
  induction p1 with
  | nil v hv =>
      intros p2 k hk
      simp [Walk.length] at hk
  | cons mid s p1' ih =>
      intros p2 k hk
      match k with
      | 0 =>
          cases p1' with
          | nil _ _ =>
              cases p2 with
              | nil _ _ => rfl
              | cons _ _ _ => rfl
          | cons _ _ _ => rfl
      | 1 =>
          cases p1' with
          | nil _ _ =>
              simp [Walk.length] at hk
          | cons _ _ _ => rfl
      | k + 2 =>
          cases p1' with
          | nil _ _ =>
              simp [Walk.length] at hk
          | cons mid' s' p1'' =>
              have hk' : k + 1 < (Walk.cons mid' s' p1'').length := by
                simp [Walk.length] at hk ⊢
                omega
              simp only [Walk.comp, Walk.IsCollider]
              exact ih p2 (k + 1) hk'

lemma Walk.HasBlockingLeftSlot_comp_left {G : CDMG Node}
    {u v w : Node} (p1 : Walk G u v) :
    ∀ (p2 : Walk G v w) (k : ℕ), k ≤ p1.length →
      (p1.comp p2).HasBlockingLeftSlot k = p1.HasBlockingLeftSlot k := by
  induction p1 with
  | nil v hv =>
      intros p2 k hk
      obtain rfl : k = 0 := by simp [Walk.length] at hk; omega
      cases p2 with
      | nil _ _ => rfl
      | cons _ _ _ => rfl
  | cons mid s p1' ih =>
      intros p2 k hk
      match k with
      | 0 => rfl
      | 1 =>
          cases s with
          | forwardE _ => rfl
          | backwardE _ => rfl
          | bidir _ => rfl
      | k + 2 =>
          cases p1' with
          | nil _ _ =>
              simp [Walk.length] at hk
          | cons mid' s' p1'' =>
              have hk' : k + 1 ≤ (Walk.cons mid' s' p1'').length := by
                simp [Walk.length] at hk ⊢
                omega
              simp only [Walk.comp, Walk.HasBlockingLeftSlot]
              exact ih p2 (k + 1) hk'

lemma Walk.HasBlockingRightSlot_comp_left {G : CDMG Node}
    {u v w : Node} (p1 : Walk G u v) :
    ∀ (p2 : Walk G v w) (k : ℕ), k < p1.length →
      (p1.comp p2).HasBlockingRightSlot k = p1.HasBlockingRightSlot k := by
  induction p1 with
  | nil v hv =>
      intros p2 k hk
      simp [Walk.length] at hk
  | cons mid s p1' ih =>
      intros p2 k hk
      match k with
      | 0 =>
          cases s with
          | forwardE _ => rfl
          | backwardE _ => rfl
          | bidir _ => rfl
      | k + 1 =>
          cases p1' with
          | nil _ _ =>
              simp [Walk.length] at hk
          | cons mid' s' p1'' =>
              have hk' : k < (Walk.cons mid' s' p1'').length := by
                simp [Walk.length] at hk ⊢
                omega
              simp only [Walk.comp, Walk.HasBlockingRightSlot]
              exact ih p2 k hk'

-- ## Composition-aware lemmas — outer-right fragment (positions > p1.length)
--
-- These mirror the `_comp_left` trio above for the suffix side: at
-- position k > p1.length on (p1.comp p2), the predicate's value reads
-- entirely off p2 at position (k - p1.length).

lemma Walk.refactor_IsCollider_comp_right {G : CDMG Node}
    {u v w : Node} (p1 : Walk G u v) :
    ∀ (p2 : Walk G v w) (k : ℕ), p1.length < k →
      (p1.comp p2).IsCollider k = p2.IsCollider (k - p1.length) := by
  induction p1 with
  | nil v hv =>
      intros p2 k _
      show p2.IsCollider k = p2.IsCollider (k - 0)
      rfl
  | cons mid s p1' ih =>
      intros p2 k hk
      have hk_ge : k ≥ 2 := by simp [Walk.length] at hk; omega
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
      have hk_ih : p1'.length < k' + 1 := by
        simp [Walk.length] at hk; omega
      have h_sub : k' + 2 - (Walk.cons mid s p1').length =
                   k' + 1 - p1'.length := by
        simp only [Walk.length]; omega
      rw [h_sub]
      simp only [Walk.comp, Walk.IsCollider]
      cases p1' with
      | nil _ _ =>
          cases p2 with
          | nil _ _ => rfl
          | cons _ _ _ => rfl
      | cons mid' s' p1'' =>
          exact ih p2 (k' + 1) hk_ih

lemma Walk.HasBlockingLeftSlot_comp_right {G : CDMG Node}
    {u v w : Node} (p1 : Walk G u v) :
    ∀ (p2 : Walk G v w) (k : ℕ), p1.length < k →
      (p1.comp p2).HasBlockingLeftSlot k = p2.HasBlockingLeftSlot (k - p1.length) := by
  induction p1 with
  | nil v hv =>
      intros p2 k _
      show p2.HasBlockingLeftSlot k = p2.HasBlockingLeftSlot (k - 0)
      rfl
  | cons mid s p1' ih =>
      intros p2 k hk
      have hk_ge : k ≥ 2 := by simp [Walk.length] at hk; omega
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
      have hk_ih : p1'.length < k' + 1 := by
        simp [Walk.length] at hk; omega
      have h_sub : k' + 2 - (Walk.cons mid s p1').length =
                   k' + 1 - p1'.length := by
        simp only [Walk.length]; omega
      rw [h_sub]
      simp only [Walk.comp, Walk.HasBlockingLeftSlot]
      exact ih p2 (k' + 1) hk_ih

lemma Walk.HasBlockingRightSlot_comp_right {G : CDMG Node}
    {u v w : Node} (p1 : Walk G u v) :
    ∀ (p2 : Walk G v w) (k : ℕ), p1.length ≤ k →
      (p1.comp p2).HasBlockingRightSlot k = p2.HasBlockingRightSlot (k - p1.length) := by
  induction p1 with
  | nil v hv =>
      intros p2 k _
      show p2.HasBlockingRightSlot k = p2.HasBlockingRightSlot (k - 0)
      rfl
  | cons mid s p1' ih =>
      intros p2 k hk
      have hk_ge : k ≥ 1 := by simp [Walk.length] at hk; omega
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have hk_ih : p1'.length ≤ k' := by
        simp [Walk.length] at hk; omega
      have h_sub : k' + 1 - (Walk.cons mid s p1').length =
                   k' - p1'.length := by
        simp only [Walk.length]; omega
      rw [h_sub]
      simp only [Walk.comp, Walk.HasBlockingRightSlot]
      exact ih p2 k' hk_ih

-- ## Cast invariance for the per-position predicates

lemma Walk.refactor_IsCollider_cast_target {G : CDMG Node} {u : Node}
    {v v' : Node} (h : v = v') (p : Walk G u v) (k : ℕ) :
    (h ▸ p).IsCollider k = p.IsCollider k := by
  subst h; rfl

lemma Walk.refactor_IsCollider_cast_source {G : CDMG Node} {v : Node}
    {u u' : Node} (h : u = u') (p : Walk G u v) (k : ℕ) :
    (h ▸ p).IsCollider k = p.IsCollider k := by
  subst h; rfl

lemma Walk.HasBlockingLeftSlot_cast_target {G : CDMG Node} {u : Node}
    {v v' : Node} (h : v = v') (p : Walk G u v) (k : ℕ) :
    (h ▸ p).HasBlockingLeftSlot k = p.HasBlockingLeftSlot k := by
  subst h; rfl

lemma Walk.HasBlockingLeftSlot_cast_source {G : CDMG Node} {v : Node}
    {u u' : Node} (h : u = u') (p : Walk G u v) (k : ℕ) :
    (h ▸ p).HasBlockingLeftSlot k = p.HasBlockingLeftSlot k := by
  subst h; rfl

lemma Walk.HasBlockingRightSlot_cast_target {G : CDMG Node} {u : Node}
    {v v' : Node} (h : v = v') (p : Walk G u v) (k : ℕ) :
    (h ▸ p).HasBlockingRightSlot k = p.HasBlockingRightSlot k := by
  subst h; rfl

lemma Walk.HasBlockingRightSlot_cast_source {G : CDMG Node} {v : Node}
    {u u' : Node} (h : u = u') (p : Walk G u v) (k : ℕ) :
    (h ▸ p).HasBlockingRightSlot k = p.HasBlockingRightSlot k := by
  subst h; rfl

-- ## Splice-interior helper: directed walk interior is non-collider
--
-- For a `.IsDirectedWalk` p of length ≥ 2, every interior position
-- k ∈ [1, p.length - 1] satisfies `p.IsCollider k = False`,
-- because each adjacent step is `.forwardE _`, whose
-- `HeadAtSource` is `False`.

lemma Walk.IsDirectedWalk.interior_not_collider {G : CDMG Node} :
    ∀ {u v : Node} (p : Walk G u v), p.IsDirectedWalk →
      ∀ (k : ℕ), 1 ≤ k → k < p.length → ¬ p.IsCollider k := by
  intros u v p
  induction p with
  | nil _ _ =>
      intros _ k _ hk2
      simp [Walk.length] at hk2
  | cons mid s p' ih =>
      intros h k hk1 hk2
      cases s with
      | forwardE _ =>
          have hp' : p'.IsDirectedWalk := h
          match k with
          | 0 => omega
          | 1 =>
              cases p' with
              | nil _ _ => simp [Walk.length] at hk2
              | cons _ s' _ =>
                  cases s' with
                  | forwardE _ =>
                      intro h_coll
                      simp [Walk.IsCollider,
                            WalkStep.HeadAtTarget,
                            WalkStep.HeadAtSource] at h_coll
                  | backwardE _ => exact hp'.elim
                  | bidir _ => exact hp'.elim
          | k' + 2 =>
              have hk1' : 1 ≤ k' + 1 := by omega
              have hk2' : k' + 1 < p'.length := by
                simp [Walk.length] at hk2; omega
              have ih_res := ih hp' (k' + 1) hk1' hk2'
              cases p' with
              | nil _ _ => simp [Walk.length] at hk2'
              | cons _ _ _ => exact ih_res
      | backwardE _ => exact h.elim
      | bidir _ => exact h.elim


-- ## Case-(ii) splice-interior helper: backward-directed walks
--
-- Mirror of `IsDirectedWalk.interior_not_collider` for "backward-
-- directed" walks (every step is `.backwardE _`).  Under the side-aware
-- reading, at adjacent `.backwardE` steps:
-- `HeadAtTarget(.backwardE _) = False`, `HeadAtSource(.backwardE _) = True`,
-- so `IsCollider = False ∧ True = False`.

def Walk.IsBackwardDirectedWalk {G : CDMG Node} :
    ∀ {u v : Node}, Walk G u v → Prop
  | _, _, .nil _ _ => True
  | _, _, .cons _ (.backwardE _) p => p.IsBackwardDirectedWalk
  | _, _, .cons _ (.forwardE _) _ => False
  | _, _, .cons _ (.bidir _) _ => False

lemma Walk.IsBackwardDirectedWalk.interior_not_collider {G : CDMG Node} :
    ∀ {u v : Node} (p : Walk G u v), p.IsBackwardDirectedWalk →
      ∀ (k : ℕ), 1 ≤ k → k < p.length → ¬ p.IsCollider k := by
  intros u v p
  induction p with
  | nil _ _ =>
      intros _ k _ hk2
      simp [Walk.length] at hk2
  | cons mid s p' ih =>
      intros h k hk1 hk2
      cases s with
      | forwardE _ => exact h.elim
      | backwardE _ =>
          have hp' : p'.IsBackwardDirectedWalk := h
          match k with
          | 0 => omega
          | 1 =>
              cases p' with
              | nil _ _ => simp [Walk.length] at hk2
              | cons _ s' _ =>
                  cases s' with
                  | forwardE _ => exact hp'.elim
                  | backwardE _ =>
                      intro h_coll
                      simp [Walk.IsCollider,
                            WalkStep.HeadAtTarget,
                            WalkStep.HeadAtSource] at h_coll
                  | bidir _ => exact hp'.elim
          | k' + 2 =>
              have hk1' : 1 ≤ k' + 1 := by omega
              have hk2' : k' + 1 < p'.length := by
                simp [Walk.length] at hk2; omega
              have ih_res := ih hp' (k' + 1) hk1' hk2'
              cases p' with
              | nil _ _ => simp [Walk.length] at hk2'
              | cons _ _ _ => exact ih_res
      | bidir _ => exact h.elim

-- IsBackwardDirectedWalk distributes over Walk.comp (mirror of
-- `Walk.isDirectedWalk_comp` from `MargPreservesAncestors.lean`).

lemma Walk.isBackwardDirectedWalk_comp {G : CDMG Node} :
    ∀ {u v w : Node} (p : Walk G u v) (q : Walk G v w),
      p.IsBackwardDirectedWalk → q.IsBackwardDirectedWalk →
        (p.comp q).IsBackwardDirectedWalk
  | _, _, _, .nil _ _, _, _, hq => hq
  | _, _, _, .cons _ (.backwardE _) p, q, hp, hq =>
      Walk.isBackwardDirectedWalk_comp p q hp hq
  | _, _, _, .cons _ (.forwardE _) _, _, hp, _ => hp.elim
  | _, _, _, .cons _ (.bidir _) _, _, hp, _ => hp.elim

-- A reversed directed walk is backward-directed.

lemma Walk.reverse_isBackwardDirected_of_directed {G : CDMG Node} :
    ∀ {u v : Node} (p : Walk G u v), p.IsDirectedWalk →
      p.reverse.IsBackwardDirectedWalk
  | _, _, .nil _ _, _ => trivial
  | u, _, .cons mid (.forwardE h_E) p', h => by
      have hp' : p'.IsDirectedWalk := h
      have hp'_rev : p'.reverse.IsBackwardDirectedWalk :=
        Walk.reverse_isBackwardDirected_of_directed p' hp'
      have hu_mem : u ∈ G :=
        WalkStep.source_mem (WalkStep.forwardE h_E : WalkStep G u mid)
      have h_q : Walk.IsBackwardDirectedWalk
          (Walk.cons u (WalkStep.backwardE h_E) (Walk.nil u hu_mem)) := by
        simp [Walk.IsBackwardDirectedWalk]
      exact Walk.isBackwardDirectedWalk_comp _ _ hp'_rev h_q
  | _, _, .cons _ (.backwardE _) _, h => h.elim
  | _, _, .cons _ (.bidir _) _, h => h.elim

-- ## Splice-boundary helpers
--
-- The two helpers below collaborate to discharge the splice-endpoint
-- COLLIDER obligation of Case (i) on `π'`.  At the splice endpoints
-- `A' = prefix.length` and `C = prefix.length + σ_ij.length`, the
-- existing `refactor_IsCollider_comp_left` / `_comp_right` lemmas do
-- not apply (their hypotheses require *strict* inequality), so the
-- argument routes through a dedicated boundary lemma:
-- `refactor_IsCollider_comp_at_p_length_no_head_source` reduces the
-- boundary collider check to "the first step of the right walk
-- contributes a head at its source-end", which is False whenever the
-- right walk is `.nil` or starts with `.forwardE _`.
-- `replaceWalkCaseI_suffix_first_step_no_head_source` supplies the
-- second helper's hypothesis for the suffix walk's first step, using
-- the case-(i) trigger `π.replaceWalkCaseI j` (`j = π.length` or
-- `a_j = (v_j, v_{j+1}) ∈ G.E`).  Together with `σ_ij.IsDirectedWalk`,
-- which forces every step of `σ_ij` to be `.forwardE _`, these two
-- helpers cover both splice endpoints uniformly.

/-- The "first step's source-side arrowhead contribution" predicate on
    walks: `False` for `.nil` (no first step at all) and the head
    step's `HeadAtSource` for `.cons`.  Used as a hypothesis-
    shape for the boundary helper below to avoid universal
    quantification over the first step's identifier (which would
    require `cons.injEq`-style destructuring at every call site). -/
def Walk.firstStepHeadAtSource {G : CDMG Node} :
    ∀ {u v : Node}, Walk G u v → Prop
  | _, _, .nil _ _ => False
  | _, _, .cons _ s _ => s.HeadAtSource

/-- Source-cast invariance of `firstStepHeadAtSource`: the predicate's
    value depends only on the walk's structure (constructor tag and
    head step), not on the type-level source index, so casting the
    source via `h ▸` leaves the value unchanged.  Used to translate
    between `suffix_walk = hmid_j_eq ▸ (π.splitAt j hjn).2.2` and
    `(π.splitAt j hjn).2.2` at the call site of the
    `replaceWalkCaseI`-extraction helper below. -/
private lemma Walk.firstStepHeadAtSource_cast_source {G : CDMG Node}
    {v : Node} {u u' : Node} (h : u = u') (p : Walk G u v) :
    (h ▸ p).firstStepHeadAtSource = p.firstStepHeadAtSource := by
  subst h; rfl

/-- At position `p.length` on the composition `p.comp q`, the
    `IsCollider` check evaluates to `False` whenever the
    walk `q`'s first-step source-side arrowhead contribution is
    `False`.  The proof is by structural induction on `p`: in the
    base case `p = .nil`, `p.comp q = q` and the collider check at
    position 0 is `False` for every walk (covered by the
    `.nil`-branch and `.cons-.nil`-branch and `.cons-.cons-0` branches
    of `IsCollider`'s definition).  In the inductive step,
    the recursion descends one `cons`-cell on `p`; the boundary
    behaviour at `(.cons _ s (.nil _ _))` (length-1 `p`) is handled
    by the `.cons _ _ (.nil _ _), _` and `.cons _ s₀ (.cons _ s₁ _), 1`
    branches; for longer `p`, the recursion call on `p'` uses the
    `.cons _ _ (p_inner@(.cons _ _ _)), k + 2 => p_inner.IsCollider (k + 1)`
    branch to step from outer position `p.length` to inner position
    `p'.length`. -/
lemma Walk.refactor_IsCollider_comp_at_p_length_no_head_source
    {G : CDMG Node} {u v : Node} (p : Walk G u v) :
    ∀ {w : Node} (q : Walk G v w),
      ¬ q.firstStepHeadAtSource →
      ¬ (p.comp q).IsCollider p.length := by
  induction p with
  | nil _ _ =>
      intros w q hq h
      -- p.length = 0, p.comp q = q
      -- h : q.IsCollider 0 — False for every walk shape at position 0.
      cases q with
      | nil _ _ => exact h
      | cons _ _ q_rest =>
          cases q_rest with
          | nil _ _ => exact h
          | cons _ _ _ => exact h
  | cons mid s p' ih =>
      intros w q hq h
      cases p' with
      | nil _ _ =>
          -- p.length = 1. p.comp q = .cons mid s q.
          cases q with
          | nil _ _ =>
              -- (.cons mid s .nil).IsCollider 1 = False (the .cons _ _ (.nil _ _), _ branch).
              exact h
          | cons _ s_q q_rest =>
              -- (.cons mid s (.cons _ s_q q_rest)).IsCollider 1
              -- = s.HeadAtTarget ∧ s_q.HeadAtSource
              -- hq : ¬ s_q.HeadAtSource (via q.firstStepHeadAtSource = s_q.HeadAtSource)
              -- h.2 has the right shape after Lean's definitional reduction.
              exact hq h.2
      | cons mid' s' p'' =>
          -- p.length = p''.length + 2. Recursion via the
          -- .cons _ _ (q'@(.cons _ _ _)), k + 2 => q'.IsCollider (k + 1) branch.
          exact ih q hq h

/-- Connect the suffix walk's first step (when it exists) back to
    `π.replaceWalkCaseI j`: in Case (i), `(π.splitAt j hjn).2.2`'s
    `firstStepHeadAtSource` is `False`.  Concretely: either the suffix
    is `.nil` (when `j = π.length`, so `firstStepHeadAtSource` is
    `False` by definition), or the suffix is `.cons _ s_j _` with
    `s_j = .forwardE _` (when `j < π.length` and the case-(i)
    trigger `a_j ∈ G.E` fires; `(.forwardE _).HeadAtSource`
    evaluates to `False`).  Proof by structural induction on `π` with
    the position index `j` simultaneously consumed: the case-split on
    the head step's constructor at `j = 0` aligns the
    `replaceWalkCaseI` value with the head step's identity, and the
    recursion at `j = j' + 1` matches the `replaceWalkCaseI`'s
    descent through the tail. -/
private lemma Walk.replaceWalkCaseI_suffix_firstStepHeadAtSource_eq_False
    {G : CDMG Node} :
    ∀ {u w : Node} (π : Walk G u w) (j : ℕ) (hjn : j ≤ π.length),
      π.replaceWalkCaseI j →
      ¬ (π.splitAt j hjn).2.2.firstStepHeadAtSource := by
  intros u w π
  induction π with
  | nil v hv =>
      intros j hjn h_caseI
      cases j with
      | zero =>
          -- splitAt 0 on .nil v hv = ⟨v, .nil v hv, .nil v hv⟩
          -- .2.2 = .nil v hv. .firstStepHeadAtSource = False. ¬ False = True.
          intro h
          exact h
      | succ _ =>
          -- absurd: j+1 ≤ 0
          simp [Walk.length] at hjn
  | cons mid s_h p' ih =>
      intros j hjn h_caseI
      cases j with
      | zero =>
          -- splitAt 0 on .cons mid s_h p' = ⟨_, .nil _ _, .cons mid s_h p'⟩
          -- .2.2 = .cons mid s_h p'. .firstStepHeadAtSource = s_h.HeadAtSource.
          -- h_caseI : (.cons mid s_h p').replaceWalkCaseI 0 — value depends on s_h.
          intro h
          cases s_h with
          | forwardE _ =>
              -- (.forwardE _).HeadAtSource = False. h is False.
              exact h
          | backwardE _ =>
              -- h_caseI = False, contradicts.
              exact h_caseI.elim
          | bidir _ =>
              exact h_caseI.elim
      | succ j' =>
          -- splitAt (j'+1) on .cons mid s_h p' = ⟨..., ..., (p'.splitAt j' _).2.2⟩
          -- .2.2 = (p'.splitAt j' _).2.2 — recurse via IH.
          have hjn' : j' ≤ p'.length := by
            simp [Walk.length] at hjn
            omega
          -- h_caseI : (.cons mid s_h p').replaceWalkCaseI (j'+1) reduces to
          --   p'.replaceWalkCaseI j' under the j+1 clause of replaceWalkCaseI's pattern
          -- match, but the reduction is not automatic on abstract WalkStep `s_h`; cases
          -- on `s_h` makes the head step concrete so the pattern-match unfolds.
          cases s_h with
          | forwardE _ => exact ih j' hjn' h_caseI
          | backwardE _ => exact ih j' hjn' h_caseI
          | bidir _ => exact ih j' hjn' h_caseI

/-- Mirror of `Walk.replaceWalkCaseI_suffix_firstStepHeadAtSource_eq_False`:
    in Case (ii) (where `¬ π.replaceWalkCaseI j`), the suffix walk's first
    step has `HeadAtSource = True`.  Concretely: by `¬ replaceWalkCaseI j`,
    we have `j < π.length` AND `s_j` on `π` is `.backwardE _` or `.bidir _`,
    both of which have `HeadAtSource = True`.  Proof by structural
    induction on π with the position index j simultaneously consumed (same
    pattern as the existing eq_False helper). -/
private lemma Walk.not_replaceWalkCaseI_suffix_firstStepHeadAtSource
    {G : CDMG Node} :
    ∀ {u w : Node} (π : Walk G u w) (j : ℕ) (hjn : j ≤ π.length),
      ¬ π.replaceWalkCaseI j →
      (π.splitAt j hjn).2.2.firstStepHeadAtSource := by
  intros u w π
  induction π with
  | nil v hv =>
      intros j hjn h_ncaseI
      cases j with
      | zero =>
          -- π = .nil v hv, j = 0. π.replaceWalkCaseI 0 = True. h_ncaseI : ¬ True.
          exfalso; exact h_ncaseI trivial
      | succ _ =>
          simp [Walk.length] at hjn
  | cons mid s_h p' ih =>
      intros j hjn h_ncaseI
      cases j with
      | zero =>
          -- π = .cons mid s_h p', j = 0.
          -- π.replaceWalkCaseI 0 depends on s_h:
          --   .forwardE → True (h_ncaseI : ¬ True, contradiction).
          --   .backwardE → False (h_ncaseI : ¬ False = True, OK).
          --   .bidir → False (similar to .backwardE).
          -- Goal: (.cons mid s_h p').firstStepHeadAtSource = s_h.HeadAtSource.
          cases s_h with
          | forwardE _ =>
              exfalso; exact h_ncaseI trivial
          | backwardE _ =>
              trivial
          | bidir _ =>
              trivial
      | succ j' =>
          -- splitAt (j'+1) on .cons mid s_h p' = ⟨..., ..., (p'.splitAt j' _).2.2⟩.
          -- replaceWalkCaseI (j'+1) on .cons mid s_h p' = p'.replaceWalkCaseI j' (clause 6).
          have hjn' : j' ≤ p'.length := by
            simp [Walk.length] at hjn
            omega
          cases s_h with
          | forwardE _ => exact ih j' hjn' h_ncaseI
          | backwardE _ => exact ih j' hjn' h_ncaseI
          | bidir _ => exact ih j' hjn' h_ncaseI

/-- `π.replaceWalkCaseI π.length = True` for every walk `π`.  Proof by
    structural induction on π: at `.nil`, π.length = 0 and the base clause
    fires.  At `.cons mid s p'`, π.length = p'.length + 1, the j+1 clause
    fires and recurses to `p'.replaceWalkCaseI p'.length` = True (by IH). -/
private lemma Walk.replaceWalkCaseI_at_length {G : CDMG Node} :
    ∀ {u v : Node} (π : Walk G u v), π.replaceWalkCaseI π.length := by
  intros u v π
  induction π with
  | nil _ _ => trivial
  | cons _ s p' ih =>
      -- π.length = p'.length + 1. replaceWalkCaseI at p'.length + 1 reduces to
      -- p'.replaceWalkCaseI p'.length via clause 6. Need cases on s for the
      -- reduction to fire on abstract WalkStep.
      cases s with
      | forwardE _ => exact ih
      | backwardE _ => exact ih
      | bidir _ => exact ih

-- ## Case (ii) splice-boundary helpers
--
-- Mirror of the Case (i) splice-boundary infrastructure (lines 889-1043
-- above) for Case (ii), where σ_ij = σ_ji.reverse is a backward-directed
-- walk: every step is `.backwardE _`.  The asymmetric pair of
-- "head-at-source / head-at-target" predicates flips: at the splice
-- endpoint A' (= position i on π'), the right slot is σ_ij's first step
-- — a `.backwardE _` whose `HeadAtSource = True`.  So the boundary
-- collider check on π' at A' reduces to "(last step of prefix).HeadAtTarget",
-- and the discharge route diverges between sub-cases (a) and (b) of the
-- LN proof's case (ii) (tex `claim_3_27_proof_LabelRoman.tex` (II.c.iii)):
--   - Sub-case (a) (s_{i-1} on π is `.backwardE _`): h_col reduces to False.
--   - Sub-case (b) (s_{i-1} on π is `.forwardE _` or `.bidir _`): v_i IS a
--     collider on π'.  Discharge via the "first-collider" argument: trace
--     forward from position i on π through the segment [i, j], finding
--     the first collider at some k ∈ [i, j], and conclude v_i ∈ Anc(v_k)
--     ⊆ AncSet C via the directed forward chain.
-- At endpoint C (= position j on π'), σ_ij.length > 0 gives σ_ij's last
-- step = `.backwardE _` → `HeadAtTarget = False`.  So the
-- boundary collider check on π' at C is uniformly False (the discharge
-- bypasses h_col).
--
-- Helpers added below:
--   1. `Walk.lastStepHeadAtTarget`: dual of `firstStepHeadAtSource`,
--      defined as `False` for `.nil`, and as the head step's
--      `HeadAtTarget` for a length-1 `.cons _ _ .nil`, with
--      recursion through the tail for longer walks.
--   2. `Walk.lastStepHeadAtTarget_cast_target`: cast-invariance for
--      target-side type-rewrites; mirror of the existing
--      `firstStepHeadAtSource_cast_source` for source-side rewrites.
--   3. `Walk.lastStepHeadAtTarget_comp_cons_nil`: a length-1 right-
--      operand version: `(p.comp (.cons _ s (.nil _ _))).lastStepHeadAtTarget
--      = s.HeadAtTarget`.  Used in the first-collider recursion to
--      establish the new-prefix's "left-head" condition after appending a
--      `.forwardE` step.
--   4. `Walk.refactor_IsCollider_comp_at_p_length_no_head_target`: mirror
--      of the existing `_no_head_source` boundary helper, discharging the
--      C endpoint via `¬ p.lastStepHeadAtTarget`.
--   5. `Walk.refactor_IsCollider_comp_at_p_length_of_heads`: the positive
--      bridge `p.lastStepHeadAtTarget → q.firstStepHeadAtSource →
--      (p.comp q).IsCollider p.length`.  Used in the first-collider
--      recursion at the .backwardE / .bidir base case (where the head-source
--      condition fires and the splice endpoint becomes a collider on π').
--   6. `Walk.IsBackwardDirectedWalk.no_lastStepHeadAtTarget`: discharger
--      for the C endpoint's hypothesis input: a backward-directed walk
--      of positive length has its last step `.backwardE _`, whose
--      `HeadAtTarget = False`.
--   7. `Walk.firstColliderAncestor_comp`: the first-collider trace lemma.
--      Recursive on the suffix walk `q` (= sub-walk of π from position i
--      forward).  Given a "left-head at x = q's source on the composed
--      walk p.comp q" and a "right-head at position d on q", concludes
--      `x ∈ G.AncSet C` via the LN's first-collider chain.

/-- Dual of `Walk.firstStepHeadAtSource`: returns `s.HeadAtTarget`
    for the LAST step of a non-trivial walk, and `False` for `.nil`.  Used
    as the "left-head at v_i on π" condition at the splice endpoint A' in
    Case (ii), and as the "no head at target" hypothesis for the C
    endpoint boundary helper. -/
def Walk.lastStepHeadAtTarget {G : CDMG Node} :
    ∀ {u v : Node}, Walk G u v → Prop
  | _, _, .nil _ _ => False
  | _, _, .cons _ s (.nil _ _) => s.HeadAtTarget
  | _, _, .cons _ _ p@(.cons _ _ _) => p.lastStepHeadAtTarget

/-- Target-cast invariance of `lastStepHeadAtTarget`: the predicate's
    value depends only on the walk's structure (constructor tag and last
    step), not on the type-level target index, so casting the target via
    `h ▸` leaves the value unchanged.  Mirror of
    `firstStepHeadAtSource_cast_source`. -/
private lemma Walk.lastStepHeadAtTarget_cast_target {G : CDMG Node}
    {u : Node} {v v' : Node} (h : v = v') (p : Walk G u v) :
    (h ▸ p).lastStepHeadAtTarget = p.lastStepHeadAtTarget := by
  subst h; rfl

/-- A length-1 right-operand version of `Walk.lastStepHeadAtTarget` under
    composition: when the right operand is a length-1 walk `.cons w s (.nil w hw)`,
    the last step of `p.comp (...)` is `s`, so `lastStepHeadAtTarget`
    evaluates to `s.HeadAtTarget`.  Proof by induction on `p`.
    Used in the `.forwardE` recursive branch of
    `firstColliderAncestor_comp` to establish the new-prefix's
    "left-head" condition after appending a `.forwardE` step. -/
private lemma Walk.lastStepHeadAtTarget_comp_cons_nil {G : CDMG Node}
    {u v : Node} (p : Walk G u v) :
    ∀ {w : Node} (s : WalkStep G v w) (hw : w ∈ G),
      (p.comp (Walk.cons w s (Walk.nil w hw))).lastStepHeadAtTarget
        = s.HeadAtTarget := by
  induction p with
  | nil _ _ =>
      -- (.nil).comp (.cons w s (.nil w hw)) = .cons w s (.nil w hw).
      -- lastStepHeadAtTarget on .cons _ s (.nil _ _) = s.HeadAtTarget.
      intros w s hw
      simp only [Walk.comp, Walk.lastStepHeadAtTarget]
  | cons _ _ p' ih =>
      intros w s hw
      cases p' with
      | nil _ _ =>
          -- p = .cons _ _ .nil. (.cons _ _ .nil).comp q = .cons _ _ q where q = .cons w s (.nil w hw).
          -- So result = .cons _ _ (.cons w s (.nil w hw)). Outer matches clause 3 → inner.
          -- Inner = .cons w s (.nil w hw) matches clause 2 → s.HeadAtTarget.
          simp only [Walk.comp, Walk.lastStepHeadAtTarget]
      | cons _ _ _ =>
          -- p = .cons _ _ (.cons _ _ _). Outer comp = .cons _ _ ((.cons _ _ _).comp q).
          -- Outer matches clause 3 → ((.cons _ _ _).comp q).lastStepHeadAtTarget.
          -- ((.cons _ _ _).comp q) = .cons _ _ (...comp q), so it's a .cons _ _ _.
          -- So .lastStepHeadAtTarget = (rest).lastStepHeadAtTarget, given by ih.
          simp only [Walk.comp, Walk.lastStepHeadAtTarget]
          exact ih s hw

/-- At position `p.length` on the composition `p.comp q`, the
    `IsCollider` check evaluates to `False` whenever the walk
    `p`'s last-step target-side arrowhead contribution is `False`.
    Mirror of `refactor_IsCollider_comp_at_p_length_no_head_source` (which
    handles the right-operand head-source side).  Proof by induction on
    `p`: at `p = .nil`, `p.length = 0` and the collider check at 0 is
    uniformly `False`; at `p = .cons _ s .nil` (length 1), the collider
    check at 1 is either `False` (when `q = .nil`) or
    `s.HeadAtTarget ∧ ...`, conjunction whose first conjunct
    contradicts the hypothesis; at longer `p`, the recursion descends one
    cons-cell. -/
lemma Walk.refactor_IsCollider_comp_at_p_length_no_head_target
    {G : CDMG Node} {u v : Node} (p : Walk G u v) :
    ∀ {w : Node} (q : Walk G v w),
      ¬ p.lastStepHeadAtTarget →
      ¬ (p.comp q).IsCollider p.length := by
  induction p with
  | nil _ _ =>
      intros w q _ h
      -- p.length = 0, p.comp q = q. IsCollider q 0 = False for any q.
      cases q with
      | nil _ _ => exact h
      | cons _ _ q_rest =>
          cases q_rest with
          | nil _ _ => exact h
          | cons _ _ _ => exact h
  | cons mid s p' ih =>
      intros w q hp h
      cases p' with
      | nil _ _ =>
          -- p = .cons mid s .nil. p.length = 1. p.lastStepHeadAtTarget = s.HeadAtTarget.
          -- hp : ¬ s.HeadAtTarget (after definitional unfolding).
          cases q with
          | nil _ _ => exact h
          | cons _ s_q _ =>
              -- (.cons mid s .nil).comp (.cons _ s_q _) = .cons mid s (.cons _ s_q _).
              -- IsCollider 1 = s.HeadAtTarget ∧ s_q.HeadAtSource.
              -- h.1 : s.HeadAtTarget. Contradiction with hp.
              simp only [Walk.lastStepHeadAtTarget] at hp
              exact hp h.1
      | cons mid' s' p'' =>
          -- p = .cons mid s (.cons mid' s' p''). p.length = p''.length + 2.
          -- p.lastStepHeadAtTarget = (.cons mid' s' p'').lastStepHeadAtTarget = p'.lastStepHeadAtTarget.
          -- p.comp q = .cons mid s (p'.comp q). IsCollider at p.length recurses to
          -- (p'.comp q).IsCollider p'.length.
          simp only [Walk.lastStepHeadAtTarget] at hp
          exact ih q hp h

/-- Positive bridge: at position `p.length` on the composition `p.comp q`,
    the `IsCollider` check evaluates to `True` whenever both
    `p`'s last-step target-side arrowhead AND `q`'s first-step source-side
    arrowhead are `True`.  Mirror of the negative
    `_no_head_source` / `_no_head_target` helpers.  Proof by induction on
    `p`: at `p = .nil`, `p.lastStepHeadAtTarget = False`, so the hypothesis
    is vacuous; at `p = .cons _ s .nil` (length 1), the collider check at 1
    is exactly `s.HeadAtTarget ∧ q_head.HeadAtSource`,
    matching the hypothesis; at longer `p`, recursion descends one
    cons-cell.  Used in the `.backwardE` / `.bidir` base case of
    `firstColliderAncestor_comp` to discharge the splice-endpoint collider
    obligation directly via `hπ.1`. -/
lemma Walk.refactor_IsCollider_comp_at_p_length_of_heads
    {G : CDMG Node} {u v : Node} (p : Walk G u v) :
    ∀ {w : Node} (q : Walk G v w),
      p.lastStepHeadAtTarget →
      q.firstStepHeadAtSource →
      (p.comp q).IsCollider p.length := by
  induction p with
  | nil _ _ =>
      intros w q hp _
      -- p.lastStepHeadAtTarget = False (by def for .nil), contradiction.
      simp only [Walk.lastStepHeadAtTarget] at hp
  | cons mid s p' ih =>
      intros w q hp hq
      cases p' with
      | nil _ _ =>
          -- p = .cons mid s .nil. p.length = 1. p.lastStepHeadAtTarget = s.HeadAtTarget.
          -- hp : s.HeadAtTarget.
          simp only [Walk.lastStepHeadAtTarget] at hp
          cases q with
          | nil _ _ =>
              -- q.firstStepHeadAtSource = False (by def for .nil). Contradiction.
              simp only [Walk.firstStepHeadAtSource] at hq
          | cons _ s_q _ =>
              -- (.cons mid s .nil).comp (.cons _ s_q _) = .cons mid s (.cons _ s_q _).
              -- IsCollider 1 = s.HeadAtTarget ∧ s_q.HeadAtSource.
              -- ⟨hp, hq⟩.
              exact ⟨hp, hq⟩
      | cons mid' s' p'' =>
          -- p = .cons mid s (.cons mid' s' p''). p.length = p''.length + 2.
          -- p.lastStepHeadAtTarget = (.cons mid' s' p'').lastStepHeadAtTarget = p'.lastStepHeadAtTarget.
          -- p.comp q = .cons mid s (p'.comp q). IsCollider at p.length recurses to
          -- (p'.comp q).IsCollider p'.length.
          simp only [Walk.lastStepHeadAtTarget] at hp
          exact ih q hp hq

/-- A backward-directed walk of positive length has its last step `.backwardE _`,
    whose `HeadAtTarget = False`.  Hence `lastStepHeadAtTarget`
    evaluates to `False`.  Mirror in spirit of
    `IsBackwardDirectedWalk.interior_not_collider`. -/
lemma Walk.IsBackwardDirectedWalk.no_lastStepHeadAtTarget {G : CDMG Node} :
    ∀ {u v : Node} (p : Walk G u v), p.IsBackwardDirectedWalk →
      0 < p.length → ¬ p.lastStepHeadAtTarget := by
  intros u v p
  induction p with
  | nil _ _ =>
      intros _ hpos
      simp [Walk.length] at hpos
  | cons _ s p' ih =>
      intros h hpos
      cases s with
      | forwardE _ => exact h.elim
      | backwardE _ =>
          have hp' : p'.IsBackwardDirectedWalk := h
          cases p' with
          | nil _ _ =>
              -- p = .cons _ (.backwardE _) .nil. lastStepHeadAtTarget = (.backwardE _).HeadAtTarget = False.
              intro h_target
              simp only [Walk.lastStepHeadAtTarget,
                WalkStep.HeadAtTarget] at h_target
          | cons mid' s' p'' =>
              -- p = .cons _ (.backwardE _) (.cons mid' s' p''). lastStepHeadAtTarget = (.cons mid' s' p'').lastStepHeadAtTarget.
              -- Apply IH to the tail .cons mid' s' p''.
              intro h_target
              simp only [Walk.lastStepHeadAtTarget] at h_target
              have hp'_pos : 0 < (Walk.cons mid' s' p'').length := by
                simp [Walk.length]
              exact ih hp' hp'_pos h_target
      | bidir _ => exact h.elim

-- ## BLOCKABLE-clause helpers
--
-- Three helpers used to discharge the BLOCKABLE clause of the Case (i)
-- σ-openness obligation:
--
-- 1. `IsDirectedWalk.no_HasBlockingLeftSlot`: a directed walk has every
--    step `.forwardE _`, but `HasBlockingLeftSlot k` requires the slot
--    `k - 1` step to be `.backwardE _`.  Hence `HasBlockingLeftSlot k`
--    is uniformly `False` on a directed walk.
--
-- 2. `no_HasBlockingRightSlot_of_all_in_SCC`: a walk whose every vertex
--    lies in a common SCC `G.Sc z` has no `HasBlockingRightSlot` at any
--    position.  Reason: `HasBlockingRightSlot k` requires the slot-`k`
--    step to be `.forwardE _ : WalkStep G u v` with `v ∉ G.Sc u`.  But
--    both `u` (= walk vertex at position `k`) and `v` (= walk vertex at
--    position `k + 1`) lie in `G.Sc z`, so by `Sc_eq_of_mem_Sc` we have
--    `G.Sc u = G.Sc z`, hence `v ∈ G.Sc u`, contradicting the blocking
--    criterion.
--
-- 3. `IsDirectedWalk.interior_not_blockable`: combining the two above
--    with `interior_not_collider`, every strict-interior position of a
--    directed walk whose vertices lie in a shared SCC is *not* a
--    `IsBlockableNonCollider`.  This is the Region-B vacuous
--    discharger of the BLOCKABLE clause, mirroring the COLLIDER
--    clause's `interior_not_collider` Region-B discharger.

lemma Walk.IsDirectedWalk.no_HasBlockingLeftSlot {G : CDMG Node} :
    ∀ {u v : Node} (p : Walk G u v), p.IsDirectedWalk →
      ∀ (k : ℕ), ¬ p.HasBlockingLeftSlot k := by
  intros u v p
  induction p with
  | nil _ _ =>
      intros _ k h
      cases k with
      | zero => exact h.elim
      | succ _ => exact h.elim
  | cons mid s p' ih =>
      intros h_dir k h
      cases s with
      | forwardE _ =>
          have hp' : p'.IsDirectedWalk := h_dir
          match k with
          | 0 => exact h.elim
          | 1 => exact h.elim
          | k' + 2 => exact ih hp' (k' + 1) h
      | backwardE _ => exact h_dir.elim
      | bidir _ => exact h_dir.elim

lemma Walk.no_HasBlockingRightSlot_of_all_in_SCC {G : CDMG Node}
    {z : Node} :
    ∀ {u v : Node} (p : Walk G u v),
      (∀ x ∈ p.vertices, x ∈ G.Sc z) →
      ∀ (k : ℕ), ¬ p.HasBlockingRightSlot k
  | _, _, .nil _ _, _, k, h => by
      cases k with
      | zero => exact h.elim
      | succ _ => exact h.elim
  | u, _, .cons mid (.forwardE _) p', hp_SCC, 0, h => by
      -- h : ¬ mid ∈ G.Sc u (the `.forwardE _, 0` branch of
      -- `HasBlockingRightSlot` checks `v ∉ G.Sc u` with v = mid, u = source).
      have h_u : u ∈ G.Sc z := by
        apply hp_SCC
        show u ∈ u :: p'.vertices
        exact List.mem_cons.mpr (Or.inl rfl)
      have h_mid_in_p' : mid ∈ p'.vertices := by
        cases p' with
        | nil _ _ => exact List.mem_singleton.mpr rfl
        | cons _ _ _ => exact List.mem_cons.mpr (Or.inl rfl)
      have h_mid : mid ∈ G.Sc z := by
        apply hp_SCC
        show mid ∈ u :: p'.vertices
        exact List.mem_cons.mpr (Or.inr h_mid_in_p')
      have h_mid_Sc_u : mid ∈ G.Sc u := by
        rw [Sc_eq_of_mem_Sc h_u]
        exact h_mid
      exact h h_mid_Sc_u
  | _, _, .cons _ (.backwardE _) _, _, 0, h => h.elim
  | _, _, .cons _ (.bidir _) _, _, 0, h => h.elim
  | u, _, .cons _ (.forwardE _) p', hp_SCC, k' + 1, h => by
      refine Walk.no_HasBlockingRightSlot_of_all_in_SCC (z := z) p' ?_ k' h
      intros x hx
      apply hp_SCC
      show x ∈ u :: p'.vertices
      exact List.mem_cons.mpr (Or.inr hx)
  | u, _, .cons _ (.backwardE _) p', hp_SCC, k' + 1, h => by
      refine Walk.no_HasBlockingRightSlot_of_all_in_SCC (z := z) p' ?_ k' h
      intros x hx
      apply hp_SCC
      show x ∈ u :: p'.vertices
      exact List.mem_cons.mpr (Or.inr hx)
  | u, _, .cons _ (.bidir _) p', hp_SCC, k' + 1, h => by
      refine Walk.no_HasBlockingRightSlot_of_all_in_SCC (z := z) p' ?_ k' h
      intros x hx
      apply hp_SCC
      show x ∈ u :: p'.vertices
      exact List.mem_cons.mpr (Or.inr hx)

lemma Walk.IsDirectedWalk.interior_not_blockable {G : CDMG Node}
    {z : Node} {u v : Node} (p : Walk G u v) (hp_dir : p.IsDirectedWalk)
    (hp_SCC : ∀ x ∈ p.vertices, x ∈ G.Sc z) :
    ∀ (k : ℕ), 1 ≤ k → k < p.length →
      ¬ p.IsBlockableNonCollider k := by
  intros k hk1 hk2 h
  obtain ⟨_, h_disj⟩ := h
  rcases h_disj with hk_eq | hk_eq | h_blkleft | h_blkright
  · omega
  · omega
  · exact Walk.IsDirectedWalk.no_HasBlockingLeftSlot p hp_dir k h_blkleft
  · exact Walk.no_HasBlockingRightSlot_of_all_in_SCC p hp_SCC k h_blkright

-- ## Case-(ii) BLOCKABLE-clause helpers
--
-- Mirrors of the Case (i) BLOCKABLE infrastructure above, adapted for
-- backward-directed walks (every step `.backwardE _`).  The asymmetry
-- between Case (i) and Case (ii) BLOCKABLE flips which disjunct of
-- `HasBlocking*Slot` is eliminated by direction vs by SCC:
--
-- - Case (i) (directed walks): `HasBlockingLeftSlot` requires a
--   `.backwardE _` slot — uniformly False on a directed walk (direction
--   argument).  `HasBlockingRightSlot` requires a `.forwardE _` slot —
--   can fire, eliminated by SCC argument.
-- - Case (ii) (backward-directed walks): `HasBlockingLeftSlot` requires
--   a `.backwardE _` slot — can fire, eliminated by SCC argument.
--   `HasBlockingRightSlot` requires a `.forwardE _` slot — uniformly
--   False on a backward-directed walk (direction argument).
--
-- Three helpers added:
--   1. `Walk.IsBackwardDirectedWalk.no_HasBlockingRightSlot`: mirror of
--      `IsDirectedWalk.no_HasBlockingLeftSlot`.
--   2. `Walk.no_HasBlockingLeftSlot_of_all_in_SCC`: mirror of
--      `no_HasBlockingRightSlot_of_all_in_SCC`.
--   3. `Walk.IsBackwardDirectedWalk.interior_not_blockable`: mirror of
--      `IsDirectedWalk.interior_not_blockable`, combining (1), (2), and
--      the existing `IsBackwardDirectedWalk.interior_not_collider`.

lemma Walk.IsBackwardDirectedWalk.no_HasBlockingRightSlot {G : CDMG Node} :
    ∀ {u v : Node} (p : Walk G u v), p.IsBackwardDirectedWalk →
      ∀ (k : ℕ), ¬ p.HasBlockingRightSlot k := by
  intros u v p
  induction p with
  | nil _ _ =>
      intros _ k h
      cases k with
      | zero => exact h.elim
      | succ _ => exact h.elim
  | cons mid s p' ih =>
      intros h_back k h
      cases s with
      | forwardE _ => exact h_back.elim
      | backwardE _ =>
          have hp' : p'.IsBackwardDirectedWalk := h_back
          match k with
          | 0 => exact h.elim
          | k' + 1 => exact ih hp' k' h
      | bidir _ => exact h_back.elim

lemma Walk.no_HasBlockingLeftSlot_of_all_in_SCC {G : CDMG Node}
    {z : Node} :
    ∀ {u v : Node} (p : Walk G u v),
      (∀ x ∈ p.vertices, x ∈ G.Sc z) →
      ∀ (k : ℕ), ¬ p.HasBlockingLeftSlot k
  | _, _, .nil _ _, _, k, h => by
      cases k with
      | zero => exact h.elim
      | succ _ => exact h.elim
  | _, _, .cons _ _ _, _, 0, h => h.elim
  | u, _, .cons mid (.backwardE _) p', hp_SCC, 1, h => by
      -- h : u ∉ G.Sc mid (from the `.backwardE _, 1` branch).
      have h_u : u ∈ G.Sc z := by
        apply hp_SCC
        show u ∈ u :: p'.vertices
        exact List.mem_cons.mpr (Or.inl rfl)
      have h_mid_in_p' : mid ∈ p'.vertices := by
        cases p' with
        | nil _ _ => exact List.mem_singleton.mpr rfl
        | cons _ _ _ => exact List.mem_cons.mpr (Or.inl rfl)
      have h_mid : mid ∈ G.Sc z := by
        apply hp_SCC
        show mid ∈ u :: p'.vertices
        exact List.mem_cons.mpr (Or.inr h_mid_in_p')
      have h_u_Sc_mid : u ∈ G.Sc mid := by
        rw [Sc_eq_of_mem_Sc h_mid]
        exact h_u
      exact h h_u_Sc_mid
  | _, _, .cons _ (.forwardE _) _, _, 1, h => h.elim
  | _, _, .cons _ (.bidir _) _, _, 1, h => h.elim
  | u, _, .cons _ _ p', hp_SCC, k' + 2, h => by
      refine Walk.no_HasBlockingLeftSlot_of_all_in_SCC (z := z) p' ?_ (k' + 1) h
      intros x hx
      apply hp_SCC
      show x ∈ u :: p'.vertices
      exact List.mem_cons.mpr (Or.inr hx)

lemma Walk.IsBackwardDirectedWalk.interior_not_blockable {G : CDMG Node}
    {z : Node} {u v : Node} (p : Walk G u v) (hp_back : p.IsBackwardDirectedWalk)
    (hp_SCC : ∀ x ∈ p.vertices, x ∈ G.Sc z) :
    ∀ (k : ℕ), 1 ≤ k → k < p.length →
      ¬ p.IsBlockableNonCollider k := by
  intros k hk1 hk2 h
  obtain ⟨_, h_disj⟩ := h
  rcases h_disj with hk_eq | hk_eq | h_blkleft | h_blkright
  · omega
  · omega
  · exact Walk.no_HasBlockingLeftSlot_of_all_in_SCC p hp_SCC k h_blkleft
  · exact Walk.IsBackwardDirectedWalk.no_HasBlockingRightSlot p hp_back k h_blkright

-- End-position non-collider helpers: any walk is a non-collider at
-- position 0 and at position `p.length`, irrespective of the
-- WalkStep tags.  Used in the splice-endpoint cases of the BLOCKABLE
-- clause to build `π.IsBlockableNonCollider` witnesses at
-- position 0 (when `i = 0`) or position `π.length` (when
-- `j = π.length`) without needing to inspect π's local pattern there.

lemma Walk.refactor_IsCollider_zero_eq_False {G : CDMG Node} :
    ∀ {u v : Node} (p : Walk G u v), ¬ p.IsCollider 0
  | _, _, .nil _ _ => fun h => h
  | _, _, .cons _ _ (.nil _ _) => fun h => h
  | _, _, .cons _ _ (.cons _ _ _) => fun h => h

lemma Walk.refactor_IsCollider_length_eq_False {G : CDMG Node} :
    ∀ {u v : Node} (p : Walk G u v), ¬ p.IsCollider p.length := by
  intros u v p
  induction p with
  | nil _ _ => exact fun h => h
  | cons mid s p' ih =>
      intro h
      cases p' with
      | nil _ _ => exact h
      | cons mid' s' p'' => exact ih h

-- Position-0 and position-`p.length` vertex extraction: the first
-- vertex of a walk is always its source, the last is always its target.
-- Used in the splice-endpoint BLOCKABLE clauses to identify `vk` at the
-- end-positions.

lemma Walk.vertices_zero_eq_source {G : CDMG Node} :
    ∀ {u v : Node} (p : Walk G u v), p.vertices[0]? = some u
  | _, _, .nil _ _ => rfl
  | _, _, .cons _ _ _ => rfl

lemma Walk.vertices_length_eq_target {G : CDMG Node} :
    ∀ {u v : Node} (p : Walk G u v), p.vertices[p.length]? = some v := by
  intros u v p
  induction p with
  | nil _ _ => rfl
  | cons mid s p' ih =>
      show (Walk.cons mid s p').vertices[(Walk.cons mid s p').length]? = some _
      change (_ :: p'.vertices)[p'.length + 1]? = _
      change p'.vertices[p'.length]? = _
      exact ih

/-- At position `p.length` on `p.comp q`, the vertex is the midpoint
    `v` (the source of `q`, the target of `p`).  Used in the splice-
    endpoint cases to identify the merged vertex. -/
lemma Walk.vertices_comp_at_left_length {G : CDMG Node} :
    ∀ {u v w : Node} (p : Walk G u v) (q : Walk G v w),
      (p.comp q).vertices[p.length]? = some v := by
  intros u v w p q
  rw [Walk.vertices_comp]
  have hp_len : p.vertices.dropLast.length = p.length := by
    rw [List.length_dropLast, Walk.vertices_length]; omega
  rw [List.getElem?_append_right (Nat.le_of_eq hp_len), hp_len, Nat.sub_self]
  exact Walk.vertices_zero_eq_source q

/-- More general position-shift on a composition: at position
    `p.length + k` on `p.comp q`, the vertex equals `q.vertices[k]?`. -/
lemma Walk.vertices_comp_right_shift {G : CDMG Node} :
    ∀ {u v w : Node} (p : Walk G u v) (q : Walk G v w) (k : ℕ),
      (p.comp q).vertices[p.length + k]? = q.vertices[k]? := by
  intros u v w p q k
  rw [Walk.vertices_comp]
  have h_drop_len : p.vertices.dropLast.length = p.length := by
    rw [List.length_dropLast, Walk.vertices_length]; omega
  have h_le : p.vertices.dropLast.length ≤ p.length + k := by omega
  rw [List.getElem?_append_right h_le, h_drop_len, Nat.add_sub_cancel_left]

-- Side-aware blockable-slot helpers: HasBlockingLeftSlot k forces the
-- slot-(k-1) step to be `.backwardE _` (which has
-- `HeadAtTarget = False`), so the position cannot be a
-- side-aware collider.  Symmetrically, HasBlockingRightSlot k forces
-- the slot-k step to be `.forwardE _` (which has
-- `HeadAtSource = False`), again ruling out a collider at
-- position k.

private lemma Walk.HasBlockingLeftSlot.not_refactor_IsCollider {G : CDMG Node} :
    ∀ {u v : Node} (p : Walk G u v) (k : ℕ),
      p.HasBlockingLeftSlot k → ¬ p.IsCollider k := by
  intros u v p
  induction p with
  | nil _ _ =>
      intros k h_blk
      cases k <;> exact h_blk.elim
  | cons mid s p' ih =>
      intros k h_blk h_coll
      match k with
      | 0 => exact h_blk.elim
      | 1 =>
          cases p' with
          | nil _ _ => exact h_coll
          | cons _ s' _ =>
              cases s with
              | forwardE _ => exact h_blk.elim
              | backwardE _ =>
                  obtain ⟨h_left, _⟩ := h_coll
                  exact h_left
              | bidir _ => exact h_blk.elim
      | k' + 2 =>
          cases p' with
          | nil _ _ => exact h_coll
          | cons _ _ _ => exact ih _ h_blk h_coll

private lemma Walk.HasBlockingRightSlot.not_refactor_IsCollider {G : CDMG Node} :
    ∀ {u v : Node} (p : Walk G u v) (k : ℕ),
      p.HasBlockingRightSlot k → ¬ p.IsCollider k := by
  intros u v p
  induction p with
  | nil _ _ =>
      intros k h_blk
      cases k <;> exact h_blk.elim
  | cons mid s p' ih =>
      intros k h_blk h_coll
      match k with
      | 0 =>
          cases p' with
          | nil _ _ => exact h_coll
          | cons _ _ _ => exact h_coll
      | k' + 1 =>
          cases p' with
          | nil _ _ => exact h_coll
          | cons _ s' p'' =>
              -- Force one step of unfolding through the def's last clause
              -- so h_blk becomes a predicate on the inner cons-walk.
              -- `change` doesn't reduce because the outer step `s` is
              -- abstract — clauses 2..4 are not provably non-firing without
              -- case-splitting on `s`.  Case on `s` first to enable reduction.
              cases s with
              | forwardE _ =>
                  change (Walk.cons _ s' p'').HasBlockingRightSlot k' at h_blk
                  match k' with
                  | 0 =>
                      cases s' with
                      | forwardE _ =>
                          obtain ⟨_, h_right⟩ := h_coll
                          exact h_right
                      | backwardE _ => change False at h_blk; exact h_blk
                      | bidir _ => change False at h_blk; exact h_blk
                  | k'' + 1 => exact ih _ h_blk h_coll
              | backwardE _ =>
                  change (Walk.cons _ s' p'').HasBlockingRightSlot k' at h_blk
                  match k' with
                  | 0 =>
                      cases s' with
                      | forwardE _ =>
                          obtain ⟨_, h_right⟩ := h_coll
                          exact h_right
                      | backwardE _ => change False at h_blk; exact h_blk
                      | bidir _ => change False at h_blk; exact h_blk
                  | k'' + 1 => exact ih _ h_blk h_coll
              | bidir _ =>
                  change (Walk.cons _ s' p'').HasBlockingRightSlot k' at h_blk
                  match k' with
                  | 0 =>
                      cases s' with
                      | forwardE _ =>
                          obtain ⟨_, h_right⟩ := h_coll
                          exact h_right
                      | backwardE _ => change False at h_blk; exact h_blk
                      | bidir _ => change False at h_blk; exact h_blk
                  | k'' + 1 => exact ih _ h_blk h_coll

-- ## Inline claim_3_21: unblockable non-collider ⇒ σ-open at that position

/-- The walk-level inline formulation of `claim_3_21`: if position `k`
    on `p` is an unblockable non-collider and `p.vertices[k]? = some vk`,
    then neither σ-open obligation fires at `k` on `p` — the position is
    automatically σ-open regardless of `C`. -/
private lemma Walk.unblockable_imp_sigma_open_at {G : CDMG Node}
    {u v : Node} (p : Walk G u v) (k : ℕ) (vk : Node)
    (h_lookup : p.vertices[k]? = some vk)
    (h_unblockable : p.IsUnblockableNonCollider k)
    (C : Set Node) :
    -- Not a collider, so the collider-clause is vacuous.
    -- Not blockable, so the blockable-clause is vacuous.
    (p.IsCollider k → vk ∈ G.AncSet C) ∧
    (p.IsBlockableNonCollider k → vk ∉ C) := by
  refine ⟨?_, ?_⟩
  · intro h_coll
    obtain ⟨h_nc, _⟩ := h_unblockable
    exact absurd h_coll h_nc.2
  · intro h_blockable
    obtain ⟨_, h_not_blockable⟩ := h_unblockable
    exact absurd h_blockable h_not_blockable

-- ## First-collider trace helper for Case (ii) splice endpoint A'
--
-- See `tex/claim_3_27_proof_LabelRoman.tex` (II.c.iii) sub-case (b) for
-- the LN proof's first-collider argument.  Idea: starting at position
-- i on π with a "left-head" (HeadAtTarget(s_{i-1}) = True), trace
-- forward until we hit either a collider (where HeadAtSource(s_l) is
-- also True) or reach position j (Case (ii) trigger: HeadAtSource(s_j)
-- = True).  Either way, we find a collider position k ∈ [i, j], and
-- v_i has a directed walk to v_k (entirely .forwardE steps).
-- σ-openness of π at v_k gives v_k ∈ AncSet C, and v_i ∈ Anc(v_k) ⊆
-- AncSet C.

/-- First-collider trace lemma for the Case (ii) splice endpoint A'.

    Given a `σ-open` composed walk `p.comp q` (where `p` is the prefix up
    to position `i` on the original walk π, and `q` is the suffix from
    position `i`), and:
    - `p.lastStepHeadAtTarget` = True (the "left-head at x = q's source"
      on the composed walk, equivalently HeadAtTarget of the step at slot
      i-1 on π = True);
    - At some position `d` on `q` with `d < q.length`, the head-at-source
      condition fires (equivalently, HeadAtSource of the step at slot
      `i + d` on π = True);

    conclude `x ∈ G.AncSet C`, where `x` is the source of `q` (= vertex at
    position i on π).

    Proof: structural recursion on `q`.  At each step, look at `q`'s head
    step:
    - If `q = .nil`: vacuous (d < 0 impossible).
    - If `q.head = .backwardE _` or `.bidir _`: HeadAtSource = True at
      position 0, so `q.firstStepHeadAtSource` fires.  Combined with
      `p.lastStepHeadAtTarget`, position `p.length` on `p.comp q` is a
      collider (via `refactor_IsCollider_comp_at_p_length_of_heads`).
      The vertex there is `x`.  By
      `(p.comp q).IsSigmaOpenGiven`'s collider clause,
      `x ∈ G.AncSet C`.
    - If `q.head = .forwardE h_E`: HeadAtSource = False, so the
      "right-head at position 0" fails.  But the directed edge
      `x → mid ∈ G.E` gives `x ∈ G.Anc(mid)`.  Recurse on `q'` (the
      tail) with `d → d - 1` and a new prefix
      `p_new = p.comp (.cons mid (.forwardE h_E) .nil)`, whose
      `lastStepHeadAtTarget` is `True` (= HeadAtTarget(.forwardE)).
      IH gives `mid ∈ G.AncSet C`.  Transitivity of `Anc` (via
      `mem_Anc_trans`) gives `x ∈ G.AncSet C`. -/
private lemma Walk.firstColliderAncestor_comp
    {G : CDMG Node} {C : Set Node} {hC : C ⊆ ↑G.J ∪ ↑G.V} :
    ∀ {x w : Node} (q : Walk G x w) {u : Node} (p : Walk G u x),
      (p.comp q).IsSigmaOpenGiven C hC →
      p.lastStepHeadAtTarget →
      ∀ (d : ℕ) (hd : d < q.length),
        (q.splitAt d (Nat.le_of_lt hd)).2.2.firstStepHeadAtSource →
        x ∈ G.AncSet C
  | _, _, .nil _ _, _, _, _, _, _, hd, _ => by simp [Walk.length] at hd
  | x, _, .cons mid s q', u, p, hπ, h_left, d, hd, h_right => by
      -- Explicit binding of x via the cons pattern keeps the outer x in scope
      -- (instead of getting renamed to a fresh u✝ as it would under `induction`).
      cases s with
      | forwardE h_E =>
          -- q = .cons mid (.forwardE h_E) q'. h_E : (x, mid) ∈ G.E.
          match d, hd, h_right with
          | 0, _, h_right_at_0 =>
              -- (.cons _ (.forwardE _) q').splitAt 0 _.2.2 = .cons _ (.forwardE _) q'.
              -- firstStepHeadAtSource = (.forwardE _).HeadAtSource = False.
              simp only [Walk.splitAt, Walk.firstStepHeadAtSource,
                WalkStep.HeadAtSource] at h_right_at_0
          | d' + 1, hd', h_right_at_succ =>
              -- d = d' + 1. Recurse on q' with d'.
              have hmid_mem : mid ∈ G :=
                Finset.mem_union_right _ (G.hE_subset h_E).2
              -- Build one-step walk consisting of the .forwardE step.
              let one_step : Walk G x mid :=
                .cons mid (.forwardE h_E) (.nil mid hmid_mem)
              let new_prefix : Walk G u mid := p.comp one_step
              -- new_prefix.comp q' = p.comp (.cons _ (.forwardE _) q') by
              -- comp_assoc + .nil left-id.
              have h_comp_eq :
                  new_prefix.comp q' = p.comp (.cons mid (.forwardE h_E) q') := by
                change (p.comp one_step).comp q' =
                  p.comp (.cons mid (.forwardE h_E) q')
                rw [Walk.comp_assoc]
                rfl
              -- σ-open hypothesis transfers via h_comp_eq.
              have hπ_new : (new_prefix.comp q').IsSigmaOpenGiven C hC := by
                rw [h_comp_eq]; exact hπ
              -- new_prefix.lastStepHeadAtTarget = (.forwardE _).HeadAtTarget
              -- = True.
              have h_new_left : new_prefix.lastStepHeadAtTarget := by
                change (p.comp one_step).lastStepHeadAtTarget
                rw [Walk.lastStepHeadAtTarget_comp_cons_nil p (.forwardE h_E) hmid_mem]
                trivial
              -- Distance: d' < q'.length.
              have hd_q' : d' < q'.length := by
                simp [Walk.length] at hd'
                omega
              -- Right-head shift: (q.splitAt (d' + 1) _).2.2 = (q'.splitAt d' _).2.2
              -- by splitAt's .cons + succ clause.
              have h_right_q' :
                  (q'.splitAt d' (Nat.le_of_lt hd_q')).2.2.firstStepHeadAtSource :=
                h_right_at_succ
              -- Apply IH recursively to q' with new_prefix to get mid ∈ G.AncSet C.
              have h_mid_anc : mid ∈ G.AncSet C :=
                Walk.firstColliderAncestor_comp q' new_prefix hπ_new h_new_left
                  d' hd_q' h_right_q'
              -- Extract a witness c ∈ C with mid ∈ Anc(c).
              simp only [CDMG.AncSet, Set.mem_iUnion] at h_mid_anc
              obtain ⟨c, hc, h_mid_anc_c⟩ := h_mid_anc
              -- x ∈ Anc(mid) via the directed edge h_E.
              have hxG : x ∈ G := WalkStep.source_mem (G := G) (.forwardE h_E)
              have h_x_anc_mid : x ∈ G.Anc mid :=
                ⟨hxG, one_step, by
                  change one_step.IsDirectedWalk
                  change (Walk.cons mid (.forwardE h_E) (Walk.nil mid hmid_mem)).IsDirectedWalk
                  exact trivial⟩
              -- Anc-transitivity: x ∈ Anc(c).
              have h_x_anc_c : x ∈ G.Anc c := mem_Anc_trans h_x_anc_mid h_mid_anc_c
              -- x ∈ G.AncSet C via c ∈ C and x ∈ G.Anc c.
              simp only [CDMG.AncSet, Set.mem_iUnion]
              exact ⟨c, hc, h_x_anc_c⟩
      | backwardE h_E =>
          -- q = .cons _ (.backwardE _) q'. q.firstStepHeadAtSource = True.
          -- Use positive bridge to get (p.comp q).IsCollider p.length
          -- = True.  Then apply hπ.1 at p.length to conclude x ∈ AncSet C.
          have h_first_head :
              (Walk.cons mid (.backwardE h_E) q').firstStepHeadAtSource := by
            change (WalkStep.backwardE h_E).HeadAtSource
            trivial
          have h_coll :
              (p.comp (Walk.cons mid (.backwardE h_E) q')).IsCollider p.length :=
            Walk.refactor_IsCollider_comp_at_p_length_of_heads p _ h_left h_first_head
          have h_vert :
              (p.comp (Walk.cons mid (.backwardE h_E) q')).vertices[p.length]? = some x :=
            Walk.vertices_comp_at_left_length p _
          exact hπ.1 p.length x h_vert h_coll
      | bidir h_L =>
          -- q = .cons _ (.bidir _) q'. q.firstStepHeadAtSource = True.
          -- Same as .backwardE case.
          have h_first_head :
              (Walk.cons mid (.bidir h_L) q').firstStepHeadAtSource := by
            change (WalkStep.bidir h_L).HeadAtSource
            trivial
          have h_coll :
              (p.comp (Walk.cons mid (.bidir h_L) q')).IsCollider p.length :=
            Walk.refactor_IsCollider_comp_at_p_length_of_heads p _ h_left h_first_head
          have h_vert :
              (p.comp (Walk.cons mid (.bidir h_L) q')).vertices[p.length]? = some x :=
            Walk.vertices_comp_at_left_length p _
          exact hπ.1 p.length x h_vert h_coll

/-- Bridge: splitting `π` at `j` directly gives the same suffix walk's
    `firstStepHeadAtSource` as splitting at `i` first, then taking the
    `(j - i)`-th suffix of the resulting suffix walk.  Both expressions
    refer to the suffix of π starting at position `j`.  Proof by induction
    on π with the position indices simultaneously case-analyzed.  Uses
    `j - i` (rather than offset `d` with `i + d`) to avoid Nat.zero_add
    arithmetic complications in the i = 0 case. -/
private lemma Walk.firstStepHeadAtSource_splitAt_at_j {G : CDMG Node} :
    ∀ {u w : Node} (π : Walk G u w) (i : ℕ) (hi_le : i ≤ π.length)
      (j : ℕ) (hij : i ≤ j) (hj_le : j ≤ π.length),
      ((π.splitAt i hi_le).2.2.splitAt (j - i)
        (by rw [Walk.splitAt_length_right π i hi_le]; omega)).2.2.firstStepHeadAtSource =
      (π.splitAt j hj_le).2.2.firstStepHeadAtSource := by
  intros u w π
  induction π with
  | nil v hv =>
      intros i hi_le j hij hj_le
      have hi : i = 0 := by simp [Walk.length] at hi_le; exact hi_le
      have hj : j = 0 := by simp [Walk.length] at hj_le; exact hj_le
      subst hi; subst hj
      rfl
  | cons mid s p' ih =>
      intros i hi_le j hij hj_le
      cases i with
      | zero =>
          -- j - 0 = j (definitional). (cons mid s p').splitAt 0 = ⟨u, .nil, cons⟩.
          -- .snd.2 = cons mid s p'. So LHS = (cons mid s p').splitAt j _.snd.2 = RHS.
          rfl
      | succ i' =>
          cases j with
          | zero => exfalso; omega
          | succ j' =>
              have hi' : i' ≤ p'.length := by simp [Walk.length] at hi_le; omega
              have hij' : i' ≤ j' := by omega
              have hj' : j' ≤ p'.length := by simp [Walk.length] at hj_le; omega
              -- After cases reduces (Walk.cons mid s p').splitAt (n+1) via clause 4, the
              -- goal becomes about p'.splitAt at indices i' and j'. (j'+1) - (i'+1) = j' - i'
              -- definitionally via Nat.sub's recursive def, after enough reduction.
              -- Lean's elaborator should handle this in the cons + succ case.
              simp only [Walk.splitAt]
              -- After simp_only, the goal might still have (j'+1 - (i'+1)) syntactically.
              -- Use rfl on the inner splitAt via Subsingleton.elim of proof args + omega.
              have h_arith : j' + 1 - (i' + 1) = j' - i' := by omega
              have h_ih := ih i' hi' j' hij' hj'
              -- Bridge the goal to h_ih via cast/equation manipulation.
              -- The trick: define an explicit walk equality and use cast.
              suffices h : ∀ (n : ℕ) (hn : n ≤ ((p'.splitAt i' hi').snd.2).length),
                  n = j' - i' →
                  ((p'.splitAt i' hi').snd.2.splitAt n hn).snd.2.firstStepHeadAtSource =
                    (p'.splitAt j' hj').snd.2.firstStepHeadAtSource by
                exact h (j' + 1 - (i' + 1))
                  (by rw [Walk.splitAt_length_right]; omega) h_arith
              intros n hn h_n_eq
              subst h_n_eq
              exact h_ih

/-- Wrapper for `firstColliderAncestor_comp`: given a `σ-open` walk π
    with a "left-head" at position i (HeadAtTarget of step `s_{i-1}` on π
    is True) and a "right-head" at position j ≤ π.length - 1
    (HeadAtSource of step `s_j` on π is True), and i ≤ j, conclude the
    vertex at position `i` on π is in `G.AncSet C`.

    Internally, this splits π via `Walk.splitAt` at position i, applies
    `firstColliderAncestor_comp` to the prefix/suffix pair, bridges the
    right-head condition via `firstStepHeadAtSource_splitAt_offset`, and
    concludes via `splitAt_comp` that the comp equals π. -/
private lemma Walk.firstColliderAncestor_π_at_pos
    {G : CDMG Node} {C : Set Node} {hC : C ⊆ ↑G.J ∪ ↑G.V}
    {u w : Node} (π : Walk G u w) (hπ : π.IsSigmaOpenGiven C hC)
    (i : ℕ) (hi_le : i ≤ π.length)
    (h_left : (π.splitAt i hi_le).2.1.lastStepHeadAtTarget)
    (j : ℕ) (hij : i ≤ j) (hj_lt : j < π.length)
    (h_right : (π.splitAt j (Nat.le_of_lt hj_lt)).2.2.firstStepHeadAtSource) :
    (π.splitAt i hi_le).1 ∈ G.AncSet C := by
  -- Set up p, q from splitAt.
  -- p = (π.splitAt i hi_le).2.1 : Walk G u (π.splitAt i hi_le).1.
  -- q = (π.splitAt i hi_le).2.2 : Walk G (π.splitAt i hi_le).1 w.
  -- p.comp q = π (by splitAt_comp).
  have h_pq_eq_π : (π.splitAt i hi_le).2.1.comp (π.splitAt i hi_le).2.2 = π :=
    Walk.splitAt_comp π i hi_le
  have hπ_comp : ((π.splitAt i hi_le).2.1.comp (π.splitAt i hi_le).2.2).IsSigmaOpenGiven C hC := by
    rw [h_pq_eq_π]; exact hπ
  -- Right-head: bridge (π.splitAt j _).2.2.firstStepHeadAtSource to
  -- the (j-i)-th suffix of (π.splitAt i _).2.2.firstStepHeadAtSource via
  -- the bridge lemma.
  have hd : j - i < (π.splitAt i hi_le).2.2.length := by
    rw [Walk.splitAt_length_right π i hi_le]; omega
  have h_right_q :
      ((π.splitAt i hi_le).2.2.splitAt (j - i) (Nat.le_of_lt hd)).2.2.firstStepHeadAtSource := by
    rw [Walk.firstStepHeadAtSource_splitAt_at_j π i hi_le j hij (Nat.le_of_lt hj_lt)]
    exact h_right
  exact Walk.firstColliderAncestor_comp (π.splitAt i hi_le).2.2 (π.splitAt i hi_le).2.1
    hπ_comp h_left (j - i) hd h_right_q

-- ## Design choice — `replaceWalk` (the main theorem)
--
-- *Existential conclusion, not a function returning a specific
--   witness walk.*  The LN writes "if we replace $\dots$ then
--   $\dots$ is $\sigma$-open", which reads as: *there exists* a
--   replacement subwalk with the desired properties.  The existential
--   `∃ σ_ij, π', \dots` packages the LN's data directly, with the
--   four relevant properties bundled as conjuncts (direction-witness
--   on $\sigma_{ij}$ keyed by case (i)/(ii); SCC-containment of
--   every $\sigma_{ij}$ vertex; vertex-list factorisation of $\pi'$
--   as the splice; and σ-openness of $\pi'$).  A function returning
--   an opaque `Walk G u w` would force every downstream consumer to
--   either re-derive the splice structure from the function's body
--   or compute with a specific witness (whose exact shape depends on
--   which case (i)/(ii) fires).  The existential keeps the splice
--   structurally visible.
--
-- *Case discriminant in the existential is the implication-pair
--   shape `caseI → directed-witness ∧ minimality`, not a single
--   disjunction `directed ∨ reverse-directed`.*  Two reasons.  First,
--   it lets the proof discharge the two cases via the same
--   constructor on the existential's outer body: both implications
--   are vacuously true on the case the proof did not produce, so the
--   prover only needs to discharge *one* implication non-vacuously
--   (the case the LN's argument actually constructs).  Second, the
--   *minimality* (shortest-path) qualifier — required by the LN's
--   "shortest directed walk" prescription — is bundled with the
--   directedness conjunct at the matching side, mirroring the
--   canonical tex's statement: "Let $\sigma_{ij}$ be a shortest
--   directed walk from $v_i$ to $v_j$ in $G$".  An `∨`-encoding
--   would force a single `(direction ∧ minimality)` pair under each
--   disjunct, with the two pairs differing only in which-endpoint
--   the minimality bounds — the implication-pair shape keeps the two
--   bounds textually adjacent to their respective direction
--   witnesses.
--
-- *Wording-check subtlety `shortest_qualifier_unused_in_proof`
--   resolution.*  The working-phase wording-check flagged that the
--   LN's "shortest" qualifier on the replacement subwalk is not
--   used directly in the LN's body proof — the SCC-containment
--   conclusion and the "intermediate nodes are non-collider chains"
--   conclusion hold for *any* directed path $v_i \to v_j$ in $G$
--   (existence guaranteed by $v_i \in \Sc^G(v_j)$).  The Lean
--   signature still bundles the minimality conjunct
--   `(∀ τ, τ.IsDirectedWalk → σ_ij.length ≤ τ.length)` at the
--   matching side because (a) the canonical tex's statement
--   explicitly writes "Let $\sigma_{ij}$ be a *shortest* directed
--   walk", so dropping it would break LN-equivalence at the
--   statement level, and (b) downstream consumers may use the
--   minimality bound to discharge length-based termination /
--   well-founded recursion arguments (e.g.\ iterative shortening of
--   a walk).  The proof-phase worker may construct the witness by
--   any concrete shortest-walk extraction (e.g.\
--   `Nat.find`-based selection over the non-empty
--   length-set), since the minimality conjunct is *provable* for the
--   selected witness — the qualifier is statement-level discipline,
--   not a load-bearing proof step inside the LN's body argument.
--
-- *Vertex-list factorisation
--   `π'.vertices = (π.vertices.take (i + 1)).dropLast ++
--                   σ_ij.vertices ++ π.vertices.drop (j + 1)`
--   as the structural pinning of $\pi'$ to the splice.*  The LN's
--   "$\pi'$ is the concatenation of the prefix $\dots$ of $\pi$, the
--   replacement subwalk $\sigma_{ij}$, and the suffix $\dots$ of
--   $\pi$" is a structural assertion on the underlying vertex
--   sequence.  Encoding it as a `List Node` equality at the
--   `vertices` level (rather than via `Walk.comp` with explicit
--   prefix / suffix walk binders) collapses the splice constraint
--   into a single equation that the prover can `simp`/`rfl` against
--   without needing a `Walk.prefix` / `Walk.suffix` infrastructure
--   (which has no counterpart under the typed `WalkStep`).
--   The `dropLast` on the prefix is load-bearing: `π.vertices.take
--   (i + 1)` reads positions $0, \dots, i$ (length $i + 1$), and its
--   `dropLast` strips the duplicate $v_i$ that would otherwise be
--   appended to $\sigma_{ij}$'s opening $w_0 = v_i$.  Similarly,
--   `π.vertices.drop (j + 1)` reads positions $j + 1, \dots, n$,
--   stripping the duplicate $v_j$ from $\sigma_{ij}$'s closing
--   $w_m = v_j$.
--
-- *Why a `(σ_ij : Walk G v_i v_j)` binder of the typed walk shape,
--   not a separate `m : ℕ` + raw vertex list.*  The typed
--   `Walk G v_i v_j` automatically pins the endpoints by type, the
--   walk-constraint at every interior position by construction, and
--   the length by `σ_ij.length`.  Splitting the data into a raw
--   vertex list `(w_0, \dots, w_m)` plus per-position validity
--   side-conditions would force the consumer (and the prover) to
--   re-derive the walk-shape from scratch at every use.
--
-- *Handling of the length-$0$ $v_i = v_j$ corner (addition to the
--   LN).*  When $v_i = v_j$ the canonical tex's "Addition to the LN"
--   paragraph admits the length-$0$ trivial directed walk
--   $\sigma_{ij} = (v_i)$ as the shortest directed walk witness on
--   either side (case (i) or (ii)).  In Lean this is the witness
--   `Walk.nil v_i h_v_i_mem : Walk G v_i v_j` — admissible because
--   `Walk.nil` requires `h : v_i ∈ G`, which is supplied by the
--   `h_Sc : v_i ∈ G.Sc v_j ⊆ ↑(G.J ∪ G.V)` hypothesis.  The
--   direction-witness `(Walk.nil _ _).IsDirectedWalk` reduces to
--   `True` by the `.nil` branch of `IsDirectedWalk`
--   (`Walks.lean:942`); the minimality conjunct reduces to
--   `∀ τ, τ.IsDirectedWalk → 0 ≤ τ.length`, which is `Nat.zero_le _`;
--   the SCC-containment conjunct reduces to "$v_i \in G.Sc v_j$",
--   which is exactly `h_Sc`; and the vertex-list factorisation
--   collapses to a length-preserving equation at the `vertices`
--   level.  No separate carve-out is needed in the signature.
--
-- *Why the length-$0$ witness discharges BOTH case (i) and case (ii)
--   implications simultaneously.*  This is the *load-bearing* reason
--   the canonical tex's "Addition to the LN" paragraph admits the
--   length-$0$ trivial replacement as the shortest-directed-walk
--   witness on either side without a separate carve-out: the witness
--   `Walk.nil v_i h_v_i_mem` is reversal-fixed by the `.nil` branch
--   of `Walk.reverse` (`SigmaSeparationSymmetric.lean:168`,
--   `(Walk.nil w hw).reverse = .nil w hw`), so the case-(ii)
--   conjunct `σ_ij.reverse.IsDirectedWalk` reduces *also* to
--   `(Walk.nil _ _).IsDirectedWalk = True` — the same reduction as
--   the case-(i) conjunct.  Likewise, the case-(ii) minimality
--   conjunct `∀ τ : Walk G v_j v_i, τ.IsDirectedWalk → 0 ≤ τ.length`
--   reduces to `Nat.zero_le _`, identical to case-(i)'s.  Net effect:
--   on the length-$0$ branch, the implication-pair shape's two
--   implications discharge by the *same* underlying lemma instances,
--   so the prover does not need to decide which case actually fires
--   at $j$ — both implications hold non-vacuously.  This is the
--   in-Lean encoding of the canonical tex's claim that "Any positive-
--   length directed walk from $v_i$ to $v_i$ in $G$ has length $\ge
--   1$ and is therefore not shorter than the length-$0$ trivial
--   directed walk, so the trivial directed walk is unconditionally
--   the unique minimum" — the same minimum witness, evaluated either
--   directly or after `reverse`, suffices for both case-(i)'s
--   $v_i \to v_j$ direction and case-(ii)'s $v_j \to v_i$ direction.
--
-- *Wording-check subtlety
--   `vi_eq_vj_combined_node_open_not_verified` resolution.*  The
--   working-phase wording-check flagged the $v_i = v_j$ case as
--   under-verified: the proof in the LN dismisses it with one
--   sentence ("Note that this holds also when $v_i = v_j$"), and a
--   careful reader might worry that the merged node on $\pi'$ — whose
--   walk-neighbours are inherited as $v_{i-1}$ on the left (from
--   $v_i$'s left side on $\pi$) and $v_{j+1}$ on the right (from
--   $v_j$'s right side on $\pi$) — may lose evidence of $\sigma$-
--   openness if e.g.\ $v_i$ on $\pi$ was open at position $i$ as a
--   collider via $v_i \in \Anc^G(C)$, since the role at position $i$
--   may not survive once the right edge changes.  The canonical-tex
--   "Addition to the LN" paragraph handles this corner head-on: the
--   length-$0$ replacement produces a strictly *shorter* modified
--   walk $\pi'$ (the $j - i$ walk-steps between positions $i$ and $j$
--   are dropped entirely), so the merged position on $\pi'$ is a
--   *single* position with one local configuration, and its
--   $\sigma$-openness is to be verified directly from the inherited
--   $v_{i-1}, v_{j+1}$ neighbours and the LN's σ-blocking criteria —
--   not as a consolidation of pre-existing openness at two distinct
--   $\pi$-positions.  The Lean statement leaves the verification to
--   the proof phase via the trailing
--   `π'.IsSigmaOpenGiven C hC` conjunct of the existential;
--   no signature-level corner-case is needed because the length-$0$
--   trivial-replacement is admitted uniformly.
--
-- *Bound `hjn : j ≤ π.length` only; `i`'s upper bound comes
--   transitively from `hij : i < j`.*  The LN's "$i, j \in
--   \{0, \dots, n\}$ with $i < j$" gives $i < j \le n =
--   \pi.\text{length}$, so a single `hjn` is sufficient; the prover
--   derives `i ≤ π.length` from `hij` and `hjn` via transitivity.
--   The two vertex-lookup hypotheses `h_get_i / h_get_j` characterise
--   $v_i$ and $v_j$ at the matching positions; under `hjn` (and the
--   transitively-derived `i ≤ π.length`) both lookups are guaranteed
--   to succeed, so the `some`-form is the natural encoding.
--
-- *`(C : Set Node)` and `(hC : C ⊆ ↑G.J ∪ ↑G.V)` matching the
--   chapter-wide σ-blocking convention.*  Same convention as
--   `IsSigmaOpenGiven` (`SigmaBlockedWalks.lean`): `C` is
--   a `Set Node` (untruncated to
--   $J \cup V$) and the LN's "$C \subseteq J \cup V$" precondition
--   is propagated as the explicit `hC` hypothesis — which is what
--   `IsSigmaOpenGiven`'s signature itself takes.  The
--   `↑G.J ∪ ↑G.V` shape on the RHS is the
--   `Finset Node → Set Node` coercion form used throughout the
--   chapter (so the union is computed at the `Set` level after
--   coercion).
-- claim_3_27 -- start statement
theorem replaceWalk
    (G : CDMG Node) (C : Set Node) (hC : C ⊆ ↑G.J ∪ ↑G.V)
    {u w : Node} (π : Walk G u w)
    (hπ : π.IsSigmaOpenGiven C hC)
    {i j : ℕ} (hij : i < j) (hjn : j ≤ π.length)
    {v_i v_j : Node}
    (h_get_i : π.vertices[i]? = some v_i)
    (h_get_j : π.vertices[j]? = some v_j)
    (h_Sc : v_i ∈ G.Sc v_j) :
    ∃ (σ_ij : Walk G v_i v_j) (π' : Walk G u w),
      (π.replaceWalkCaseI j →
         σ_ij.IsDirectedWalk ∧
         (∀ τ : Walk G v_i v_j, τ.IsDirectedWalk → σ_ij.length ≤ τ.length)) ∧
      (¬ π.replaceWalkCaseI j →
         σ_ij.reverse.IsDirectedWalk ∧
         (∀ τ : Walk G v_j v_i, τ.IsDirectedWalk → σ_ij.reverse.length ≤ τ.length)) ∧
      (∀ x ∈ σ_ij.vertices, x ∈ G.Sc v_j) ∧
      π'.vertices = (π.vertices.take (i + 1)).dropLast ++ σ_ij.vertices ++
          π.vertices.drop (j + 1) ∧
      π'.IsSigmaOpenGiven C hC
-- claim_3_27 -- end statement
:= by
  -- # Preliminary facts
  have hi_le : i ≤ π.length := Nat.le_of_lt (Nat.lt_of_lt_of_le hij hjn)
  have hvi_mem : v_i ∈ G := mem_G_of_mem_Sc h_Sc
  have hvj_mem : v_j ∈ G := mem_G_of_mem_Sc (mem_Sc_symm h_Sc)
  -- # Extract prefix / suffix walks from π via `splitAt`, casting via
  --   the midpoint identities `hmid_i_eq` / `hmid_j_eq`.
  have hmid_i_eq : (π.splitAt i hi_le).1 = v_i := by
    have h := Walk.splitAt_mid_get π i hi_le
    rw [h_get_i] at h
    exact (Option.some.inj h).symm
  have hmid_j_eq : (π.splitAt j hjn).1 = v_j := by
    have h := Walk.splitAt_mid_get π j hjn
    rw [h_get_j] at h
    exact (Option.some.inj h).symm
  -- Build the prefix and suffix walks at the right types.  The
  -- type-level cast via `hmid_*_eq ▸ ...` is necessary because the
  -- `splitAt` result lives in an arbitrary `Σ'`-type and we need to
  -- coerce to the `Walk G u v_i` / `Walk G v_j w` types that match the
  -- existential's binder shape.
  let prefix_walk : Walk G u v_i := hmid_i_eq ▸ (π.splitAt i hi_le).2.1
  let suffix_walk : Walk G v_j w := hmid_j_eq ▸ (π.splitAt j hjn).2.2
  -- # Case split on `replaceWalkCaseI` to pick the σ_ij witness.
  by_cases h_caseI : π.replaceWalkCaseI j
  · -- ## Case (i): σ_ij = shortest directed walk from v_i to v_j
    have h_walk_exists : ∃ p : Walk G v_i v_j, p.IsDirectedWalk :=
      (mem_Anc_of_mem_Sc h_Sc).2
    -- Destructure via `obtain` (not `let`) so σ_ij is a free variable
    -- amenable to `cases σ_ij` in the splice-endpoint sub-proofs.
    obtain ⟨σ_ij, hσ_dir, hσ_min⟩ := Walk.shortestDirectedWalk h_walk_exists
    let π' : Walk G u w := prefix_walk.comp (σ_ij.comp suffix_walk)
    refine ⟨σ_ij, π', ?_, ?_, ?_, ?_, ?_⟩
    · -- Conjunct 1: caseI → directed + minimal
      intro _
      exact ⟨hσ_dir, hσ_min⟩
    · -- Conjunct 2: ¬caseI → vacuously true (contradicts h_caseI)
      intro h_not_caseI
      exact absurd h_caseI h_not_caseI
    · -- Conjunct 3: SCC containment of σ_ij.vertices
      intro x hx
      have h_anc_vj : x ∈ G.Anc v_j :=
        Walk.directed_vertex_mem_Anc σ_ij hσ_dir hx
      have h_desc_vi : x ∈ G.Desc v_i :=
        Walk.directed_vertex_mem_Desc σ_ij hσ_dir hx
      have h_vi_desc_vj : v_i ∈ G.Desc v_j := mem_Desc_of_mem_Sc h_Sc
      have h_desc_vj : x ∈ G.Desc v_j := mem_Desc_trans h_desc_vi h_vi_desc_vj
      exact ⟨h_anc_vj, h_desc_vj⟩
    · -- Conjunct 4: vertex equation
      have h_prefix_vertices : prefix_walk.vertices = π.vertices.take (i + 1) := by
        show (hmid_i_eq ▸ (π.splitAt i hi_le).2.1).vertices = π.vertices.take (i + 1)
        rw [Walk.vertices_cast_target hmid_i_eq]
        exact Walk.splitAt_vertices_left π i hi_le
      have h_suffix_vertices : suffix_walk.vertices = π.vertices.drop j := by
        show (hmid_j_eq ▸ (π.splitAt j hjn).2.2).vertices = π.vertices.drop j
        rw [Walk.vertices_cast_source hmid_j_eq]
        exact Walk.splitAt_vertices_right π j hjn
      have h_lt : j < π.vertices.length := by
        rw [Walk.vertices_length]; omega
      have h_get : π.vertices[j]'h_lt = v_j := by
        have h := h_get_j
        rw [List.getElem?_eq_getElem h_lt] at h
        exact Option.some.inj h
      have h_drop_j : π.vertices.drop j = v_j :: π.vertices.drop (j + 1) := by
        rw [← List.cons_getElem_drop_succ (h := h_lt), h_get]
      have h_ne : σ_ij.vertices ≠ [] := Walk.vertices_ne_nil σ_ij
      have h_σ_last : σ_ij.vertices.getLast h_ne = v_j :=
        Walk.last_vertex_eq_target σ_ij
      have h_σ_dropLast : σ_ij.vertices.dropLast ++ [v_j] = σ_ij.vertices := by
        conv_rhs => rw [← List.dropLast_append_getLast h_ne, h_σ_last]
      show (prefix_walk.comp (σ_ij.comp suffix_walk)).vertices = _
      rw [Walk.vertices_comp, Walk.vertices_comp,
          h_prefix_vertices, h_suffix_vertices, h_drop_j]
      -- LHS: (π.vertices.take (i+1)).dropLast ++ (σ_ij.vertices.dropLast ++ (v_j :: π.vertices.drop (j+1)))
      -- RHS: (π.vertices.take (i+1)).dropLast ++ σ_ij.vertices ++ π.vertices.drop (j+1)
      rw [show σ_ij.vertices.dropLast ++ (v_j :: π.vertices.drop (j + 1)) =
            (σ_ij.vertices.dropLast ++ [v_j]) ++ π.vertices.drop (j + 1) by
          simp [List.append_assoc]]
      rw [h_σ_dropLast, ← List.append_assoc]
    · -- Conjunct 5: σ-openness of π' (Case (i)).
      -- Decompose into the COLLIDER and BLOCKABLE clauses.
      refine ⟨?_, ?_⟩
      · -- COLLIDER clause
        intro k vk h_get h_col
        have h_prefix_len : prefix_walk.length = i := by
          show (hmid_i_eq ▸ (π.splitAt i hi_le).2.1).length = i
          rw [Walk.length_cast_target hmid_i_eq]
          exact Walk.splitAt_length_left π i hi_le
        by_cases hk_int_strict :
            prefix_walk.length < k ∧ k < prefix_walk.length + σ_ij.length
        · -- Region B (strict interior of σ_ij, vacuous via interior_not_collider)
          obtain ⟨hk_lo, hk_hi⟩ := hk_int_strict
          have h_iscoll_eq1 :
              (prefix_walk.comp (σ_ij.comp suffix_walk)).IsCollider k =
              (σ_ij.comp suffix_walk).IsCollider
                (k - prefix_walk.length) :=
            Walk.refactor_IsCollider_comp_right
              prefix_walk (σ_ij.comp suffix_walk) k hk_lo
          have hk' : k - prefix_walk.length < σ_ij.length := by omega
          have h_iscoll_eq2 :
              (σ_ij.comp suffix_walk).IsCollider
                (k - prefix_walk.length) =
              σ_ij.IsCollider (k - prefix_walk.length) :=
            Walk.refactor_IsCollider_comp_left σ_ij suffix_walk
              (k - prefix_walk.length) hk'
          rw [h_iscoll_eq1, h_iscoll_eq2] at h_col
          have hk1 : 1 ≤ k - prefix_walk.length := by omega
          have hk2 : k - prefix_walk.length < σ_ij.length := hk'
          exact absurd h_col
            (Walk.IsDirectedWalk.interior_not_collider σ_ij hσ_dir _ hk1 hk2)
        · -- Other regions: outer-left, outer-right, splice endpoints
          push_neg at hk_int_strict
          by_cases hk_d : prefix_walk.length + σ_ij.length < k
          · -- Region D (suffix interior, position-shift to π)
            have hk_lo : prefix_walk.length < k := by omega
            have h_eq1 :
                (prefix_walk.comp (σ_ij.comp suffix_walk)).IsCollider k =
                (σ_ij.comp suffix_walk).IsCollider
                  (k - prefix_walk.length) :=
              Walk.refactor_IsCollider_comp_right
                prefix_walk (σ_ij.comp suffix_walk) k hk_lo
            have hk_lo2 : σ_ij.length < k - prefix_walk.length := by omega
            have h_eq2 :
                (σ_ij.comp suffix_walk).IsCollider
                  (k - prefix_walk.length) =
                suffix_walk.IsCollider
                  (k - prefix_walk.length - σ_ij.length) :=
              Walk.refactor_IsCollider_comp_right σ_ij suffix_walk
                (k - prefix_walk.length) hk_lo2
            rw [h_eq1, h_eq2] at h_col
            have h_eq3 :
                suffix_walk.IsCollider
                  (k - prefix_walk.length - σ_ij.length) =
                (π.splitAt j hjn).2.2.IsCollider
                  (k - prefix_walk.length - σ_ij.length) := by
              show (hmid_j_eq ▸ (π.splitAt j hjn).2.2).IsCollider _ = _
              rw [Walk.refactor_IsCollider_cast_source hmid_j_eq]
            rw [h_eq3] at h_col
            have h_split_len : (π.splitAt j hjn).2.1.length = j :=
              Walk.splitAt_length_left π j hjn
            have hk_lo3 :
                (π.splitAt j hjn).2.1.length <
                  j + (k - prefix_walk.length - σ_ij.length) := by
              rw [h_split_len]; omega
            have h_eq4 :
                Walk.IsCollider
                    ((π.splitAt j hjn).2.1.comp (π.splitAt j hjn).2.2)
                  (j + (k - prefix_walk.length - σ_ij.length)) =
                Walk.IsCollider (π.splitAt j hjn).2.2
                  ((j + (k - prefix_walk.length - σ_ij.length)) -
                    (π.splitAt j hjn).2.1.length) :=
              Walk.refactor_IsCollider_comp_right
                (π.splitAt j hjn).2.1 (π.splitAt j hjn).2.2 _ hk_lo3
            rw [Walk.splitAt_comp π j hjn] at h_eq4
            rw [h_split_len] at h_eq4
            have h_arith : j + (k - prefix_walk.length - σ_ij.length) - j =
                          k - prefix_walk.length - σ_ij.length := by omega
            rw [h_arith] at h_eq4
            rw [← h_eq4] at h_col
            -- h_col : π.IsCollider (j + k - prefix.length - σ_ij.length)
            -- Derive vertex correspondence inline via π'.vertices computation.
            have h_prefix_v : prefix_walk.vertices = π.vertices.take (i + 1) := by
              show (hmid_i_eq ▸ (π.splitAt i hi_le).2.1).vertices = π.vertices.take (i + 1)
              rw [Walk.vertices_cast_target hmid_i_eq]
              exact Walk.splitAt_vertices_left π i hi_le
            have h_suffix_v : suffix_walk.vertices = π.vertices.drop j := by
              show (hmid_j_eq ▸ (π.splitAt j hjn).2.2).vertices = π.vertices.drop j
              rw [Walk.vertices_cast_source hmid_j_eq]
              exact Walk.splitAt_vertices_right π j hjn
            have h_π'_v_raw :
                (prefix_walk.comp (σ_ij.comp suffix_walk)).vertices =
                  prefix_walk.vertices.dropLast ++ σ_ij.vertices.dropLast ++
                    suffix_walk.vertices := by
              rw [Walk.vertices_comp, Walk.vertices_comp, ← List.append_assoc]
            rw [h_π'_v_raw, h_prefix_v, h_suffix_v] at h_get
            have h_take_len : π.vertices.length = π.length + 1 :=
              Walk.vertices_length π
            have h_σ_len : σ_ij.vertices.length = σ_ij.length + 1 :=
              Walk.vertices_length σ_ij
            have h_len_take : (π.vertices.take (i + 1)).dropLast.length = i := by
              rw [List.length_dropLast, List.length_take, h_take_len]
              omega
            have h_len_σ_dropLast : σ_ij.vertices.dropLast.length = σ_ij.length := by
              rw [List.length_dropLast, h_σ_len]
              omega
            have h_len_combined :
                ((π.vertices.take (i + 1)).dropLast ++ σ_ij.vertices.dropLast).length
                  = i + σ_ij.length := by
              rw [List.length_append, h_len_take, h_len_σ_dropLast]
            have h_k_combined :
                ((π.vertices.take (i + 1)).dropLast ++ σ_ij.vertices.dropLast).length
                  ≤ k := by
              rw [h_len_combined, ← h_prefix_len]; omega
            rw [List.getElem?_append_right h_k_combined, h_len_combined,
                List.getElem?_drop] at h_get
            have h_idx_eq :
                j + (k - (i + σ_ij.length)) =
                  j + (k - prefix_walk.length - σ_ij.length) := by
              rw [h_prefix_len]; omega
            rw [h_idx_eq] at h_get
            exact hπ.1 _ vk h_get h_col
          · -- Other regions: A, A', C
            by_cases hk_a : k < prefix_walk.length
            · -- Region A (prefix interior, k < i)
              have h_eq1 :
                  (prefix_walk.comp (σ_ij.comp suffix_walk)).IsCollider k =
                  prefix_walk.IsCollider k :=
                Walk.refactor_IsCollider_comp_left
                  prefix_walk (σ_ij.comp suffix_walk) k hk_a
              have h_eq2 :
                  prefix_walk.IsCollider k =
                  (π.splitAt i hi_le).2.1.IsCollider k := by
                show (hmid_i_eq ▸ (π.splitAt i hi_le).2.1).IsCollider k = _
                rw [Walk.refactor_IsCollider_cast_target hmid_i_eq]
              rw [h_eq1, h_eq2] at h_col
              have h_split_len : (π.splitAt i hi_le).2.1.length = i :=
                Walk.splitAt_length_left π i hi_le
              have hk_split : k < (π.splitAt i hi_le).2.1.length := by
                rw [h_split_len, ← h_prefix_len]; exact hk_a
              have h_eq3 :
                  Walk.IsCollider
                      ((π.splitAt i hi_le).2.1.comp (π.splitAt i hi_le).2.2) k =
                  (π.splitAt i hi_le).2.1.IsCollider k :=
                Walk.refactor_IsCollider_comp_left
                  (π.splitAt i hi_le).2.1 (π.splitAt i hi_le).2.2 k hk_split
              rw [Walk.splitAt_comp π i hi_le] at h_eq3
              rw [← h_eq3] at h_col
              -- Vertex correspondence
              have h_prefix_v : prefix_walk.vertices = π.vertices.take (i + 1) := by
                show (hmid_i_eq ▸ (π.splitAt i hi_le).2.1).vertices = π.vertices.take (i + 1)
                rw [Walk.vertices_cast_target hmid_i_eq]
                exact Walk.splitAt_vertices_left π i hi_le
              have h_suffix_v : suffix_walk.vertices = π.vertices.drop j := by
                show (hmid_j_eq ▸ (π.splitAt j hjn).2.2).vertices = π.vertices.drop j
                rw [Walk.vertices_cast_source hmid_j_eq]
                exact Walk.splitAt_vertices_right π j hjn
              have h_π'_v_raw :
                  (prefix_walk.comp (σ_ij.comp suffix_walk)).vertices =
                    prefix_walk.vertices.dropLast ++ σ_ij.vertices.dropLast ++
                      suffix_walk.vertices := by
                rw [Walk.vertices_comp, Walk.vertices_comp, ← List.append_assoc]
              rw [h_π'_v_raw, h_prefix_v, h_suffix_v] at h_get
              have h_take_len : π.vertices.length = π.length + 1 :=
                Walk.vertices_length π
              have h_len_take : (π.vertices.take (i + 1)).dropLast.length = i := by
                rw [List.length_dropLast, List.length_take, h_take_len]; omega
              have hk_in_first :
                  k < ((π.vertices.take (i + 1)).dropLast).length := by
                rw [h_len_take, ← h_prefix_len]; exact hk_a
              have hk_in_combined :
                  k < ((π.vertices.take (i + 1)).dropLast ++
                       σ_ij.vertices.dropLast).length := by
                rw [List.length_append]; omega
              rw [List.getElem?_append_left hk_in_combined,
                  List.getElem?_append_left hk_in_first] at h_get
              -- Gotcha: List.take_take produces `min i (i + 1)` in that order,
              -- not `min (i + 1) i`; need the matching `show` for the rewrite.
              have h_take_drop_eq :
                  (π.vertices.take (i + 1)).dropLast = π.vertices.take i := by
                rw [List.dropLast_eq_take, List.length_take, h_take_len,
                    show min (i + 1) (π.length + 1) = i + 1 by omega,
                    show i + 1 - 1 = i from rfl, List.take_take,
                    show min i (i + 1) = i by omega]
              -- Gotcha: `if_pos hk_a` fails because the if-condition gets
              -- reduced to `k < i` (via h_prefix_len in scope); need an
              -- inline `(show k < i by omega)`.
              rw [h_take_drop_eq, List.getElem?_take,
                  if_pos (show k < i by omega)] at h_get
              exact hπ.1 _ vk h_get h_col
            · -- A' (k = prefix.length) or C (k = prefix.length + σ_ij.length)
              -- The splice endpoints in Case (i) are never colliders on π'
              -- (see tex/claim_3_27_proof_LabelRoman.tex II.c.i):
              --   - at A' the right slot is `σ_ij`'s first step, which is
              --     `.forwardE` (or absent when `σ_ij = .nil`), so the
              --     side-aware `HeadAtSource` reads `False` (or
              --     falls through to `suffix_walk`'s first step, also
              --     `.forwardE` by `h_caseI`);
              --   - at C the right slot is `suffix_walk`'s first step,
              --     which is `.forwardE` (or absent when `j = π.length`)
              --     by the case-(i) trigger `h_caseI`.
              -- The boundary helper
              -- `refactor_IsCollider_comp_at_p_length_no_head_source`
              -- reduces the boundary collider check to "the right walk's
              -- `firstStepHeadAtSource`", which is `False` in both
              -- sub-cases.  The argument is uniform via the helper plus
              -- the case-split on `σ_ij` (forced `.forwardE`-or-`.nil` by
              -- `hσ_dir : σ_ij.IsDirectedWalk`) and on whether the C
              -- position falls back to the A' branch when `σ_ij.length = 0`.
              -- ¬ suffix_walk.firstStepHeadAtSource (case-(i) suffix
              -- structure, via h_caseI through the cast).
              have h_suffix_no_head : ¬ suffix_walk.firstStepHeadAtSource := by
                change ¬ (hmid_j_eq ▸ (π.splitAt j hjn).2.2 :
                            Walk G v_j w).firstStepHeadAtSource
                rw [Walk.firstStepHeadAtSource_cast_source hmid_j_eq]
                exact Walk.replaceWalkCaseI_suffix_firstStepHeadAtSource_eq_False
                  π j hjn h_caseI
              -- ¬ (σ_ij.comp suffix_walk).firstStepHeadAtSource (A' usage).
              have h_q_no_head : ¬ (σ_ij.comp suffix_walk).firstStepHeadAtSource := by
                cases σ_ij with
                | nil _ _ =>
                    -- σ_ij = .nil ⇒ σ_ij.comp suffix_walk = suffix_walk
                    -- by `Walk.comp`'s `.nil` pattern.
                    exact h_suffix_no_head
                | cons _ s_head σ_ij_rest =>
                    -- σ_ij = .cons _ s_head σ_ij_rest ⇒
                    -- σ_ij.comp suffix_walk = .cons _ s_head (...)
                    -- ⇒ firstStepHeadAtSource = s_head.HeadAtSource
                    cases s_head with
                    | forwardE _ =>
                        -- (.forwardE _).HeadAtSource = False
                        intro h_false; exact h_false
                    | backwardE _ => exact hσ_dir.elim
                    | bidir _ => exact hσ_dir.elim
              -- Now case-split on whether k = A' or k = C, then close each
              -- branch via the boundary helper.
              have h_k_eq : k = prefix_walk.length ∨
                            k = prefix_walk.length + σ_ij.length := by omega
              rcases h_k_eq with hk_eq | hk_eq
              · -- A': k = prefix.length
                subst hk_eq
                exact absurd h_col
                  (Walk.refactor_IsCollider_comp_at_p_length_no_head_source
                    prefix_walk (σ_ij.comp suffix_walk) h_q_no_head)
              · -- C: k = prefix.length + σ_ij.length
                subst hk_eq
                by_cases hσ_len : σ_ij.length = 0
                · -- σ_ij.length = 0 ⇒ C collapses to A', reuse h_q_no_head.
                  rw [hσ_len, Nat.add_zero] at h_col
                  exact absurd h_col
                    (Walk.refactor_IsCollider_comp_at_p_length_no_head_source
                      prefix_walk (σ_ij.comp suffix_walk) h_q_no_head)
                · -- σ_ij.length > 0 ⇒ use `_comp_right` to peel off prefix,
                  -- then apply the boundary helper with p = σ_ij, q = suffix.
                  have h_lo : prefix_walk.length <
                              prefix_walk.length + σ_ij.length := by
                    have : 0 < σ_ij.length := Nat.pos_of_ne_zero hσ_len
                    omega
                  have h_eq1 :
                      (prefix_walk.comp (σ_ij.comp suffix_walk)).IsCollider
                          (prefix_walk.length + σ_ij.length) =
                      (σ_ij.comp suffix_walk).IsCollider
                          (prefix_walk.length + σ_ij.length - prefix_walk.length) :=
                    Walk.refactor_IsCollider_comp_right
                      prefix_walk (σ_ij.comp suffix_walk)
                      (prefix_walk.length + σ_ij.length) h_lo
                  have h_idx_simp :
                      prefix_walk.length + σ_ij.length - prefix_walk.length =
                      σ_ij.length := by omega
                  rw [h_idx_simp] at h_eq1
                  rw [h_eq1] at h_col
                  exact absurd h_col
                    (Walk.refactor_IsCollider_comp_at_p_length_no_head_source
                      σ_ij suffix_walk h_suffix_no_head)
      · -- BLOCKABLE clause: mirrors the COLLIDER clause's region
        -- partition (Region B / Region D / Region A / splice endpoints
        -- A' or C), with the COLLIDER predicate replaced by the
        -- BLOCKABLE predicate `IsBlockableNonCollider`.  At
        -- each region, either:
        --   (i)   the predicate is vacuously False on π' (Region B's
        --         σ_ij interior, by `interior_not_blockable`);
        --   (ii)  the predicate is transported back to π at the
        --         appropriate position via the `_comp_left/right` /
        --         `_cast_*` infrastructure (Regions A and D);
        --   (iii) at splice endpoints A' / C, either some
        --         disjunct (HasBlockingRightSlot at A', or
        --         HasBlockingLeftSlot at C with σ_ij.length > 0) is
        --         eliminated via σ_ij's directedness or SCC
        --         containment, and the surviving disjuncts transport
        --         to π's blockability at position i (left of merged)
        --         or position j (right of merged).
        intro k vk h_get h_blk
        have h_prefix_len : prefix_walk.length = i := by
          show (hmid_i_eq ▸ (π.splitAt i hi_le).2.1).length = i
          rw [Walk.length_cast_target hmid_i_eq]
          exact Walk.splitAt_length_left π i hi_le
        have h_suffix_len : suffix_walk.length = π.length - j := by
          show (hmid_j_eq ▸ (π.splitAt j hjn).2.2).length = π.length - j
          rw [Walk.length_cast_source hmid_j_eq]
          exact Walk.splitAt_length_right π j hjn
        have h_π'_len :
            (prefix_walk.comp (σ_ij.comp suffix_walk)).length =
              i + σ_ij.length + (π.length - j) := by
          rw [Walk.length_comp, Walk.length_comp, h_prefix_len, h_suffix_len]
          omega
        have h_σ_SCC : ∀ x ∈ σ_ij.vertices, x ∈ G.Sc v_j := by
          intro x hx
          have h_anc_vj : x ∈ G.Anc v_j :=
            Walk.directed_vertex_mem_Anc σ_ij hσ_dir hx
          have h_desc_vi : x ∈ G.Desc v_i :=
            Walk.directed_vertex_mem_Desc σ_ij hσ_dir hx
          exact ⟨h_anc_vj, mem_Desc_trans h_desc_vi (mem_Desc_of_mem_Sc h_Sc)⟩
        have h_prefix_v : prefix_walk.vertices = π.vertices.take (i + 1) := by
          show (hmid_i_eq ▸ (π.splitAt i hi_le).2.1).vertices = π.vertices.take (i + 1)
          rw [Walk.vertices_cast_target hmid_i_eq]
          exact Walk.splitAt_vertices_left π i hi_le
        have h_suffix_v : suffix_walk.vertices = π.vertices.drop j := by
          show (hmid_j_eq ▸ (π.splitAt j hjn).2.2).vertices = π.vertices.drop j
          rw [Walk.vertices_cast_source hmid_j_eq]
          exact Walk.splitAt_vertices_right π j hjn
        have h_π'_v_raw :
            (prefix_walk.comp (σ_ij.comp suffix_walk)).vertices =
              prefix_walk.vertices.dropLast ++ σ_ij.vertices.dropLast ++
                suffix_walk.vertices := by
          rw [Walk.vertices_comp, Walk.vertices_comp, ← List.append_assoc]
        have h_take_len : π.vertices.length = π.length + 1 :=
          Walk.vertices_length π
        have h_σ_len : σ_ij.vertices.length = σ_ij.length + 1 :=
          Walk.vertices_length σ_ij
        have h_suffix_vlen : suffix_walk.vertices.length = suffix_walk.length + 1 :=
          Walk.vertices_length suffix_walk
        have h_len_take : (π.vertices.take (i + 1)).dropLast.length = i := by
          rw [List.length_dropLast, List.length_take, h_take_len]; omega
        have h_len_σ_dropLast : σ_ij.vertices.dropLast.length = σ_ij.length := by
          rw [List.length_dropLast, h_σ_len]; omega
        have h_len_combined :
            ((π.vertices.take (i + 1)).dropLast ++ σ_ij.vertices.dropLast).length
              = i + σ_ij.length := by
          rw [List.length_append, h_len_take, h_len_σ_dropLast]
        by_cases hk_int_strict :
            prefix_walk.length < k ∧ k < prefix_walk.length + σ_ij.length
        · -- Region B (strict interior of σ_ij): vacuous via
          -- `interior_not_blockable`.
          obtain ⟨hk_lo, hk_hi⟩ := hk_int_strict
          exfalso
          obtain ⟨h_nc, h_disj⟩ := h_blk
          apply Walk.IsDirectedWalk.interior_not_blockable σ_ij hσ_dir h_σ_SCC
            (k - prefix_walk.length) (by omega) (by omega)
          refine ⟨?_, ?_⟩
          · refine ⟨by omega, ?_⟩
            intro h_coll_σ
            apply h_nc.2
            have h_eq1 :
                (prefix_walk.comp (σ_ij.comp suffix_walk)).IsCollider k =
                (σ_ij.comp suffix_walk).IsCollider
                  (k - prefix_walk.length) :=
              Walk.refactor_IsCollider_comp_right
                prefix_walk (σ_ij.comp suffix_walk) k hk_lo
            have h_eq2 :
                (σ_ij.comp suffix_walk).IsCollider
                  (k - prefix_walk.length) =
                σ_ij.IsCollider (k - prefix_walk.length) :=
              Walk.refactor_IsCollider_comp_left σ_ij suffix_walk
                (k - prefix_walk.length) (by omega)
            rw [h_eq1, h_eq2]
            exact h_coll_σ
          · rcases h_disj with hk_eq | hk_eq | h_blkleft | h_blkright
            · omega
            · exfalso
              rw [h_π'_len] at hk_eq
              rw [h_prefix_len] at hk_hi
              omega
            · right; right; left
              have h_eq1 :=
                Walk.HasBlockingLeftSlot_comp_right
                  prefix_walk (σ_ij.comp suffix_walk) k hk_lo
              have h_eq2 :=
                Walk.HasBlockingLeftSlot_comp_left σ_ij suffix_walk
                  (k - prefix_walk.length) (by omega)
              rw [h_eq1, h_eq2] at h_blkleft
              exact h_blkleft
            · right; right; right
              have h_eq1 :=
                Walk.HasBlockingRightSlot_comp_right
                  prefix_walk (σ_ij.comp suffix_walk) k (by omega)
              have h_eq2 :=
                Walk.HasBlockingRightSlot_comp_left σ_ij suffix_walk
                  (k - prefix_walk.length) (by omega)
              rw [h_eq1, h_eq2] at h_blkright
              exact h_blkright
        · push_neg at hk_int_strict
          by_cases hk_d : prefix_walk.length + σ_ij.length < k
          · -- Region D (suffix interior): transport h_blk back to π at
            -- position j + (k - i - σ_ij.length).  Mirror of the
            -- COLLIDER clause's Region D with the IsCollider transport
            -- extended by parallel HasBlockingLeftSlot /
            -- HasBlockingRightSlot transports.
            obtain ⟨h_nc, h_disj⟩ := h_blk
            have hk_lo : prefix_walk.length < k := by omega
            have hk_lo2 : σ_ij.length < k - prefix_walk.length := by omega
            have h_split_len : (π.splitAt j hjn).2.1.length = j :=
              Walk.splitAt_length_left π j hjn
            -- Define k_π for clarity
            set k_π : ℕ := j + (k - prefix_walk.length - σ_ij.length)
              with hk_π_def
            have hk_π_le : k_π ≤ π.length := by
              have h_k_le :
                  k ≤ (prefix_walk.comp (σ_ij.comp suffix_walk)).length := h_nc.1
              rw [h_π'_len] at h_k_le
              rw [hk_π_def, h_prefix_len]
              omega
            have hk_lo3 :
                (π.splitAt j hjn).2.1.length <
                  j + (k - prefix_walk.length - σ_ij.length) := by
              rw [h_split_len]; omega
            -- IsCollider transport
            have h_eq1_coll :
                (prefix_walk.comp (σ_ij.comp suffix_walk)).IsCollider k =
                (σ_ij.comp suffix_walk).IsCollider
                  (k - prefix_walk.length) :=
              Walk.refactor_IsCollider_comp_right
                prefix_walk (σ_ij.comp suffix_walk) k hk_lo
            have h_eq2_coll :
                (σ_ij.comp suffix_walk).IsCollider
                  (k - prefix_walk.length) =
                suffix_walk.IsCollider
                  (k - prefix_walk.length - σ_ij.length) :=
              Walk.refactor_IsCollider_comp_right σ_ij suffix_walk
                (k - prefix_walk.length) hk_lo2
            have h_eq3_coll :
                suffix_walk.IsCollider
                  (k - prefix_walk.length - σ_ij.length) =
                (π.splitAt j hjn).2.2.IsCollider
                  (k - prefix_walk.length - σ_ij.length) := by
              show (hmid_j_eq ▸ (π.splitAt j hjn).2.2).IsCollider _ = _
              rw [Walk.refactor_IsCollider_cast_source hmid_j_eq]
            have h_eq4_coll :
                Walk.IsCollider
                    ((π.splitAt j hjn).2.1.comp (π.splitAt j hjn).2.2)
                  (j + (k - prefix_walk.length - σ_ij.length)) =
                Walk.IsCollider (π.splitAt j hjn).2.2
                  ((j + (k - prefix_walk.length - σ_ij.length)) -
                    (π.splitAt j hjn).2.1.length) :=
              Walk.refactor_IsCollider_comp_right
                (π.splitAt j hjn).2.1 (π.splitAt j hjn).2.2 _ hk_lo3
            rw [Walk.splitAt_comp π j hjn] at h_eq4_coll
            rw [h_split_len] at h_eq4_coll
            have h_arith :
                j + (k - prefix_walk.length - σ_ij.length) - j =
                k - prefix_walk.length - σ_ij.length := by omega
            rw [h_arith] at h_eq4_coll
            -- HasBlockingLeftSlot transport
            have h_eq1_left :
                (prefix_walk.comp (σ_ij.comp suffix_walk)).HasBlockingLeftSlot k =
                (σ_ij.comp suffix_walk).HasBlockingLeftSlot
                  (k - prefix_walk.length) :=
              Walk.HasBlockingLeftSlot_comp_right prefix_walk
                (σ_ij.comp suffix_walk) k hk_lo
            have h_eq2_left :
                (σ_ij.comp suffix_walk).HasBlockingLeftSlot
                  (k - prefix_walk.length) =
                suffix_walk.HasBlockingLeftSlot
                  (k - prefix_walk.length - σ_ij.length) :=
              Walk.HasBlockingLeftSlot_comp_right σ_ij suffix_walk
                (k - prefix_walk.length) hk_lo2
            have h_eq3_left :
                suffix_walk.HasBlockingLeftSlot
                  (k - prefix_walk.length - σ_ij.length) =
                (π.splitAt j hjn).2.2.HasBlockingLeftSlot
                  (k - prefix_walk.length - σ_ij.length) := by
              show (hmid_j_eq ▸ (π.splitAt j hjn).2.2).HasBlockingLeftSlot _ = _
              rw [Walk.HasBlockingLeftSlot_cast_source hmid_j_eq]
            have h_eq4_left :
                Walk.HasBlockingLeftSlot
                    ((π.splitAt j hjn).2.1.comp (π.splitAt j hjn).2.2)
                  (j + (k - prefix_walk.length - σ_ij.length)) =
                Walk.HasBlockingLeftSlot (π.splitAt j hjn).2.2
                  ((j + (k - prefix_walk.length - σ_ij.length)) -
                    (π.splitAt j hjn).2.1.length) :=
              Walk.HasBlockingLeftSlot_comp_right
                (π.splitAt j hjn).2.1 (π.splitAt j hjn).2.2 _ hk_lo3
            rw [Walk.splitAt_comp π j hjn] at h_eq4_left
            rw [h_split_len, h_arith] at h_eq4_left
            -- HasBlockingRightSlot transport (≤ instead of <)
            have h_eq1_right :
                (prefix_walk.comp (σ_ij.comp suffix_walk)).HasBlockingRightSlot k =
                (σ_ij.comp suffix_walk).HasBlockingRightSlot
                  (k - prefix_walk.length) :=
              Walk.HasBlockingRightSlot_comp_right prefix_walk
                (σ_ij.comp suffix_walk) k (by omega)
            have h_eq2_right :
                (σ_ij.comp suffix_walk).HasBlockingRightSlot
                  (k - prefix_walk.length) =
                suffix_walk.HasBlockingRightSlot
                  (k - prefix_walk.length - σ_ij.length) :=
              Walk.HasBlockingRightSlot_comp_right σ_ij suffix_walk
                (k - prefix_walk.length) (by omega)
            have h_eq3_right :
                suffix_walk.HasBlockingRightSlot
                  (k - prefix_walk.length - σ_ij.length) =
                (π.splitAt j hjn).2.2.HasBlockingRightSlot
                  (k - prefix_walk.length - σ_ij.length) := by
              show (hmid_j_eq ▸ (π.splitAt j hjn).2.2).HasBlockingRightSlot _ = _
              rw [Walk.HasBlockingRightSlot_cast_source hmid_j_eq]
            have h_eq4_right :
                Walk.HasBlockingRightSlot
                    ((π.splitAt j hjn).2.1.comp (π.splitAt j hjn).2.2)
                  (j + (k - prefix_walk.length - σ_ij.length)) =
                Walk.HasBlockingRightSlot (π.splitAt j hjn).2.2
                  ((j + (k - prefix_walk.length - σ_ij.length)) -
                    (π.splitAt j hjn).2.1.length) :=
              Walk.HasBlockingRightSlot_comp_right
                (π.splitAt j hjn).2.1 (π.splitAt j hjn).2.2 _ (by
                  rw [h_split_len]; omega)
            rw [Walk.splitAt_comp π j hjn] at h_eq4_right
            rw [h_split_len, h_arith] at h_eq4_right
            -- Build π.IsBlockableNonCollider k_π
            have h_nc_π : π.IsNonCollider k_π := by
              refine ⟨hk_π_le, ?_⟩
              intro h_coll_π
              apply h_nc.2
              rw [h_eq1_coll, h_eq2_coll, h_eq3_coll, ← h_eq4_coll]
              exact h_coll_π
            have h_disj_π : k_π = 0 ∨ k_π = π.length ∨
                π.HasBlockingLeftSlot k_π ∨ π.HasBlockingRightSlot k_π := by
              rcases h_disj with hk_eq | hk_eq | h_blkleft | h_blkright
              · -- k = 0 impossible since k > prefix.length + σ_ij.length ≥ 0
                omega
              · -- k = π'.length → k_π = π.length
                right; left
                rw [h_π'_len] at hk_eq
                show k_π = π.length
                rw [hk_π_def]
                omega
              · right; right; left
                rw [h_eq1_left, h_eq2_left, h_eq3_left, ← h_eq4_left] at h_blkleft
                exact h_blkleft
              · right; right; right
                rw [h_eq1_right, h_eq2_right, h_eq3_right, ← h_eq4_right]
                  at h_blkright
                exact h_blkright
            -- Translate h_get to π at position k_π
            rw [h_π'_v_raw, h_prefix_v, h_suffix_v] at h_get
            have h_k_combined :
                ((π.vertices.take (i + 1)).dropLast ++ σ_ij.vertices.dropLast).length
                  ≤ k := by
              rw [h_len_combined, ← h_prefix_len]; omega
            rw [List.getElem?_append_right h_k_combined, h_len_combined,
                List.getElem?_drop] at h_get
            have h_idx_eq :
                j + (k - (i + σ_ij.length)) = k_π := by
              rw [hk_π_def, h_prefix_len]; omega
            rw [h_idx_eq] at h_get
            exact hπ.2 k_π vk h_get ⟨h_nc_π, h_disj_π⟩
          · by_cases hk_a : k < prefix_walk.length
            · -- Region A (prefix interior): transport h_blk back to π
              -- at position k.  Mirror of the COLLIDER clause's Region
              -- A, with the IsCollider transport extended by parallel
              -- HasBlockingLeftSlot / HasBlockingRightSlot transports.
              obtain ⟨h_nc, h_disj⟩ := h_blk
              have h_split_len : (π.splitAt i hi_le).2.1.length = i :=
                Walk.splitAt_length_left π i hi_le
              have hk_split : k < (π.splitAt i hi_le).2.1.length := by
                rw [h_split_len, ← h_prefix_len]; exact hk_a
              -- IsCollider transport: π' k → prefix k → split.2.1 k → π k
              have h_eq1_coll :
                  (prefix_walk.comp (σ_ij.comp suffix_walk)).IsCollider k =
                  prefix_walk.IsCollider k :=
                Walk.refactor_IsCollider_comp_left
                  prefix_walk (σ_ij.comp suffix_walk) k hk_a
              have h_eq2_coll :
                  prefix_walk.IsCollider k =
                  (π.splitAt i hi_le).2.1.IsCollider k := by
                show (hmid_i_eq ▸ (π.splitAt i hi_le).2.1).IsCollider k = _
                rw [Walk.refactor_IsCollider_cast_target hmid_i_eq]
              have h_eq3_coll :
                  Walk.IsCollider
                      ((π.splitAt i hi_le).2.1.comp (π.splitAt i hi_le).2.2) k =
                  (π.splitAt i hi_le).2.1.IsCollider k :=
                Walk.refactor_IsCollider_comp_left
                  (π.splitAt i hi_le).2.1 (π.splitAt i hi_le).2.2 k hk_split
              rw [Walk.splitAt_comp π i hi_le] at h_eq3_coll
              -- HasBlockingLeftSlot transport
              have h_eq1_left :
                  (prefix_walk.comp (σ_ij.comp suffix_walk)).HasBlockingLeftSlot k =
                  prefix_walk.HasBlockingLeftSlot k :=
                Walk.HasBlockingLeftSlot_comp_left prefix_walk
                  (σ_ij.comp suffix_walk) k (by omega)
              have h_eq2_left :
                  prefix_walk.HasBlockingLeftSlot k =
                  (π.splitAt i hi_le).2.1.HasBlockingLeftSlot k := by
                show (hmid_i_eq ▸ (π.splitAt i hi_le).2.1).HasBlockingLeftSlot k = _
                rw [Walk.HasBlockingLeftSlot_cast_target hmid_i_eq]
              have h_eq3_left :
                  Walk.HasBlockingLeftSlot
                      ((π.splitAt i hi_le).2.1.comp (π.splitAt i hi_le).2.2) k =
                  (π.splitAt i hi_le).2.1.HasBlockingLeftSlot k :=
                Walk.HasBlockingLeftSlot_comp_left
                  (π.splitAt i hi_le).2.1 (π.splitAt i hi_le).2.2 k (by omega)
              rw [Walk.splitAt_comp π i hi_le] at h_eq3_left
              -- HasBlockingRightSlot transport (note: comp_left requires k < p1.length)
              have h_eq1_right :
                  (prefix_walk.comp (σ_ij.comp suffix_walk)).HasBlockingRightSlot k =
                  prefix_walk.HasBlockingRightSlot k :=
                Walk.HasBlockingRightSlot_comp_left prefix_walk
                  (σ_ij.comp suffix_walk) k hk_a
              have h_eq2_right :
                  prefix_walk.HasBlockingRightSlot k =
                  (π.splitAt i hi_le).2.1.HasBlockingRightSlot k := by
                show (hmid_i_eq ▸ (π.splitAt i hi_le).2.1).HasBlockingRightSlot k = _
                rw [Walk.HasBlockingRightSlot_cast_target hmid_i_eq]
              have h_eq3_right :
                  Walk.HasBlockingRightSlot
                      ((π.splitAt i hi_le).2.1.comp (π.splitAt i hi_le).2.2) k =
                  (π.splitAt i hi_le).2.1.HasBlockingRightSlot k :=
                Walk.HasBlockingRightSlot_comp_left
                  (π.splitAt i hi_le).2.1 (π.splitAt i hi_le).2.2 k hk_split
              rw [Walk.splitAt_comp π i hi_le] at h_eq3_right
              -- Build π.IsBlockableNonCollider k
              have h_nc_π : π.IsNonCollider k := by
                refine ⟨by omega, ?_⟩
                intro h_coll_π
                apply h_nc.2
                rw [h_eq1_coll, h_eq2_coll, ← h_eq3_coll]
                exact h_coll_π
              have h_disj_π : k = 0 ∨ k = π.length ∨
                  π.HasBlockingLeftSlot k ∨ π.HasBlockingRightSlot k := by
                rcases h_disj with hk_eq | hk_eq | h_blkleft | h_blkright
                · exact Or.inl hk_eq
                · exfalso
                  rw [h_π'_len] at hk_eq
                  omega
                · right; right; left
                  rw [h_eq1_left, h_eq2_left, ← h_eq3_left] at h_blkleft
                  exact h_blkleft
                · right; right; right
                  rw [h_eq1_right, h_eq2_right, ← h_eq3_right] at h_blkright
                  exact h_blkright
              -- Translate h_get to π
              rw [h_π'_v_raw, h_prefix_v, h_suffix_v] at h_get
              have hk_in_first :
                  k < ((π.vertices.take (i + 1)).dropLast).length := by
                rw [h_len_take, ← h_prefix_len]; exact hk_a
              have hk_in_combined :
                  k < ((π.vertices.take (i + 1)).dropLast ++
                       σ_ij.vertices.dropLast).length := by
                rw [List.length_append]; omega
              rw [List.getElem?_append_left hk_in_combined,
                  List.getElem?_append_left hk_in_first] at h_get
              have h_take_drop_eq :
                  (π.vertices.take (i + 1)).dropLast = π.vertices.take i := by
                rw [List.dropLast_eq_take, List.length_take, h_take_len,
                    show min (i + 1) (π.length + 1) = i + 1 by omega,
                    show i + 1 - 1 = i from rfl, List.take_take,
                    show min i (i + 1) = i by omega]
              rw [h_take_drop_eq, List.getElem?_take,
                  if_pos (show k < i by omega)] at h_get
              exact hπ.2 k vk h_get ⟨h_nc_π, h_disj_π⟩
            · -- Splice endpoints A' (k = prefix.length) or
              -- C (k = prefix.length + σ_ij.length).  By case-splits
              -- above: prefix.length ≤ k ≤ prefix.length + σ_ij.length,
              -- and k = prefix.length OR k = prefix.length + σ_ij.length.
              obtain ⟨h_nc, h_disj⟩ := h_blk
              rcases h_disj with hk0 | hkπ' | h_blkleft | h_blkright
              · -- Disjunct: k = 0.  Forces prefix.length = 0, i.e., i = 0.
                -- vk is the source u of π'.
                subst hk0
                have hi_zero : i = 0 := by omega
                have h_π'_zero :
                    (prefix_walk.comp (σ_ij.comp suffix_walk)).vertices[0]? = some u :=
                  Walk.vertices_zero_eq_source _
                rw [h_π'_zero] at h_get
                have hvk_u : vk = u := (Option.some.inj h_get).symm
                have h_get_π : π.vertices[0]? = some vk := by
                  rw [Walk.vertices_zero_eq_source π, hvk_u]
                refine hπ.2 0 vk h_get_π ⟨⟨by omega, ?_⟩, Or.inl rfl⟩
                exact Walk.refactor_IsCollider_zero_eq_False π
              · -- Disjunct: k = π'.length.  Forces suffix.length = 0,
                -- i.e., j = π.length.  vk is the target w of π'.
                have hkπ'_unfolded :
                    k = (prefix_walk.comp (σ_ij.comp suffix_walk)).length := hkπ'
                have h_π'_end :
                    (prefix_walk.comp (σ_ij.comp suffix_walk)).vertices[
                      (prefix_walk.comp (σ_ij.comp suffix_walk)).length]? = some w :=
                  Walk.vertices_length_eq_target _
                rw [hkπ'_unfolded, h_π'_end] at h_get
                have hvk_w : vk = w := (Option.some.inj h_get).symm
                -- Derive j = π.length from k ≤ prefix.length + σ_ij.length and
                -- k = π'.length = prefix.length + σ_ij.length + suffix.length:
                have h_j_eq : j = π.length := by
                  have h_π'_eq : (prefix_walk.comp (σ_ij.comp suffix_walk)).length =
                      i + σ_ij.length + (π.length - j) := h_π'_len
                  have hk_eq_π'_len : k = i + σ_ij.length + (π.length - j) := by
                    rw [hkπ'_unfolded]; exact h_π'_eq
                  -- k ≤ prefix.length + σ_ij.length (from hk_d negation), with
                  -- h_prefix_len : prefix.length = i. So k ≤ i + σ_ij.length.
                  -- Combined with hk_eq_π'_len, π.length - j ≤ 0, so j = π.length
                  -- (using hjn : j ≤ π.length).
                  have hk_le : k ≤ i + σ_ij.length := by
                    rw [← h_prefix_len]; omega
                  omega
                -- Apply hπ.2 at π.length, vk = w.
                have h_get_π : π.vertices[π.length]? = some vk := by
                  rw [Walk.vertices_length_eq_target π, hvk_w]
                refine hπ.2 π.length vk h_get_π
                  ⟨⟨Nat.le_refl _, ?_⟩, Or.inr (Or.inl rfl)⟩
                exact Walk.refactor_IsCollider_length_eq_False π
              · -- Disjunct: HasBlockingLeftSlot k.
                -- Splice constraint gives k = prefix.length OR k = prefix.length + σ_ij.length.
                -- If k = prefix.length: slot k-1 in prefix → π.HasBlockingLeftSlot i.
                -- If k > prefix.length: slot k-1 in σ_ij → False via directed.
                by_cases hk_at_A : k = prefix_walk.length
                · -- A': k = prefix.length
                  subst hk_at_A
                  have h_eq1_left :
                      (prefix_walk.comp (σ_ij.comp suffix_walk)).HasBlockingLeftSlot
                          prefix_walk.length =
                      prefix_walk.HasBlockingLeftSlot prefix_walk.length :=
                    Walk.HasBlockingLeftSlot_comp_left prefix_walk
                      (σ_ij.comp suffix_walk) prefix_walk.length (Nat.le_refl _)
                  rw [h_eq1_left, h_prefix_len] at h_blkleft
                  have h_eq2_left :
                      prefix_walk.HasBlockingLeftSlot i =
                      (π.splitAt i hi_le).2.1.HasBlockingLeftSlot i := by
                    show (hmid_i_eq ▸ (π.splitAt i hi_le).2.1).HasBlockingLeftSlot i = _
                    rw [Walk.HasBlockingLeftSlot_cast_target hmid_i_eq]
                  rw [h_eq2_left] at h_blkleft
                  have h_eq3_left :
                      Walk.HasBlockingLeftSlot
                          ((π.splitAt i hi_le).2.1.comp (π.splitAt i hi_le).2.2) i =
                      (π.splitAt i hi_le).2.1.HasBlockingLeftSlot i :=
                    Walk.HasBlockingLeftSlot_comp_left
                      (π.splitAt i hi_le).2.1 (π.splitAt i hi_le).2.2 i (by
                        rw [Walk.splitAt_length_left π i hi_le])
                  rw [Walk.splitAt_comp π i hi_le] at h_eq3_left
                  rw [← h_eq3_left] at h_blkleft
                  -- h_blkleft : π.HasBlockingLeftSlot i
                  -- vk = v_i
                  have h_π'_v_at_i :
                      (prefix_walk.comp (σ_ij.comp suffix_walk)).vertices[
                        prefix_walk.length]? = some v_i :=
                    Walk.vertices_comp_at_left_length prefix_walk (σ_ij.comp suffix_walk)
                  rw [h_π'_v_at_i] at h_get
                  have hvk_vi : vk = v_i := (Option.some.inj h_get).symm
                  have h_get_π : π.vertices[i]? = some vk := by
                    rw [h_get_i, hvk_vi]
                  refine hπ.2 i vk h_get_π
                    ⟨⟨hi_le, ?_⟩, Or.inr (Or.inr (Or.inl h_blkleft))⟩
                  exact Walk.HasBlockingLeftSlot.not_refactor_IsCollider π i h_blkleft
                · -- C: k > prefix.length (so k = prefix.length + σ_ij.length AND σ_ij.length > 0).
                  have hk_at_C : k = prefix_walk.length + σ_ij.length := by omega
                  have hσ_pos : 0 < σ_ij.length := by omega
                  subst hk_at_C
                  exfalso
                  have h_eq1_left :
                      (prefix_walk.comp (σ_ij.comp suffix_walk)).HasBlockingLeftSlot
                          (prefix_walk.length + σ_ij.length) =
                      (σ_ij.comp suffix_walk).HasBlockingLeftSlot σ_ij.length := by
                    have := Walk.HasBlockingLeftSlot_comp_right prefix_walk
                      (σ_ij.comp suffix_walk) (prefix_walk.length + σ_ij.length)
                      (by omega)
                    rw [show prefix_walk.length + σ_ij.length - prefix_walk.length =
                          σ_ij.length by omega] at this
                    exact this
                  have h_eq2_left :
                      (σ_ij.comp suffix_walk).HasBlockingLeftSlot σ_ij.length =
                      σ_ij.HasBlockingLeftSlot σ_ij.length :=
                    Walk.HasBlockingLeftSlot_comp_left σ_ij suffix_walk σ_ij.length
                      (Nat.le_refl _)
                  rw [h_eq1_left, h_eq2_left] at h_blkleft
                  exact Walk.IsDirectedWalk.no_HasBlockingLeftSlot σ_ij hσ_dir _ h_blkleft
              · -- Disjunct: HasBlockingRightSlot k.
                -- If σ_ij.length > 0 AND k = prefix.length: slot is σ_ij's first
                --   (.forwardE, target ∈ Sc(v_i)).  HasBlockingRightSlot False → contradiction.
                -- Otherwise (σ_ij.length = 0, OR k = prefix.length + σ_ij.length):
                --   slot is suffix's first.  Transport to π.HasBlockingRightSlot j.
                by_cases hσ_pos : 0 < σ_ij.length
                · -- σ_ij.length > 0
                  by_cases hk_at_A : k = prefix_walk.length
                  · -- A' with σ_ij.length > 0: slot in σ_ij first, contradiction
                    subst hk_at_A
                    exfalso
                    have h_eq1_right :
                        (prefix_walk.comp (σ_ij.comp suffix_walk)).HasBlockingRightSlot
                            prefix_walk.length =
                        (σ_ij.comp suffix_walk).HasBlockingRightSlot 0 := by
                      have := Walk.HasBlockingRightSlot_comp_right prefix_walk
                        (σ_ij.comp suffix_walk) prefix_walk.length (Nat.le_refl _)
                      rw [Nat.sub_self] at this
                      exact this
                    have h_eq2_right :
                        (σ_ij.comp suffix_walk).HasBlockingRightSlot 0 =
                        σ_ij.HasBlockingRightSlot 0 :=
                      Walk.HasBlockingRightSlot_comp_left σ_ij suffix_walk 0 hσ_pos
                    rw [h_eq1_right, h_eq2_right] at h_blkright
                    exact Walk.no_HasBlockingRightSlot_of_all_in_SCC σ_ij h_σ_SCC 0
                      h_blkright
                  · -- C: k = prefix.length + σ_ij.length, slot in suffix
                    have hk_at_C : k = prefix_walk.length + σ_ij.length := by omega
                    subst hk_at_C
                    -- Transport π'.HasBlockingRightSlot to π.HasBlockingRightSlot j
                    have h_eq1_right :
                        (prefix_walk.comp (σ_ij.comp suffix_walk)).HasBlockingRightSlot
                            (prefix_walk.length + σ_ij.length) =
                        (σ_ij.comp suffix_walk).HasBlockingRightSlot σ_ij.length := by
                      have := Walk.HasBlockingRightSlot_comp_right prefix_walk
                        (σ_ij.comp suffix_walk) (prefix_walk.length + σ_ij.length)
                        (by omega)
                      rw [show prefix_walk.length + σ_ij.length - prefix_walk.length =
                            σ_ij.length by omega] at this
                      exact this
                    have h_eq2_right :
                        (σ_ij.comp suffix_walk).HasBlockingRightSlot σ_ij.length =
                        suffix_walk.HasBlockingRightSlot 0 := by
                      have := Walk.HasBlockingRightSlot_comp_right σ_ij suffix_walk
                        σ_ij.length (Nat.le_refl _)
                      rw [Nat.sub_self] at this
                      exact this
                    rw [h_eq1_right, h_eq2_right] at h_blkright
                    -- Transport suffix.HasBlockingRightSlot 0 to π.HasBlockingRightSlot j
                    have h_eq3_right :
                        suffix_walk.HasBlockingRightSlot 0 =
                        (π.splitAt j hjn).2.2.HasBlockingRightSlot 0 := by
                      show (hmid_j_eq ▸ (π.splitAt j hjn).2.2).HasBlockingRightSlot 0 = _
                      rw [Walk.HasBlockingRightSlot_cast_source hmid_j_eq]
                    rw [h_eq3_right] at h_blkright
                    have h_split_len : (π.splitAt j hjn).2.1.length = j :=
                      Walk.splitAt_length_left π j hjn
                    have h_eq4_right :
                        Walk.HasBlockingRightSlot
                            ((π.splitAt j hjn).2.1.comp (π.splitAt j hjn).2.2) j =
                        (π.splitAt j hjn).2.2.HasBlockingRightSlot 0 := by
                      have := Walk.HasBlockingRightSlot_comp_right
                        (π.splitAt j hjn).2.1 (π.splitAt j hjn).2.2 j (by
                          rw [h_split_len])
                      rw [h_split_len, Nat.sub_self] at this
                      exact this
                    rw [Walk.splitAt_comp π j hjn] at h_eq4_right
                    rw [← h_eq4_right] at h_blkright
                    -- h_blkright : π.HasBlockingRightSlot j
                    -- vk = v_j
                    have h_π'_v_at_C :
                        (prefix_walk.comp (σ_ij.comp suffix_walk)).vertices[
                          prefix_walk.length + σ_ij.length]? = some v_j := by
                      rw [Walk.vertices_comp_right_shift]
                      exact Walk.vertices_comp_at_left_length σ_ij suffix_walk
                    rw [h_π'_v_at_C] at h_get
                    have hvk_vj : vk = v_j := (Option.some.inj h_get).symm
                    have h_get_π : π.vertices[j]? = some vk := by
                      rw [h_get_j, hvk_vj]
                    refine hπ.2 j vk h_get_π
                      ⟨⟨hjn, ?_⟩, Or.inr (Or.inr (Or.inr h_blkright))⟩
                    exact Walk.HasBlockingRightSlot.not_refactor_IsCollider π j h_blkright
                · -- σ_ij.length = 0: σ_ij is nil, σ_ij.comp suffix = suffix
                  have hσ_zero : σ_ij.length = 0 := by omega
                  have hk_at : k = prefix_walk.length := by omega
                  subst hk_at
                  -- Transport via h_eq_combined:
                  -- π'.HasBlockingRightSlot prefix.length = (σ_ij.comp suffix).HasBlockingRightSlot 0
                  --   (via comp_right at k = prefix.length, k - prefix.length = 0)
                  -- = suffix.HasBlockingRightSlot 0 (since σ_ij = nil, σ_ij.comp suffix = suffix
                  --   structurally: cases σ_ij; alternatively: comp_right at 0 with σ_ij.length = 0)
                  -- Hmm, with σ_ij.length = 0, comp_right helper needs p1.length ≤ k = 0. So σ_ij.length ≤ 0, holds.
                  -- comp_right gives (σ_ij.comp suffix).HasBlockingRightSlot 0 = suffix.HasBlockingRightSlot (0 - σ_ij.length) = suffix.HasBlockingRightSlot 0.
                  have h_eq1_right :
                      (prefix_walk.comp (σ_ij.comp suffix_walk)).HasBlockingRightSlot
                          prefix_walk.length =
                      (σ_ij.comp suffix_walk).HasBlockingRightSlot 0 := by
                    have := Walk.HasBlockingRightSlot_comp_right prefix_walk
                      (σ_ij.comp suffix_walk) prefix_walk.length (Nat.le_refl _)
                    rw [Nat.sub_self] at this
                    exact this
                  have h_eq2_right :
                      (σ_ij.comp suffix_walk).HasBlockingRightSlot 0 =
                      suffix_walk.HasBlockingRightSlot (0 - σ_ij.length) :=
                    Walk.HasBlockingRightSlot_comp_right σ_ij suffix_walk 0 (by omega)
                  rw [hσ_zero, Nat.zero_sub] at h_eq2_right
                  rw [h_eq1_right, h_eq2_right] at h_blkright
                  -- h_blkright : suffix.HasBlockingRightSlot 0
                  have h_eq3_right :
                      suffix_walk.HasBlockingRightSlot 0 =
                      (π.splitAt j hjn).2.2.HasBlockingRightSlot 0 := by
                    show (hmid_j_eq ▸ (π.splitAt j hjn).2.2).HasBlockingRightSlot 0 = _
                    rw [Walk.HasBlockingRightSlot_cast_source hmid_j_eq]
                  rw [h_eq3_right] at h_blkright
                  have h_split_len : (π.splitAt j hjn).2.1.length = j :=
                    Walk.splitAt_length_left π j hjn
                  have h_eq4_right :
                      Walk.HasBlockingRightSlot
                          ((π.splitAt j hjn).2.1.comp (π.splitAt j hjn).2.2) j =
                      (π.splitAt j hjn).2.2.HasBlockingRightSlot 0 := by
                    have := Walk.HasBlockingRightSlot_comp_right
                      (π.splitAt j hjn).2.1 (π.splitAt j hjn).2.2 j (by
                        rw [h_split_len])
                    rw [h_split_len, Nat.sub_self] at this
                    exact this
                  rw [Walk.splitAt_comp π j hjn] at h_eq4_right
                  rw [← h_eq4_right] at h_blkright
                  -- h_blkright : π.HasBlockingRightSlot j
                  -- vk = (vertex at prefix.length on π')
                  -- With σ_ij.length = 0, σ_ij = .nil v_i hv_i, v_i = v_j (forced by type).
                  -- Vertex at prefix.length on π' = v_i (by vertices_comp_at_left_length).
                  -- vk = v_i.
                  have h_π'_v_at :
                      (prefix_walk.comp (σ_ij.comp suffix_walk)).vertices[
                        prefix_walk.length]? = some v_i :=
                    Walk.vertices_comp_at_left_length prefix_walk (σ_ij.comp suffix_walk)
                  rw [h_π'_v_at] at h_get
                  have hvk_vi : vk = v_i := (Option.some.inj h_get).symm
                  -- We need π.vertices[j]? = some vk = some v_i.
                  -- We have h_get_j : π.vertices[j]? = some v_j.
                  -- Need v_i = v_j (from σ_ij.length = 0 forcing the type's source = target).
                  have h_vi_eq_vj : v_i = v_j := by
                    cases h_σ_ij_nil : σ_ij with
                    | nil _ _ => rfl
                    | cons _ _ _ =>
                        -- contradicts σ_ij.length = 0
                        rw [h_σ_ij_nil] at hσ_zero
                        simp [Walk.length] at hσ_zero
                  have h_get_π : π.vertices[j]? = some vk := by
                    rw [h_get_j, hvk_vi, h_vi_eq_vj]
                  refine hπ.2 j vk h_get_π
                    ⟨⟨hjn, ?_⟩, Or.inr (Or.inr (Or.inr h_blkright))⟩
                  exact Walk.HasBlockingRightSlot.not_refactor_IsCollider π j h_blkright
  · -- ## Case (ii): σ_ij = reverse of shortest directed walk v_j → v_i
    have h_walk_exists : ∃ p : Walk G v_j v_i, p.IsDirectedWalk :=
      (mem_Desc_of_mem_Sc h_Sc).2
    -- Destructure σ_ji via `obtain` (free variable, not `let`).
    obtain ⟨σ_ji, hσ_ji_dir, hσ_ji_min⟩ :=
      Walk.shortestDirectedWalk h_walk_exists
    let σ_ij : Walk G v_i v_j := σ_ji.reverse
    have h_rev_eq : σ_ij.reverse = σ_ji := Walk.reverse_involution σ_ji
    have hσ_rev_dir : σ_ij.reverse.IsDirectedWalk :=
      h_rev_eq ▸ hσ_ji_dir
    have hσ_rev_min : ∀ τ : Walk G v_j v_i, τ.IsDirectedWalk →
        σ_ij.reverse.length ≤ τ.length := by
      intro τ hτ
      rw [h_rev_eq]
      exact hσ_ji_min τ hτ
    let π' : Walk G u w := prefix_walk.comp (σ_ij.comp suffix_walk)
    refine ⟨σ_ij, π', ?_, ?_, ?_, ?_, ?_⟩
    · -- Conjunct 1: caseI → vacuously true (contradicts ¬h_caseI)
      intro h
      exact absurd h h_caseI
    · -- Conjunct 2: ¬caseI → reverse directed + minimal
      intro _
      exact ⟨hσ_rev_dir, hσ_rev_min⟩
    · -- Conjunct 3: SCC containment of σ_ij.vertices
      -- σ_ij.vertices = σ_ji.reverse.vertices = σ_ji.vertices.reverse
      have h_vert_eq : σ_ij.vertices = σ_ji.vertices.reverse :=
        Walk.vertices_reverse σ_ji
      intro x hx
      rw [h_vert_eq, List.mem_reverse] at hx
      have h_anc_vi : x ∈ G.Anc v_i :=
        Walk.directed_vertex_mem_Anc σ_ji hσ_ji_dir hx
      have h_desc_vj : x ∈ G.Desc v_j :=
        Walk.directed_vertex_mem_Desc σ_ji hσ_ji_dir hx
      have h_vi_anc_vj : v_i ∈ G.Anc v_j := mem_Anc_of_mem_Sc h_Sc
      have h_anc_vj : x ∈ G.Anc v_j := mem_Anc_trans h_anc_vi h_vi_anc_vj
      exact ⟨h_anc_vj, h_desc_vj⟩
    · -- Conjunct 4: vertex equation
      have h_prefix_vertices : prefix_walk.vertices = π.vertices.take (i + 1) := by
        show (hmid_i_eq ▸ (π.splitAt i hi_le).2.1).vertices = π.vertices.take (i + 1)
        rw [Walk.vertices_cast_target hmid_i_eq]
        exact Walk.splitAt_vertices_left π i hi_le
      have h_suffix_vertices : suffix_walk.vertices = π.vertices.drop j := by
        show (hmid_j_eq ▸ (π.splitAt j hjn).2.2).vertices = π.vertices.drop j
        rw [Walk.vertices_cast_source hmid_j_eq]
        exact Walk.splitAt_vertices_right π j hjn
      have h_lt : j < π.vertices.length := by
        rw [Walk.vertices_length]; omega
      have h_get : π.vertices[j]'h_lt = v_j := by
        have h := h_get_j
        rw [List.getElem?_eq_getElem h_lt] at h
        exact Option.some.inj h
      have h_drop_j : π.vertices.drop j = v_j :: π.vertices.drop (j + 1) := by
        rw [← List.cons_getElem_drop_succ (h := h_lt), h_get]
      have h_ne : σ_ij.vertices ≠ [] := Walk.vertices_ne_nil σ_ij
      have h_σ_last : σ_ij.vertices.getLast h_ne = v_j :=
        Walk.last_vertex_eq_target σ_ij
      have h_σ_dropLast : σ_ij.vertices.dropLast ++ [v_j] = σ_ij.vertices := by
        conv_rhs => rw [← List.dropLast_append_getLast h_ne, h_σ_last]
      show (prefix_walk.comp (σ_ij.comp suffix_walk)).vertices = _
      rw [Walk.vertices_comp, Walk.vertices_comp,
          h_prefix_vertices, h_suffix_vertices, h_drop_j]
      rw [show σ_ij.vertices.dropLast ++ (v_j :: π.vertices.drop (j + 1)) =
            (σ_ij.vertices.dropLast ++ [v_j]) ++ π.vertices.drop (j + 1) by
          simp [List.append_assoc]]
      rw [h_σ_dropLast, ← List.append_assoc]
    · -- Conjunct 5: σ-openness of π' (Case (ii)).
      -- Decompose into the COLLIDER and BLOCKABLE clauses.
      refine ⟨?_, ?_⟩
      · -- COLLIDER clause
        intro k vk h_get h_col
        have h_prefix_len : prefix_walk.length = i := by
          show (hmid_i_eq ▸ (π.splitAt i hi_le).2.1).length = i
          rw [Walk.length_cast_target hmid_i_eq]
          exact Walk.splitAt_length_left π i hi_le
        have hσ_ij_back_dir : σ_ij.IsBackwardDirectedWalk := by
          show (σ_ji.reverse : Walk G v_i v_j).IsBackwardDirectedWalk
          exact Walk.reverse_isBackwardDirected_of_directed σ_ji hσ_ji_dir
        by_cases hk_int_strict :
            prefix_walk.length < k ∧ k < prefix_walk.length + σ_ij.length
        · -- Region B (strict interior of σ_ij, vacuous via backward interior_not_collider)
          obtain ⟨hk_lo, hk_hi⟩ := hk_int_strict
          have h_iscoll_eq1 :
              (prefix_walk.comp (σ_ij.comp suffix_walk)).IsCollider k =
              (σ_ij.comp suffix_walk).IsCollider
                (k - prefix_walk.length) :=
            Walk.refactor_IsCollider_comp_right
              prefix_walk (σ_ij.comp suffix_walk) k hk_lo
          have hk' : k - prefix_walk.length < σ_ij.length := by omega
          have h_iscoll_eq2 :
              (σ_ij.comp suffix_walk).IsCollider
                (k - prefix_walk.length) =
              σ_ij.IsCollider (k - prefix_walk.length) :=
            Walk.refactor_IsCollider_comp_left σ_ij suffix_walk
              (k - prefix_walk.length) hk'
          rw [h_iscoll_eq1, h_iscoll_eq2] at h_col
          have hk1 : 1 ≤ k - prefix_walk.length := by omega
          exact absurd h_col
            (Walk.IsBackwardDirectedWalk.interior_not_collider σ_ij
              hσ_ij_back_dir _ hk1 hk')
        · -- Other regions: outer-left, outer-right, splice endpoints
          push_neg at hk_int_strict
          by_cases hk_d : prefix_walk.length + σ_ij.length < k
          · -- Region D (suffix interior, position-shift to π)
            have hk_lo : prefix_walk.length < k := by omega
            have h_eq1 :
                (prefix_walk.comp (σ_ij.comp suffix_walk)).IsCollider k =
                (σ_ij.comp suffix_walk).IsCollider
                  (k - prefix_walk.length) :=
              Walk.refactor_IsCollider_comp_right
                prefix_walk (σ_ij.comp suffix_walk) k hk_lo
            have hk_lo2 : σ_ij.length < k - prefix_walk.length := by omega
            have h_eq2 :
                (σ_ij.comp suffix_walk).IsCollider
                  (k - prefix_walk.length) =
                suffix_walk.IsCollider
                  (k - prefix_walk.length - σ_ij.length) :=
              Walk.refactor_IsCollider_comp_right σ_ij suffix_walk
                (k - prefix_walk.length) hk_lo2
            rw [h_eq1, h_eq2] at h_col
            have h_eq3 :
                suffix_walk.IsCollider
                  (k - prefix_walk.length - σ_ij.length) =
                (π.splitAt j hjn).2.2.IsCollider
                  (k - prefix_walk.length - σ_ij.length) := by
              show (hmid_j_eq ▸ (π.splitAt j hjn).2.2).IsCollider _ = _
              rw [Walk.refactor_IsCollider_cast_source hmid_j_eq]
            rw [h_eq3] at h_col
            have h_split_len : (π.splitAt j hjn).2.1.length = j :=
              Walk.splitAt_length_left π j hjn
            have hk_lo3 :
                (π.splitAt j hjn).2.1.length <
                  j + (k - prefix_walk.length - σ_ij.length) := by
              rw [h_split_len]; omega
            have h_eq4 :
                Walk.IsCollider
                    ((π.splitAt j hjn).2.1.comp (π.splitAt j hjn).2.2)
                  (j + (k - prefix_walk.length - σ_ij.length)) =
                Walk.IsCollider (π.splitAt j hjn).2.2
                  ((j + (k - prefix_walk.length - σ_ij.length)) -
                    (π.splitAt j hjn).2.1.length) :=
              Walk.refactor_IsCollider_comp_right
                (π.splitAt j hjn).2.1 (π.splitAt j hjn).2.2 _ hk_lo3
            rw [Walk.splitAt_comp π j hjn] at h_eq4
            rw [h_split_len] at h_eq4
            have h_arith : j + (k - prefix_walk.length - σ_ij.length) - j =
                          k - prefix_walk.length - σ_ij.length := by omega
            rw [h_arith] at h_eq4
            rw [← h_eq4] at h_col
            have h_prefix_v : prefix_walk.vertices = π.vertices.take (i + 1) := by
              show (hmid_i_eq ▸ (π.splitAt i hi_le).2.1).vertices = π.vertices.take (i + 1)
              rw [Walk.vertices_cast_target hmid_i_eq]
              exact Walk.splitAt_vertices_left π i hi_le
            have h_suffix_v : suffix_walk.vertices = π.vertices.drop j := by
              show (hmid_j_eq ▸ (π.splitAt j hjn).2.2).vertices = π.vertices.drop j
              rw [Walk.vertices_cast_source hmid_j_eq]
              exact Walk.splitAt_vertices_right π j hjn
            have h_π'_v_raw :
                (prefix_walk.comp (σ_ij.comp suffix_walk)).vertices =
                  prefix_walk.vertices.dropLast ++ σ_ij.vertices.dropLast ++
                    suffix_walk.vertices := by
              rw [Walk.vertices_comp, Walk.vertices_comp, ← List.append_assoc]
            rw [h_π'_v_raw, h_prefix_v, h_suffix_v] at h_get
            have h_take_len : π.vertices.length = π.length + 1 :=
              Walk.vertices_length π
            have h_σ_len : σ_ij.vertices.length = σ_ij.length + 1 :=
              Walk.vertices_length σ_ij
            have h_len_take : (π.vertices.take (i + 1)).dropLast.length = i := by
              rw [List.length_dropLast, List.length_take, h_take_len]
              omega
            have h_len_σ_dropLast : σ_ij.vertices.dropLast.length = σ_ij.length := by
              rw [List.length_dropLast, h_σ_len]
              omega
            have h_len_combined :
                ((π.vertices.take (i + 1)).dropLast ++ σ_ij.vertices.dropLast).length
                  = i + σ_ij.length := by
              rw [List.length_append, h_len_take, h_len_σ_dropLast]
            have h_k_combined :
                ((π.vertices.take (i + 1)).dropLast ++ σ_ij.vertices.dropLast).length
                  ≤ k := by
              rw [h_len_combined, ← h_prefix_len]; omega
            rw [List.getElem?_append_right h_k_combined, h_len_combined,
                List.getElem?_drop] at h_get
            have h_idx_eq :
                j + (k - (i + σ_ij.length)) =
                  j + (k - prefix_walk.length - σ_ij.length) := by
              rw [h_prefix_len]; omega
            rw [h_idx_eq] at h_get
            exact hπ.1 _ vk h_get h_col
          · -- Other regions: A, A', C
            by_cases hk_a : k < prefix_walk.length
            · -- Region A (prefix interior, k < i)
              have h_eq1 :
                  (prefix_walk.comp (σ_ij.comp suffix_walk)).IsCollider k =
                  prefix_walk.IsCollider k :=
                Walk.refactor_IsCollider_comp_left
                  prefix_walk (σ_ij.comp suffix_walk) k hk_a
              have h_eq2 :
                  prefix_walk.IsCollider k =
                  (π.splitAt i hi_le).2.1.IsCollider k := by
                show (hmid_i_eq ▸ (π.splitAt i hi_le).2.1).IsCollider k = _
                rw [Walk.refactor_IsCollider_cast_target hmid_i_eq]
              rw [h_eq1, h_eq2] at h_col
              have h_split_len : (π.splitAt i hi_le).2.1.length = i :=
                Walk.splitAt_length_left π i hi_le
              have hk_split : k < (π.splitAt i hi_le).2.1.length := by
                rw [h_split_len, ← h_prefix_len]; exact hk_a
              have h_eq3 :
                  Walk.IsCollider
                      ((π.splitAt i hi_le).2.1.comp (π.splitAt i hi_le).2.2) k =
                  (π.splitAt i hi_le).2.1.IsCollider k :=
                Walk.refactor_IsCollider_comp_left
                  (π.splitAt i hi_le).2.1 (π.splitAt i hi_le).2.2 k hk_split
              rw [Walk.splitAt_comp π i hi_le] at h_eq3
              rw [← h_eq3] at h_col
              have h_prefix_v : prefix_walk.vertices = π.vertices.take (i + 1) := by
                show (hmid_i_eq ▸ (π.splitAt i hi_le).2.1).vertices = π.vertices.take (i + 1)
                rw [Walk.vertices_cast_target hmid_i_eq]
                exact Walk.splitAt_vertices_left π i hi_le
              have h_suffix_v : suffix_walk.vertices = π.vertices.drop j := by
                show (hmid_j_eq ▸ (π.splitAt j hjn).2.2).vertices = π.vertices.drop j
                rw [Walk.vertices_cast_source hmid_j_eq]
                exact Walk.splitAt_vertices_right π j hjn
              have h_π'_v_raw :
                  (prefix_walk.comp (σ_ij.comp suffix_walk)).vertices =
                    prefix_walk.vertices.dropLast ++ σ_ij.vertices.dropLast ++
                      suffix_walk.vertices := by
                rw [Walk.vertices_comp, Walk.vertices_comp, ← List.append_assoc]
              rw [h_π'_v_raw, h_prefix_v, h_suffix_v] at h_get
              have h_take_len : π.vertices.length = π.length + 1 :=
                Walk.vertices_length π
              have h_len_take : (π.vertices.take (i + 1)).dropLast.length = i := by
                rw [List.length_dropLast, List.length_take, h_take_len]; omega
              have hk_in_first :
                  k < ((π.vertices.take (i + 1)).dropLast).length := by
                rw [h_len_take, ← h_prefix_len]; exact hk_a
              have hk_in_combined :
                  k < ((π.vertices.take (i + 1)).dropLast ++
                       σ_ij.vertices.dropLast).length := by
                rw [List.length_append]; omega
              rw [List.getElem?_append_left hk_in_combined,
                  List.getElem?_append_left hk_in_first] at h_get
              -- Gotcha: List.take_take produces `min i (i + 1)` in that order,
              -- not `min (i + 1) i`; need the matching `show` for the rewrite.
              have h_take_drop_eq :
                  (π.vertices.take (i + 1)).dropLast = π.vertices.take i := by
                rw [List.dropLast_eq_take, List.length_take, h_take_len,
                    show min (i + 1) (π.length + 1) = i + 1 by omega,
                    show i + 1 - 1 = i from rfl, List.take_take,
                    show min i (i + 1) = i by omega]
              -- Gotcha: `if_pos hk_a` fails because the if-condition gets
              -- reduced to `k < i` (via h_prefix_len in scope); need an
              -- inline `(show k < i by omega)`.
              rw [h_take_drop_eq, List.getElem?_take,
                  if_pos (show k < i by omega)] at h_get
              exact hπ.1 _ vk h_get h_col
            · -- A' (k = prefix.length) or C (k = prefix.length + σ_ij.length)
              -- Case (ii) splice endpoints.
              -- - A' (k = i): the right slot is σ_ij's first step = .backwardE _ (or
              --   first step of suffix = .backwardE/.bidir _ when σ_ij = .nil), both
              --   with HeadAtSource = True. So h_col reduces to HeadAtTarget(s_{i-1} on π).
              --   If this is True, position i is collider on π: use first-collider trace
              --   to derive v_i ∈ AncSet C (per tex (II.c.iii) sub-case (b)).
              -- - C (k = j, σ_ij.length > 0): last step of σ_ij = .backwardE _,
              --   HeadAtTarget = False. h_col reduces to False; contradiction.
              -- σ_ij.length = 0 case: C = A', handle uniformly.
              -- From hk_int_strict (already push_neg'd), hk_d, hk_a:
              -- k = prefix.length OR k = prefix.length + σ_ij.length.
              have hk_choices : k = prefix_walk.length ∨
                  k = prefix_walk.length + σ_ij.length := by omega
              -- Establish j < π.length from ¬ h_caseI.
              have h_j_lt : j < π.length := by
                rcases lt_or_eq_of_le hjn with h_lt | h_eq
                · exact h_lt
                · exfalso; apply h_caseI; rw [h_eq]
                  exact Walk.replaceWalkCaseI_at_length π
              -- suffix_walk has positive length.
              have h_suffix_len_eq : suffix_walk.length = π.length - j := by
                show (hmid_j_eq ▸ (π.splitAt j hjn).2.2).length = π.length - j
                rw [Walk.length_cast_source hmid_j_eq]
                exact Walk.splitAt_length_right π j hjn
              have h_suffix_pos : 0 < suffix_walk.length := by
                rw [h_suffix_len_eq]; omega
              rcases hk_choices with hk_eq | hk_eq
              · -- A': k = prefix.length.
                subst hk_eq
                -- Step 1: vk = v_i.
                have h_v_at :
                    (prefix_walk.comp (σ_ij.comp suffix_walk)).vertices[prefix_walk.length]? =
                      some v_i :=
                  Walk.vertices_comp_at_left_length prefix_walk (σ_ij.comp suffix_walk)
                rw [h_v_at] at h_get
                have hvk_vi : vk = v_i := (Option.some.inj h_get).symm
                subst hvk_vi
                -- Step 2: derive prefix_walk.lastStepHeadAtTarget from h_col.
                have h_prefix_last : prefix_walk.lastStepHeadAtTarget := by
                  by_contra h_not
                  exact (Walk.refactor_IsCollider_comp_at_p_length_no_head_target
                    prefix_walk (σ_ij.comp suffix_walk) h_not) h_col
                -- Step 3: transport prefix_walk.lastStepHeadAtTarget to (π.splitAt i _).snd.1.
                have h_left_on_π : (π.splitAt i hi_le).snd.1.lastStepHeadAtTarget := by
                  show (π.splitAt i hi_le).2.1.lastStepHeadAtTarget
                  rw [← Walk.lastStepHeadAtTarget_cast_target hmid_i_eq]
                  exact h_prefix_last
                -- Step 4: derive (π.splitAt j _).snd.2.firstStepHeadAtSource from ¬ h_caseI.
                have h_right_on_π :
                    (π.splitAt j (Nat.le_of_lt h_j_lt)).2.2.firstStepHeadAtSource := by
                  -- Use the helper for ¬ replaceWalkCaseI.
                  exact Walk.not_replaceWalkCaseI_suffix_firstStepHeadAtSource π j
                    (Nat.le_of_lt h_j_lt) h_caseI
                -- Step 5: apply firstColliderAncestor_π_at_pos.
                have h_anc : (π.splitAt i hi_le).fst ∈ G.AncSet C :=
                  Walk.firstColliderAncestor_π_at_pos π hπ i hi_le h_left_on_π
                    j (Nat.le_of_lt hij) h_j_lt h_right_on_π
                -- Step 6: bridge (π.splitAt i hi_le).fst = v_i via hmid_i_eq.
                rw [hmid_i_eq] at h_anc
                exact h_anc
              · -- C: k = prefix.length + σ_ij.length.
                subst hk_eq
                -- Cases on σ_ij.length: if 0, this collapses to A' position; if > 0,
                -- discharge via no_head_target (last step of σ_ij is .backwardE).
                by_cases hσ_len : σ_ij.length = 0
                · -- σ_ij.length = 0. Reduce to A' case.
                  rw [hσ_len, Nat.add_zero] at h_col h_get
                  -- Now we're at position prefix_walk.length, same as A'.
                  -- Step 1: vk = v_i (same as A').
                  have h_v_at :
                      (prefix_walk.comp (σ_ij.comp suffix_walk)).vertices[prefix_walk.length]? =
                        some v_i :=
                    Walk.vertices_comp_at_left_length prefix_walk (σ_ij.comp suffix_walk)
                  rw [h_v_at] at h_get
                  have hvk_vi : vk = v_i := (Option.some.inj h_get).symm
                  subst hvk_vi
                  have h_prefix_last : prefix_walk.lastStepHeadAtTarget := by
                    by_contra h_not
                    exact (Walk.refactor_IsCollider_comp_at_p_length_no_head_target
                      prefix_walk (σ_ij.comp suffix_walk) h_not) h_col
                  have h_left_on_π : (π.splitAt i hi_le).snd.1.lastStepHeadAtTarget := by
                    show (π.splitAt i hi_le).2.1.lastStepHeadAtTarget
                    rw [← Walk.lastStepHeadAtTarget_cast_target hmid_i_eq]
                    exact h_prefix_last
                  have h_right_on_π :
                      (π.splitAt j (Nat.le_of_lt h_j_lt)).2.2.firstStepHeadAtSource :=
                    Walk.not_replaceWalkCaseI_suffix_firstStepHeadAtSource π j
                      (Nat.le_of_lt h_j_lt) h_caseI
                  have h_anc : (π.splitAt i hi_le).fst ∈ G.AncSet C :=
                    Walk.firstColliderAncestor_π_at_pos π hπ i hi_le h_left_on_π
                      j (Nat.le_of_lt hij) h_j_lt h_right_on_π
                  rw [hmid_i_eq] at h_anc
                  exact h_anc
                · -- σ_ij.length > 0. Discharge via no_head_target.
                  have hσ_pos : 0 < σ_ij.length := Nat.pos_of_ne_zero hσ_len
                  exfalso
                  -- Reduce h_col via _comp_right: π'.IsCollider (prefix + σ_ij.length)
                  -- = (σ_ij.comp suffix).IsCollider σ_ij.length.
                  have h_eq1 :
                      (prefix_walk.comp (σ_ij.comp suffix_walk)).IsCollider
                          (prefix_walk.length + σ_ij.length) =
                      (σ_ij.comp suffix_walk).IsCollider σ_ij.length := by
                    have := Walk.refactor_IsCollider_comp_right prefix_walk
                      (σ_ij.comp suffix_walk) (prefix_walk.length + σ_ij.length) (by omega)
                    rw [show prefix_walk.length + σ_ij.length - prefix_walk.length =
                          σ_ij.length by omega] at this
                    exact this
                  rw [h_eq1] at h_col
                  -- σ_ij is backward-directed with positive length: last step is .backwardE,
                  -- so lastStepHeadAtTarget = False.
                  have h_no_target : ¬ σ_ij.lastStepHeadAtTarget :=
                    Walk.IsBackwardDirectedWalk.no_lastStepHeadAtTarget σ_ij
                      hσ_ij_back_dir hσ_pos
                  exact (Walk.refactor_IsCollider_comp_at_p_length_no_head_target
                    σ_ij suffix_walk h_no_target) h_col
      · -- BLOCKABLE clause: mirrors Case (i) BLOCKABLE with the
        -- backward-directed σ_ij asymmetries flipped:
        --   - Region B: vacuous via `IsBackwardDirectedWalk.interior_not_blockable`.
        --   - A' HasBlockingRightSlot (σ_ij.length > 0): contradicts via
        --     `IsBackwardDirectedWalk.no_HasBlockingRightSlot` (Case (i) used SCC).
        --   - C HasBlockingLeftSlot (σ_ij.length > 0): contradicts via
        --     `no_HasBlockingLeftSlot_of_all_in_SCC` (Case (i) used direction).
        -- All other regions are mechanically identical to Case (i) BLOCKABLE.
        intro k vk h_get h_blk
        have h_prefix_len : prefix_walk.length = i := by
          show (hmid_i_eq ▸ (π.splitAt i hi_le).2.1).length = i
          rw [Walk.length_cast_target hmid_i_eq]
          exact Walk.splitAt_length_left π i hi_le
        have h_suffix_len : suffix_walk.length = π.length - j := by
          show (hmid_j_eq ▸ (π.splitAt j hjn).2.2).length = π.length - j
          rw [Walk.length_cast_source hmid_j_eq]
          exact Walk.splitAt_length_right π j hjn
        have h_π'_len :
            (prefix_walk.comp (σ_ij.comp suffix_walk)).length =
              i + σ_ij.length + (π.length - j) := by
          rw [Walk.length_comp, Walk.length_comp, h_prefix_len, h_suffix_len]
          omega
        have hσ_ij_back_dir : σ_ij.IsBackwardDirectedWalk := by
          show (σ_ji.reverse : Walk G v_i v_j).IsBackwardDirectedWalk
          exact Walk.reverse_isBackwardDirected_of_directed σ_ji hσ_ji_dir
        have h_σ_SCC : ∀ x ∈ σ_ij.vertices, x ∈ G.Sc v_j := by
          have h_vert_eq : σ_ij.vertices = σ_ji.vertices.reverse :=
            Walk.vertices_reverse σ_ji
          intro x hx
          rw [h_vert_eq, List.mem_reverse] at hx
          have h_anc_vi : x ∈ G.Anc v_i :=
            Walk.directed_vertex_mem_Anc σ_ji hσ_ji_dir hx
          have h_desc_vj : x ∈ G.Desc v_j :=
            Walk.directed_vertex_mem_Desc σ_ji hσ_ji_dir hx
          have h_vi_anc_vj : v_i ∈ G.Anc v_j := mem_Anc_of_mem_Sc h_Sc
          exact ⟨mem_Anc_trans h_anc_vi h_vi_anc_vj, h_desc_vj⟩
        have h_prefix_v : prefix_walk.vertices = π.vertices.take (i + 1) := by
          show (hmid_i_eq ▸ (π.splitAt i hi_le).2.1).vertices = π.vertices.take (i + 1)
          rw [Walk.vertices_cast_target hmid_i_eq]
          exact Walk.splitAt_vertices_left π i hi_le
        have h_suffix_v : suffix_walk.vertices = π.vertices.drop j := by
          show (hmid_j_eq ▸ (π.splitAt j hjn).2.2).vertices = π.vertices.drop j
          rw [Walk.vertices_cast_source hmid_j_eq]
          exact Walk.splitAt_vertices_right π j hjn
        have h_π'_v_raw :
            (prefix_walk.comp (σ_ij.comp suffix_walk)).vertices =
              prefix_walk.vertices.dropLast ++ σ_ij.vertices.dropLast ++
                suffix_walk.vertices := by
          rw [Walk.vertices_comp, Walk.vertices_comp, ← List.append_assoc]
        have h_take_len : π.vertices.length = π.length + 1 :=
          Walk.vertices_length π
        have h_σ_len : σ_ij.vertices.length = σ_ij.length + 1 :=
          Walk.vertices_length σ_ij
        have h_len_take : (π.vertices.take (i + 1)).dropLast.length = i := by
          rw [List.length_dropLast, List.length_take, h_take_len]; omega
        have h_len_σ_dropLast : σ_ij.vertices.dropLast.length = σ_ij.length := by
          rw [List.length_dropLast, h_σ_len]; omega
        have h_len_combined :
            ((π.vertices.take (i + 1)).dropLast ++ σ_ij.vertices.dropLast).length
              = i + σ_ij.length := by
          rw [List.length_append, h_len_take, h_len_σ_dropLast]
        by_cases hk_int_strict :
            prefix_walk.length < k ∧ k < prefix_walk.length + σ_ij.length
        · -- Region B (strict interior of σ_ij): vacuous via
          -- `IsBackwardDirectedWalk.interior_not_blockable`.
          obtain ⟨hk_lo, hk_hi⟩ := hk_int_strict
          exfalso
          obtain ⟨h_nc, h_disj⟩ := h_blk
          apply Walk.IsBackwardDirectedWalk.interior_not_blockable σ_ij
            hσ_ij_back_dir h_σ_SCC (k - prefix_walk.length) (by omega) (by omega)
          refine ⟨?_, ?_⟩
          · refine ⟨by omega, ?_⟩
            intro h_coll_σ
            apply h_nc.2
            have h_eq1 :
                (prefix_walk.comp (σ_ij.comp suffix_walk)).IsCollider k =
                (σ_ij.comp suffix_walk).IsCollider
                  (k - prefix_walk.length) :=
              Walk.refactor_IsCollider_comp_right
                prefix_walk (σ_ij.comp suffix_walk) k hk_lo
            have h_eq2 :
                (σ_ij.comp suffix_walk).IsCollider
                  (k - prefix_walk.length) =
                σ_ij.IsCollider (k - prefix_walk.length) :=
              Walk.refactor_IsCollider_comp_left σ_ij suffix_walk
                (k - prefix_walk.length) (by omega)
            rw [h_eq1, h_eq2]
            exact h_coll_σ
          · rcases h_disj with hk_eq | hk_eq | h_blkleft | h_blkright
            · omega
            · exfalso
              rw [h_π'_len] at hk_eq
              rw [h_prefix_len] at hk_hi
              omega
            · right; right; left
              have h_eq1 :=
                Walk.HasBlockingLeftSlot_comp_right
                  prefix_walk (σ_ij.comp suffix_walk) k hk_lo
              have h_eq2 :=
                Walk.HasBlockingLeftSlot_comp_left σ_ij suffix_walk
                  (k - prefix_walk.length) (by omega)
              rw [h_eq1, h_eq2] at h_blkleft
              exact h_blkleft
            · right; right; right
              have h_eq1 :=
                Walk.HasBlockingRightSlot_comp_right
                  prefix_walk (σ_ij.comp suffix_walk) k (by omega)
              have h_eq2 :=
                Walk.HasBlockingRightSlot_comp_left σ_ij suffix_walk
                  (k - prefix_walk.length) (by omega)
              rw [h_eq1, h_eq2] at h_blkright
              exact h_blkright
        · push_neg at hk_int_strict
          by_cases hk_d : prefix_walk.length + σ_ij.length < k
          · -- Region D (suffix interior): transport back to π at
            -- position j + (k - i - σ_ij.length).  Mechanically identical
            -- to Case (i) Region D — σ_ij's directedness is not consulted.
            obtain ⟨h_nc, h_disj⟩ := h_blk
            have hk_lo : prefix_walk.length < k := by omega
            have hk_lo2 : σ_ij.length < k - prefix_walk.length := by omega
            have h_split_len : (π.splitAt j hjn).2.1.length = j :=
              Walk.splitAt_length_left π j hjn
            set k_π : ℕ := j + (k - prefix_walk.length - σ_ij.length)
              with hk_π_def
            have hk_π_le : k_π ≤ π.length := by
              have h_k_le :
                  k ≤ (prefix_walk.comp (σ_ij.comp suffix_walk)).length := h_nc.1
              rw [h_π'_len] at h_k_le
              rw [hk_π_def, h_prefix_len]
              omega
            have hk_lo3 :
                (π.splitAt j hjn).2.1.length <
                  j + (k - prefix_walk.length - σ_ij.length) := by
              rw [h_split_len]; omega
            -- IsCollider transport
            have h_eq1_coll :
                (prefix_walk.comp (σ_ij.comp suffix_walk)).IsCollider k =
                (σ_ij.comp suffix_walk).IsCollider
                  (k - prefix_walk.length) :=
              Walk.refactor_IsCollider_comp_right
                prefix_walk (σ_ij.comp suffix_walk) k hk_lo
            have h_eq2_coll :
                (σ_ij.comp suffix_walk).IsCollider
                  (k - prefix_walk.length) =
                suffix_walk.IsCollider
                  (k - prefix_walk.length - σ_ij.length) :=
              Walk.refactor_IsCollider_comp_right σ_ij suffix_walk
                (k - prefix_walk.length) hk_lo2
            have h_eq3_coll :
                suffix_walk.IsCollider
                  (k - prefix_walk.length - σ_ij.length) =
                (π.splitAt j hjn).2.2.IsCollider
                  (k - prefix_walk.length - σ_ij.length) := by
              show (hmid_j_eq ▸ (π.splitAt j hjn).2.2).IsCollider _ = _
              rw [Walk.refactor_IsCollider_cast_source hmid_j_eq]
            have h_eq4_coll :
                Walk.IsCollider
                    ((π.splitAt j hjn).2.1.comp (π.splitAt j hjn).2.2)
                  (j + (k - prefix_walk.length - σ_ij.length)) =
                Walk.IsCollider (π.splitAt j hjn).2.2
                  ((j + (k - prefix_walk.length - σ_ij.length)) -
                    (π.splitAt j hjn).2.1.length) :=
              Walk.refactor_IsCollider_comp_right
                (π.splitAt j hjn).2.1 (π.splitAt j hjn).2.2 _ hk_lo3
            rw [Walk.splitAt_comp π j hjn] at h_eq4_coll
            rw [h_split_len] at h_eq4_coll
            have h_arith :
                j + (k - prefix_walk.length - σ_ij.length) - j =
                k - prefix_walk.length - σ_ij.length := by omega
            rw [h_arith] at h_eq4_coll
            -- HasBlockingLeftSlot transport
            have h_eq1_left :
                (prefix_walk.comp (σ_ij.comp suffix_walk)).HasBlockingLeftSlot k =
                (σ_ij.comp suffix_walk).HasBlockingLeftSlot
                  (k - prefix_walk.length) :=
              Walk.HasBlockingLeftSlot_comp_right prefix_walk
                (σ_ij.comp suffix_walk) k hk_lo
            have h_eq2_left :
                (σ_ij.comp suffix_walk).HasBlockingLeftSlot
                  (k - prefix_walk.length) =
                suffix_walk.HasBlockingLeftSlot
                  (k - prefix_walk.length - σ_ij.length) :=
              Walk.HasBlockingLeftSlot_comp_right σ_ij suffix_walk
                (k - prefix_walk.length) hk_lo2
            have h_eq3_left :
                suffix_walk.HasBlockingLeftSlot
                  (k - prefix_walk.length - σ_ij.length) =
                (π.splitAt j hjn).2.2.HasBlockingLeftSlot
                  (k - prefix_walk.length - σ_ij.length) := by
              show (hmid_j_eq ▸ (π.splitAt j hjn).2.2).HasBlockingLeftSlot _ = _
              rw [Walk.HasBlockingLeftSlot_cast_source hmid_j_eq]
            have h_eq4_left :
                Walk.HasBlockingLeftSlot
                    ((π.splitAt j hjn).2.1.comp (π.splitAt j hjn).2.2)
                  (j + (k - prefix_walk.length - σ_ij.length)) =
                Walk.HasBlockingLeftSlot (π.splitAt j hjn).2.2
                  ((j + (k - prefix_walk.length - σ_ij.length)) -
                    (π.splitAt j hjn).2.1.length) :=
              Walk.HasBlockingLeftSlot_comp_right
                (π.splitAt j hjn).2.1 (π.splitAt j hjn).2.2 _ hk_lo3
            rw [Walk.splitAt_comp π j hjn] at h_eq4_left
            rw [h_split_len, h_arith] at h_eq4_left
            -- HasBlockingRightSlot transport (≤ instead of <)
            have h_eq1_right :
                (prefix_walk.comp (σ_ij.comp suffix_walk)).HasBlockingRightSlot k =
                (σ_ij.comp suffix_walk).HasBlockingRightSlot
                  (k - prefix_walk.length) :=
              Walk.HasBlockingRightSlot_comp_right prefix_walk
                (σ_ij.comp suffix_walk) k (by omega)
            have h_eq2_right :
                (σ_ij.comp suffix_walk).HasBlockingRightSlot
                  (k - prefix_walk.length) =
                suffix_walk.HasBlockingRightSlot
                  (k - prefix_walk.length - σ_ij.length) :=
              Walk.HasBlockingRightSlot_comp_right σ_ij suffix_walk
                (k - prefix_walk.length) (by omega)
            have h_eq3_right :
                suffix_walk.HasBlockingRightSlot
                  (k - prefix_walk.length - σ_ij.length) =
                (π.splitAt j hjn).2.2.HasBlockingRightSlot
                  (k - prefix_walk.length - σ_ij.length) := by
              show (hmid_j_eq ▸ (π.splitAt j hjn).2.2).HasBlockingRightSlot _ = _
              rw [Walk.HasBlockingRightSlot_cast_source hmid_j_eq]
            have h_eq4_right :
                Walk.HasBlockingRightSlot
                    ((π.splitAt j hjn).2.1.comp (π.splitAt j hjn).2.2)
                  (j + (k - prefix_walk.length - σ_ij.length)) =
                Walk.HasBlockingRightSlot (π.splitAt j hjn).2.2
                  ((j + (k - prefix_walk.length - σ_ij.length)) -
                    (π.splitAt j hjn).2.1.length) :=
              Walk.HasBlockingRightSlot_comp_right
                (π.splitAt j hjn).2.1 (π.splitAt j hjn).2.2 _ (by
                  rw [h_split_len]; omega)
            rw [Walk.splitAt_comp π j hjn] at h_eq4_right
            rw [h_split_len, h_arith] at h_eq4_right
            -- Build π.IsBlockableNonCollider k_π
            have h_nc_π : π.IsNonCollider k_π := by
              refine ⟨hk_π_le, ?_⟩
              intro h_coll_π
              apply h_nc.2
              rw [h_eq1_coll, h_eq2_coll, h_eq3_coll, ← h_eq4_coll]
              exact h_coll_π
            have h_disj_π : k_π = 0 ∨ k_π = π.length ∨
                π.HasBlockingLeftSlot k_π ∨ π.HasBlockingRightSlot k_π := by
              rcases h_disj with hk_eq | hk_eq | h_blkleft | h_blkright
              · omega
              · right; left
                rw [h_π'_len] at hk_eq
                show k_π = π.length
                rw [hk_π_def]
                omega
              · right; right; left
                rw [h_eq1_left, h_eq2_left, h_eq3_left, ← h_eq4_left] at h_blkleft
                exact h_blkleft
              · right; right; right
                rw [h_eq1_right, h_eq2_right, h_eq3_right, ← h_eq4_right]
                  at h_blkright
                exact h_blkright
            -- Translate h_get to π at position k_π
            rw [h_π'_v_raw, h_prefix_v, h_suffix_v] at h_get
            have h_k_combined :
                ((π.vertices.take (i + 1)).dropLast ++ σ_ij.vertices.dropLast).length
                  ≤ k := by
              rw [h_len_combined, ← h_prefix_len]; omega
            rw [List.getElem?_append_right h_k_combined, h_len_combined,
                List.getElem?_drop] at h_get
            have h_idx_eq :
                j + (k - (i + σ_ij.length)) = k_π := by
              rw [hk_π_def, h_prefix_len]; omega
            rw [h_idx_eq] at h_get
            exact hπ.2 k_π vk h_get ⟨h_nc_π, h_disj_π⟩
          · by_cases hk_a : k < prefix_walk.length
            · -- Region A (prefix interior): mechanically identical to Case (i).
              obtain ⟨h_nc, h_disj⟩ := h_blk
              have h_split_len : (π.splitAt i hi_le).2.1.length = i :=
                Walk.splitAt_length_left π i hi_le
              have hk_split : k < (π.splitAt i hi_le).2.1.length := by
                rw [h_split_len, ← h_prefix_len]; exact hk_a
              -- IsCollider transport: π' k → prefix k → split.2.1 k → π k
              have h_eq1_coll :
                  (prefix_walk.comp (σ_ij.comp suffix_walk)).IsCollider k =
                  prefix_walk.IsCollider k :=
                Walk.refactor_IsCollider_comp_left
                  prefix_walk (σ_ij.comp suffix_walk) k hk_a
              have h_eq2_coll :
                  prefix_walk.IsCollider k =
                  (π.splitAt i hi_le).2.1.IsCollider k := by
                show (hmid_i_eq ▸ (π.splitAt i hi_le).2.1).IsCollider k = _
                rw [Walk.refactor_IsCollider_cast_target hmid_i_eq]
              have h_eq3_coll :
                  Walk.IsCollider
                      ((π.splitAt i hi_le).2.1.comp (π.splitAt i hi_le).2.2) k =
                  (π.splitAt i hi_le).2.1.IsCollider k :=
                Walk.refactor_IsCollider_comp_left
                  (π.splitAt i hi_le).2.1 (π.splitAt i hi_le).2.2 k hk_split
              rw [Walk.splitAt_comp π i hi_le] at h_eq3_coll
              -- HasBlockingLeftSlot transport
              have h_eq1_left :
                  (prefix_walk.comp (σ_ij.comp suffix_walk)).HasBlockingLeftSlot k =
                  prefix_walk.HasBlockingLeftSlot k :=
                Walk.HasBlockingLeftSlot_comp_left prefix_walk
                  (σ_ij.comp suffix_walk) k (by omega)
              have h_eq2_left :
                  prefix_walk.HasBlockingLeftSlot k =
                  (π.splitAt i hi_le).2.1.HasBlockingLeftSlot k := by
                show (hmid_i_eq ▸ (π.splitAt i hi_le).2.1).HasBlockingLeftSlot k = _
                rw [Walk.HasBlockingLeftSlot_cast_target hmid_i_eq]
              have h_eq3_left :
                  Walk.HasBlockingLeftSlot
                      ((π.splitAt i hi_le).2.1.comp (π.splitAt i hi_le).2.2) k =
                  (π.splitAt i hi_le).2.1.HasBlockingLeftSlot k :=
                Walk.HasBlockingLeftSlot_comp_left
                  (π.splitAt i hi_le).2.1 (π.splitAt i hi_le).2.2 k (by omega)
              rw [Walk.splitAt_comp π i hi_le] at h_eq3_left
              -- HasBlockingRightSlot transport
              have h_eq1_right :
                  (prefix_walk.comp (σ_ij.comp suffix_walk)).HasBlockingRightSlot k =
                  prefix_walk.HasBlockingRightSlot k :=
                Walk.HasBlockingRightSlot_comp_left prefix_walk
                  (σ_ij.comp suffix_walk) k hk_a
              have h_eq2_right :
                  prefix_walk.HasBlockingRightSlot k =
                  (π.splitAt i hi_le).2.1.HasBlockingRightSlot k := by
                show (hmid_i_eq ▸ (π.splitAt i hi_le).2.1).HasBlockingRightSlot k = _
                rw [Walk.HasBlockingRightSlot_cast_target hmid_i_eq]
              have h_eq3_right :
                  Walk.HasBlockingRightSlot
                      ((π.splitAt i hi_le).2.1.comp (π.splitAt i hi_le).2.2) k =
                  (π.splitAt i hi_le).2.1.HasBlockingRightSlot k :=
                Walk.HasBlockingRightSlot_comp_left
                  (π.splitAt i hi_le).2.1 (π.splitAt i hi_le).2.2 k hk_split
              rw [Walk.splitAt_comp π i hi_le] at h_eq3_right
              -- Build π.IsBlockableNonCollider k
              have h_nc_π : π.IsNonCollider k := by
                refine ⟨by omega, ?_⟩
                intro h_coll_π
                apply h_nc.2
                rw [h_eq1_coll, h_eq2_coll, ← h_eq3_coll]
                exact h_coll_π
              have h_disj_π : k = 0 ∨ k = π.length ∨
                  π.HasBlockingLeftSlot k ∨ π.HasBlockingRightSlot k := by
                rcases h_disj with hk_eq | hk_eq | h_blkleft | h_blkright
                · exact Or.inl hk_eq
                · exfalso
                  rw [h_π'_len] at hk_eq
                  omega
                · right; right; left
                  rw [h_eq1_left, h_eq2_left, ← h_eq3_left] at h_blkleft
                  exact h_blkleft
                · right; right; right
                  rw [h_eq1_right, h_eq2_right, ← h_eq3_right] at h_blkright
                  exact h_blkright
              -- Translate h_get to π
              rw [h_π'_v_raw, h_prefix_v, h_suffix_v] at h_get
              have hk_in_first :
                  k < ((π.vertices.take (i + 1)).dropLast).length := by
                rw [h_len_take, ← h_prefix_len]; exact hk_a
              have hk_in_combined :
                  k < ((π.vertices.take (i + 1)).dropLast ++
                       σ_ij.vertices.dropLast).length := by
                rw [List.length_append]; omega
              rw [List.getElem?_append_left hk_in_combined,
                  List.getElem?_append_left hk_in_first] at h_get
              have h_take_drop_eq :
                  (π.vertices.take (i + 1)).dropLast = π.vertices.take i := by
                rw [List.dropLast_eq_take, List.length_take, h_take_len,
                    show min (i + 1) (π.length + 1) = i + 1 by omega,
                    show i + 1 - 1 = i from rfl, List.take_take,
                    show min i (i + 1) = i by omega]
              rw [h_take_drop_eq, List.getElem?_take,
                  if_pos (show k < i by omega)] at h_get
              exact hπ.2 k vk h_get ⟨h_nc_π, h_disj_π⟩
            · -- Splice endpoints A' (k = prefix.length) or
              -- C (k = prefix.length + σ_ij.length).
              obtain ⟨h_nc, h_disj⟩ := h_blk
              rcases h_disj with hk0 | hkπ' | h_blkleft | h_blkright
              · -- Disjunct: k = 0. Forces i = 0. vk = u.
                subst hk0
                have hi_zero : i = 0 := by omega
                have h_π'_zero :
                    (prefix_walk.comp (σ_ij.comp suffix_walk)).vertices[0]? = some u :=
                  Walk.vertices_zero_eq_source _
                rw [h_π'_zero] at h_get
                have hvk_u : vk = u := (Option.some.inj h_get).symm
                have h_get_π : π.vertices[0]? = some vk := by
                  rw [Walk.vertices_zero_eq_source π, hvk_u]
                refine hπ.2 0 vk h_get_π ⟨⟨by omega, ?_⟩, Or.inl rfl⟩
                exact Walk.refactor_IsCollider_zero_eq_False π
              · -- Disjunct: k = π'.length. Forces j = π.length. vk = w.
                have hkπ'_unfolded :
                    k = (prefix_walk.comp (σ_ij.comp suffix_walk)).length := hkπ'
                have h_π'_end :
                    (prefix_walk.comp (σ_ij.comp suffix_walk)).vertices[
                      (prefix_walk.comp (σ_ij.comp suffix_walk)).length]? = some w :=
                  Walk.vertices_length_eq_target _
                rw [hkπ'_unfolded, h_π'_end] at h_get
                have hvk_w : vk = w := (Option.some.inj h_get).symm
                have h_j_eq : j = π.length := by
                  have h_π'_eq : (prefix_walk.comp (σ_ij.comp suffix_walk)).length =
                      i + σ_ij.length + (π.length - j) := h_π'_len
                  have hk_eq_π'_len : k = i + σ_ij.length + (π.length - j) := by
                    rw [hkπ'_unfolded]; exact h_π'_eq
                  have hk_le : k ≤ i + σ_ij.length := by
                    rw [← h_prefix_len]; omega
                  omega
                have h_get_π : π.vertices[π.length]? = some vk := by
                  rw [Walk.vertices_length_eq_target π, hvk_w]
                refine hπ.2 π.length vk h_get_π
                  ⟨⟨Nat.le_refl _, ?_⟩, Or.inr (Or.inl rfl)⟩
                exact Walk.refactor_IsCollider_length_eq_False π
              · -- Disjunct: HasBlockingLeftSlot k.
                -- Splice constraint gives k = prefix.length OR
                -- k = prefix.length + σ_ij.length.
                by_cases hk_at_A : k = prefix_walk.length
                · -- A': k = prefix.length.  Identical to Case (i):
                  -- transport prefix.HasBlockingLeftSlot to π.HasBlockingLeftSlot i.
                  subst hk_at_A
                  have h_eq1_left :
                      (prefix_walk.comp (σ_ij.comp suffix_walk)).HasBlockingLeftSlot
                          prefix_walk.length =
                      prefix_walk.HasBlockingLeftSlot prefix_walk.length :=
                    Walk.HasBlockingLeftSlot_comp_left prefix_walk
                      (σ_ij.comp suffix_walk) prefix_walk.length (Nat.le_refl _)
                  rw [h_eq1_left, h_prefix_len] at h_blkleft
                  have h_eq2_left :
                      prefix_walk.HasBlockingLeftSlot i =
                      (π.splitAt i hi_le).2.1.HasBlockingLeftSlot i := by
                    show (hmid_i_eq ▸ (π.splitAt i hi_le).2.1).HasBlockingLeftSlot i = _
                    rw [Walk.HasBlockingLeftSlot_cast_target hmid_i_eq]
                  rw [h_eq2_left] at h_blkleft
                  have h_eq3_left :
                      Walk.HasBlockingLeftSlot
                          ((π.splitAt i hi_le).2.1.comp (π.splitAt i hi_le).2.2) i =
                      (π.splitAt i hi_le).2.1.HasBlockingLeftSlot i :=
                    Walk.HasBlockingLeftSlot_comp_left
                      (π.splitAt i hi_le).2.1 (π.splitAt i hi_le).2.2 i (by
                        rw [Walk.splitAt_length_left π i hi_le])
                  rw [Walk.splitAt_comp π i hi_le] at h_eq3_left
                  rw [← h_eq3_left] at h_blkleft
                  have h_π'_v_at_i :
                      (prefix_walk.comp (σ_ij.comp suffix_walk)).vertices[
                        prefix_walk.length]? = some v_i :=
                    Walk.vertices_comp_at_left_length prefix_walk (σ_ij.comp suffix_walk)
                  rw [h_π'_v_at_i] at h_get
                  have hvk_vi : vk = v_i := (Option.some.inj h_get).symm
                  have h_get_π : π.vertices[i]? = some vk := by
                    rw [h_get_i, hvk_vi]
                  refine hπ.2 i vk h_get_π
                    ⟨⟨hi_le, ?_⟩, Or.inr (Or.inr (Or.inl h_blkleft))⟩
                  exact Walk.HasBlockingLeftSlot.not_refactor_IsCollider π i h_blkleft
                · -- C: k > prefix.length (so k = prefix.length + σ_ij.length
                  --   AND σ_ij.length > 0).  σ_ij is backward-directed and its
                  --   vertices all lie in Sc(v_j), so HasBlockingLeftSlot is
                  --   ruled out by the SCC argument (mirror of Case (i)'s
                  --   direction argument for HasBlockingRightSlot at C).
                  have hk_at_C : k = prefix_walk.length + σ_ij.length := by omega
                  have hσ_pos : 0 < σ_ij.length := by omega
                  subst hk_at_C
                  exfalso
                  have h_eq1_left :
                      (prefix_walk.comp (σ_ij.comp suffix_walk)).HasBlockingLeftSlot
                          (prefix_walk.length + σ_ij.length) =
                      (σ_ij.comp suffix_walk).HasBlockingLeftSlot σ_ij.length := by
                    have := Walk.HasBlockingLeftSlot_comp_right prefix_walk
                      (σ_ij.comp suffix_walk) (prefix_walk.length + σ_ij.length)
                      (by omega)
                    rw [show prefix_walk.length + σ_ij.length - prefix_walk.length =
                          σ_ij.length by omega] at this
                    exact this
                  have h_eq2_left :
                      (σ_ij.comp suffix_walk).HasBlockingLeftSlot σ_ij.length =
                      σ_ij.HasBlockingLeftSlot σ_ij.length :=
                    Walk.HasBlockingLeftSlot_comp_left σ_ij suffix_walk σ_ij.length
                      (Nat.le_refl _)
                  rw [h_eq1_left, h_eq2_left] at h_blkleft
                  exact Walk.no_HasBlockingLeftSlot_of_all_in_SCC σ_ij h_σ_SCC _
                    h_blkleft
              · -- Disjunct: HasBlockingRightSlot k.
                -- If σ_ij.length > 0 AND k = prefix.length: slot is σ_ij's first
                --   (.backwardE).  HasBlockingRightSlot requires .forwardE — under
                --   backward-direction this is uniformly False (mirror of Case (i)'s
                --   SCC argument).
                -- Otherwise (σ_ij.length = 0, OR k = prefix.length + σ_ij.length):
                --   slot is suffix's first.  Transport to π.HasBlockingRightSlot j.
                by_cases hσ_pos : 0 < σ_ij.length
                · -- σ_ij.length > 0
                  by_cases hk_at_A : k = prefix_walk.length
                  · -- A' with σ_ij.length > 0: slot in σ_ij first,
                    --   .backwardE in σ_ij contradicts HasBlockingRightSlot.
                    subst hk_at_A
                    exfalso
                    have h_eq1_right :
                        (prefix_walk.comp (σ_ij.comp suffix_walk)).HasBlockingRightSlot
                            prefix_walk.length =
                        (σ_ij.comp suffix_walk).HasBlockingRightSlot 0 := by
                      have := Walk.HasBlockingRightSlot_comp_right prefix_walk
                        (σ_ij.comp suffix_walk) prefix_walk.length (Nat.le_refl _)
                      rw [Nat.sub_self] at this
                      exact this
                    have h_eq2_right :
                        (σ_ij.comp suffix_walk).HasBlockingRightSlot 0 =
                        σ_ij.HasBlockingRightSlot 0 :=
                      Walk.HasBlockingRightSlot_comp_left σ_ij suffix_walk 0 hσ_pos
                    rw [h_eq1_right, h_eq2_right] at h_blkright
                    exact Walk.IsBackwardDirectedWalk.no_HasBlockingRightSlot σ_ij
                      hσ_ij_back_dir 0 h_blkright
                  · -- C: k = prefix.length + σ_ij.length, slot in suffix
                    have hk_at_C : k = prefix_walk.length + σ_ij.length := by omega
                    subst hk_at_C
                    have h_eq1_right :
                        (prefix_walk.comp (σ_ij.comp suffix_walk)).HasBlockingRightSlot
                            (prefix_walk.length + σ_ij.length) =
                        (σ_ij.comp suffix_walk).HasBlockingRightSlot σ_ij.length := by
                      have := Walk.HasBlockingRightSlot_comp_right prefix_walk
                        (σ_ij.comp suffix_walk) (prefix_walk.length + σ_ij.length)
                        (by omega)
                      rw [show prefix_walk.length + σ_ij.length - prefix_walk.length =
                            σ_ij.length by omega] at this
                      exact this
                    have h_eq2_right :
                        (σ_ij.comp suffix_walk).HasBlockingRightSlot σ_ij.length =
                        suffix_walk.HasBlockingRightSlot 0 := by
                      have := Walk.HasBlockingRightSlot_comp_right σ_ij suffix_walk
                        σ_ij.length (Nat.le_refl _)
                      rw [Nat.sub_self] at this
                      exact this
                    rw [h_eq1_right, h_eq2_right] at h_blkright
                    have h_eq3_right :
                        suffix_walk.HasBlockingRightSlot 0 =
                        (π.splitAt j hjn).2.2.HasBlockingRightSlot 0 := by
                      show (hmid_j_eq ▸ (π.splitAt j hjn).2.2).HasBlockingRightSlot 0 = _
                      rw [Walk.HasBlockingRightSlot_cast_source hmid_j_eq]
                    rw [h_eq3_right] at h_blkright
                    have h_split_len : (π.splitAt j hjn).2.1.length = j :=
                      Walk.splitAt_length_left π j hjn
                    have h_eq4_right :
                        Walk.HasBlockingRightSlot
                            ((π.splitAt j hjn).2.1.comp (π.splitAt j hjn).2.2) j =
                        (π.splitAt j hjn).2.2.HasBlockingRightSlot 0 := by
                      have := Walk.HasBlockingRightSlot_comp_right
                        (π.splitAt j hjn).2.1 (π.splitAt j hjn).2.2 j (by
                          rw [h_split_len])
                      rw [h_split_len, Nat.sub_self] at this
                      exact this
                    rw [Walk.splitAt_comp π j hjn] at h_eq4_right
                    rw [← h_eq4_right] at h_blkright
                    have h_π'_v_at_C :
                        (prefix_walk.comp (σ_ij.comp suffix_walk)).vertices[
                          prefix_walk.length + σ_ij.length]? = some v_j := by
                      rw [Walk.vertices_comp_right_shift]
                      exact Walk.vertices_comp_at_left_length σ_ij suffix_walk
                    rw [h_π'_v_at_C] at h_get
                    have hvk_vj : vk = v_j := (Option.some.inj h_get).symm
                    have h_get_π : π.vertices[j]? = some vk := by
                      rw [h_get_j, hvk_vj]
                    refine hπ.2 j vk h_get_π
                      ⟨⟨hjn, ?_⟩, Or.inr (Or.inr (Or.inr h_blkright))⟩
                    exact Walk.HasBlockingRightSlot.not_refactor_IsCollider π j h_blkright
                · -- σ_ij.length = 0: σ_ij is nil, σ_ij.comp suffix = suffix
                  --   (modulo definitional reduction).  Slot is suffix's first.
                  --   Same shape as Case (i)'s σ_ij = .nil branch.
                  have hσ_zero : σ_ij.length = 0 := by omega
                  have hk_at : k = prefix_walk.length := by omega
                  subst hk_at
                  have h_eq1_right :
                      (prefix_walk.comp (σ_ij.comp suffix_walk)).HasBlockingRightSlot
                          prefix_walk.length =
                      (σ_ij.comp suffix_walk).HasBlockingRightSlot 0 := by
                    have := Walk.HasBlockingRightSlot_comp_right prefix_walk
                      (σ_ij.comp suffix_walk) prefix_walk.length (Nat.le_refl _)
                    rw [Nat.sub_self] at this
                    exact this
                  have h_eq2_right :
                      (σ_ij.comp suffix_walk).HasBlockingRightSlot 0 =
                      suffix_walk.HasBlockingRightSlot (0 - σ_ij.length) :=
                    Walk.HasBlockingRightSlot_comp_right σ_ij suffix_walk 0 (by omega)
                  rw [hσ_zero, Nat.zero_sub] at h_eq2_right
                  rw [h_eq1_right, h_eq2_right] at h_blkright
                  have h_eq3_right :
                      suffix_walk.HasBlockingRightSlot 0 =
                      (π.splitAt j hjn).2.2.HasBlockingRightSlot 0 := by
                    show (hmid_j_eq ▸ (π.splitAt j hjn).2.2).HasBlockingRightSlot 0 = _
                    rw [Walk.HasBlockingRightSlot_cast_source hmid_j_eq]
                  rw [h_eq3_right] at h_blkright
                  have h_split_len : (π.splitAt j hjn).2.1.length = j :=
                    Walk.splitAt_length_left π j hjn
                  have h_eq4_right :
                      Walk.HasBlockingRightSlot
                          ((π.splitAt j hjn).2.1.comp (π.splitAt j hjn).2.2) j =
                      (π.splitAt j hjn).2.2.HasBlockingRightSlot 0 := by
                    have := Walk.HasBlockingRightSlot_comp_right
                      (π.splitAt j hjn).2.1 (π.splitAt j hjn).2.2 j (by
                        rw [h_split_len])
                    rw [h_split_len, Nat.sub_self] at this
                    exact this
                  rw [Walk.splitAt_comp π j hjn] at h_eq4_right
                  rw [← h_eq4_right] at h_blkright
                  have h_π'_v_at :
                      (prefix_walk.comp (σ_ij.comp suffix_walk)).vertices[
                        prefix_walk.length]? = some v_i :=
                    Walk.vertices_comp_at_left_length prefix_walk (σ_ij.comp suffix_walk)
                  rw [h_π'_v_at] at h_get
                  have hvk_vi : vk = v_i := (Option.some.inj h_get).symm
                  -- v_i = v_j via σ_ji's structure: σ_ij = σ_ji.reverse, and
                  -- σ_ij.length = 0 → σ_ji.length = 0 (length_reverse) → σ_ji = .nil v_j,
                  -- type-forced v_j = v_i.
                  have hσ_ji_zero : σ_ji.length = 0 := by
                    have h_eq : σ_ij.length = σ_ji.length := by
                      change σ_ji.reverse.length = σ_ji.length
                      exact Walk.length_reverse σ_ji
                    omega
                  have h_vi_eq_vj : v_i = v_j := by
                    cases h_σ_ji_nil : σ_ji with
                    | nil _ _ => rfl
                    | cons _ _ _ =>
                        rw [h_σ_ji_nil] at hσ_ji_zero
                        simp [Walk.length] at hσ_ji_zero
                  have h_get_π : π.vertices[j]? = some vk := by
                    rw [h_get_j, hvk_vi, h_vi_eq_vj]
                  refine hπ.2 j vk h_get_π
                    ⟨⟨hjn, ?_⟩, Or.inr (Or.inr (Or.inr h_blkright))⟩
                  exact Walk.HasBlockingRightSlot.not_refactor_IsCollider π j h_blkright

end CDMG

end Causality
