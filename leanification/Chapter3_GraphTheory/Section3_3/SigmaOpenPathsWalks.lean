import Chapter3_GraphTheory.Section3_1.CDMG
import Chapter3_GraphTheory.Section3_1.CDMGNotation
import Chapter3_GraphTheory.Section3_1.Walks
import Chapter3_GraphTheory.Section3_1.FamilyRelationships
import Chapter3_GraphTheory.Section3_3.CollidersAndNon
import Chapter3_GraphTheory.Section3_3.BlockableAndUnblockable
import Chapter3_GraphTheory.Section3_3.SigmaBlockedWalks
import Chapter3_GraphTheory.Section3_3.LabelRoman

namespace Causality

/-!
# σ-open walks vs paths vs C-colliders (`claim_3_23` / `prp:sigma_opens`)

This file formalises `claim_3_23` (`\label{prp:sigma_opens}`), the
σ-version of the classical "walks vs paths" three-way equivalence for
C-σ-open walks in a CDMG.

> Let G = (J, V, E, L) be a CDMG.  For C ⊆ J ∪ V, and w₁, w₂ ∈ J ∪ V,
> the following are equivalent:
>
>   1. there exists a C-σ-open *path* between w₁ and w₂ in G;
>   2. there exists a C-σ-open *walk* between w₁ and w₂ in G;
>   3. there exists a C-σ-open *walk* between w₁ and w₂ in G such that
>      all its colliders lie in C (and not just in Ancᴳ(C)).

The authoritative spec is the rewritten canonical tex statement at
`leanification/Chapter3_GraphTheory/Section3_3/tex/`
`claim_3_23_statement_SigmaOpenPathsWalks.tex`, verified equivalent
to the LN block (`graphs.tex`, line 1384, the `\restateprpsigmaopens`
`\begin{restatable}` block).  The rewrite spells out the three
existential quantifiers, pins down the path/walk/σ-open predicates
to their respective LN definition references (`def_3_4` items i and
v for walks and paths, `def:sigma_blocking` item 1 for the σ-open
predicate, `def:collider_noncollider` item ii for the collider
classification used in variant (3)), and disambiguates the
`w₁ = w₂` corner case (the length-0 trivial walk vacuously witnesses
all three variants).

`addition_to_the_LN` for this row is empty — the LN, as captured by
the rewrite, is authoritative.

## Design pillars

1. **`List.TFAE` over a length-3 list, not nested `Iff`s.**  The
   LN's literal "the following three statements are equivalent" is
   the canonical `List.TFAE [P, Q, R]` shape in Mathlib — every
   pairwise implication is recoverable via `List.TFAE.out`, and the
   downstream proof can chain `1 → 2 → 3 → 1`-style cyclic
   implications via `tfae_have` / `tfae_finish`.  A bare three-way
   `Iff` would force a non-canonical associativity choice at the
   statement site (the LN treats the three statements symmetrically,
   not as a left-associated chain).

2. **Existentials over `Walk G w₁ w₂`, not bundled tuples / sigma
   types.**  Walks are `Type`-level data in this chapter
   (`def_3_4`, `Walks.lean`), but the LN's "there exists … such
   that" is `Prop`-level existence; `∃ (π : Walk G w₁ w₂), …` is
   the natural encoding.  Out-of-graph endpoints (`w₁ ∉ G` or
   `w₂ ∉ G` with `w₁ ≠ w₂`) yield no walks, so the existential is
   vacuously false in those cases — consistent with the LN's
   universal quantification over `w₁, w₂ ∈ J ∪ V` (the explicit
   hypothesis below).

3. **Reuse `Walk.IsPath` / `Walk.IsSigmaOpenGiven` / `Walk.IsCollider`
   verbatim, no redefinition of "C-σ-open path" or "C-σ-open walk"
   as bundled predicates.**  The LN's "C-σ-open path" is literally
   "a path that is C-σ-open", encoded as `π.IsPath ∧
   π.IsSigmaOpenGiven C hC`; "C-σ-open walk" is literally
   `π.IsSigmaOpenGiven C hC`; variant (3)'s strengthening is the
   inlined `∀ k vk, π.vertices[k]? = some vk → π.IsCollider k →
   vk ∈ C` (one-clause universal — does not earn its own helper
   under the worker's three-signal rule).

4. **`hC : C ⊆ ↑G.J ∪ ↑G.V` and `hw₁ / hw₂ ∈ ↑G.J ∪ ↑G.V` as
   explicit hypotheses.**  Matches `def_3_17`'s `IsSigmaOpenGiven`
   signature (which already takes `hC`) and the canonical tex
   spec's "Let C ⊆ J ∪ V; let w₁, w₂ ∈ J ∪ V" wording.  The
   `w₁ = w₂` corner case (vacuously witnessed by the length-0
   trivial walk `Walk.nil w₁ hw₁`) is admissible under these
   hypotheses — the trivial walk's `IsPath`, `IsSigmaOpenGiven C hC`,
   and "all colliders in C" predicates are all vacuously true (no
   collider positions, no blockable non-collider positions).

The substantive per-direction design rationale for the proof itself
lives in the comment block immediately above the
`-- claim_3_23 -- start statement` marker, and is filled in by
`add_design_choice_comments` once the proof lands.
-/

end Causality

namespace Causality

namespace CDMG

-- ## Design choice — section-wide statement context
--
-- *Polymorphic `Node : Type*` with `[DecidableEq Node]`.*  Same
--   chapter-wide convention used by every `CDMG`-opening file in
--   Sections 3.1, 3.2 and 3.3 (`Section3_1/CDMG.lean`,
--   `Section3_1/Walks.lean`, `Section3_3/SigmaBlockedWalks.lean`,
--   `Section3_3/SigmaSeparationSymmetric.lean`, etc.).  The
--   `IsSigmaOpenGiven`, `IsPath`, `IsCollider` predicates referenced
--   in the theorem signature below are all parameterised over this
--   same implicit binder block, so the theorem auto-binds these
--   binders into its type.
--
-- *Three-dash `--- start helper` / `--- end helper` markers.*  This
--   `variable` block is statement-typing infrastructure that the
--   wrapped theorem signature cannot compile without — chapter
--   convention for that kind of declaration is the three-dash helper
--   flavour, distinct from the two-dash main-statement marker used
--   to wrap the theorem itself.  Matches the marker convention at
--   `claim_3_22`'s `SigmaSeparationSymmetric.lean:78-80`.
-- claim_3_23 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- claim_3_23 --- end helper

-- ref: claim_3_23 / Prp `prp:sigma_opens`
--
-- Three-way equivalence: for any conditioning set `C ⊆ J ∪ V` and
-- any two graph nodes `w₁, w₂ ∈ J ∪ V`, the following three
-- existence statements are equivalent:
--
--   1. there exists a walk `π` from `w₁` to `w₂` in `G` such that
--      `π` is a path (no repeated vertex) and `π` is C-σ-open;
--   2. there exists a walk `π` from `w₁` to `w₂` in `G` such that
--      `π` is C-σ-open (path-ness dropped);
--   3. there exists a walk `π` from `w₁` to `w₂` in `G` such that
--      `π` is C-σ-open and every collider position `k` on `π`
--      satisfies `v_k ∈ C` (strengthening the LN's `v_k ∈ Anc^G(C)`
--      already enforced by `IsSigmaOpenGiven`).
--
-- LN tex (claim 3.23 / `prp:sigma_opens`, `graphs.tex` line 1384):
--
/-
\begin{restatable}{Prp}{restateprpsigmaopens}\label{prp:sigma_opens}
  Let $G=(J,V,E,L)$ be a CDMG. For $C \subseteq J \cup V$, and
  $w_1, w_2 \in J \cup V$, the following are equivalent:
  \begin{enumerate}
      \item there exists a $C$-$\sigma$-open \emph{path} between
        $w_1$ and $w_2$ in $G$;
      \item there exists a $C$-$\sigma$-open \emph{walk} between
        $w_1$ and $w_2$ in $G$;
      \item there exists a $C$-$\sigma$-open \emph{walk} between
        $w_1$ and $w_2$ in $G$ such that all its colliders lie in
        $C$ (and not just in $\Anc^G(C)$).
  \end{enumerate}
\end{restatable}
-/
--
-- ## Design choice — sigma_open_paths_walks (statement shape)
--
-- *`List.TFAE` over a length-3 list, not nested `Iff` and not three
--   separate `_iff_` lemmas.*  The LN literally states "the
--   following three statements are equivalent", and downstream
--   consumers from chapter 4 onward cite this proposition for
--   *different* pairs of items (sometimes (1)↔(2) for path/walk
--   interchange, sometimes (1)↔(3) for path-with-`C`-colliders,
--   sometimes (3) alone, sometimes all three at once).
--   `List.TFAE` exposes each pair uniformly via `List.TFAE.out i j`
--   and lets the proof itself be written cyclically with
--   `tfae_have 1 → 2 → 3 → 1` / `tfae_finish`.  A nested-`Iff` form
--   like `P ↔ Q ∧ Q ↔ R` would force a non-canonical associativity
--   choice at every call site, and three separate lemmas would
--   pre-commit to one cyclic orientation the LN does not pick.
--
-- *Existentials over `Walk G w₁ w₂`, not bundled tuples / sigma
--   types.*  Walks are `Type`-level data in this chapter
--   (`def_3_4`, `Walks.lean`), but the LN's "there exists … such
--   that" is `Prop`-level; `∃ (π : Walk G w₁ w₂), …` is the
--   natural encoding.  Out-of-graph endpoints yield no walks, so
--   the existential is vacuously false there — consistent with
--   the LN's universal quantification over `w₁, w₂ ∈ J ∪ V`
--   (preserved as the explicit `hw₁ / hw₂` hypotheses below).
--
-- *`π.IsPath ∧ π.IsSigmaOpenGiven C hC` for variant (1); no bundled
--   "is a C-σ-open path" predicate.*  A `def IsSigmaOpenPath`
--   bundling the two would be a one-clause helper (just an `∧`),
--   failing the worker's "needs substantive content" signal for
--   helper extraction; inlining keeps the LN's "is a path AND is
--   C-σ-open" reading visible at the statement surface.
--
-- *Variant (3)'s "all colliders lie in $C$ (and not just in
--   $\Anc^G(C)$)" encoded as an extra conjunct on the same
--   existential, not as a separate predicate.*  The LN literally
--   adds a stronger side condition to the same "C-σ-open walk"
--   notion; encoding it as
--   `π.IsSigmaOpenGiven C hC ∧ <all-colliders-in-C>` with the
--   second conjunct inlined verbatim as
--     `∀ (k : ℕ) (vk : Node), π.vertices[k]? = some vk →
--          π.IsCollider k → vk ∈ C`
--   keeps the LN's wording structure visible at a glance.  The
--   collider predicate `Walk.IsCollider` is `def_3_15` from
--   `Section3_3/CollidersAndNon.lean` (already imported); the
--   `∈ C` (vs.\ `∈ G.AncSet C` inside `IsSigmaOpenGiven`) is the
--   exact strengthening the LN's parenthetical "and not just in
--   $\Anc^G(C)$" calls out.  The conjunct is *not* lifted to a
--   `Walk.AllCollidersIn` helper (single universal quantification,
--   one-shot use at the statement surface); if a downstream row
--   needs it as an independent hypothesis, extracting a helper is
--   a trivial refactor.
--
-- *`hC : C ⊆ ↑G.J ∪ ↑G.V` threaded into the signature, not
--   absorbed into `C`'s type.*  `def_3_17`'s `IsSigmaOpenGiven`
--   (`Section3_3/SigmaBlockedWalks.lean:200-206`) literally takes
--   `(hC : C ⊆ ↑G.J ∪ ↑G.V)` as a hypothesis bundled with `C`, so
--   reusing the *same* `hC` on the outer signature is the only way
--   to make all three TFAE items syntactically about a single `C`
--   — otherwise each existential's body would need its own subset
--   proof and the three items would no longer visibly share their
--   conditioning set.  The `↑G.J ∪ ↑G.V` RHS uses the
--   `Finset Node → Set Node` coercion so the union is computed at
--   the `Set` level.
--
-- *`hw₁ : w₁ ∈ ↑G.J ∪ ↑G.V` and `hw₂ : w₂ ∈ ↑G.J ∪ ↑G.V` on the
--   signature, not bundled into a subtype.*  Two reasons.  (a) The
--   LN's literal "for $w_1, w_2 \in J \cup V$" is preserved
--   verbatim — no implicit conventions.  (b) The corner case
--   `w₁ = w₂` (flagged by the LN wording-check as subtlety
--   `w1_equals_w2_unspecified_trivial_path_walk` in
--   `leanification/working_subtlety_register.json`) is witnessed
--   *uniformly* across all three TFAE items by the length-0
--   trivial walk `Walk.nil w₁ hw₁`; that witness needs `hw₁` in
--   scope to construct, so the proof writer can dispose of
--   `w₁ = w₂` in one line by exhibiting `⟨Walk.nil w₁ hw₁, …⟩`
--   for each item (vacuously a path, vacuously C-σ-open, vacuously
--   with all colliders in `C`) without splitting on endpoint
--   equality.  Moving `hw₁ / hw₂` onto a subtype of `w₁ / w₂`
--   would still work but would obscure the LN-faithful read of
--   the signature.
--
-- *Upstream load-bearing tool for the proof: `claim_3_27`
--   (`Causality.CDMG.replaceWalk` at
--   `Section3_3/LabelRoman.lean:2112`, LN label `lem:replace_walk`,
--   proven 2026-06-20).*  The LN's `(2) ⟹ (1)` direction (walk →
--   path) literally invokes `Lemma replace_walk` to contract a
--   sibling-class (i.e.\ `Sc^G`) subwalk between two occurrences
--   of the same node into a directed path inside that SCC,
--   decreasing the multiplicity of repeated vertices by one each
--   pass; iterating until no node repeats produces the path.  This
--   row was reordered behind `claim_3_27` (manager tip above, and
--   `data.json` order) for exactly this dependency, so the proof
--   writer should plan to call `replaceWalk` as the workhorse in
--   that direction.  `(3) ⟹ (2)` and `(1) ⟹ (2)` are trivial
--   weakenings (drop the strengthening conjunct / drop the
--   `IsPath` conjunct); `(2) ⟹ (3)` is the
--   "pull each non-`C` collider out along its `Anc^G(C)` witness
--   path and back" construction and does not need `replaceWalk`.
--
-- *`set_option linter.unusedVariables false in` prefix.*  Matches
--   the chapter convention for theorems whose `hw₁ / hw₂` (and
--   `hC`) hypotheses are LN-faithful but body-inert at the
--   statement surface — the unused-binder warning is suppressed so
--   the signature reads literally as the LN states.
-- TeX proof: claim_3_23_proof_SigmaOpenPathsWalks.tex
--
-- ## Proof helpers — `sigma_open_paths_walks` proof support
--
-- The helpers below are *proof helpers* (no markers) supporting the
-- four-direction TFAE proof.  They are organised in order of use:
--
-- * `Walk.repeatCount` — the (IV) termination measure
--   `#vertices − #(distinct vertices)`.  Zero iff the walk is a path.
-- * `Walk.repeatCount_zero_iff_isPath` — equivalence with `IsPath`.
-- * `Walk.sigma_open_to_path` — (IV) direction's helper: turns a
--   σ-open walk into a σ-open path via strong induction on
--   `repeatCount`, invoking `replaceWalk` at the inductive step.
-- * `Walk.sigma_open_colliders_to_C` — (III) direction's helper: turns
--   a σ-open walk into a σ-open walk with every collider in `C`.

namespace Walk

variable {G : CDMG Node}

/-- The set of vertices on `π` that occur at more than one position.
This is the "repeated nodes" set from the LN's termination measure
`R(π) := #{w ∈ J ∪ V : w occurs at more than one position on π}`. -/
private def repeatedNodes {u v : Node} (π : Walk G u v) : Finset Node :=
  π.vertices.toFinset.filter (fun x => π.vertices.count x ≥ 2)

/-- The (IV) termination measure: number of distinct nodes that occur
more than once on `π`.  Zero iff `π.IsPath`. -/
private def repeatedCount {u v : Node} (π : Walk G u v) : ℕ :=
  (π.repeatedNodes).card

private lemma repeatedCount_zero_iff_isPath {u v : Node} (π : Walk G u v) :
    π.repeatedCount = 0 ↔ π.IsPath := by
  unfold repeatedCount repeatedNodes IsPath
  constructor
  · intro h_card
    -- card of filter = 0 → filter is empty → no x has count ≥ 2
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h_card
    -- h_card : ∀ x ∈ toFinset, ¬ count x ≥ 2
    -- Need: vertices.Nodup, i.e. ∀ a, count a vertices ≤ 1
    rw [List.nodup_iff_count_le_one]
    intro a
    by_cases ha : a ∈ π.vertices
    · have ha' : a ∈ π.vertices.toFinset := List.mem_toFinset.mpr ha
      have h_not_two := h_card ha'
      omega
    · rw [List.count_eq_zero.mpr ha]
      omega
  · intro h_nodup
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x hx_mem h_count_ge_two
    have h_le_one : π.vertices.count x ≤ 1 :=
      List.nodup_iff_count_le_one.mp h_nodup x
    omega

end Walk

end CDMG

end Causality

namespace Causality

namespace CDMG

variable {Node : Type*} [DecidableEq Node]

-- Helper: a list with a vertex appearing ≥ 2 times has two distinct
-- positions both containing that vertex.  Provides the i < j ≤ length
-- positions we need to feed into `replaceWalk`.
private lemma List.exists_distinct_positions_of_count_ge_two
    {α : Type*} [DecidableEq α] {l : List α} {a : α} (h : 2 ≤ l.count a) :
    ∃ i j : ℕ, i < j ∧ j < l.length ∧ l[i]? = some a ∧ l[j]? = some a := by
  induction l with
  | nil => simp at h
  | cons hd tl ih =>
    by_cases h_eq : hd = a
    · -- hd = a; so tl must contain a ≥ 1 time.
      have h_tl : 1 ≤ tl.count a := by
        rw [List.count_cons, if_pos (by simp [h_eq])] at h
        omega
      have h_mem_tl : a ∈ tl := List.count_pos_iff.mp h_tl
      rw [List.mem_iff_getElem] at h_mem_tl
      obtain ⟨k, hk_lt, hk_eq⟩ := h_mem_tl
      refine ⟨0, k + 1, by omega,
              by rw [List.length_cons]; omega, ?_, ?_⟩
      · -- (hd :: tl)[0]? = some a
        show (hd :: tl)[0]? = some a
        rw [List.getElem?_cons_zero, h_eq]
      · -- (hd :: tl)[k+1]? = some a
        show (hd :: tl)[k + 1]? = some a
        rw [List.getElem?_cons_succ]
        rw [List.getElem?_eq_some_iff]
        exact ⟨hk_lt, hk_eq⟩
    · -- hd ≠ a; recurse on tl.
      have h' : 2 ≤ tl.count a := by
        rw [List.count_cons,
            if_neg (by
              rw [beq_iff_eq]
              exact fun h_eq' => h_eq h_eq')] at h
        omega
      obtain ⟨i, j, hij, hjn, hi, hj⟩ := ih h'
      refine ⟨i + 1, j + 1, by omega,
              by rw [List.length_cons]; omega,
              ?_, ?_⟩
      · show (hd :: tl)[i + 1]? = some a
        rw [List.getElem?_cons_succ]; exact hi
      · show (hd :: tl)[j + 1]? = some a
        rw [List.getElem?_cons_succ]; exact hj

-- The (2) → (1) helper.  Given a σ-open walk, produce a σ-open path
-- with the same endpoints.  Strong induction on `π.length`; each
-- inductive step picks any repeated vertex `w` on `π`, takes its first
-- and last positions `i < j` (so `v_i = v_j = w` and `v_i ∈ Sc(v_j)`
-- via `self_mem_Sc`), applies `replaceWalk` (= `claim_3_27`).  Since
-- `v_i = v_j`, the replacement walk `σ_ij` is the trivial length-0
-- walk on `w`, and the splice strictly shortens `π`.
private lemma Walk.sigma_open_to_path
    {G : CDMG Node} {C : Set Node} {hC : C ⊆ ↑G.J ∪ ↑G.V}
    {u v : Node} (π : Walk G u v) (hπ : π.IsSigmaOpenGiven C hC) :
    ∃ π' : Walk G u v, π'.IsPath ∧ π'.IsSigmaOpenGiven C hC := by
  -- Strong induction on `π.length`.
  induction h_len : π.length using Nat.strong_induction_on
    generalizing u v π with
  | _ n ih =>
    by_cases h_path : π.IsPath
    · exact ⟨π, h_path, hπ⟩
    · -- π is not a path → its vertices list has a duplicate.
      have h_not_nodup : ¬ π.vertices.Nodup := h_path
      -- Find some w occurring ≥ 2 times on π.
      have h_dup : ∃ w ∈ π.vertices, 2 ≤ π.vertices.count w := by
        classical
        by_contra h_no_dup
        apply h_not_nodup
        rw [List.nodup_iff_count_le_one]
        intro w
        by_cases hw_mem : w ∈ π.vertices
        · -- If count ≥ 2 then ⟨w, hw_mem, _⟩ is a witness for h_no_dup.
          by_contra h_count
          have h_count' : 2 ≤ π.vertices.count w := Nat.lt_iff_add_one_le.mp
            (Nat.lt_of_not_le h_count)
          exact h_no_dup ⟨w, hw_mem, h_count'⟩
        · rw [List.count_eq_zero.mpr hw_mem]; omega
      obtain ⟨w, hw_mem, hw_count⟩ := h_dup
      -- Extract the first/last positions i < j of w on π.
      obtain ⟨i, j, hij, hj_lt_vlen, h_get_i, h_get_j⟩ :=
        List.exists_distinct_positions_of_count_ge_two hw_count
      -- π.vertices.length = π.length + 1, so j ≤ π.length.
      have hj_le : j ≤ π.length := by
        have h_vl : π.vertices.length = π.length + 1 := Walk.vertices_length π
        rw [h_vl] at hj_lt_vlen
        omega
      -- w is in G (every vertex on a walk lies in G).
      have hw_G : w ∈ G := Walk.mem_of_mem_vertices π hw_mem
      -- w ∈ Sc(w) via the length-0 trivial directed walk.
      have hw_sc_self : w ∈ G.Sc w := by
        refine ⟨⟨hw_G, Walk.nil w hw_G, trivial⟩,
                ⟨hw_G, Walk.nil w hw_G, trivial⟩⟩
      -- Apply replaceWalk with v_i = v_j = w.
      obtain ⟨σ_ij, π', _h_caseI_impl, _h_caseII_impl, _h_Sc_v, h_π'_vert, h_π'_open⟩ :=
        Causality.CDMG.replaceWalk G C hC π hπ hij hj_le h_get_i h_get_j hw_sc_self
      -- Show π'.length < π.length.  Since v_i = v_j = w, the
      -- shortest directed walk from w to w is `Walk.nil w hw_G` of
      -- length 0; replaceWalk's σ_ij is shortest in both case (i) and
      -- (via reverse) case (ii), so σ_ij.length = 0.  The splice then
      -- strictly shortens π by (j - i) (positive since i < j).
      have h_σ_zero : σ_ij.length = 0 := by
        by_cases h_caseI : π.replaceWalkCaseI j
        · -- Case (i): σ_ij.IsDirectedWalk, σ_ij.length ≤ any directed walk.
          obtain ⟨hσ_dir, hσ_min⟩ := _h_caseI_impl h_caseI
          have h_nil_dir : (Walk.nil w hw_G : Walk G w w).IsDirectedWalk :=
            trivial
          have h_le := hσ_min (Walk.nil w hw_G) h_nil_dir
          have h_nil_len : (Walk.nil w hw_G : Walk G w w).length = 0 := rfl
          omega
        · -- Case (ii): σ_ij.reverse.IsDirectedWalk, minimal.
          obtain ⟨hσ_rev_dir, hσ_rev_min⟩ := _h_caseII_impl h_caseI
          have h_nil_dir : (Walk.nil w hw_G : Walk G w w).IsDirectedWalk :=
            trivial
          have h_le := hσ_rev_min (Walk.nil w hw_G) h_nil_dir
          have h_nil_len : (Walk.nil w hw_G : Walk G w w).length = 0 := rfl
          rw [Walk.length_reverse] at h_le
          omega
      have h_π'_len : π'.length < π.length := by
        -- Compute π'.vertices.length from the factoring.
        have h_π'_vlen : π'.vertices.length = π.length + σ_ij.length + 1 + i - j := by
          rw [h_π'_vert]
          rw [List.length_append, List.length_append]
          rw [List.length_dropLast, List.length_take, List.length_drop,
              Walk.vertices_length π, Walk.vertices_length σ_ij]
          have h_take_min : min (i + 1) (π.length + 1) = i + 1 := by omega
          rw [h_take_min]
          omega
        have h_π'_len_eq : π'.length + 1 = π.length + σ_ij.length + 1 + i - j := by
          rw [← Walk.vertices_length π']
          exact h_π'_vlen
        -- π'.length = π.length + σ_ij.length + i - j; since σ_ij.length = 0 and i < j, < π.length.
        rw [h_σ_zero] at h_π'_len_eq
        omega
      -- Apply the inductive hypothesis to π'.
      exact ih π'.length (h_len ▸ h_π'_len) π' h_π'_open rfl

-- The (2) → (3) helper.  Given a σ-open walk π, produce a σ-open walk
-- π' with every collider position on π' having its vertex in C.
--
-- ## Proof outline (matches beat (III) of the TeX proof)
--
-- Strong induction on the termination measure
--   `M(π) := #{ k : k is a collider on π ∧ v_k ∉ C }`.
--
-- *Base case `M = 0`.*  Every collider position on π already has
-- `v_k ∈ C`; the witness for (3) is π itself with σ-open property `hπ`
-- and the trivial check `M = 0`.
--
-- *Inductive case `M ≥ 1`.*  Let `k` be the smallest collider position
-- with `v_k ∉ C`.  Since π is σ-open and `k` is a collider, `v_k ∈
-- G.AncSet C` (from `hπ.1`); combined with `v_k ∉ C`, there exists a
-- directed path `d : Walk G v_k c` with `c ∈ C`, of minimal length ≥ 1
-- (interior nodes `u_1, …, u_{m-1}` all outside C by minimality).
--
-- Splice `d` and its reverse `d.reverse` into π at position k via
-- `Walk.splitAt` + `Walk.comp`:
--   `π' := (π.splitAt k).prefix.comp (d.comp (d.reverse.comp (π.splitAt k).suffix))`
--
-- Then `π'` satisfies:
-- (a) `π'.IsSigmaOpenGiven C hC` — verified position-by-position:
--     - positions in `(π.splitAt k).prefix` and `(π.splitAt k).suffix`
--       preserve their collider/blockable status from π (collider-comp
--       shifting), σ-open preserved;
--     - the two copies of `v_k` at the splice boundaries are
--       non-colliders (one head + one tail) with `v_k ∉ C`, σ-open;
--     - interior `u_p` of forward `d`: directed-walk interior, hence
--       non-collider; `u_p ∉ C` by minimality, σ-open;
--     - the centre `c`: collider (head from both sides), `c ∈ C ⊆
--       G.AncSet C`, σ-open;
--     - interior `u_p` of `d.reverse`: backward-directed walk interior,
--       non-collider; `u_p ∉ C`, σ-open.
-- (b) `M(π') = M(π) - 1` — the collider at `v_k` is destroyed, the new
--     collider at `c` has `c ∈ C` (contributes 0 to `M`), all other
--     collider positions are unchanged.
--
-- Recurse via the inductive hypothesis on π'.

-- =================================================================
-- Section: helpers for `sigma_open_colliders_to_C`
-- =================================================================

/-- IsCollider on .nil reduces to False at every position. -/
private lemma Walk.isCollider_nil_false {G : CDMG Node}
    {v : Node} (hv : v ∈ G) (k : ℕ) :
    (Walk.nil v hv : Walk G v v).IsCollider k = False := by
  cases k <;> rfl

/-- IsCollider on .cons _ _ .nil reduces to False at every position
    (length-1 walks have no interior). -/
private lemma Walk.isCollider_cons_nil_false {G : CDMG Node}
    {u mid : Node} (s : WalkStep G u mid) (hv : mid ∈ G) (k : ℕ) :
    (Walk.cons mid s (Walk.nil mid hv) : Walk G u mid).IsCollider k = False := by
  cases k <;> rfl

/-- A collider position k must satisfy `1 ≤ k < p.length`.
    Both adjacent walk-steps must exist for the collider pattern. -/
private lemma Walk.isCollider_lt_length {G : CDMG Node} :
    ∀ {u v : Node} (p : Walk G u v) (k : ℕ),
      p.IsCollider k → k < p.length := by
  intros u v p k
  induction p generalizing k with
  | nil v hv =>
      intros h
      rw [Walk.isCollider_nil_false hv] at h
      exact h.elim
  | cons mid s p' ih =>
      intros h
      cases p' with
      | nil _ hv =>
          rw [Walk.isCollider_cons_nil_false s hv] at h
          exact h.elim
      | cons mid' s' p'' =>
          match k with
          | 0 => exact absurd h (Walk.refactor_IsCollider_zero_eq_False _)
          | 1 => simp [Walk.length]
          | k' + 2 =>
              have ih_res := ih (k' + 1) h
              simp [Walk.length] at ih_res ⊢
              omega

/-- A collider position k satisfies `1 ≤ k`. -/
private lemma Walk.isCollider_one_le {G : CDMG Node} :
    ∀ {u v : Node} (p : Walk G u v) (k : ℕ),
      p.IsCollider k → 1 ≤ k := by
  intros u v p k h
  by_contra h_zero
  push_neg at h_zero
  interval_cases k
  exact Walk.refactor_IsCollider_zero_eq_False p h

/-- A length-0 walk has source = target. -/
private lemma Walk.target_eq_source_of_length_zero {G : CDMG Node}
    {u v : Node} (p : Walk G u v) (h : p.length = 0) : u = v := by
  cases p with
  | nil _ _ => rfl
  | cons _ _ _ => simp [Walk.length] at h

/-- Membership in `AncSet C` unfolds to: there exists `c ∈ C` such that
    `v ∈ Anc c`. -/
private lemma mem_AncSet_iff {G : CDMG Node} {C : Set Node} {v : Node} :
    v ∈ G.AncSet C ↔ ∃ c ∈ C, v ∈ G.Anc c := by
  unfold CDMG.AncSet
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨c, hc, h⟩
    exact ⟨c, hc, h⟩
  · rintro ⟨c, hc, h⟩
    exact ⟨c, hc, h⟩

/-- Given a vertex `v ∈ G.AncSet C` with `v ∉ C`, there exists a directed
    walk `d : Walk G v c` of minimal positive length such that
    `c ∈ C` and no interior vertex (positions 1 ≤ p < d.length) lies
    in C.  Stated as an existential at `Prop` level (not a Σ'-bundle)
    so `Exists.choose` is available for downstream use. -/
private lemma Walk.exists_minimalDirectedToC {G : CDMG Node} {C : Set Node}
    {v : Node} (hv_anc : v ∈ G.AncSet C) (hv_nin : v ∉ C) :
    ∃ (c : Node) (d : Walk G v c),
      c ∈ C ∧ d.IsDirectedWalk ∧ 1 ≤ d.length ∧
      (∀ (p : ℕ) (vp : Node), d.vertices[p]? = some vp →
        1 ≤ p → p < d.length → vp ∉ C) := by
  classical
  -- Predicate P n: "there exists a directed walk from v to some c ∈ C of length n".
  let P : ℕ → Prop := fun n =>
    ∃ (c : Node) (d : Walk G v c), c ∈ C ∧ d.IsDirectedWalk ∧ d.length = n
  -- P is non-empty: by hv_anc + hv_nin, find some c ∈ C with directed walk
  -- v ⟶ c; length must be ≥ 1 (otherwise v = c ∈ C, contradiction).
  have hP_exists : ∃ n, P n := by
    rcases mem_AncSet_iff.mp hv_anc with ⟨c, hc_C, hvc⟩
    obtain ⟨_, d, hd_dir⟩ := hvc
    exact ⟨d.length, c, d, hc_C, hd_dir, rfl⟩
  -- Minimal length using Nat.find.
  let n_min : ℕ := Nat.find hP_exists
  have h_n_min : P n_min := Nat.find_spec hP_exists
  obtain ⟨c, d, hc_C, hd_dir, hd_len⟩ := h_n_min
  -- d.length = n_min ≥ 1: if d.length = 0, then v = c ∈ C, contradicting hv_nin.
  have hd_len_pos : 1 ≤ d.length := by
    by_contra h_zero
    have h_d_zero : d.length = 0 := by omega
    -- d : Walk G v c with length 0 ⇒ v = c.
    have hv_eq : v = c := Walk.target_eq_source_of_length_zero d h_d_zero
    rw [hv_eq] at hv_nin
    exact hv_nin hc_C
  -- Interior of d: no vertex in C.  If some interior vertex u_p ∈ C with
  -- 1 ≤ p < d.length, then truncating d to its prefix of length p gives
  -- a shorter directed walk to a vertex in C, contradicting minimality.
  have h_interior : ∀ (p : ℕ) (vp : Node), d.vertices[p]? = some vp →
      1 ≤ p → p < d.length → vp ∉ C := by
    intros p vp h_get hp_lo hp_hi h_vp_C
    -- Truncate d at position p via splitAt.
    have hp_le : p ≤ d.length := le_of_lt hp_hi
    have hmid_eq : (d.splitAt p hp_le).1 = vp := by
      have h := Walk.splitAt_mid_get d p hp_le
      rw [h_get] at h
      exact (Option.some.inj h).symm
    -- The prefix `d_pre : Walk G v vp` of length p, directed.
    let d_pre : Walk G v vp := hmid_eq ▸ (d.splitAt p hp_le).2.1
    have h_d_pre_len : d_pre.length = p := by
      show (hmid_eq ▸ (d.splitAt p hp_le).2.1).length = p
      rw [Walk.length_cast_target hmid_eq]
      exact Walk.splitAt_length_left d p hp_le
    have h_d_pre_dir : d_pre.IsDirectedWalk := by
      show (hmid_eq ▸ (d.splitAt p hp_le).2.1).IsDirectedWalk
      rw [Walk.IsDirectedWalk_cast_target hmid_eq]
      -- d_pre = (d.splitAt p hp_le).2.1, want IsDirectedWalk.
      have h_d_eq : d = (d.splitAt p hp_le).2.1.comp (d.splitAt p hp_le).2.2 :=
        (Walk.splitAt_comp d p hp_le).symm
      have : ((d.splitAt p hp_le).2.1.comp
              (d.splitAt p hp_le).2.2).IsDirectedWalk := h_d_eq ▸ hd_dir
      exact Walk.IsDirectedWalk_of_comp_left _ _ this
    -- Thus P p holds (vp ∈ C, d_pre directed, d_pre.length = p), so by
    -- minimality of n_min, p ≥ n_min = d.length, contradicting p < d.length.
    have h_P_p : P p := ⟨vp, d_pre, h_vp_C, h_d_pre_dir, h_d_pre_len⟩
    have h_min : Nat.find hP_exists ≤ p := Nat.find_min' hP_exists h_P_p
    have h_eq : d.length = Nat.find hP_exists := hd_len
    rw [← h_eq] at h_min
    omega
  exact ⟨c, d, hc_C, hd_dir, hd_len_pos, h_interior⟩

-- =================================================================
-- Section: badColliderSet, badColliderCount and characterizations
-- =================================================================

/-- The "bad collider" set for a walk `π` and conditioning set `C`:
    positions `k` such that `π` is a collider at `k` but the vertex
    at `k` is NOT in `C`.  The termination measure `M(π) := |this set|`
    drops by exactly one at every splice step. -/
private noncomputable def Walk.badColliderSet {G : CDMG Node}
    {u v : Node} (π : Walk G u v) (C : Set Node) : Finset ℕ := by
  classical
  exact (Finset.range (π.length + 1)).filter fun k =>
    π.IsCollider k ∧ ∀ vk, π.vertices[k]? = some vk → vk ∉ C

/-- The (III) termination measure: cardinality of the bad-collider set. -/
private noncomputable def Walk.badColliderCount {G : CDMG Node}
    {u v : Node} (π : Walk G u v) (C : Set Node) : ℕ :=
  (π.badColliderSet C).card

/-- `badColliderCount = 0` iff every collider position has its vertex in C. -/
private lemma Walk.badColliderCount_eq_zero_iff {G : CDMG Node}
    {u v : Node} (π : Walk G u v) (C : Set Node) :
    π.badColliderCount C = 0 ↔
      (∀ (k : ℕ) (vk : Node),
        π.vertices[k]? = some vk → π.IsCollider k → vk ∈ C) := by
  classical
  unfold Walk.badColliderCount Walk.badColliderSet
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h k vk h_get h_col
    by_contra h_vk_nin
    have hk_lt : k < π.length + 1 := by
      have h_len : k < π.length := Walk.isCollider_lt_length π k h_col
      omega
    have hk_range : k ∈ Finset.range (π.length + 1) :=
      Finset.mem_range.mpr hk_lt
    have h_specific : π.IsCollider k ∧ ∀ vk', π.vertices[k]? = some vk' → vk' ∉ C := by
      refine ⟨h_col, ?_⟩
      intros vk' h_get'
      rw [h_get] at h_get'
      have : vk' = vk := Option.some.inj h_get'.symm
      rw [this]
      exact h_vk_nin
    exact h hk_range h_specific
  · intros h k _ h_props
    by_contra h_false
    push_neg at h_false
    obtain ⟨h_col, h_all_nin⟩ := h_props
    -- Need to find vk such that vertices[k]? = some vk.  Since k < length+1,
    -- the lookup is some vk.
    have hk_lt : k < π.vertices.length := by
      rw [Walk.vertices_length]
      have h_len : k < π.length := Walk.isCollider_lt_length π k h_col
      omega
    have h_some : π.vertices[k]? = some (π.vertices[k]'hk_lt) :=
      List.getElem?_eq_getElem hk_lt
    exact h_all_nin _ h_some (h k _ h_some h_col)

/-- If `badColliderCount > 0`, there exists a smallest position k that
    is a bad collider — i.e. a position `k0 ≤ π.length` with
    `π.IsCollider k0` and `vk0 ∉ C` (where `vk0` is the vertex at k0),
    and additionally every collider position `k < k0` has its vertex in C. -/
private lemma Walk.exists_min_bad_collider {G : CDMG Node}
    {u v : Node} (π : Walk G u v) (C : Set Node)
    (h_pos : 0 < π.badColliderCount C) :
    ∃ k0 vk0, π.vertices[k0]? = some vk0 ∧ π.IsCollider k0 ∧ vk0 ∉ C := by
  classical
  unfold Walk.badColliderCount Walk.badColliderSet at h_pos
  rw [Finset.card_pos] at h_pos
  obtain ⟨k, hk⟩ := h_pos
  rw [Finset.mem_filter] at hk
  obtain ⟨hk_range, h_col, h_all_nin⟩ := hk
  rw [Finset.mem_range] at hk_range
  have hk_lt_v : k < π.vertices.length := by
    rw [Walk.vertices_length]
    have h_len : k < π.length := Walk.isCollider_lt_length π k h_col
    omega
  have h_some : π.vertices[k]? = some (π.vertices[k]'hk_lt_v) :=
    List.getElem?_eq_getElem hk_lt_v
  exact ⟨k, _, h_some, h_col, h_all_nin _ h_some⟩

-- ===========================================================
-- Section: the splice step
--
-- Given a σ-open walk π with a bad collider at position k₀
-- (`π.IsCollider k₀`, vertex vk₀ ∉ C), produce a new σ-open walk
-- π' with strictly fewer bad colliders.
--
-- Splice shape:
--   π'  :=  pre.comp ((d.comp d.reverse).comp suf)
-- where:
--   pre = (π.splitAt k₀).2.1 cast to Walk G u vk₀, length k₀
--   suf = (π.splitAt k₀).2.2 cast to Walk G vk₀ v, length π.length-k₀
--   d   = minimal directed walk from vk₀ to some c ∈ C, length ≥ 1
--
-- Position layout on π':
--   Region A   0  ≤ k < k₀             pre-interior, transports from π
--   Position k = k₀                     boundary 1 (v_k₀, non-collider)
--   Region B   k₀ < k < k₀+m            d-interior (non-collider)
--   Position k = k₀+m                   centre c (collider, c ∈ C)
--   Region C   k₀+m < k < k₀+2m         d.reverse-interior (non-collider)
--   Position k = k₀+2m                  boundary 2 (v_k₀, non-collider)
--   Region D   k₀+2m < k ≤ π.length+2m  suf-interior, transports from π
-- ===========================================================

-- Auxiliary: dropLast of `l.take (k+1)` is `l.take k` when k < l.length.
private lemma List.take_succ_dropLast_eq_take {α : Type*}
    (l : List α) (k : ℕ) (h : k < l.length) :
    (l.take (k + 1)).dropLast = l.take k := by
  rw [List.dropLast_eq_take, List.length_take]
  rw [show min (k + 1) l.length = k + 1 from by omega]
  rw [show k + 1 - 1 = k from rfl, List.take_take]
  rw [show min k (k + 1) = k from by omega]

/-- Helper that builds the splice walk and characterises its key vertex
    look-ups.  We expose this as a standalone helper because the splice
    construction is the largest piece of work in the proof and pulling
    its vertex-layout calculations out keeps the σ-openness verification
    readable. -/
private structure Walk.SpliceBundle
    {G : CDMG Node} {C : Set Node}
    {u v : Node} (π : Walk G u v) (k₀ : ℕ) (vk₀ : Node)
    (c : Node) (d : Walk G vk₀ c) where
  hk₀_le : k₀ ≤ π.length
  pre : Walk G u vk₀
  suf : Walk G vk₀ v
  d_rev : Walk G c vk₀
  loop : Walk G vk₀ vk₀
  π' : Walk G u v
  h_pre_len : pre.length = k₀
  h_suf_len : suf.length = π.length - k₀
  h_d_rev_eq : d_rev = d.reverse
  h_d_rev_back : d_rev.IsBackwardDirectedWalk
  h_loop_eq : loop = d.comp d_rev
  h_π'_eq : π' = pre.comp (loop.comp suf)
  h_pre_v : pre.vertices = π.vertices.take (k₀ + 1)
  h_suf_v : suf.vertices = π.vertices.drop k₀
  h_pre_suf : pre.comp suf = π

/-- Construct the splice bundle. -/
private noncomputable def Walk.mkSpliceBundle
    {G : CDMG Node} {C : Set Node}
    {u v : Node} (π : Walk G u v) (k₀ : ℕ) (vk₀ : Node)
    (h_get_k₀ : π.vertices[k₀]? = some vk₀)
    (hk₀_le : k₀ ≤ π.length)
    (c : Node) (d : Walk G vk₀ c) (hd_dir : d.IsDirectedWalk) :
    Walk.SpliceBundle (C := C) π k₀ vk₀ c d := by
  have hmid_eq : (π.splitAt k₀ hk₀_le).1 = vk₀ := by
    have h := Walk.splitAt_mid_get π k₀ hk₀_le
    rw [h_get_k₀] at h
    exact (Option.some.inj h).symm
  let pre : Walk G u vk₀ := hmid_eq ▸ (π.splitAt k₀ hk₀_le).2.1
  let suf : Walk G vk₀ v := hmid_eq ▸ (π.splitAt k₀ hk₀_le).2.2
  let d_rev : Walk G c vk₀ := d.reverse
  let loop : Walk G vk₀ vk₀ := d.comp d_rev
  let π' : Walk G u v := pre.comp (loop.comp suf)
  refine ⟨hk₀_le, pre, suf, d_rev, loop, π', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (hmid_eq ▸ (π.splitAt k₀ hk₀_le).2.1).length = k₀
    rw [Walk.length_cast_target hmid_eq]
    exact Walk.splitAt_length_left π k₀ hk₀_le
  · show (hmid_eq ▸ (π.splitAt k₀ hk₀_le).2.2).length = π.length - k₀
    rw [Walk.length_cast_source hmid_eq]
    exact Walk.splitAt_length_right π k₀ hk₀_le
  · rfl
  · show d.reverse.IsBackwardDirectedWalk
    exact Walk.reverse_isBackwardDirected_of_directed d hd_dir
  · rfl
  · rfl
  · show (hmid_eq ▸ (π.splitAt k₀ hk₀_le).2.1).vertices = π.vertices.take (k₀ + 1)
    rw [Walk.vertices_cast_target hmid_eq]
    exact Walk.splitAt_vertices_left π k₀ hk₀_le
  · show (hmid_eq ▸ (π.splitAt k₀ hk₀_le).2.2).vertices = π.vertices.drop k₀
    rw [Walk.vertices_cast_source hmid_eq]
    exact Walk.splitAt_vertices_right π k₀ hk₀_le
  · -- pre.comp suf = π
    subst hmid_eq
    exact Walk.splitAt_comp π k₀ hk₀_le

/-- The σ-open splice helper.  Given a σ-open walk `π` with a bad collider
    at position `k₀`, produce a new σ-open walk `π'` whose bad-collider
    count is strictly smaller. -/
private lemma Walk.spliceBadCollider
    {G : CDMG Node} {C : Set Node} {hC : C ⊆ ↑G.J ∪ ↑G.V}
    {u v : Node} (π : Walk G u v) (hπ : π.IsSigmaOpenGiven C hC)
    {k₀ : ℕ} {vk₀ : Node} (h_get_k₀ : π.vertices[k₀]? = some vk₀)
    (h_col_k₀ : π.IsCollider k₀) (h_vk₀_nin : vk₀ ∉ C) :
    ∃ π' : Walk G u v,
      π'.IsSigmaOpenGiven C hC ∧
      π'.badColliderCount C < π.badColliderCount C := by
  classical
  -- # Preliminaries.
  have hk₀_lt : k₀ < π.length := Walk.isCollider_lt_length π k₀ h_col_k₀
  have hk₀_le : k₀ ≤ π.length := le_of_lt hk₀_lt
  have h_vk₀_anc : vk₀ ∈ G.AncSet C := hπ.1 k₀ vk₀ h_get_k₀ h_col_k₀
  obtain ⟨c, d, hc_C, hd_dir, hd_pos, hd_int⟩ :=
    Walk.exists_minimalDirectedToC h_vk₀_anc h_vk₀_nin
  let B := Walk.mkSpliceBundle (C := C) π k₀ vk₀ h_get_k₀ hk₀_le c d hd_dir
  -- Unpack the bundle.
  obtain ⟨_, pre, suf, d_rev, loop, π',
    h_pre_len, h_suf_len, h_d_rev_eq, h_d_rev_back, h_loop_eq,
    h_π'_eq, h_pre_v, h_suf_v, h_pre_suf⟩ := B
  -- # Useful length facts.
  have h_d_rev_len : d_rev.length = d.length := by
    rw [h_d_rev_eq]; exact Walk.length_reverse d
  have h_d_rev_v : d_rev.vertices = d.vertices.reverse := by
    rw [h_d_rev_eq]; exact Walk.vertices_reverse d
  have h_loop_len : loop.length = 2 * d.length := by
    rw [h_loop_eq, Walk.length_comp, h_d_rev_len]; ring
  have h_π'_len : π'.length = π.length + 2 * d.length := by
    rw [h_π'_eq, Walk.length_comp, Walk.length_comp, h_pre_len, h_suf_len,
        h_loop_len]
    omega
  -- d.vertices ⊆ G.AncSet C (via Anc(c) and c ∈ C).
  have h_d_anc_C : ∀ x ∈ d.vertices, x ∈ G.AncSet C := by
    intros x hx
    have h_anc_c : x ∈ G.Anc c := Walk.directed_vertex_mem_Anc d hd_dir hx
    exact mem_AncSet_iff.mpr ⟨c, hc_C, h_anc_c⟩
  -- d_rev's interior matches d's interior (vertices outside C).
  have h_d_rev_int : ∀ (p : ℕ) (vp : Node), d_rev.vertices[p]? = some vp →
      1 ≤ p → p < d_rev.length → vp ∉ C := by
    intros p vp h_get hp_lo hp_hi h_vp_C
    rw [h_d_rev_v] at h_get
    rw [h_d_rev_len] at hp_hi
    have h_p_lt_dvl : p < d.vertices.length := by
      rw [Walk.vertices_length]; omega
    rw [List.getElem?_reverse h_p_lt_dvl] at h_get
    -- h_get : d.vertices[d.vertices.length - 1 - p]? = some vp
    have h_idx_lt : d.vertices.length - 1 - p < d.length := by
      rw [Walk.vertices_length]; omega
    have h_idx_ge : 1 ≤ d.vertices.length - 1 - p := by
      rw [Walk.vertices_length]; omega
    exact hd_int _ _ h_get h_idx_ge h_idx_lt (by exact h_vp_C)
  -- vk₀ vertex on d_rev at position d.length (last vertex).
  have h_d_rev_target_vk₀ :
      d_rev.vertices[d.length]? = some vk₀ := by
    rw [h_d_rev_v]
    have h_d_vlen : d.vertices.length = d.length + 1 := Walk.vertices_length d
    have h_lt : d.length < d.vertices.length := by rw [h_d_vlen]; omega
    rw [List.getElem?_reverse h_lt]
    have h_idx : d.vertices.length - 1 - d.length = 0 := by rw [h_d_vlen]; omega
    rw [h_idx]
    exact Walk.vertices_zero_eq_source d
  -- ============================================================
  -- # Loop is σ-open: every collider in loop has vertex in C (= AncSet C);
  --   every blockable non-collider has vertex ∉ C.
  -- We prove this for `loop = d.comp d_rev` standalone.
  --
  -- Positions on loop (length 2*d.length):
  --   0:        vk₀ (non-collider, ∉ C — vacuous)
  --   1..d-1:   interior of d, non-collider (directed walk), ∉ C
  --   d.length: c, COLLIDER (both halves head at c), c ∈ C ⊆ AncSet C
  --   d+1..2d-1: interior of d_rev, non-collider (backward-directed), ∉ C
  --   2*d.length: vk₀ (non-collider, ∉ C — vacuous)
  -- ============================================================
  -- First, loop's vertex layout:
  --   loop.vertices = d.vertices.dropLast ++ d_rev.vertices
  have h_loop_v : loop.vertices = d.vertices.dropLast ++ d_rev.vertices := by
    rw [h_loop_eq, Walk.vertices_comp]
  have h_d_drop_len : d.vertices.dropLast.length = d.length := by
    rw [List.length_dropLast, Walk.vertices_length d]; omega
  have h_d_rev_vlen : d_rev.vertices.length = d.length + 1 := by
    rw [Walk.vertices_length, h_d_rev_len]
  have h_d_rev_drop_len : d_rev.vertices.dropLast.length = d.length := by
    rw [List.length_dropLast, h_d_rev_vlen]; omega
  -- # Vertex lookups on loop.
  -- loop.vertices[p]? for p < d.length: = d.vertices[p]?
  -- loop.vertices[d.length + p]? for 0 ≤ p ≤ d.length: = d_rev.vertices[p]?
  have h_loop_v_left : ∀ (p : ℕ), p < d.length →
      loop.vertices[p]? = d.vertices[p]? := by
    intros p hp
    rw [h_loop_v]
    have h_lt : p < d.vertices.dropLast.length := by rw [h_d_drop_len]; exact hp
    rw [List.getElem?_append_left h_lt]
    rw [List.getElem?_dropLast]
    -- Goal: (if p < d.vertices.length - 1 then d.vertices[p]? else none) = d.vertices[p]?
    rw [if_pos (by rw [Walk.vertices_length]; omega)]
  have h_loop_v_right : ∀ (p : ℕ),
      loop.vertices[d.length + p]? = d_rev.vertices[p]? := by
    intros p
    -- loop = d.comp d_rev, vertices_comp_right_shift gives this directly.
    rw [h_loop_eq]
    exact Walk.vertices_comp_right_shift d d_rev p
  -- # Loop's σ-openness will be combined with pre/suf's σ-openness later.
  -- ============================================================
  -- # Now verify σ-openness of π'.
  -- We use the per-position approach with case analysis on the
  -- region.  The result has two clauses (COLLIDER, BLOCKABLE).
  -- ============================================================
  -- Helpful lemma: π'.vertices[k]? characterisation per region.
  -- For brevity, we'll work directly with comp_left/right/cast in each case.
  refine ⟨π', ?_, ?_⟩
  · -- # π'.IsSigmaOpenGiven C hC
    refine ⟨?_, ?_⟩
    · -- ## COLLIDER clause
      intros k vk h_get_π' h_col_π'
      -- Region analysis: where does k sit on π' = pre.comp (loop.comp suf)?
      by_cases hk_pre : k < pre.length
      · -- Region A: k < pre.length = k₀. Transport π'.IsCollider k → pre.IsCollider k.
        have h_col_pre : pre.IsCollider k := by
          have h_eq : (pre.comp (loop.comp suf)).IsCollider k = pre.IsCollider k :=
            Walk.refactor_IsCollider_comp_left pre (loop.comp suf) k hk_pre
          have : π'.IsCollider k = pre.IsCollider k := by rw [h_π'_eq]; exact h_eq
          rw [this] at h_col_π'
          exact h_col_π'
        -- Then pre.IsCollider k = π.IsCollider k (since pre.comp suf = π, and k < pre.length).
        have h_col_π : π.IsCollider k := by
          rw [← h_pre_suf]
          rw [Walk.refactor_IsCollider_comp_left pre suf k hk_pre]
          exact h_col_pre
        -- Vertex correspondence: π'.vertices[k]? = π.vertices[k]?
        have h_get_π : π.vertices[k]? = some vk := by
          have h_eq : π'.vertices[k]? = π.vertices[k]? := by
            -- π' = pre.comp (loop.comp suf), pre.comp suf = π.
            -- π'.vertices = (pre.comp suf).vertices = π.vertices for positions < pre.length.
            have h_eq1 : π'.vertices[k]? = pre.vertices[k]? := by
              rw [h_π'_eq, Walk.vertices_comp]
              have h_drop_lt : k < pre.vertices.dropLast.length := by
                rw [List.length_dropLast, Walk.vertices_length, h_pre_len]; omega
              rw [List.getElem?_append_left h_drop_lt]
              rw [List.getElem?_dropLast, if_pos (by
                rw [Walk.vertices_length, h_pre_len]; omega)]
            have h_eq2 : pre.vertices[k]? = π.vertices[k]? := by
              -- pre.comp suf = π, so π.vertices = pre.vertices.dropLast ++ suf.vertices.
              -- For k < pre.length, π.vertices[k]? = pre.vertices.dropLast[k]? = pre.vertices[k]?.
              rw [← h_pre_suf, Walk.vertices_comp]
              have h_drop_lt : k < pre.vertices.dropLast.length := by
                rw [List.length_dropLast, Walk.vertices_length, h_pre_len]; omega
              rw [List.getElem?_append_left h_drop_lt]
              rw [List.getElem?_dropLast, if_pos (by
                rw [Walk.vertices_length, h_pre_len]; omega)]
            rw [h_eq1, h_eq2]
          rw [← h_eq]; exact h_get_π'
        -- Apply σ-openness of π.
        exact hπ.1 k vk h_get_π h_col_π
      · push_neg at hk_pre
        by_cases hk_loop_end : k = pre.length
        · -- Boundary A': k = pre.length. Use the no-head-source helper.
          -- loop's first step is d's first step.
          -- We need: (loop.comp suf).firstStepHeadAtSource = False.
          -- loop = d.comp d_rev. Since d.length ≥ 1, d = .cons ... (something), with
          -- first step .forwardE (since d directed).
          -- So loop = .cons ... (d_rest.comp d_rev), and its first step is .forwardE.
          -- (loop.comp suf).firstStepHeadAtSource = loop's first step's HeadAtSource = False.
          exfalso
          -- Need to derive π'.IsCollider k = False at k = pre.length.
          have h_loop_comp_suf_no_head : ¬ (loop.comp suf).firstStepHeadAtSource := by
            rw [h_loop_eq]
            -- (d.comp d_rev).comp suf = d.comp (d_rev.comp suf) by associativity... but we don't need that.
            -- Actually (d.comp d_rev).comp suf, the first step is from d (since d.length ≥ 1).
            -- We need to see that.
            have h_d_nontrivial : d.length ≥ 1 := hd_pos
            -- d is non-nil so d = .cons _ s _ where s = .forwardE (by hd_dir).
            cases d with
            | nil _ _ => simp [Walk.length] at h_d_nontrivial
            | cons _ s d_rest =>
                -- ((cons _ s d_rest).comp d_rev).comp suf
                -- = (cons _ s (d_rest.comp d_rev)).comp suf
                -- = cons _ s ((d_rest.comp d_rev).comp suf)
                -- firstStepHeadAtSource = s.HeadAtSource
                -- s must be .forwardE by hd_dir
                cases s with
                | forwardE _ =>
                    intro h_head
                    -- h_head : firstStepHeadAtSource = ((forwardE _).HeadAtSource) = False
                    exact h_head
                | backwardE _ => exact hd_dir.elim
                | bidir _ => exact hd_dir.elim
          subst hk_loop_end
          have h_col_eq :
              π'.IsCollider pre.length =
                (pre.comp (loop.comp suf)).IsCollider pre.length := by rw [h_π'_eq]
          rw [h_col_eq] at h_col_π'
          exact Walk.refactor_IsCollider_comp_at_p_length_no_head_source
            pre (loop.comp suf) h_loop_comp_suf_no_head h_col_π'
        · push_neg at hk_loop_end
          have hk_pre_lt : pre.length < k := lt_of_le_of_ne hk_pre (Ne.symm hk_loop_end)
          -- Now k > pre.length. So (pre.comp X).IsCollider k = X.IsCollider (k - pre.length).
          have hk_post_pre : k - pre.length ≥ 1 := by omega
          set q := k - pre.length with hq_def
          have hk_eq : k = pre.length + q := by omega
          have h_col_X : (loop.comp suf).IsCollider q := by
            have h_eq : (pre.comp (loop.comp suf)).IsCollider k =
                (loop.comp suf).IsCollider (k - pre.length) :=
              Walk.refactor_IsCollider_comp_right pre (loop.comp suf) k hk_pre_lt
            have : π'.IsCollider k = (loop.comp suf).IsCollider (k - pre.length) := by
              rw [h_π'_eq]; exact h_eq
            rw [this] at h_col_π'
            exact h_col_π'
          have h_get_X : (loop.comp suf).vertices[q]? = some vk := by
            have h_eq : π'.vertices[pre.length + q]? =
                (loop.comp suf).vertices[q]? := by
              rw [h_π'_eq]
              exact Walk.vertices_comp_right_shift pre (loop.comp suf) q
            rw [← h_eq, ← hk_eq]
            exact h_get_π'
          -- Sub-region analysis on (loop.comp suf) at position q.
          by_cases hq_loop : q < loop.length
          · -- q is inside loop.
            -- (loop.comp suf).IsCollider q = loop.IsCollider q.
            have h_col_loop : loop.IsCollider q := by
              have h_eq : (loop.comp suf).IsCollider q = loop.IsCollider q :=
                Walk.refactor_IsCollider_comp_left loop suf q hq_loop
              rw [h_eq] at h_col_X
              exact h_col_X
            have h_get_loop : loop.vertices[q]? = some vk := by
              have h_eq : (loop.comp suf).vertices[0 + q]? = loop.vertices[q]? ∨ True := by
                -- Use that loop.comp suf, for q < loop.length, reads off loop.
                right; trivial
              -- Actually we need a different fact.
              -- For q < loop.length, (loop.comp suf).vertices[q]? = loop.vertices[q]?.
              -- Use loop.vertices.dropLast for first loop.length positions.
              -- (loop.comp suf).vertices = loop.vertices.dropLast ++ suf.vertices.
              rw [Walk.vertices_comp] at h_get_X
              have h_drop_len_loop : loop.vertices.dropLast.length = loop.length := by
                rw [List.length_dropLast, Walk.vertices_length]; omega
              have hq_lt_drop : q < loop.vertices.dropLast.length := by
                rw [h_drop_len_loop]; exact hq_loop
              rw [List.getElem?_append_left hq_lt_drop] at h_get_X
              rw [List.getElem?_dropLast] at h_get_X
              rw [if_pos (by rw [Walk.vertices_length]; omega)] at h_get_X
              exact h_get_X
            -- Now case split: q < d.length (Region B in d) vs q = d.length (centre c)
            -- vs q > d.length (Region C in d_rev).
            by_cases hq_d_left : q < d.length
            · -- Region B: interior of d.
              -- loop.IsCollider q = d.IsCollider q.
              have h_col_d : d.IsCollider q := by
                have h_eq : loop.IsCollider q = d.IsCollider q := by
                  rw [h_loop_eq]
                  exact Walk.refactor_IsCollider_comp_left d d_rev q hq_d_left
                rw [h_eq] at h_col_loop
                exact h_col_loop
              -- But d is directed and q ∈ [1, d.length), so d.IsCollider q = False.
              exfalso
              have hq_ge_1 : 1 ≤ q := hk_post_pre
              exact Walk.IsDirectedWalk.interior_not_collider d hd_dir q hq_ge_1
                hq_d_left h_col_d
            · push_neg at hq_d_left
              by_cases hq_d_eq : q = d.length
              · -- Boundary: q = d.length, centre c.
                rw [hq_d_eq] at h_get_loop h_col_loop
                -- Vertex at this position is c.
                have h_get_c : loop.vertices[d.length]? = some c := by
                  rw [h_loop_eq]
                  rw [Walk.vertices_comp_at_left_length d d_rev]
                -- So vk = c.
                have h_vk_c : vk = c := by
                  rw [h_get_c] at h_get_loop
                  exact (Option.some.inj h_get_loop).symm
                rw [h_vk_c]
                -- c ∈ C ⊆ G.AncSet C.
                exact mem_AncSet_iff.mpr ⟨c, hc_C, mem_Anc_refl
                  (Walk.target_mem d)⟩
              · push_neg at hq_d_eq
                have hq_d_gt : d.length < q := lt_of_le_of_ne hq_d_left (Ne.symm hq_d_eq)
                -- Region C: interior of d_rev.
                -- loop.IsCollider q = d_rev.IsCollider (q - d.length).
                set q' := q - d.length with hq'_def
                have hq_eq : q = d.length + q' := by omega
                have h_col_d_rev : d_rev.IsCollider q' := by
                  have h_eq : loop.IsCollider q = d_rev.IsCollider (q - d.length) := by
                    rw [h_loop_eq]
                    exact Walk.refactor_IsCollider_comp_right d d_rev q hq_d_gt
                  rw [h_eq] at h_col_loop
                  exact h_col_loop
                -- q' ≥ 1, q' < d_rev.length = d.length.
                have hq'_lo : 1 ≤ q' := by omega
                have hq'_hi : q' < d_rev.length := by rw [h_d_rev_len]; omega
                -- d_rev is backward-directed, so interior is not a collider.
                exfalso
                exact Walk.IsBackwardDirectedWalk.interior_not_collider d_rev
                  h_d_rev_back q' hq'_lo hq'_hi h_col_d_rev
          · -- q ≥ loop.length: position is at or past loop's end.
            push_neg at hq_loop
            by_cases hq_loop_eq : q = loop.length
            · -- Boundary C': q = loop.length. (loop.comp suf).IsCollider loop.length.
              -- loop.lastStepHeadAtTarget: d_rev's last step is .backwardE, so HeadAtTarget = False.
              -- Then the boundary helper gives False.
              exfalso
              rw [hq_loop_eq] at h_col_X
              -- Need: loop.lastStepHeadAtTarget = False.
              -- loop = d.comp d_rev. The last step of loop is the last step of d_rev
              -- (since d_rev is non-trivial: d_rev.length = d.length ≥ 1).
              -- d_rev is backward-directed and length ≥ 1, so its last step is .backwardE,
              -- so lastStepHeadAtTarget = False.
              have h_d_rev_pos : 0 < d_rev.length := by rw [h_d_rev_len]; omega
              have h_d_rev_no_head : ¬ d_rev.lastStepHeadAtTarget :=
                Walk.IsBackwardDirectedWalk.no_lastStepHeadAtTarget d_rev h_d_rev_back
                  h_d_rev_pos
              -- Need loop.lastStepHeadAtTarget = d_rev.lastStepHeadAtTarget.
              -- That requires a lemma: `(p.comp q).lastStepHeadAtTarget = q.lastStepHeadAtTarget`
              -- when q is non-trivial.  Let me derive it inline.
              have h_loop_no_head : ¬ loop.lastStepHeadAtTarget := by
                rw [h_loop_eq]
                -- d.comp d_rev's last step is d_rev's last step.
                -- Show by induction on d.
                clear h_loop_eq h_loop_len h_loop_v h_loop_v_left h_loop_v_right
                  h_col_X h_get_X
                -- Just need to show: (d.comp d_rev).lastStepHeadAtTarget = d_rev.lastStepHeadAtTarget.
                -- We'll prove a small inline helper.
                suffices h : ∀ {a b e : Node} (p1 : Walk G a b) (p2 : Walk G b e),
                    0 < p2.length →
                    ((p1.comp p2).lastStepHeadAtTarget ↔ p2.lastStepHeadAtTarget) by
                  rw [h d d_rev h_d_rev_pos]; exact h_d_rev_no_head
                intros a b e p1 p2 hp2_pos
                induction p1 with
                | nil _ _ => rfl
                | cons _ _ p1' ih =>
                    -- (cons _ s p1').comp p2 = cons _ s (p1'.comp p2)
                    cases p1' with
                    | nil _ _ =>
                        -- length-1 p1.  (cons _ s nil).comp p2 = cons _ s p2.
                        -- lastStepHeadAtTarget on cons _ s p2: depends on p2.
                        cases p2 with
                        | nil _ _ => simp [Walk.length] at hp2_pos
                        | cons _ _ p2' =>
                            simp only [Walk.comp, Walk.lastStepHeadAtTarget]
                    | cons _ _ _ =>
                        -- p1 = cons _ s (cons _ _ _). Recurse.
                        simp only [Walk.comp, Walk.lastStepHeadAtTarget]
                        exact ih p2 hp2_pos
              have h_col_eq :
                  (loop.comp suf).IsCollider loop.length = False := by
                apply eq_false
                exact Walk.refactor_IsCollider_comp_at_p_length_no_head_target
                  loop suf h_loop_no_head
              rw [h_col_eq] at h_col_X
              exact h_col_X
            · -- q > loop.length. Region D: in suf.
              push_neg at hq_loop_eq
              have hq_loop_gt : loop.length < q := lt_of_le_of_ne hq_loop (Ne.symm hq_loop_eq)
              set r := q - loop.length with hr_def
              have hq_eq : q = loop.length + r := by omega
              have h_col_suf : suf.IsCollider r := by
                have h_eq : (loop.comp suf).IsCollider q = suf.IsCollider (q - loop.length) :=
                  Walk.refactor_IsCollider_comp_right loop suf q hq_loop_gt
                rw [h_eq] at h_col_X
                exact h_col_X
              -- We need π.IsCollider (k₀ + r) and π.vertices[k₀ + r]? = some vk.
              -- Use π = pre.comp suf, position k₀ + r on π = position r on suf
              -- when r > 0 (i.e., k₀ + r > pre.length).
              -- Specifically: π.IsCollider (k₀ + r) = (pre.comp suf).IsCollider (k₀ + r)
              --   = suf.IsCollider r (by comp_right, since k₀ + r > k₀ = pre.length).
              -- We need r > 0. Yes, since r = q - loop.length and q > loop.length.
              have hr_pos : 0 < r := by omega
              have hk_π_def : k₀ + r = q - 2 * d.length + k₀ := by
                rw [hr_def, h_loop_len]; omega
              have h_col_π : π.IsCollider (k₀ + r) := by
                rw [← h_pre_suf]
                have h_eq : (pre.comp suf).IsCollider (k₀ + r) =
                    suf.IsCollider (k₀ + r - pre.length) := by
                  apply Walk.refactor_IsCollider_comp_right
                  rw [h_pre_len]; omega
                rw [h_eq]
                have h_arith : k₀ + r - pre.length = r := by rw [h_pre_len]; omega
                rw [h_arith]
                exact h_col_suf
              -- Vertex lookup:
              have h_get_π : π.vertices[k₀ + r]? = some vk := by
                rw [← h_pre_suf, Walk.vertices_comp]
                have h_drop_len_pre : pre.vertices.dropLast.length = k₀ := by
                  rw [List.length_dropLast, Walk.vertices_length, h_pre_len]; omega
                have h_ge : pre.vertices.dropLast.length ≤ k₀ + r := by
                  rw [h_drop_len_pre]; omega
                rw [List.getElem?_append_right h_ge, h_drop_len_pre]
                have h_arith : k₀ + r - k₀ = r := by omega
                rw [h_arith]
                -- suf.vertices[r]? = ?
                -- We have h_get_X : (loop.comp suf).vertices[q]? = some vk
                -- and q = loop.length + r.
                -- (loop.comp suf).vertices[loop.length + r]? = suf.vertices[r]?
                -- by vertices_comp_right_shift.
                have h_eq : (loop.comp suf).vertices[loop.length + r]? = suf.vertices[r]? :=
                  Walk.vertices_comp_right_shift loop suf r
                rw [hq_eq] at h_get_X
                rw [h_eq] at h_get_X
                exact h_get_X
              exact hπ.1 (k₀ + r) vk h_get_π h_col_π
    · -- ## BLOCKABLE clause
      intros k vk h_get_π' h_blk
      -- Same region analysis as the COLLIDER clause.
      by_cases hk_pre : k < pre.length
      · -- Region A. Transport blockable status to π.
        obtain ⟨h_nc, h_disj⟩ := h_blk
        -- π'.IsNonCollider k ↔ k ≤ π'.length ∧ ¬ π'.IsCollider k.
        -- We have h_nc.1 : k ≤ π'.length and h_nc.2 : ¬ π'.IsCollider k.
        have h_pi_le : k ≤ π.length := by
          -- k < pre.length = k₀ ≤ π.length.
          rw [h_pre_len] at hk_pre; omega
        have h_pi_get : π.vertices[k]? = some vk := by
          -- Same as in collider clause Region A.
          have h_eq1 : π'.vertices[k]? = pre.vertices[k]? := by
            rw [h_π'_eq, Walk.vertices_comp]
            have h_drop_lt : k < pre.vertices.dropLast.length := by
              rw [List.length_dropLast, Walk.vertices_length, h_pre_len]; omega
            rw [List.getElem?_append_left h_drop_lt]
            rw [List.getElem?_dropLast, if_pos (by
              rw [Walk.vertices_length, h_pre_len]; omega)]
          have h_eq2 : pre.vertices[k]? = π.vertices[k]? := by
            rw [← h_pre_suf, Walk.vertices_comp]
            have h_drop_lt : k < pre.vertices.dropLast.length := by
              rw [List.length_dropLast, Walk.vertices_length, h_pre_len]; omega
            rw [List.getElem?_append_left h_drop_lt]
            rw [List.getElem?_dropLast, if_pos (by
              rw [Walk.vertices_length, h_pre_len]; omega)]
          rw [← h_eq2, ← h_eq1]; exact h_get_π'
        -- Build π.IsBlockableNonCollider k.
        have h_blk_π : π.IsBlockableNonCollider k := by
          refine ⟨⟨h_pi_le, ?_⟩, ?_⟩
          · intro h_col_π
            apply h_nc.2
            rw [← h_pre_suf] at h_col_π
            rw [Walk.refactor_IsCollider_comp_left pre suf k hk_pre] at h_col_π
            rw [h_π'_eq]
            rw [Walk.refactor_IsCollider_comp_left pre (loop.comp suf) k hk_pre]
            exact h_col_π
          · -- Transport the disjunction.
            rcases h_disj with h_zero | h_eq_len | h_blk_left | h_blk_right
            · exact Or.inl h_zero
            · -- k = π'.length. But k < pre.length ≤ π.length ≤ π'.length, so k ≠ π'.length unless...
              -- Actually k < pre.length = k₀, and π'.length = π.length + 2*d.length.
              -- For h_eq_len to hold with k < k₀, π'.length < k₀ which is false.
              exfalso
              rw [h_π'_len] at h_eq_len
              omega
            · -- HasBlockingLeftSlot k on π'.
              right; right; left
              -- π'.HasBlockingLeftSlot k = pre.HasBlockingLeftSlot k (for k ≤ pre.length).
              -- We need k ≤ pre.length: k < pre.length so OK.
              rw [h_π'_eq] at h_blk_left
              rw [Walk.HasBlockingLeftSlot_comp_left pre (loop.comp suf) k
                (le_of_lt hk_pre)] at h_blk_left
              rw [← h_pre_suf]
              rw [Walk.HasBlockingLeftSlot_comp_left pre suf k (le_of_lt hk_pre)]
              exact h_blk_left
            · -- HasBlockingRightSlot k on π'.
              right; right; right
              rw [h_π'_eq] at h_blk_right
              rw [Walk.HasBlockingRightSlot_comp_left pre (loop.comp suf) k hk_pre]
                at h_blk_right
              rw [← h_pre_suf]
              rw [Walk.HasBlockingRightSlot_comp_left pre suf k hk_pre]
              exact h_blk_right
        exact hπ.2 k vk h_pi_get h_blk_π
      · push_neg at hk_pre
        by_cases hk_pre_eq : k = pre.length
        · -- Boundary A': k = pre.length, vk = vk₀ ∉ C.
          subst hk_pre_eq
          intro h_vk_C
          -- π'.vertices[pre.length]? = (pre.comp (loop.comp suf)).vertices[pre.length]?
          --   = (loop.comp suf).vertices[0]? = vk₀.
          have h_vert :
              π'.vertices[pre.length]? = some vk₀ := by
            rw [h_π'_eq]
            have h_eq : (pre.comp (loop.comp suf)).vertices[pre.length + 0]? =
                (loop.comp suf).vertices[0]? :=
              Walk.vertices_comp_right_shift pre (loop.comp suf) 0
            simp only [Nat.add_zero] at h_eq
            rw [h_eq]
            exact Walk.vertices_zero_eq_source _
          rw [h_vert] at h_get_π'
          have h_vk_eq : vk = vk₀ := (Option.some.inj h_get_π').symm
          subst h_vk_eq
          exact h_vk₀_nin h_vk_C
        · push_neg at hk_pre_eq
          have hk_pre_lt : pre.length < k := lt_of_le_of_ne hk_pre (Ne.symm hk_pre_eq)
          set q := k - pre.length with hq_def
          have hk_eq : k = pre.length + q := by omega
          have hq_pos : 0 < q := by omega
          -- Vertex on (loop.comp suf) at position q.
          have h_get_X : (loop.comp suf).vertices[q]? = some vk := by
            have h_eq : π'.vertices[pre.length + q]? =
                (loop.comp suf).vertices[q]? := by
              rw [h_π'_eq]
              exact Walk.vertices_comp_right_shift pre (loop.comp suf) q
            rw [← h_eq, ← hk_eq]
            exact h_get_π'
          by_cases hq_loop : q < loop.length
          · -- Inside loop.  Need to verify: if blockable, then vk ∉ C.
            -- Use the fact that all interior of loop have vertices ∉ C
            -- (interior of d / d_rev / vk₀ at boundaries / c at centre).
            -- For the blockable clause, the only loop vertex potentially IN C is c (at q = d.length).
            -- But c is a COLLIDER position (head from both sides), not a non-collider.
            -- So vk ∈ C only at c, which isn't a non-collider position.
            -- For other positions on loop: vk ∉ C.
            -- Implementation: extract vk's value, case on q < d.length, q = d.length, q > d.length.
            intro h_vk_C
            -- Get loop.vertices[q]? = some vk
            have h_get_loop : loop.vertices[q]? = some vk := by
              rw [Walk.vertices_comp] at h_get_X
              have h_drop_len_loop : loop.vertices.dropLast.length = loop.length := by
                rw [List.length_dropLast, Walk.vertices_length]; omega
              have hq_lt_drop : q < loop.vertices.dropLast.length := by
                rw [h_drop_len_loop]; exact hq_loop
              rw [List.getElem?_append_left hq_lt_drop] at h_get_X
              rw [List.getElem?_dropLast,
                  if_pos (by rw [Walk.vertices_length]; omega)] at h_get_X
              exact h_get_X
            by_cases hq_lt_d : q < d.length
            · -- Region B: interior of d.
              -- loop.vertices[q]? = d.vertices[q]? (h_loop_v_left).
              have h_get_d : d.vertices[q]? = some vk := by
                rw [← h_loop_v_left q hq_lt_d]; exact h_get_loop
              -- d.vertices[q]? = some vk with 1 ≤ q < d.length → vk ∉ C by hd_int.
              exact hd_int q vk h_get_d hq_pos hq_lt_d h_vk_C
            · push_neg at hq_lt_d
              by_cases hq_d_eq : q = d.length
              · -- Centre c. vk = c ∈ C. But c is a collider not a non-collider.
                exfalso
                -- The position q = d.length is a collider on loop, hence on (loop.comp suf),
                -- hence on π'. But h_blk says it's a non-collider, contradiction.
                obtain ⟨h_nc, _⟩ := h_blk
                apply h_nc.2
                -- Need: π'.IsCollider k. We have k = pre.length + d.length.
                rw [hk_eq, h_π'_eq, hq_d_eq]
                -- (pre.comp (loop.comp suf)).IsCollider (pre.length + d.length)
                -- = (loop.comp suf).IsCollider d.length (by comp_right)
                -- = loop.IsCollider d.length (by comp_left, since d.length < loop.length)
                -- = True (centre c).
                have hd_lt_loop : d.length < loop.length := by rw [h_loop_len]; omega
                have h_eq1 :
                    (pre.comp (loop.comp suf)).IsCollider (pre.length + d.length) =
                    (loop.comp suf).IsCollider d.length := by
                  have : pre.length < pre.length + d.length := by omega
                  rw [Walk.refactor_IsCollider_comp_right pre (loop.comp suf)
                    _ this]
                  congr 1; omega
                have h_eq2 :
                    (loop.comp suf).IsCollider d.length =
                    loop.IsCollider d.length :=
                  Walk.refactor_IsCollider_comp_left loop suf d.length hd_lt_loop
                rw [h_eq1, h_eq2]
                -- loop = d.comp d_rev. d.length is a collider since d.lastStepHeadAtTarget = True
                -- (last step is .forwardE, since d is directed and length ≥ 1)
                -- and d_rev.firstStepHeadAtSource = True (first step is .backwardE since d_rev
                -- is backward-directed and length ≥ 1).
                rw [h_loop_eq]
                apply Walk.refactor_IsCollider_comp_at_p_length_of_heads d d_rev
                · -- d.lastStepHeadAtTarget: d is directed and length ≥ 1, last step is .forwardE
                  -- → HeadAtTarget = True. Need a positive lemma.
                  -- Let me derive it inline.
                  clear h_get_loop h_get_X h_get_π'
                  -- Inline proof: d is directed (every step .forwardE), so its last step
                  -- (which exists since length ≥ 1) has HeadAtTarget = True.
                  -- We need d.lastStepHeadAtTarget = True.
                  have : ∀ {a b : Node} (p : Walk G a b), p.IsDirectedWalk →
                      0 < p.length → p.lastStepHeadAtTarget := by
                    intros a b p hp_dir hp_pos
                    induction p with
                    | nil _ _ => simp [Walk.length] at hp_pos
                    | cons _ s p' ih =>
                        cases s with
                        | forwardE _ =>
                            have hp' : p'.IsDirectedWalk := hp_dir
                            cases p' with
                            | nil _ _ =>
                                -- (cons _ (.forwardE _) nil).lastStepHeadAtTarget
                                -- definitionally unfolds via the second pattern of
                                -- lastStepHeadAtTarget: `cons _ s (nil _ _) ↦ s.HeadAtTarget`.
                                -- For .forwardE, HeadAtTarget = True.
                                simp only [Walk.lastStepHeadAtTarget,
                                  WalkStep.HeadAtTarget]
                            | cons mid' s' p'' =>
                                -- (cons _ s (cons mid' s' p'')).lastStepHeadAtTarget
                                -- reduces to (cons mid' s' p'').lastStepHeadAtTarget via clause 3.
                                simp only [Walk.lastStepHeadAtTarget]
                                exact ih hp' (by simp [Walk.length])
                        | backwardE _ => exact hp_dir.elim
                        | bidir _ => exact hp_dir.elim
                  exact this d hd_dir hd_pos
                · -- d_rev.firstStepHeadAtSource = True.
                  -- d_rev is backward-directed length ≥ 1, first step is .backwardE, HeadAtSource = True.
                  have : ∀ {a b : Node} (p : Walk G a b), p.IsBackwardDirectedWalk →
                      0 < p.length → p.firstStepHeadAtSource := by
                    intros a b p hp_back hp_pos
                    cases p with
                    | nil _ _ => simp [Walk.length] at hp_pos
                    | cons _ s _ =>
                        cases s with
                        | forwardE _ => exact hp_back.elim
                        | backwardE _ => trivial
                        | bidir _ => exact hp_back.elim
                  have h_d_rev_pos : 0 < d_rev.length := by rw [h_d_rev_len]; omega
                  exact this d_rev h_d_rev_back h_d_rev_pos
              · push_neg at hq_d_eq
                have hq_d_gt : d.length < q := lt_of_le_of_ne hq_lt_d (Ne.symm hq_d_eq)
                -- Region C: interior of d_rev.
                -- loop.vertices[q]? = d_rev.vertices[q - d.length]? (h_loop_v_right).
                set q' := q - d.length with hq'_def
                have hq_eq : q = d.length + q' := by omega
                have h_get_d_rev : d_rev.vertices[q']? = some vk := by
                  rw [← h_loop_v_right q']
                  rw [show d.length + q' = q from by omega]
                  exact h_get_loop
                have hq'_pos : 1 ≤ q' := by omega
                have hq'_lt : q' < d_rev.length := by
                  rw [h_d_rev_len]; omega
                exact h_d_rev_int q' vk h_get_d_rev hq'_pos hq'_lt h_vk_C
          · push_neg at hq_loop
            by_cases hq_loop_eq : q = loop.length
            · -- Boundary C'': k = pre.length + loop.length. Vertex is vk₀ ∉ C.
              intro h_vk_C
              rw [hq_loop_eq] at h_get_X
              -- vk = vk₀.
              have h_vert : (loop.comp suf).vertices[loop.length]? = some vk₀ := by
                -- (loop.comp suf).vertices[loop.length + 0]? = suf.vertices[0]? = vk₀.
                have h_eq : (loop.comp suf).vertices[loop.length + 0]? =
                    suf.vertices[0]? :=
                  Walk.vertices_comp_right_shift loop suf 0
                simp only [Nat.add_zero] at h_eq
                rw [h_eq]
                exact Walk.vertices_zero_eq_source suf
              rw [h_vert] at h_get_X
              have h_vk_eq : vk = vk₀ := (Option.some.inj h_get_X).symm
              rw [h_vk_eq] at h_vk_C
              exact h_vk₀_nin h_vk_C
            · -- Region D: in suf.
              push_neg at hq_loop_eq
              have hq_loop_gt : loop.length < q := lt_of_le_of_ne hq_loop (Ne.symm hq_loop_eq)
              set r := q - loop.length with hr_def
              have hq_eq : q = loop.length + r := by omega
              have hr_pos : 0 < r := by omega
              -- Transport to π. Position k₀ + r on π.
              obtain ⟨h_nc, h_disj⟩ := h_blk
              have h_pi_le_kr : k₀ + r ≤ π.length := by
                have h_k_le : k ≤ π'.length := h_nc.1
                rw [h_π'_len, hk_eq, hq_eq, h_loop_len] at h_k_le
                rw [← h_pre_len]; omega
              have h_get_π_kr : π.vertices[k₀ + r]? = some vk := by
                rw [← h_pre_suf, Walk.vertices_comp]
                have h_drop_len_pre : pre.vertices.dropLast.length = k₀ := by
                  rw [List.length_dropLast, Walk.vertices_length, h_pre_len]; omega
                have h_ge : pre.vertices.dropLast.length ≤ k₀ + r := by
                  rw [h_drop_len_pre]; omega
                rw [List.getElem?_append_right h_ge, h_drop_len_pre]
                have h_arith : k₀ + r - k₀ = r := by omega
                rw [h_arith]
                -- (loop.comp suf).vertices[loop.length + r]? = suf.vertices[r]?
                have h_eq : (loop.comp suf).vertices[loop.length + r]? =
                    suf.vertices[r]? :=
                  Walk.vertices_comp_right_shift loop suf r
                rw [hq_eq] at h_get_X
                rw [h_eq] at h_get_X
                exact h_get_X
              -- Build π.IsBlockableNonCollider (k₀ + r) and apply hπ.2.
              have h_blk_π : π.IsBlockableNonCollider (k₀ + r) := by
                refine ⟨⟨h_pi_le_kr, ?_⟩, ?_⟩
                · intro h_col_π
                  apply h_nc.2
                  rw [← h_pre_suf] at h_col_π
                  have h_pre_lt : pre.length < k₀ + r := by rw [h_pre_len]; omega
                  rw [Walk.refactor_IsCollider_comp_right pre suf _ h_pre_lt] at h_col_π
                  rw [show k₀ + r - pre.length = r from by rw [h_pre_len]; omega]
                    at h_col_π
                  rw [hk_eq, hq_eq, h_π'_eq]
                  have h_pre_lt' : pre.length < pre.length + (loop.length + r) := by omega
                  rw [Walk.refactor_IsCollider_comp_right pre (loop.comp suf) _ h_pre_lt']
                  rw [show pre.length + (loop.length + r) - pre.length = loop.length + r
                       from by omega]
                  have h_loop_lt : loop.length < loop.length + r := by omega
                  rw [Walk.refactor_IsCollider_comp_right loop suf _ h_loop_lt]
                  rw [show loop.length + r - loop.length = r from by omega]
                  exact h_col_π
                · -- Disjunction transport.
                  rcases h_disj with h_zero | h_eq_len | h_blk_left | h_blk_right
                  · -- k = 0, but k > pre.length ≥ 1, contradiction unless k₀ = 0.
                    -- Actually k = pre.length + q with q ≥ 1 (hq_pos), so k ≥ 1.
                    omega
                  · -- k = π'.length → k₀ + r = π.length.
                    right; left
                    rw [hk_eq, hq_eq, h_π'_len, h_loop_len] at h_eq_len
                    rw [← h_pre_len]; omega
                  · -- HasBlockingLeftSlot k on π'.
                    right; right; left
                    rw [hk_eq, hq_eq, h_π'_eq] at h_blk_left
                    have h_pre_lt' : pre.length < pre.length + (loop.length + r) := by omega
                    rw [Walk.HasBlockingLeftSlot_comp_right pre (loop.comp suf) _ h_pre_lt']
                      at h_blk_left
                    rw [show pre.length + (loop.length + r) - pre.length = loop.length + r
                         from by omega] at h_blk_left
                    have h_loop_lt : loop.length < loop.length + r := by omega
                    rw [Walk.HasBlockingLeftSlot_comp_right loop suf _ h_loop_lt] at h_blk_left
                    rw [show loop.length + r - loop.length = r from by omega]
                      at h_blk_left
                    rw [← h_pre_suf]
                    have h_pre_lt'' : pre.length < k₀ + r := by rw [h_pre_len]; omega
                    rw [Walk.HasBlockingLeftSlot_comp_right pre suf _ h_pre_lt'']
                    rw [show k₀ + r - pre.length = r from by rw [h_pre_len]; omega]
                    exact h_blk_left
                  · right; right; right
                    rw [hk_eq, hq_eq, h_π'_eq] at h_blk_right
                    have h_pre_le' : pre.length ≤ pre.length + (loop.length + r) := by omega
                    rw [Walk.HasBlockingRightSlot_comp_right pre (loop.comp suf) _ h_pre_le']
                      at h_blk_right
                    rw [show pre.length + (loop.length + r) - pre.length = loop.length + r
                         from by omega] at h_blk_right
                    have h_loop_le : loop.length ≤ loop.length + r := by omega
                    rw [Walk.HasBlockingRightSlot_comp_right loop suf _ h_loop_le]
                      at h_blk_right
                    rw [show loop.length + r - loop.length = r from by omega]
                      at h_blk_right
                    rw [← h_pre_suf]
                    have h_pre_le'' : pre.length ≤ k₀ + r := by rw [h_pre_len]; omega
                    rw [Walk.HasBlockingRightSlot_comp_right pre suf _ h_pre_le'']
                    rw [show k₀ + r - pre.length = r from by rw [h_pre_len]; omega]
                    exact h_blk_right
              exact hπ.2 (k₀ + r) vk h_get_π_kr h_blk_π
  · -- # badColliderCount decrease.
    -- We show that the bad-collider image of π' lives entirely inside
    -- (pre's old bad colliders) ∪ (suf's old bad colliders) — which is a
    -- subset of π's bad colliders.  Critically the position k₀ (which is
    -- a bad collider on π) is NOT in this image, so the cardinality strictly
    -- drops.  We prove this by exhibiting an injection f : π'.bad → π.bad
    -- whose image avoids k₀.
    --
    -- Concretely:
    --   * For k < pre.length on π', the corresponding π-position is k itself.
    --   * For k > pre.length + loop.length on π', the corresponding π-position
    --     is k - loop.length (= k - 2*d.length).
    --   * Positions k ∈ [pre.length, pre.length + loop.length] on π' are
    --     never bad colliders (they are either non-colliders or the centre c
    --     which has c ∈ C, so not bad).
    --
    -- We first establish the "no bad collider in the loop region" claim
    -- as an inline lemma.
    have h_loop_region_no_bad : ∀ k, pre.length ≤ k →
        k ≤ pre.length + loop.length →
        ¬ (π'.IsCollider k ∧
           ∀ vk, π'.vertices[k]? = some vk → vk ∉ C) := by
      intros k hk_lo hk_hi h_bad
      obtain ⟨h_col, h_all_nin⟩ := h_bad
      -- The collider clause of σ-openness already proven: π' is σ-open.
      -- So if π'.IsCollider k, then vertex at k is in AncSet C.
      -- For positions in the loop region with k = pre.length + d.length (centre c),
      -- the vertex is c ∈ C, not bad.
      -- For other positions in the loop region, π'.IsCollider k = False (so no contradiction).
      -- Hence we just need to identify the cases.
      by_cases hk_pre_eq : k = pre.length
      · -- Position is first copy of vk₀ on π'. Non-collider — contradict h_col.
        rw [hk_pre_eq] at h_col
        -- Need: π'.IsCollider pre.length = False. (Boundary A')
        have h_loop_comp_suf_no_head : ¬ (loop.comp suf).firstStepHeadAtSource := by
          rw [h_loop_eq]
          have h_d_nontrivial : d.length ≥ 1 := hd_pos
          cases d with
          | nil _ _ => simp [Walk.length] at h_d_nontrivial
          | cons _ s d_rest =>
              cases s with
              | forwardE _ =>
                  intro h_head; exact h_head
              | backwardE _ => exact hd_dir.elim
              | bidir _ => exact hd_dir.elim
        have h_col_eq :
            π'.IsCollider pre.length =
              (pre.comp (loop.comp suf)).IsCollider pre.length := by rw [h_π'_eq]
        rw [h_col_eq] at h_col
        exact Walk.refactor_IsCollider_comp_at_p_length_no_head_source
          pre (loop.comp suf) h_loop_comp_suf_no_head h_col
      · push_neg at hk_pre_eq
        have hk_pre_lt : pre.length < k := lt_of_le_of_ne hk_lo (Ne.symm hk_pre_eq)
        set q := k - pre.length with hq_def
        have hk_eq : k = pre.length + q := by omega
        have hq_pos : 0 < q := by omega
        have hq_le_loop : q ≤ loop.length := by omega
        -- π'.IsCollider k = (loop.comp suf).IsCollider q (comp_right).
        have h_col_X : (loop.comp suf).IsCollider q := by
          have h_eq : (pre.comp (loop.comp suf)).IsCollider k =
              (loop.comp suf).IsCollider (k - pre.length) :=
            Walk.refactor_IsCollider_comp_right pre (loop.comp suf) k hk_pre_lt
          have h_π'_col : π'.IsCollider k = (loop.comp suf).IsCollider (k - pre.length) := by
            rw [h_π'_eq]; exact h_eq
          rw [h_π'_col] at h_col
          exact h_col
        by_cases hq_loop_eq : q = loop.length
        · -- Boundary C': not a collider on (loop.comp suf).
          rw [hq_loop_eq] at h_col_X
          have h_d_rev_pos : 0 < d_rev.length := by rw [h_d_rev_len]; omega
          have h_d_rev_no_head : ¬ d_rev.lastStepHeadAtTarget :=
            Walk.IsBackwardDirectedWalk.no_lastStepHeadAtTarget d_rev h_d_rev_back
              h_d_rev_pos
          have h_loop_no_head : ¬ loop.lastStepHeadAtTarget := by
            rw [h_loop_eq]
            suffices h : ∀ {a b e : Node} (p1 : Walk G a b) (p2 : Walk G b e),
                0 < p2.length →
                ((p1.comp p2).lastStepHeadAtTarget ↔ p2.lastStepHeadAtTarget) by
              rw [h d d_rev h_d_rev_pos]; exact h_d_rev_no_head
            intros a b e p1 p2 hp2_pos
            induction p1 with
            | nil _ _ => rfl
            | cons _ _ p1' ih =>
                cases p1' with
                | nil _ _ =>
                    cases p2 with
                    | nil _ _ => simp [Walk.length] at hp2_pos
                    | cons _ _ _ =>
                        simp only [Walk.comp, Walk.lastStepHeadAtTarget]
                | cons _ _ _ =>
                    simp only [Walk.comp, Walk.lastStepHeadAtTarget]
                    exact ih p2 hp2_pos
          exact Walk.refactor_IsCollider_comp_at_p_length_no_head_target
            loop suf h_loop_no_head h_col_X
        · push_neg at hq_loop_eq
          have hq_loop_lt : q < loop.length := lt_of_le_of_ne hq_le_loop hq_loop_eq
          -- (loop.comp suf).IsCollider q = loop.IsCollider q (comp_left).
          have h_col_loop : loop.IsCollider q := by
            rw [Walk.refactor_IsCollider_comp_left loop suf q hq_loop_lt] at h_col_X
            exact h_col_X
          -- Get loop.vertices[q]? = some vk.
          have h_get_loop : ∃ vk, loop.vertices[q]? = some vk := by
            have hq_lt_vlen : q < loop.vertices.length := by
              rw [Walk.vertices_length]; omega
            exact ⟨loop.vertices[q]'hq_lt_vlen, List.getElem?_eq_getElem hq_lt_vlen⟩
          obtain ⟨vk, h_get_loop_vk⟩ := h_get_loop
          have h_get_π' : π'.vertices[k]? = some vk := by
            rw [hk_eq, h_π'_eq]
            have h_eq1 : (pre.comp (loop.comp suf)).vertices[pre.length + q]? =
                (loop.comp suf).vertices[q]? :=
              Walk.vertices_comp_right_shift pre (loop.comp suf) q
            rw [h_eq1, Walk.vertices_comp]
            have h_drop_len_loop : loop.vertices.dropLast.length = loop.length := by
              rw [List.length_dropLast, Walk.vertices_length]; omega
            have hq_lt_drop : q < loop.vertices.dropLast.length := by
              rw [h_drop_len_loop]; exact hq_loop_lt
            rw [List.getElem?_append_left hq_lt_drop, List.getElem?_dropLast,
                if_pos (by rw [Walk.vertices_length]; omega)]
            exact h_get_loop_vk
          have h_vk_nin : vk ∉ C := h_all_nin vk h_get_π'
          -- Case-split: q < d.length, q = d.length (centre), q > d.length.
          by_cases hq_lt_d : q < d.length
          · -- Region B: not a collider on d → not on loop.
            have h_col_d : d.IsCollider q := by
              rw [h_loop_eq, Walk.refactor_IsCollider_comp_left d d_rev q hq_lt_d]
                at h_col_loop
              exact h_col_loop
            exact Walk.IsDirectedWalk.interior_not_collider d hd_dir q hq_pos
              hq_lt_d h_col_d
          · push_neg at hq_lt_d
            by_cases hq_d_eq : q = d.length
            · -- Centre c. vk = c ∈ C, but h_vk_nin says vk ∉ C. Contradict.
              rw [hq_d_eq] at h_get_loop_vk
              have h_get_c : loop.vertices[d.length]? = some c := by
                rw [h_loop_eq, Walk.vertices_comp_at_left_length d d_rev]
              rw [h_get_c] at h_get_loop_vk
              have h_vk_eq : vk = c := (Option.some.inj h_get_loop_vk).symm
              rw [h_vk_eq] at h_vk_nin
              exact h_vk_nin hc_C
            · push_neg at hq_d_eq
              have hq_d_gt : d.length < q := lt_of_le_of_ne hq_lt_d (Ne.symm hq_d_eq)
              set q' := q - d.length with hq'_def
              have hq'_pos : 1 ≤ q' := by omega
              have hq'_lt : q' < d_rev.length := by rw [h_d_rev_len]; omega
              have h_col_d_rev : d_rev.IsCollider q' := by
                rw [h_loop_eq, Walk.refactor_IsCollider_comp_right d d_rev q hq_d_gt]
                  at h_col_loop
                exact h_col_loop
              exact Walk.IsBackwardDirectedWalk.interior_not_collider d_rev
                h_d_rev_back q' hq'_pos hq'_lt h_col_d_rev
    -- Now do the injection / cardinality argument.
    show (π'.badColliderSet C).card < (π.badColliderSet C).card
    -- Define f : ℕ → ℕ: maps loop region to (irrelevant), elsewhere transports back.
    let f : ℕ → ℕ := fun k => if k < pre.length then k else k - 2 * d.length
    have h_pi'_bad_def :
        π'.badColliderSet C = (Finset.range (π'.length + 1)).filter
          (fun k => π'.IsCollider k ∧ ∀ vk, π'.vertices[k]? = some vk → vk ∉ C) := rfl
    -- Show: f-image of π'.badColliderSet ⊆ π.badColliderSet ∖ {k₀}.
    -- For each k ∈ π'.badColliderSet, f k ∈ π.badColliderSet, and f k ≠ k₀.
    -- Then apply Finset.card_image_of_injOn + Finset.card_lt_card.
    have h_image_sub :
        (π'.badColliderSet C).image f ⊆ (π.badColliderSet C).erase k₀ := by
      intros j hj
      rw [Finset.mem_image] at hj
      obtain ⟨k, hk_in_bad, hf_eq⟩ := hj
      simp only [Walk.badColliderSet, Finset.mem_filter, Finset.mem_range] at hk_in_bad
      obtain ⟨hk_range, hk_col, hk_all_nin⟩ := hk_in_bad
      have hk_lt_π' : k < π'.length := Walk.isCollider_lt_length π' k hk_col
      -- f k:
      -- case k < pre.length: f k = k. Position k on π' is in Region A, identified with π's position k.
      -- case k ≥ pre.length: by h_loop_region_no_bad, k > pre.length + loop.length (since the loop region has no bad colliders).
      --   In that case f k = k - 2*d.length = k - loop.length. Position on π = k - loop.length.
      have h_not_loop : ¬ (pre.length ≤ k ∧ k ≤ pre.length + loop.length) := by
        intro ⟨hk_lo, hk_hi⟩
        exact h_loop_region_no_bad k hk_lo hk_hi ⟨hk_col, hk_all_nin⟩
      push_neg at h_not_loop
      rw [Finset.mem_erase]
      refine ⟨?_, ?_⟩
      · -- f k ≠ k₀.
        subst hf_eq
        simp only [f]
        by_cases hk_pre : k < pre.length
        · -- f k = k. Need k ≠ k₀.  Since k < pre.length = k₀, k < k₀, so k ≠ k₀.
          simp only [if_pos hk_pre]
          rw [h_pre_len] at hk_pre
          omega
        · push_neg at hk_pre
          simp only [if_neg (not_lt.mpr hk_pre)]
          -- k ≥ pre.length, so by h_not_loop, k > pre.length + loop.length (the second
          -- disjunct of `¬ (a ∧ b)`).
          have hk_gt_loop : pre.length + loop.length < k := h_not_loop hk_pre
          -- f k = k - 2*d.length. Need this ≠ k₀.
          -- k - 2*d.length > pre.length + loop.length - 2*d.length = pre.length = k₀.
          rw [h_loop_len] at hk_gt_loop
          rw [h_pre_len] at hk_pre
          omega
      · -- f k ∈ π.badColliderSet C.
        subst hf_eq
        simp only [Walk.badColliderSet, Finset.mem_filter, Finset.mem_range]
        simp only [f]
        by_cases hk_pre : k < pre.length
        · simp only [if_pos hk_pre]
          rw [h_pre_len] at hk_pre
          -- Need: k < π.length + 1 AND π.IsCollider k AND π.vertices[k]? = ... ∉ C.
          refine ⟨?_, ?_, ?_⟩
          · -- k < π.length + 1. Since k < k₀ ≤ π.length.
            omega
          · -- π.IsCollider k follows from π'.IsCollider k via transport.
            rw [← h_pre_suf]
            rw [Walk.refactor_IsCollider_comp_left pre suf k (by rw [h_pre_len]; exact hk_pre)]
            rw [h_π'_eq] at hk_col
            rw [Walk.refactor_IsCollider_comp_left pre (loop.comp suf) k
              (by rw [h_pre_len]; exact hk_pre)] at hk_col
            exact hk_col
          · -- vertex transport.
            intros vk h_get
            apply hk_all_nin
            -- π.vertices[k]? = π'.vertices[k]?
            rw [h_π'_eq]
            -- (pre.comp (loop.comp suf)).vertices[k]? = pre.vertices[k]?
            have h_eq1 : (pre.comp (loop.comp suf)).vertices[k]? = pre.vertices[k]? := by
              rw [Walk.vertices_comp]
              have h_drop_lt : k < pre.vertices.dropLast.length := by
                rw [List.length_dropLast, Walk.vertices_length, h_pre_len]; omega
              rw [List.getElem?_append_left h_drop_lt, List.getElem?_dropLast]
              rw [if_pos (by rw [Walk.vertices_length, h_pre_len]; omega)]
            have h_eq2 : pre.vertices[k]? = π.vertices[k]? := by
              rw [← h_pre_suf, Walk.vertices_comp]
              have h_drop_lt : k < pre.vertices.dropLast.length := by
                rw [List.length_dropLast, Walk.vertices_length, h_pre_len]; omega
              rw [List.getElem?_append_left h_drop_lt, List.getElem?_dropLast]
              rw [if_pos (by rw [Walk.vertices_length, h_pre_len]; omega)]
            rw [h_eq1, h_eq2]
            exact h_get
        · push_neg at hk_pre
          simp only [if_neg (not_lt.mpr hk_pre)]
          have hk_gt_loop : pre.length + loop.length < k := h_not_loop hk_pre
          -- f k = k - 2 * d.length. Set r := k - 2*d.length = k - loop.length (with h_loop_len).
          set r := k - 2 * d.length with hr_def
          have hk_eq : k = r + 2 * d.length := by
            have hk_ge : 2 * d.length ≤ k := by rw [← h_loop_len]; omega
            omega
          -- r corresponds to π position via π = pre.comp suf, position = k - 2*d.length = r.
          -- π.IsCollider r follows from π'.IsCollider k.
          -- Wait, r = k - 2*d.length, but we need to relate to π's positions. π has length π.length.
          -- pre = first k₀ steps, suf = remaining π.length - k₀ steps.
          -- On π, the position corresponding to π'-position k > pre.length + loop.length is k - loop.length = k - 2*d.length = r.
          refine ⟨?_, ?_, ?_⟩
          · -- r < π.length + 1.
            rw [h_π'_len] at hk_lt_π'
            omega
          · -- π.IsCollider r. Use π = pre.comp suf and r > pre.length (since k > pre.length + loop.length).
            have hr_gt_pre : pre.length < r := by
              rw [h_loop_len] at hk_gt_loop
              omega
            have hr_pre_eq : r - pre.length = k - 2 * d.length - pre.length := by rfl
            rw [← h_pre_suf]
            rw [Walk.refactor_IsCollider_comp_right pre suf r hr_gt_pre]
            -- π'.IsCollider k = suf.IsCollider (k - pre.length - 2*d.length)... = suf.IsCollider (r - pre.length).
            rw [h_π'_eq] at hk_col
            have h_pre_lt_k : pre.length < k := by
              have : pre.length ≤ pre.length + loop.length := Nat.le_add_right _ _
              omega
            rw [Walk.refactor_IsCollider_comp_right pre (loop.comp suf) k h_pre_lt_k] at hk_col
            have h_loop_lt : loop.length < k - pre.length := by omega
            rw [Walk.refactor_IsCollider_comp_right loop suf (k - pre.length) h_loop_lt] at hk_col
            have h_arith : k - pre.length - loop.length = r - pre.length := by
              rw [hr_def, h_loop_len]; omega
            rw [h_arith] at hk_col
            exact hk_col
          · -- vertex transport: h_get : π.vertices[r]? = some vk → goal vk ∉ C.
            -- Use hk_all_nin : ∀ vk, π'.vertices[k]? = some vk → vk ∉ C.
            -- Show: π.vertices[r]? = some vk → π'.vertices[k]? = some vk.
            intros vk h_get
            apply hk_all_nin
            -- π.vertices[r]?:  r > k₀ (because k > pre.length + loop.length = k₀ + 2*d.length),
            -- so reading r on π = pre.comp suf gives suf.vertices[r - k₀]?.
            -- π'.vertices[k]?: k > pre.length + loop.length, so reading k on π' gives
            -- suf.vertices[k - pre.length - loop.length]? = suf.vertices[r - k₀]?.
            -- The two are equal.
            -- Compute π.vertices[r]?:
            rw [← h_pre_suf, Walk.vertices_comp] at h_get
            have h_drop_len_pre : pre.vertices.dropLast.length = k₀ := by
              rw [List.length_dropLast, Walk.vertices_length, h_pre_len]; omega
            have h_ge : pre.vertices.dropLast.length ≤ r := by
              rw [h_drop_len_pre]
              rw [h_loop_len] at hk_gt_loop
              omega
            rw [List.getElem?_append_right h_ge, h_drop_len_pre] at h_get
            -- h_get : suf.vertices[r - k₀]? = some vk.
            -- Now compute π'.vertices[k]?:
            rw [h_π'_eq]
            have h_pre_lt_k : pre.length < k := by
              have : pre.length ≤ pre.length + loop.length := Nat.le_add_right _ _
              omega
            have h_eq1 : (pre.comp (loop.comp suf)).vertices[pre.length + (k - pre.length)]? =
                (loop.comp suf).vertices[k - pre.length]? :=
              Walk.vertices_comp_right_shift pre (loop.comp suf) (k - pre.length)
            have h_k_eq : pre.length + (k - pre.length) = k := by omega
            rw [h_k_eq] at h_eq1
            rw [h_eq1]
            have h_loop_lt : loop.length < k - pre.length := by
              rw [h_loop_len]; omega
            have h_eq2 : (loop.comp suf).vertices[loop.length + (k - pre.length - loop.length)]? =
                suf.vertices[k - pre.length - loop.length]? :=
              Walk.vertices_comp_right_shift loop suf (k - pre.length - loop.length)
            have h_loop_k_eq : loop.length + (k - pre.length - loop.length) = k - pre.length := by
              omega
            rw [h_loop_k_eq] at h_eq2
            rw [h_eq2]
            -- Goal: suf.vertices[k - pre.length - loop.length]? = some vk.
            -- h_get : suf.vertices[r - k₀]? = some vk.
            have h_arith : k - pre.length - loop.length = r - k₀ := by
              rw [hr_def, h_loop_len, h_pre_len]; omega
            rw [h_arith]
            exact h_get
    -- Now use h_image_sub.
    -- |π'.badColliderSet C| = |image f| (by injectivity).
    -- |image f| ≤ |π.badColliderSet C ∖ {k₀}| = |π.badColliderSet C| - 1.
    -- And k₀ ∈ π.badColliderSet C, so |π.badColliderSet C| ≥ 1.
    -- Hence |π'.badColliderSet C| < |π.badColliderSet C|.
    have h_k₀_in : k₀ ∈ π.badColliderSet C := by
      simp only [Walk.badColliderSet, Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, h_col_k₀, ?_⟩
      intros vk h_get
      rw [h_get_k₀] at h_get
      have : vk = vk₀ := Option.some.inj h_get.symm
      rw [this]; exact h_vk₀_nin
    -- Show f is injective on π'.badColliderSet C.
    have h_inj : Set.InjOn f ↑(π'.badColliderSet C) := by
      intros x hx y hy h_fxy
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Walk.badColliderSet,
                 Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hx hy
      obtain ⟨_, hx_col, hx_nin⟩ := hx
      obtain ⟨_, hy_col, hy_nin⟩ := hy
      -- x and y both ∈ π'.badColliderSet, so they're bad.
      -- f(x) = f(y): case analysis.
      have hx_not_loop : ¬ (pre.length ≤ x ∧ x ≤ pre.length + loop.length) := by
        intro ⟨hx_lo, hx_hi⟩
        exact h_loop_region_no_bad x hx_lo hx_hi ⟨hx_col, hx_nin⟩
      have hy_not_loop : ¬ (pre.length ≤ y ∧ y ≤ pre.length + loop.length) := by
        intro ⟨hy_lo, hy_hi⟩
        exact h_loop_region_no_bad y hy_lo hy_hi ⟨hy_col, hy_nin⟩
      push_neg at hx_not_loop hy_not_loop
      simp only [f] at h_fxy
      by_cases hx_pre : x < pre.length
      · by_cases hy_pre : y < pre.length
        · simp only [if_pos hx_pre, if_pos hy_pre] at h_fxy; exact h_fxy
        · push_neg at hy_pre
          have hy_gt_loop : pre.length + loop.length < y := hy_not_loop hy_pre
          simp only [if_pos hx_pre, if_neg (not_lt.mpr hy_pre)] at h_fxy
          -- h_fxy : x = y - 2*d.length. But x < pre.length, y - 2*d.length > pre.length.
          rw [h_loop_len] at hy_gt_loop; omega
      · push_neg at hx_pre
        have hx_gt_loop : pre.length + loop.length < x := hx_not_loop hx_pre
        by_cases hy_pre : y < pre.length
        · simp only [if_neg (not_lt.mpr hx_pre), if_pos hy_pre] at h_fxy
          rw [h_loop_len] at hx_gt_loop; omega
        · push_neg at hy_pre
          have hy_gt_loop : pre.length + loop.length < y := hy_not_loop hy_pre
          simp only [if_neg (not_lt.mpr hx_pre), if_neg (not_lt.mpr hy_pre)] at h_fxy
          rw [h_loop_len] at hx_gt_loop hy_gt_loop
          omega
    -- |image f| = |source|.
    have h_card_image :
        ((π'.badColliderSet C).image f).card = (π'.badColliderSet C).card :=
      Finset.card_image_of_injOn h_inj
    -- |image f| ≤ |target ∖ {k₀}|.
    have h_card_le_image := Finset.card_le_card h_image_sub
    -- |target ∖ {k₀}| = |target| - 1.
    have h_card_erase : ((π.badColliderSet C).erase k₀).card = (π.badColliderSet C).card - 1 :=
      Finset.card_erase_of_mem h_k₀_in
    -- Final inequality.
    have h_target_pos : 1 ≤ (π.badColliderSet C).card :=
      Finset.card_pos.mpr ⟨k₀, h_k₀_in⟩
    -- Goal here is `(π'.badColliderSet C).card < (π.badColliderSet C).card`
    -- after the outer `unfold Walk.badColliderCount` reduced both sides.
    -- However, that unfolding may have happened at a different syntactic level.
    -- Let's combine the bounds explicitly.
    have h_chain :
        (π'.badColliderSet C).card ≤ (π.badColliderSet C).card - 1 := by
      rw [← h_card_image, ← h_card_erase]
      exact h_card_le_image
    omega

private lemma Walk.sigma_open_colliders_to_C
    {G : CDMG Node} {C : Set Node} {hC : C ⊆ ↑G.J ∪ ↑G.V}
    {u v : Node} (π : Walk G u v) (hπ : π.IsSigmaOpenGiven C hC) :
    ∃ π' : Walk G u v, π'.IsSigmaOpenGiven C hC ∧
      (∀ (k : ℕ) (vk : Node),
          π'.vertices[k]? = some vk → π'.IsCollider k → vk ∈ C) := by
  -- Strong induction on π.badColliderCount C.
  induction h_count : π.badColliderCount C using Nat.strong_induction_on
    generalizing u v π with
  | _ n ih =>
    by_cases h_zero : n = 0
    · -- Base case: badColliderCount = 0.
      -- Every collider position on π has its vertex in C.
      subst h_zero
      have h_all_in_C := (Walk.badColliderCount_eq_zero_iff π C).mp h_count
      exact ⟨π, hπ, h_all_in_C⟩
    · -- Inductive step: badColliderCount > 0.
      have h_pos : 0 < π.badColliderCount C := by rw [h_count]; omega
      obtain ⟨k₀, vk₀, h_get_k₀, h_col_k₀, h_vk₀_nin⟩ :=
        Walk.exists_min_bad_collider π C h_pos
      -- Apply the splice helper to get π' with smaller bad count.
      obtain ⟨π', hπ'_open, h_count_lt⟩ :=
        Walk.spliceBadCollider π hπ h_get_k₀ h_col_k₀ h_vk₀_nin
      -- Apply IH to π'.
      have h_count' : π'.badColliderCount C < n := by rw [h_count] at h_count_lt; exact h_count_lt
      exact ih (π'.badColliderCount C) h_count' π' hπ'_open rfl

set_option linter.unusedVariables false in
-- claim_3_23 -- start statement
theorem sigma_open_paths_walks
    (G : CDMG Node) (C : Set Node) (hC : C ⊆ ↑G.J ∪ ↑G.V)
    {w₁ w₂ : Node}
    (hw₁ : w₁ ∈ (↑G.J ∪ ↑G.V : Set Node))
    (hw₂ : w₂ ∈ (↑G.J ∪ ↑G.V : Set Node)) :
    List.TFAE
      [ ∃ (π : Walk G w₁ w₂), π.IsPath ∧ π.IsSigmaOpenGiven C hC,
        ∃ (π : Walk G w₁ w₂), π.IsSigmaOpenGiven C hC,
        ∃ (π : Walk G w₁ w₂), π.IsSigmaOpenGiven C hC ∧
          (∀ (k : ℕ) (vk : Node),
              π.vertices[k]? = some vk → π.IsCollider k → vk ∈ C) ]
-- claim_3_23 -- end statement
  := by
  -- Cyclic TFAE proof: (1 → 2), (3 → 2), (2 → 1), (2 → 3).
  tfae_have h12 : 1 → 2 := fun ⟨π, _, hσ⟩ => ⟨π, hσ⟩
  tfae_have h32 : 3 → 2 := fun ⟨π, hσ, _⟩ => ⟨π, hσ⟩
  tfae_have h21 : 2 → 1 := fun ⟨π, hσ⟩ =>
    Walk.sigma_open_to_path π hσ
  tfae_have h23 : 2 → 3 := fun ⟨π, hσ⟩ =>
    Walk.sigma_open_colliders_to_C π hσ
  tfae_finish

end CDMG

end Causality
