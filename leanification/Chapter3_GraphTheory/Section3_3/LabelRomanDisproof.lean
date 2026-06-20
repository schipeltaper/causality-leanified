import Chapter3_GraphTheory.Section3_3.SigmaSeparationSymmetric

namespace Causality

/-!
# Disprove-side of `LabelRoman`  (`claim_3_27` / `lem:replace_walk`)

TeX proof: `claim_3_27_disproof_LabelRoman.tex`.

Disprove-side of `Section3_3/LabelRoman.lean` — the row's manager
emitted `mistake`.  The prove-side `LabelRoman.lean` is intentionally
left intact (with its `:= by sorry` placeholder) in case the manager
flips back via `unmistake`.  This file only adds the negation
theorem; it does not modify the prove-side file.

## Design choice — disprove-side encoding

*Shape (b), existential-witness counter-example form.*  The prove-side
`replace_walk` uses an explicit theorem parameter list rather than a
`∀ ...`-block.  Per the `prove_claim_in_lean.md` worker prompt and the
manager's task description, when the prove-side uses an explicit
parameter list the existential-witness counter-example form is the
cleaner negation shape: `not_replace_walk` exhibits concrete witnesses
for every universally-quantified parameter of the prove-side AND for
the existentially-bound `σ_ij` and `π'`, proves the structural
conjuncts of the prove-side's existential body, and finally proves
`¬ π'.IsSigmaOpenGiven C hC` for the exhibited `π'`.  Equivalently:
the witness exhibits a concrete instance on which the LN's case-(i)
replacement procedure fails, contradicting the prove-side's claim
that some valid `(σ_ij, π')` exists.

*Disprove-mode rationale.*  Case (i) of the LN lemma fails for walks
traversing a directed self-loop under the canonical Lean encoding.
Two registered subtleties from `leanification/working_subtlety_register.json`
land on this row:
- `self_loop_makes_tuh_and_hut_simultaneously_true` (chapter-wide,
  against `def_3_15`): the `WalkStep.IsInto` helper fires for both
  endpoints of a directed self-loop encoded as `.forwardE` or
  `.backwardE`, by node-equality on type indices.
- `claim_3_27_case_i_fails_for_self_loops` (row-level): the
  consumer-side propagation — the LN's case-(i) shortest directed
  replacement introduces a collider at the boundary between the new
  path and the original suffix's self-loop step, breaking σ-openness
  on the modified walk.

*Cross-reference to prove-side.*  `Section3_3/LabelRoman.lean` holds
the positive theorem signature with a `:= by sorry` placeholder,
intentionally left intact for the `unmistake` flip-back path.  The
`sorry` warning emitted by `lake build` on the prove-side file is
expected during the disprove flow; the row's `main_lean_file` will
be re-pointed at `LabelRomanDisproof.lean` at cleanup time.
-/

namespace CDMG

-- ## Design choice — `claim_3_27` section-wide statement context
--
-- *Polymorphic `Node : Type*` with `[DecidableEq Node]`.*  Matches the
--   chapter-wide convention used by every `CDMG`-opening file in
--   Sections 3.1, 3.2 and 3.3 — see
--   `Section3_3/SigmaSeparationSymmetric.lean:88` for the same block
--   in `claim_3_22`, and `Section3_3/SigmaBlockedWalks.lean` for the
--   same block in `def_3_17`.  The `CDMG`, `Walk`, `Sc`,
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

-- ## Design choice — `Walk.replaceWalkCaseI` (case-(i)/case-(ii) discriminant)
--
-- *Role.*  Captures the LN's case-(i)/case-(ii) discriminant of
--   `lem:replace_walk`: case (i) is "`j = π.length`  OR  the walk-step
--   at position `j` on `π` is `.forwardE _` (the directed E-edge
--   `v_j → v_{j+1}`)"; case (ii) is the negation.  Used in the
--   theorem signature below to disjunctively switch the
--   direction-witness on the replacement subwalk `σ_ij`: in case (i)
--   we have `σ_ij.IsDirectedWalk`; in case (ii) we have
--   `σ_ij.reverse.IsDirectedWalk`.
--
-- *Why a dedicated helper predicate, not an inline disjunction.*
--   Encoding the case-(i)/case-(ii) disjunction inline in the theorem
--   signature would force two near-duplicate disjunction-of-Walk-step-
--   constructor patterns into the binder block (one positive for the
--   `σ_ij.IsDirectedWalk` direction-witness, one negated for the
--   `σ_ij.reverse.IsDirectedWalk` direction-witness).  Pulling out a
--   named helper consolidates the discriminant into a single Prop on
--   `(π, j)`, makes the signature readable, and gives the proof-phase
--   worker a clean `(h : π.replaceWalkCaseI j)` /
--   `(h : ¬ π.replaceWalkCaseI j)` hypothesis to case-split on.
--
-- *Why exclude `.bidir` from case (i).*  The LN's case-(i) trigger is
--   "`v_j \tuh v_{j+1}` on `π`" — the `\tuh` macro encodes the
--   directed E-edge `(v_j, v_{j+1}) ∈ E` (tail at `v_j`, head at
--   `v_{j+1}`).  A `.bidir` walk-step encodes a bidirected `L`-edge
--   `s(v_j, v_{j+1}) ∈ G.L`, which places arrowheads at BOTH `v_j`
--   and `v_{j+1}` — this is `\huh` in the LN's symbol set, NOT
--   `\tuh`.  Bidirected steps therefore fall under case (ii) in the
--   LN.  The canonical rewritten tex statement
--   (`tex/claim_3_27_statement_LabelRoman.tex` case (i)) explicitly
--   says `a_j = (v_j, v_{j+1}) \in E`, which excludes bidirected
--   `L`-edges.
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

namespace claim_3_27_disproof

/-! ### Concrete counter-example data over `Bool` -/

-- The CDMG `G = (J, V, E, L)` over `Bool` (`false = a`, `true = b`):
--   * `J = ∅`;
--   * `V = {false, true}` (= `Finset.univ`);
--   * `E = {(false, true), (true, false), (true, true)}` — the directed
--     2-cycle plus the directed self-loop `(true, true)` (legal in a
--     CDMG: `def_3_1` imposes no irreflexivity on `E`, only on `L`;
--     see `CDMG.lean`'s "directed self-loops" design bullet);
--   * `L = ∅`.
-- Declared as `abbrev` so the structure projections (`G.E`, `G.L`,
-- `G.J`, `G.V`) reduce definitionally for the `decide`/`rfl`/`trivial`
-- closures below.
abbrev G : CDMG Bool where
  J := ∅
  V := Finset.univ
  hJV_disj := by simp
  E := {(false, true), (true, false), (true, true)}
  hE_subset := by
    intro e he
    fin_cases he <;> exact ⟨by decide, by decide⟩
  L := ∅
  hL_subset := by intro _ hs; cases hs
  hL_irrefl := by intro _ hs; cases hs

-- E-membership witnesses for the three directed edges.
private lemma h_ab : ((false, true) : Bool × Bool) ∈ G.E := by decide
private lemma h_ba : ((true, false) : Bool × Bool) ∈ G.E := by decide
private lemma h_bb : ((true, true) : Bool × Bool) ∈ G.E := by decide

-- Vertex-membership witnesses (`false ∈ G`, `true ∈ G`).  The CDMG
-- membership instance (`v ∈ G ↔ v ∈ G.J ∪ G.V`) is not directly
-- decidable in the synthesizer's eye, so unfold to `Finset.mem_union`
-- + `Finset.mem_univ`.
private lemma h_a_mem : (false : Bool) ∈ G :=
  show false ∈ G.J ∪ G.V from Finset.mem_union.mpr (Or.inr (Finset.mem_univ _))
private lemma h_b_mem : (true : Bool) ∈ G :=
  show true ∈ G.J ∪ G.V from Finset.mem_union.mpr (Or.inr (Finset.mem_univ _))

-- The walk `π = (false, .backwardE h_ba, true, .forwardE h_bb, true)`
-- in `G`.  Vertex sequence `[false, true, true]`, length 2.  The
-- middle step is the directed self-loop traversed forward.
def π : Walk G false true :=
  Walk.cons true (WalkStep.backwardE h_ba)
    (Walk.cons true (WalkStep.forwardE h_bb)
      (Walk.nil true h_b_mem))

-- The LN's case-(i) prescribed shortest directed walk from
-- `v_i = false` to `v_j = true`: the single directed edge
-- `(false, true) ∈ G.E`.  Vertex sequence `[false, true]`, length 1.
def σ_ij : Walk G false true :=
  Walk.cons true (WalkStep.forwardE h_ab) (Walk.nil true h_b_mem)

-- The modified walk `π'` obtained from `π` by replacing the subwalk at
-- positions 0..1 by `σ_ij`.  Vertex sequence `[false, true, true]`,
-- length 2.  The first step is the new `.forwardE h_ab` (from
-- `σ_ij`); the second step is the original `.forwardE h_bb` (the
-- self-loop, inherited from `π`'s suffix at position `j = 1`).
def π' : Walk G false true :=
  Walk.cons true (WalkStep.forwardE h_ab)
    (Walk.cons true (WalkStep.forwardE h_bb)
      (Walk.nil true h_b_mem))

/-! ### Supporting facts -/

-- `σ_ij` is a directed walk (its single step is `.forwardE`).
private lemma σ_ij_isDirected : σ_ij.IsDirectedWalk := trivial

-- `π` is in case (i) at position `j = 1`: the step at position 1 is
-- `.forwardE h_bb` (the self-loop, encoded forward).
private lemma π_replaceWalkCaseI_one : π.replaceWalkCaseI 1 := trivial

-- `true ∈ G.Sc true` via the length-0 trivial walk witness on each side.
private lemma Sc_b_b : true ∈ G.Sc true := by
  refine ⟨⟨h_b_mem, Walk.nil true h_b_mem, ?_⟩,
           ⟨h_b_mem, Walk.nil true h_b_mem, ?_⟩⟩
  · trivial
  · trivial

-- `false ∈ G.Sc true` via the directed 2-cycle `false ↔ true`.
private lemma Sc_a_b : false ∈ G.Sc true := by
  refine ⟨⟨h_a_mem, σ_ij, ?_⟩,
           ⟨h_a_mem,
            Walk.cons false (WalkStep.forwardE h_ba) (Walk.nil false h_a_mem),
            ?_⟩⟩
  · trivial
  · trivial

-- `π` is `∅`-σ-open.  Position 1 (the only interior position) is a
-- non-collider because the incoming step `.backwardE h_ba` has type
-- `WalkStep G false true`, so `IsInto true` on it unfolds to
-- `true = false ∨ s(false,true) ∈ ∅ ∧ _ = False`.  Positions 0 and 2
-- are endpoints (not colliders by the IsCollider def's cons-nil
-- branches).  The blockable-non-collider clause is vacuous because
-- `vk ∉ ∅` is universally `True`.
private lemma π_isSigmaOpen
    (hC : (∅ : Set Bool) ⊆ ↑G.J ∪ ↑G.V) :
    π.IsSigmaOpenGiven (∅ : Set Bool) hC := by
  refine ⟨?_, ?_⟩
  · -- collider clause: no collider exists at any position on π
    rintro k _ _ hcol
    exfalso
    match k with
    | 0 => exact hcol
    | 1 =>
      -- `hcol.1 : (WalkStep.backwardE h_ba).IsInto true`
      -- unfolds to `true = false ∨ s(false,true) ∈ G.L ∧ _`
      rcases hcol.1 with h | ⟨hL, _⟩
      · exact absurd h (by decide)
      · exact absurd hL (by decide)
    | k + 2 => exact hcol
  · -- blockable clause: `vk ∉ ∅` is universally True
    rintro _ _ _ _ h
    exact h

-- `π'.IsCollider 1` — the load-bearing fact.  At position 1 on `π'`,
-- vertex `true`, both incident steps `.forwardE h_ab` and
-- `.forwardE h_bb` satisfy `IsInto true` via the `w = v` disjunct
-- (target index `v = true` matches `w = true`).  The conjunction
-- fires `True ∧ True = True`.  This is the manifestation of the
-- subtlety `self_loop_makes_tuh_and_hut_simultaneously_true`: the
-- self-loop's type indices are both `true`, so `IsInto true` fires
-- on it regardless of constructor tag, and combined with the new
-- `.forwardE h_ab` from `σ_ij` (which legitimately points into
-- `true`), produces a collider at `true`.
private lemma π'_isCollider_one : π'.IsCollider 1 :=
  ⟨Or.inl rfl, Or.inl rfl⟩

private lemma π'_vertices_one : π'.vertices[1]? = some true := rfl

/-! ### The negation theorem -/

set_option linter.unusedVariables false in
-- ref: claim_3_27 (disprove, existential-witness counter-example)
--
-- *Human-language summary.*  We exhibit a concrete CDMG `G` over
-- `Bool`, a subset `C = ∅`, a walk `π = (a, b, b)` in `G` that is
-- `C`-σ-open, positions `i = 0, j = 1` satisfying the prove-side's
-- hypotheses, AND concrete witnesses for the existentially-bound
-- `σ_ij` and `π'` (the LN's case-(i) prescribed shortest directed
-- replacement) that satisfy all structural conjuncts of the
-- prove-side existential EXCEPT the σ-openness of `π'` — which fails
-- because `π'` has a collider at position 1, the `b` vertex where
-- the new directed edge into `b` meets the inherited self-loop.
-- The σ-blocked verdict at position 1 derives from `b ∉ AncSet ∅`.
--
-- ## Design choice — disprove-side counter-example encoding
--
-- *(1) Existential-witness counter-example form, shape (b) over (a).*
--   Two negation shapes were considered:
--     (a) flat `¬ (∀ G C hC u w π … ∃ σ_ij π', P(σ_ij, π'))` —
--         instantiates as nested `intro`s over every prove-side
--         binder (16 binders here), then `refine ⟨_, _, …, ?_⟩` to
--         destructure the existential body and refute it.  Tactic
--         bookkeeping scales linearly with the binder count.
--     (b) explicit-witness existential
--         `∃ Node _inst G C hC u w π … σ_ij π', (structural
--         conjuncts) ∧ ¬ π'.IsSigmaOpenGiven C hC` — packs every
--         witness into a single `refine ⟨…⟩` block and discharges
--         every structural conjunct on the same `refine` line.
--   Shape (b) is chosen because the prove-side `replace_walk` uses
--   an explicit parameter list (not a `∀ ...`-block in the
--   conclusion), so the witness-list shape mirrors the prove-side
--   parameter list one-for-one — a reader can trace each witness
--   back to a prove-side binder by position.  Witness positions ↔
--   prove-side binders:
--     `Node      := Bool`;
--     `_inst     := inferInstance` (the canonical `DecidableEq Bool`);
--     `G         := claim_3_27_disproof.G` (the 2-cycle + self-loop);
--     `C         := (∅ : Set Bool)`;
--     `hC        := Set.empty_subset _`;
--     `u, w      := false, true`;
--     `π         := claim_3_27_disproof.π` (vertex seq `[a, b, b]`,
--                   steps `.backwardE h_ba` then `.forwardE h_bb`);
--     `hπ        := π_isSigmaOpen (Set.empty_subset _)`;
--     `i, j      := 0, 1`;
--     `hij, hjn  := Nat.zero_lt_one, (by decide : 1 ≤ π.length)`;
--     `v_i, v_j  := false, true`;
--     `h_get_i,
--      h_get_j   := rfl, rfl`;
--     `h_Sc      := Sc_a_b`;
--     `σ_ij      := claim_3_27_disproof.σ_ij` (single-edge
--                   `.forwardE h_ab`);
--     `π'        := claim_3_27_disproof.π'` (vertex seq `[a, b, b]`,
--                   steps `.forwardE h_ab` then `.forwardE h_bb`).
--   The five existential-body conjuncts discharge as:
--     case-(i) directedness AND minimality of σ_ij over directed
--       walks v_i → v_j — `σ_ij_isDirected` paired with the
--       one-line minimality discharge `Nat.succ_le_succ
--       (Nat.zero_le _)` on the `.cons` branch of the `match` (the
--       `.nil` branch is eliminated by `Bool` constructor
--       injectivity, since `Walk.nil v hv : Walk G v v` cannot
--       inhabit `Walk G false true`);
--     case-(ii) vacuity — `absurd π_replaceWalkCaseI_one hno`, which
--       discharges the whole `σ_ij.reverse.IsDirectedWalk ∧
--       (∀ τ, …)` conjunction at once since `π.replaceWalkCaseI 1`
--       holds for our `π`;
--     SCC-containment of `σ_ij.vertices` — `Sc_a_b` / `Sc_b_b`;
--     vertex-list factorisation — `rfl`;
--     σ-blockedness of `π'` — `π'_isCollider_one` together with
--     `AncSet ∅ = ∅` collapsing `b ∈ AncSet ∅` to `False`.
--
-- *(1b) σ_ij pinned as a shortest directed walk via a minimality
--   conjunct on each case branch.*  The LN's `lem:replace_walk`
--   prescribes σ_ij as a *shortest* directed walk from v_i to v_j in
--   case (i), and the reverse of a shortest directed walk from v_j
--   to v_i in case (ii); see
--   `tex/claim_3_27_statement_LabelRoman.tex` lines 48-95.  The
--   negation signature accordingly carries the minimality clause on
--   each case branch as a second conjunct alongside the direction
--   witness:
--     case (i):  `σ_ij.IsDirectedWalk ∧ (∀ τ : Walk G v_i v_j,
--                  τ.IsDirectedWalk → σ_ij.length ≤ τ.length)`;
--     case (ii): `σ_ij.reverse.IsDirectedWalk ∧ (∀ τ : Walk G v_j v_i,
--                  τ.IsDirectedWalk → σ_ij.reverse.length ≤ τ.length)`.
--   Without the minimality clause the negation would be strictly
--   weaker than `¬ (LN claim)`: a non-shortest σ_ij in `Sc(v_j)`
--   might fail σ-openness on its π' splice even when the LN's
--   shortest does not, so a downstream consumer reading only the
--   direction witness could not extract "the LN's shortest σ_ij is
--   σ-blocked" without separately rebuilding minimality.  The strict-
--   equivalence checker flagged exactly this drift on an earlier
--   version of this file (the friendly checker missed it because
--   `σ_ij.IsDirectedWalk` is sufficient for σ_ij to be a *directed*
--   walk in the LN sense but does not pin its length).  Adding the
--   minimality quantifier brings the Lean signature back into one-
--   for-one correspondence with the LN's prose "shortest directed
--   walk... of minimum length over all directed walks from v_i to
--   v_j in G".  Our concrete σ_ij = (false, .forwardE h_ab, true) IS
--   the unique shortest directed walk from false to true in G — no
--   length-0 candidate exists (would require false = true), and
--   length 1 is realised by the single forward edge `h_ab`.
--
-- *(2) Witness minimality / canonicity.*
--   Two nodes is the minimum cardinality of `V` for any counter-
--   example: the prove-side hypothesis `i < j` plus `v_i ∈ G.Sc v_j`
--   forces a non-trivial SCC component.  A one-node CDMG would
--   collapse the SCC condition to the trivial reflexive case and
--   would not admit `i < j` over a meaningful walk.  Two nodes
--   (`false = a`, `true = b`) together with the directed 2-cycle
--   `(a, b), (b, a)` is the simplest configuration that makes
--   `G.Sc true = {false, true}` non-trivial.  The directed self-
--   loop `(b, b)` is the load-bearing third edge — it is the
--   syntactic source of the new collider on `π'` (see point (3))
--   without affecting the SCC computation (the `a ↔ b` cycle
--   already establishes the SCC; the self-loop is consistent with
--   it but not needed for it).  Removing any of the three edges
--   destroys either the SCC hypothesis or the collider mechanism.
--   `L := ∅` is the simplest choice that keeps `WalkStep.bidir`
--   out of scope (every walk-step is `.forwardE` or `.backwardE`),
--   isolating the failure to the directed-edge encoding.  The
--   underlying type `Bool` (vs an abstract `Fin 2` or a sum
--   carrier) makes every `CDMG` field reduce decidably, so
--   `decide` / `rfl` / `trivial` discharge the structural fields
--   and the supporting `σ_ij_isDirected` / `π_replaceWalkCaseI_one`
--   closures without classical reasoning.
--
-- *(3) Where the LN's reasoning breaks down (load-bearing).*
--   The LN's case-(i) closing argument (`graphs.tex` ~line 1635,
--   directly after `\label{lem:replace_walk}`) reads: "By
--   assumption v_j is either a fork or a right chain (or the right
--   endnode) on π that is C-σ-open.  Since the same blocking
--   criteria apply to v_j on π' it remains C-σ-open on π'."
--   Translation: the LN's pictorial classification of v_j as a
--   fork / right chain reads off only the RIGHT-outgoing step `a_j`
--   (its `tuh` orientation puts a tail at v_j) and concludes
--   non-collider-ness from that.  Since the LN's replacement edits
--   only `a_0, …, a_{j-1}`, leaving `a_j` syntactically unchanged,
--   the LN claims v_j's non-collider status carries to π'.  The
--   follow-up sentence "the new directed path v_i → ⋯ → v_j in
--   π' is C-σ-open at v_i because all nodes in between lie in the
--   same strongly connected component Sc^G(v_i)" only addresses
--   the *interior* of the new directed path, never re-examining
--   the *boundary* mark at v_j.
--
--   Under the canonical Lean encoding, `Walk.IsCollider π 1`
--   reduces to the CONJUNCTION `s₀.IsInto v_j ∧ s₁.IsInto v_j`
--   where `s₀` is the left-incoming step (at index 0 on `π`) and
--   `s₁` is the right-outgoing step (at index 1).  Both incident
--   steps are examined.  The LN's "same blocking criteria apply"
--   claim is correct for `s₁` (`a_j`, unchanged across the
--   replacement) but silently relies on `s₀` (= `a_{j-1}`)
--   contributing NO arrowhead at v_j on π — a property which the
--   LN's pictorial classification does not record, and which the
--   replacement actively destroys.  Concretely on the counter-
--   example, with `v_j = true`:
--     - On `π`, position `j = 1`: `s₀ = .backwardE h_ba` of type
--       `WalkStep G false true` (so `u = false`, `v = true`).
--       `IsInto true` fires the `w = u` disjunct, evaluating
--       `true = false = False`; the `L = ∅` disjunct also fails.
--       So `s₀.IsInto true = False`.  `s₁ = .forwardE h_bb` of
--       type `WalkStep G true true` (`u = v = true`).  `IsInto
--       true` fires the `w = v` disjunct, evaluating `true = true
--       = True`.  So `s₁.IsInto true = True`.  Collider check
--       `= False ∧ True = False` — non-collider on `π`.
--     - On `π'`, position `j = 1`: `s₀' = .forwardE h_ab` (the
--       last edge of the new shortest directed path, type
--       `WalkStep G false true`).  `IsInto true` fires the `w = v`
--       disjunct, `True`.  `s₁' = .forwardE h_bb` inherited
--       verbatim, still `True`.  Collider check `= True ∧ True =
--       True` — COLLIDER on `π'`.
--   The right-outgoing self-loop's arrowhead at `v_j` was already
--   present in BOTH `π` and `π'` (a direct consequence of
--   `self_loop_makes_tuh_and_hut_simultaneously_true`: the type
--   indices `(b, b)` make `IsInto true` fire on the `w = v`
--   disjunct regardless of `.forwardE` vs `.backwardE` tag).  On
--   `π`, that arrowhead was compensated by the left-incoming
--   `.backwardE h_ba`'s failure to contribute (its head sits at
--   `u = false`, not at `v_j = true`).  After the replacement,
--   the new left-incoming `.forwardE h_ab` adds a SECOND
--   arrowhead at `v_j` and the conjunction flips `True`.  Since
--   `v_j = true ∉ G.AncSet ∅ = ∅`, the new collider blocks `π'`
--   at position 1, contradicting the LN's conclusion.
--
-- *(4) Cross-references to the registered subtleties.*
--   See `leanification/working_subtlety_register.json`:
--     - `self_loop_makes_tuh_and_hut_simultaneously_true`
--       (observed_by_ref: `def_3_15`, chapter-wide).  Root cause:
--       `WalkStep.IsInto w` reads the head-at-`w` mark via type-
--       index equality (`w = u` for the head end of `.backwardE`,
--       `w = v` for the head end of `.forwardE`, or the `L`-
--       disjunct for `.bidir`), so a self-loop with `u = v` fires
--       the predicate on the `w = v` disjunct independent of the
--       constructor tag.
--     - `claim_3_27_case_i_fails_for_self_loops` (observed_by_ref:
--       `claim_3_27`, row-level, registered earlier in this run).
--       Consumer-side propagation: documents the case-(i) failure
--       mode of `claim_3_27`, records the concrete counter-example
--       (the one realised in this file), AND lays out three
--       remediation options — (1) tighten case (i)'s trigger via
--       `addition_to_the_LN` to exclude `v_{j+1} = v_j`, re-
--       routing self-loops at slot `j` into case (ii); (2) accept
--       the disprove verdict and prove only the negation under the
--       canonical encoding; (3) refactor `def_3_15` /
--       `WalkStep.IsInto` so self-loops contribute exactly one
--       arrowhead.  This file realises option (2).
--
-- *(5) Case (i) is the active failure trigger, not case (ii).*
--   The prove-side existential has two direction-witness conjuncts:
--     `(π.replaceWalkCaseI j → σ_ij.IsDirectedWalk)` (case (i)),
--     `(¬ π.replaceWalkCaseI j → σ_ij.reverse.IsDirectedWalk)`
--                                                  (case (ii)).
--   For the chosen `π`, the step at position `j = 1` is
--   `.forwardE h_bb`, so `π.replaceWalkCaseI 1 = True` (see
--   `π_replaceWalkCaseI_one` above) — case (i) is the firing
--   branch.  The case-(ii) implication discharges vacuously via
--   `(fun hno => absurd π_replaceWalkCaseI_one hno)`; no case-(ii)
--   `σ_ij.reverse.IsDirectedWalk` witness needs to be built.  A
--   symmetric counter-example aimed at case (ii) would mirror this
--   construction with a `.backwardE h_bb` self-loop step at slot
--   `j` (encoding the self-loop traversal backward) and a case-
--   (ii) reverse-directed replacement; the two would be
--   `Walk.reverse`-conjugate.  Building both is unnecessary — the
--   prove-side claim is universally quantified, so a single
--   concrete failing instance suffices to refute it.  Case (i) is
--   the cleaner direction because the LN's "shortest directed
--   path v_i → ⋯ → v_j" reads forward and lines up with
--   `WalkStep.forwardE`'s default orientation: the case-(i)
--   collider mechanism is directly readable in the Lean term as
--   `π'.IsCollider 1 = (.forwardE h_ab).IsInto true ∧
--   (.forwardE h_bb).IsInto true`, discharged by
--   `π'_isCollider_one` above.
--
-- *(6) Cross-reference to the prove-side `unmistake` flip-back.*
--   `Section3_3/LabelRoman.lean` holds the positive theorem
--   signature with a `:= by sorry` placeholder, intentionally left
--   intact for the manager's `unmistake` flip-back path.  If the
--   manager flips back — for example because the orchestrator
--   chooses remediation option (1) of
--   `claim_3_27_case_i_fails_for_self_loops` (tighten case (i)'s
--   trigger via `addition_to_the_LN` to exclude `v_{j+1} = v_j`,
--   re-routing self-loops at slot `j` into case (ii) where they
--   are absorbed without introducing a new collider) and re-routes
--   `claim_3_27` to the prove path under the tightened spec —
--   this disproof file remains as historical documentation but is
--   no longer aggregated into `Chapter3_GraphTheory.lean`.  The
--   `sorry` warning emitted by `lake build` on the prove-side file
--   is expected during the disprove flow; the row's
--   `main_lean_file` is re-pointed at `LabelRomanDisproof.lean` at
--   cleanup time.
-- claim_3_27 -- start statement
theorem not_replace_walk :
    ∃ (Node : Type) (_inst : DecidableEq Node) (G : CDMG Node)
      (C : Set Node) (hC : C ⊆ ↑G.J ∪ ↑G.V) (u w : Node)
      (π : Walk G u w) (hπ : π.IsSigmaOpenGiven C hC)
      (i j : ℕ) (hij : i < j) (hjn : j ≤ π.length)
      (v_i v_j : Node)
      (h_get_i : π.vertices[i]? = some v_i)
      (h_get_j : π.vertices[j]? = some v_j)
      (h_Sc : v_i ∈ G.Sc v_j)
      (σ_ij : Walk G v_i v_j) (π' : Walk G u w),
      (π.replaceWalkCaseI j →
         σ_ij.IsDirectedWalk ∧
         (∀ τ : Walk G v_i v_j, τ.IsDirectedWalk → σ_ij.length ≤ τ.length)) ∧
      (¬ π.replaceWalkCaseI j →
         σ_ij.reverse.IsDirectedWalk ∧
         (∀ τ : Walk G v_j v_i, τ.IsDirectedWalk → σ_ij.reverse.length ≤ τ.length)) ∧
      (∀ x ∈ σ_ij.vertices, x ∈ G.Sc v_j) ∧
      π'.vertices = (π.vertices.take (i + 1)).dropLast ++ σ_ij.vertices ++
          π.vertices.drop (j + 1) ∧
      ¬ π'.IsSigmaOpenGiven C hC
-- claim_3_27 -- end statement
  := by
    refine ⟨Bool, inferInstance, G, ∅, Set.empty_subset _, false, true, π,
            π_isSigmaOpen (Set.empty_subset _), 0, 1, Nat.zero_lt_one,
            (by decide : 1 ≤ π.length), false, true, rfl, rfl, Sc_a_b,
            σ_ij, π',
            ?hCaseI,
            (fun hno => absurd π_replaceWalkCaseI_one hno),
            ?hP3, rfl, ?hP5⟩
    case hCaseI =>
      -- Case (i) fires (`π.replaceWalkCaseI 1` holds via the
      -- `.forwardE h_bb` self-loop step at position 1 on `π`).  The
      -- conjunction has two parts:
      --   (a) `σ_ij.IsDirectedWalk`              — `σ_ij_isDirected`;
      --   (b) `∀ τ, τ.IsDirectedWalk → σ_ij.length ≤ τ.length`
      --                                          — discharged below.
      -- For (b): `σ_ij.length = 1` (a single `.forwardE` cons cell),
      -- so we need `1 ≤ τ.length` for any directed walk
      -- `τ : Walk G false true`.  A length-0 walk would be `Walk.nil
      -- v hv` of type `Walk G v v`, which would force `v = false` and
      -- `v = true` — impossible by `Bool` constructor injectivity.
      -- Lean's index unifier eliminates the `.nil` branch of the
      -- `match` automatically; only the `.cons _ _ p` branch survives,
      -- and its length is `p.length + 1 ≥ 1`.
      intro _
      refine ⟨σ_ij_isDirected, ?_⟩
      intro τ _hτ
      match τ with
      | .cons _ _ p =>
          change σ_ij.length ≤ p.length + 1
          change (1 : ℕ) ≤ p.length + 1
          exact Nat.succ_le_succ (Nat.zero_le _)
    case hP3 =>
      intro x hx
      -- σ_ij.vertices = [false, true]; split on x = false vs x = true.
      rcases List.mem_cons.mp hx with rfl | hx2
      · exact Sc_a_b
      · rcases List.mem_cons.mp hx2 with rfl | hx3
        · exact Sc_b_b
        · cases hx3
    case hP5 =>
      intro hopen
      obtain ⟨hcol, _⟩ := hopen
      have hin : true ∈ G.AncSet (∅ : Set Bool) :=
        hcol 1 true π'_vertices_one π'_isCollider_one
      -- `G.AncSet ∅ = ⋃ v ∈ ∅, G.Anc v = ∅`, so `true ∈ ∅` is False.
      simp [CDMG.AncSet] at hin

end claim_3_27_disproof

end CDMG

end Causality
