import Chapter3_GraphTheory.Section3_1.CDMG
import Chapter3_GraphTheory.Section3_1.CDMGTypes
import Chapter3_GraphTheory.Section3_2.HardInterventionOn
import Chapter3_GraphTheory.Section3_2.NodeSplittingOn
import Chapter3_GraphTheory.Section3_2.NodeSplittingHard
import Chapter3_GraphTheory.Section3_2.MarginalizationAK
import Chapter3_GraphTheory.Section3_2.TwoDisjointNode

-- The proof body uses `show` extensively to make definitional rewrites
-- explicit at the reader's level (rather than `change`, which the style
-- linter prefers — but where every `show` here is followed by a tactic
-- consuming the surfaced goal, so `show` reads more naturally).  The
-- linter is silenced file-wide to keep the build noise-free; semantics
-- are unchanged.
set_option linter.style.show false

namespace Causality

/-!
# Marginalizing out the output part of splitted nodes equals hard intervention (`claim_3_19`)

This file formalises the LN lemma `claim_3_19`
(`\label{marginalizing-out-the-output-part-of-splitted-nodes-equals-hard-intervention}`
in `graphs.tex`): for any CDMG `G = (J, V, E, L)` and any subset
`W ⊆ V` of output nodes, the CDMG obtained by first node-splitting on
`W` (SWIG, `def_3_12` `nodeSplittingHard`) and then marginalising out
the output-side copies `W^o` (`def_3_14` `marginalize`) is the same
CDMG as the hard-intervention `G_{doit(W)}` (`def_3_10`
`hardInterventionOn`):
`G_{doit(W)} ≅ (G_{swig(W)})^{∖ W^o}, w ↦ w^i`.

The authoritative spec is the rewritten canonical tex statement at
`leanification/Chapter3_GraphTheory/Section3_2/tex/`
`claim_3_19_statement_MarginalizingOutThe.tex`, verified equivalent
to the LN block.  `addition_to_the_LN` is empty for this row.  The
rewrite spells the LN's literal one-clause map "`w ↦ w^i`" out as the
full three-case bijection
`φ : G_{doit(W)} → (G_{swig(W)})^{∖ W^o}` that is the identity on
`J`, the identity on `V ∖ W`, and `w ↦ w^i` on `W` (per the LN-critic
working-phase subtlety `isomorphism_map_unspecified_outside_W`,
made explicit by the rewrite).

## Carrier-mismatch wrinkle (the load-bearing Lean-shape decision)

The LHS `G.hardInterventionOn W _` lives in `CDMG Node` (hard
intervention preserves the carrier).  The RHS
`(G.nodeSplittingHard hG W hW).marginalize (W.image .copy0) _` lives
in `CDMG (SplitNode Node)`: `nodeSplittingHard` (`def_3_12`) lifts
the carrier from `Node` to `SplitNode Node`, and `marginalize`
(`def_3_14`) preserves the (lifted) carrier.  `Node` and
`SplitNode Node` are not Lean-equal as types, so a literal `=`
between the two CDMGs is not type-correct.  The LN's "$\cong$" is
rendered via `claim_3_7`'s `eqViaNodeMap` predicate, with the
bijection function `toCopy1 W : Node → SplitNode Node`
(`def_3_11` `NodeSplittingOn`) realising the LN's three-case `φ`
literally:
* `toCopy1 W v = .unsplit v` for `v ∉ W` (i.e.\ `v ∈ J ∪ (V ∖ W)`),
  which is the LN's "identity on `J ∪ (V ∖ W)`" branch under the
  carrier-lift `Node ↪ SplitNode Node`;
* `toCopy1 W w = .copy1 w` for `w ∈ W`, which is the LN's
  "`w ↦ w^i`" branch under the SWIG-side reading
  `.copy1 ↔ ^i` (the input-copy convention fixed by `def_3_12`).

Same paradigm as `claim_3_15` (`AddingInterventionNodesSwig`) and
`claim_3_7` (`TwoDisjointNode`); the choice of operand order on
`eqViaNodeMap` follows the LN's explicitly-stated direction
`φ : LHS → RHS` (see the Design choice block on the theorem for the
contrast with `claim_3_15`, which has no LN-specified direction).

The body is filled in by `prove_claim_in_lean` (Manager B), following
the to-be-written tex proof at
`tex/claim_3_19_proof_MarginalizingOutThe.tex`.
-/

namespace CDMG

-- ## Design choice — statement context
--
-- *`Node : Type*` with `[DecidableEq Node]`.*  Inherited from
--   `def_3_1` (`CDMG.lean`), `def_3_10` (`HardInterventionOn.lean`),
--   `def_3_11` (`NodeSplittingOn.lean` — the `SplitNode` inductive
--   and the `toCopy1` helper), `def_3_12` (`NodeSplittingHard.lean`)
--   and `def_3_14` (`MarginalizationAK.lean`).  Load-bearing because
--   the signature references `CDMG Node`, `CDMG (SplitNode Node)`,
--   `Finset.image SplitNode.copy0`, `toCopy1 W`, and the four
--   operators (`hardInterventionOn`, `nodeSplittingHard`,
--   `marginalize`, and `eqViaNodeMap` from `claim_3_7`'s
--   `TwoDisjointNode.lean`), each of which carries a `[DecidableEq]`
--   constraint into its return type's `CDMG` structure.  Stronger
--   instances (`Fintype`, `LinearOrder`) are not needed at the
--   statement level and are deferred to the proof body's use sites.
-- claim_3_19 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- claim_3_19 --- end helper

-- ## Helper — `W ⊆ G.J ∪ G.V` from `W ⊆ G.V`
--
-- Used once in the statement signature: the LHS
-- `G.hardInterventionOn W ?_` requires
-- `?_ : W ⊆ G.J ∪ G.V` (per `def_3_10`'s `hardInterventionOn`
-- signature, which admits any `W ⊆ G.J ∪ G.V`), while the LN's
-- standing hypothesis on this row only supplies `W ⊆ G.V`.  The
-- transport is the one-liner "`G.V ⊆ G.J ∪ G.V`" composed with
-- the standing `hW`.
--
-- ## Design choice
--
-- *Stand-alone helper, wrapped with three-dash markers — litmus test
--   for marker wrapping returns YES.*  The main theorem signature
--   reads `G.hardInterventionOn W (subset_J_union_V_of_subset_V hW)`;
--   without the named term, the wrapped main theorem head does not
--   type-check.  Mirrors the helper pattern in the sibling
--   `claim_3_15` (`AddingInterventionNodesSwig.lean`) and
--   `claim_3_18` (`MarginalizationAndIntervention.lean`).
--
-- *Implicit `G`, `W`; explicit `hW`.*  At the call site
--   `subset_J_union_V_of_subset_V hW`, the implicit `G` and `W` are
--   synthesised from the goal type, and the call reads left-to-right
--   as "transport `hW`".
--
-- *Term-mode one-liner via `Finset.mem_union_right`, not a tactic
--   proof.*  The conclusion is a direct restatement of "the right
--   summand of a union contains every element of itself"; a
--   `by`-block would add tactic-state noise for zero readability gain.
-- claim_3_19 --- start helper
private lemma subset_J_union_V_of_subset_V {G : CDMG Node} {W : Finset Node}
    (hW : W ⊆ G.V) : W ⊆ G.J ∪ G.V
-- claim_3_19 --- end helper
:= fun _ hv => Finset.mem_union_right _ (hW hv)

-- ## Helper — `W.image .copy0 ⊆ V_{swig(W)}`
--
-- Used once in the statement signature: the RHS's outer
-- `.marginalize (W.image SplitNode.copy0) ?_` (applied to the inner
-- SWIG `G.nodeSplittingHard hG W hW`) requires
-- `?_ : W.image .copy0 ⊆ (G.nodeSplittingHard hG W hW).V`.
-- By `def_3_12` item ii, the RHS-V is
-- `(G.V \ W).image .unsplit ∪ W.image .copy0`, so the conclusion is
-- "`W.image .copy0` sits in the right summand".  No disjointness
-- needed (only the structure of the union).
--
-- *`.copy0` is the "output" copy of the chapter-wide split
--   convention.*  In `def_3_11` `SplitNode` (`NodeSplittingOn.lean`)
--   and `def_3_12` `nodeSplittingHard` (`NodeSplittingHard.lean`),
--   the LN's tagged copies "$w^o$" and "$w^i$" are encoded as the
--   constructors `SplitNode.copy0` (output) and `SplitNode.copy1`
--   (input) respectively.  `W.image SplitNode.copy0 : Finset
--   (SplitNode Node)` is the literal Lean rendering of "$W^o$" — the
--   *output-side* copies of `W` that the outer `marginalize` strips
--   off.  This `.copy0 ↔ ^o` numeric/superscript correspondence is
--   genuinely arbitrary (the LN uses superscript suffixes, the
--   codebase picks `0`/`1` constructor indices) and is the kind of
--   indexing detail that bites readers later if left implicit, so the
--   helper's name and signature stay close to the LN's `W^o`
--   throughout.
--
-- ## Design choice
--
-- *Stand-alone helper, wrapped with three-dash markers — litmus test
--   returns YES.*  Without the named term the wrapped main theorem
--   head does not type-check (the inner marginalize's `hW`-argument
--   cannot be discharged inline without ballooning the rendered
--   statement).  Mirrors the
--   `image_unsplit_subset_nodeSplittingHard_carrier` helper pattern
--   in `claim_3_15` (`AddingInterventionNodesSwig.lean`).
--
-- *Implicit `G`, `hG`, `W`, `hW`.*  None of them is consumed in the
--   body; all appear only in the goal type
--   `(G.nodeSplittingHard hG W hW).V` and are inferred from the call
--   site's goal (`hG` and `hW` by proof irrelevance, `G` and `W` by
--   syntactic unification).  Matches the convention of
--   `image_unsplit_subset_extendingCDMGsWith_V` in
--   `AddingInterventionNodesSwig.lean`: when no hypothesis is
--   consumed in the body, every binder is implicit.
--
-- *`change`-then-`exact` tactic shape.*  The `change` step unfolds
--   the `(G.nodeSplittingHard hG W hW).V` projection into the
--   underlying union, after which `Finset.mem_union_right _ hx`
--   discharges the goal.  An alternative term-mode form would
--   require chasing the `where`-syntax field reduction by hand; the
--   two-line tactic form is shorter and reads identically to the
--   `claim_3_15` helper above.
-- claim_3_19 --- start helper
private lemma image_copy0_subset_nodeSplittingHard_V
    {G : CDMG Node} {hG : G.IsCADMG}
    {W : Finset Node} {hW : W ⊆ G.V} :
    W.image SplitNode.copy0 ⊆ (G.nodeSplittingHard hG W hW).V
-- claim_3_19 --- end helper
:= by
  intro x hx
  change x ∈ (G.V \ W).image SplitNode.unsplit ∪ W.image SplitNode.copy0
  exact Finset.mem_union_right _ hx

-- Proof helper: structural observation from the verified tex proof.
-- No directed edge of `(G.nodeSplittingHard hG W hW).E` has its source
-- in `W.image SplitNode.copy0`.  Reason: every such edge has the form
-- `(toCopy1 W a, toCopy0 W b)` for some `(a, b) ∈ G.E`, and the source
-- slot `toCopy1 W a` is either `.unsplit a` (when `a ∉ W`) or `.copy1 a`
-- (when `a ∈ W`) — never `.copy0 _`.  This is the lynchpin observation
-- that the proof of clauses (c) and (d) repeatedly invokes.
private lemma swig_edge_source_notMem_W_copy0
    {G : CDMG Node} (hG : G.IsCADMG) {W : Finset Node} (hW : W ⊆ G.V)
    {e : SplitNode Node × SplitNode Node}
    (he : e ∈ (G.nodeSplittingHard hG W hW).E) :
    e.1 ∉ W.image SplitNode.copy0 := by
  change e ∈ G.E.image (fun e => (toCopy1 W e.1, toCopy0 W e.2)) at he
  obtain ⟨e', _, rfl⟩ := Finset.mem_image.mp he
  intro hContra
  obtain ⟨_, _, hweq⟩ := Finset.mem_image.mp hContra
  -- `hweq : SplitNode.copy0 _ = toCopy1 W e'.1`.
  unfold toCopy1 at hweq
  split_ifs at hweq <;> contradiction

-- Proof helper: any walk's vertex list is non-empty.  Mirrors
-- `Walk.vertices_ne_nil` of `MargPreservesAncestors.lean`, kept local
-- to avoid a chapter-wide cross-import in this file (which would only
-- be needed for this single utility).
private lemma swig_vertices_ne_nil
    {G : CDMG Node} (hG : G.IsCADMG) {W : Finset Node} (hW : W ⊆ G.V) :
    ∀ {a b : SplitNode Node} (p : Walk (G.nodeSplittingHard hG W hW) a b),
      p.vertices ≠ []
  | _, _, .nil _ _ => by simp [Walk.vertices]
  | _, _, .cons _ _ _ _ => by simp [Walk.vertices]

-- Proof helper: middle vertex of a length-`≥ 2` walk `cons w a h q`
-- (with `q` non-trivial) appears in `p.vertices.tail.dropLast` — i.e.\
-- it is registered as a marginalisation intermediate.
private lemma swig_middle_vertex_mem_tail_dropLast
    {G : CDMG Node} (hG : G.IsCADMG) {W : Finset Node} (hW : W ⊆ G.V)
    {a b : SplitNode Node} (w : SplitNode Node) (c : SplitNode Node × SplitNode Node)
    (h : (G.nodeSplittingHard hG W hW).WalkStep a c w)
    {bMid : SplitNode Node} (c' : SplitNode Node × SplitNode Node)
    (h' : (G.nodeSplittingHard hG W hW).WalkStep w c' bMid)
    (r : Walk (G.nodeSplittingHard hG W hW) bMid b) :
    w ∈ (Walk.cons w c h (Walk.cons bMid c' h' r)).vertices.tail.dropLast := by
  have hr_ne : r.vertices ≠ [] := swig_vertices_ne_nil hG hW r
  -- vertices = a :: (cons bMid c' h' r).vertices = a :: w :: r.vertices
  change w ∈ (a :: w :: r.vertices).tail.dropLast
  rw [List.tail_cons]
  rw [List.dropLast_cons_of_ne_nil hr_ne]
  exact List.mem_cons.mpr (Or.inl rfl)

-- Proof helper: `swig.MarginalizationΦE (W.image .copy0) u v` iff
-- `(u, v) ∈ swig.E`.  The structural observation collapses any
-- directed walk in `swig` with intermediates in `W^o` to a single
-- edge (a walk of length `≥ 2` would have a `copy0`-tagged
-- intermediate as the source of its next edge — impossible).  The
-- converse direction constructs the trivial length-1 walk.
private lemma swig_marginalization_phi_E_W_copy0_iff
    (G : CDMG Node) (hG : G.IsCADMG) (W : Finset Node) (hW : W ⊆ G.V)
    (u v : SplitNode Node) :
    (G.nodeSplittingHard hG W hW).MarginalizationΦE
        (W.image SplitNode.copy0) u v
      ↔ (u, v) ∈ (G.nodeSplittingHard hG W hW).E := by
  constructor
  · rintro ⟨p, hp_dir, hp_len, hp_inter⟩
    cases p with
    | nil v hv =>
      simp [Walk.length] at hp_len
    | cons w a h q =>
      simp only [Walk.IsDirectedWalk] at hp_dir
      obtain ⟨ha_eq, ha_E, hq_dir⟩ := hp_dir
      cases q with
      | nil v' hv' =>
        subst ha_eq
        exact ha_E
      | cons w' a' h' r =>
        simp only [Walk.IsDirectedWalk] at hq_dir
        obtain ⟨ha'_eq, ha'_E, _⟩ := hq_dir
        have h_w_mem : w ∈ W.image SplitNode.copy0 :=
          hp_inter w (swig_middle_vertex_mem_tail_dropLast hG hW w a h a' h' r)
        have h_a'_in : (w, w') ∈ (G.nodeSplittingHard hG W hW).E := by
          rw [← ha'_eq]; exact ha'_E
        exact (swig_edge_source_notMem_W_copy0 hG hW h_a'_in h_w_mem).elim
  · intro h_edge
    have hv_in : v ∈ G.nodeSplittingHard hG W hW := by
      show v ∈ (G.nodeSplittingHard hG W hW).J ∪ (G.nodeSplittingHard hG W hW).V
      refine Finset.mem_union_right _ ?_
      exact ((G.nodeSplittingHard hG W hW).hE_subset h_edge).2
    refine ⟨Walk.cons v (u, v) (Or.inl ⟨rfl, Or.inl h_edge⟩) (Walk.nil v hv_in),
      ?_, ?_, ?_⟩
    · exact ⟨rfl, h_edge, trivial⟩
    · show 0 + 1 ≥ 1; omega
    · intro x hx
      simp [Walk.vertices, List.tail] at hx

-- Proof helper: q.IsBifurcationWithSplit i implies q is non-trivial (cons).
private lemma swig_bif_with_split_cons_form
    {G : CDMG Node} (hG : G.IsCADMG) {W : Finset Node} (hW : W ⊆ G.V) :
    ∀ {a b : SplitNode Node} (q : Walk (G.nodeSplittingHard hG W hW) a b) (i : ℕ),
      q.IsBifurcationWithSplit i →
      ∃ (mid : SplitNode Node) (c : SplitNode Node × SplitNode Node)
        (h : (G.nodeSplittingHard hG W hW).WalkStep a c mid)
        (r : Walk (G.nodeSplittingHard hG W hW) mid b),
        q = Walk.cons mid c h r
  | _, _, .nil _ _, _, hSpl => by simp only [Walk.IsBifurcationWithSplit] at hSpl
  | _, _, .cons mid c h r, _, _ => ⟨mid, c, h, r, rfl⟩

-- Proof helper: `swig.MarginalizationΦL (W.image .copy0) u v` iff
-- `(u, v) ∈ swig.L`.  Bifurcation walks in `swig` with intermediates
-- in `W^o` collapse to the `n = 1` (single bidirected edge) case for
-- the same structural reason: any intermediate in `W^o` would be the
-- source of a left-arm / hinge / right-arm directed edge.
private lemma swig_marginalization_phi_L_W_copy0_iff
    (G : CDMG Node) (hG : G.IsCADMG) (W : Finset Node) (hW : W ⊆ G.V)
    (u v : SplitNode Node) :
    (G.nodeSplittingHard hG W hW).MarginalizationΦL
        (W.image SplitNode.copy0) u v
      ↔ (u, v) ∈ (G.nodeSplittingHard hG W hW).L := by
  -- Inner helper: a bifurcation-with-split walk through `W^o` reduces
  -- to a direct bidirected edge.
  have bifSplitAux :
      ∀ {a b : SplitNode Node} (i : ℕ)
        (p : Walk (G.nodeSplittingHard hG W hW) a b),
        p.IsBifurcationWithSplit i →
        (∀ x ∈ p.vertices.tail.dropLast, x ∈ W.image SplitNode.copy0) →
        (a, b) ∈ (G.nodeSplittingHard hG W hW).L := by
    intro a b i
    induction i generalizing a b with
    | zero =>
      intro p hSpl hInter
      cases p with
      | nil v hv =>
        simp only [Walk.IsBifurcationWithSplit] at hSpl
      | cons w c h q =>
        cases q with
        | nil v' hv' =>
          simp only [Walk.IsBifurcationWithSplit] at hSpl
          obtain ⟨hc_eq, hc_L⟩ := hSpl
          rw [hc_eq] at hc_L
          exact hc_L
        | cons w' c' h' r =>
          simp only [Walk.IsBifurcationWithSplit] at hSpl
          obtain ⟨_, hq_dir⟩ := hSpl
          simp only [Walk.IsDirectedWalk] at hq_dir
          obtain ⟨hc'_eq, hc'_E, _⟩ := hq_dir
          have h_w_mem : w ∈ W.image SplitNode.copy0 :=
            hInter w (swig_middle_vertex_mem_tail_dropLast hG hW w c h c' h' r)
          have h_c'_in : (w, w') ∈ (G.nodeSplittingHard hG W hW).E := by
            rw [← hc'_eq]; exact hc'_E
          exact (swig_edge_source_notMem_W_copy0 hG hW h_c'_in h_w_mem).elim
    | succ k ih =>
      intro p hSpl hInter
      cases p with
      | nil v hv =>
        simp only [Walk.IsBifurcationWithSplit] at hSpl
      | cons w c h q =>
        simp only [Walk.IsBifurcationWithSplit] at hSpl
        obtain ⟨hc_eq, hc_E, hRec⟩ := hSpl
        -- `(w, a) ∈ swig.E` from the first left-arm edge.
        have h_c_in : (w, a) ∈ (G.nodeSplittingHard hG W hW).E := by
          rw [← hc_eq]; exact hc_E
        -- `w` is the first intermediate of the larger walk via swig_middle_vertex.
        -- q must be cons (since IsBifurcationWithSplit on nil is False).
        obtain ⟨wMid, c', h', r, hq_eq⟩ :=
          swig_bif_with_split_cons_form hG hW q k hRec
        have h_w_mem : w ∈ W.image SplitNode.copy0 := by
          apply hInter
          rw [hq_eq]
          exact swig_middle_vertex_mem_tail_dropLast hG hW w c h c' h' r
        exact (swig_edge_source_notMem_W_copy0 hG hW h_c_in h_w_mem).elim
  constructor
  · rintro (⟨p, hp_bif, hp_inter⟩ | ⟨p, hp_bif, hp_inter⟩)
    · obtain ⟨_, _, _, i, hi⟩ := hp_bif
      exact bifSplitAux i p hi hp_inter
    · obtain ⟨_, _, _, i, hi⟩ := hp_bif
      exact (G.nodeSplittingHard hG W hW).hL_symm (bifSplitAux i p hi hp_inter)
  · intro h_edge
    -- Build the length-1 bifurcation walk: cons v (u, v) ⟨Or.inl ⟨rfl, Or.inr h_edge⟩⟩ (nil v _).
    have hv_in : v ∈ G.nodeSplittingHard hG W hW := by
      show v ∈ (G.nodeSplittingHard hG W hW).J ∪ (G.nodeSplittingHard hG W hW).V
      refine Finset.mem_union_right _ ?_
      exact ((G.nodeSplittingHard hG W hW).hL_subset h_edge).2
    have hu_ne_v : u ≠ v := (G.nodeSplittingHard hG W hW).hL_irrefl h_edge
    refine Or.inl ⟨Walk.cons v (u, v) (Or.inl ⟨rfl, Or.inr h_edge⟩) (Walk.nil v hv_in),
      ?_, ?_⟩
    · refine ⟨hu_ne_v, ?_, ?_, 0, ⟨rfl, h_edge⟩⟩
      · -- u ∉ p.vertices.tail = u ∉ [v]
        simp [Walk.vertices]
        intro h_eq
        exact hu_ne_v h_eq
      · -- v ∉ p.vertices.dropLast = v ∉ [u]
        simp [Walk.vertices]
        intro h_eq
        exact hu_ne_v h_eq.symm
    · intro x hx
      simp [Walk.vertices, List.tail] at hx

-- ref: claim_3_19
--
-- For any CDMG `G : CDMG Node` and any subset `W ⊆ G.V` of output
-- nodes, the LN's displayed equivalence
--   `G_{doit(W)} ≅ (G_{swig(W)})^{∖ W^o}, w ↦ w^i`
-- is rendered (per the rewritten tex's "Distinct carriers and the
-- canonical relabelling identifying them" paragraph, paralleling
-- `claim_3_15`) as
-- `eqViaNodeMap LHS RHS (toCopy1 W)`: the four `Finset` data fields
-- of the LHS `G.hardInterventionOn W _`, after applying
-- `toCopy1 W : Node → SplitNode Node` field-wise, coincide with the
-- four data fields of the RHS
-- `(G.nodeSplittingHard hG W hW).marginalize (W.image .copy0) _`.
--
-- The `toCopy1 W` map is the literal Lean realisation of the LN's
-- three-case bijection `φ` from the rewritten canonical statement:
-- on `J ∪ (V ∖ W)` it returns `.unsplit v` (the LN's identity branch
-- under the `Node ↪ SplitNode Node` carrier-lift); on `W` it returns
-- `.copy1 w` (the LN's "`w ↦ w^i`" branch under the SWIG-side
-- reading `.copy1 ↔ ^i` fixed by `def_3_12`).  Because `toCopy1 W`
-- is total on `Node`, the LHS's input-node carrier `J ∪ W` and
-- output-node carrier `V ∖ W` are each lifted to the RHS in a single
-- pass — no separate case-split on the four (a)–(d) clauses of the
-- rewritten canonical statement is needed at the statement level
-- (the conjunctive unpacking into per-field bijection / edge-
-- preservation statements is deferred to the proof per the
-- rewritten tex's closing remark).
/-
LN tex (rewritten canonical statement for `claim_3_19`, in essence):

  Let `G = (J, V, E, L)` be a CDMG and `W ⊆ V`.  Then there is a
  CDMG-isomorphism `φ : G_{doit(W)} → (G_{swig(W)})^{∖ W^o}`
  defined by
    φ(v) := v          if v ∈ J,
    φ(v) := v          if v ∈ V ∖ W,
    φ(w) := w^i        if w ∈ W,
  whose four-clause unpacking states:
    (a) φ maps input nodes to input nodes;
    (b) φ maps output nodes to output nodes;
    (c) φ preserves directed edges (iff);
    (d) φ preserves bidirected edges (iff).

LN block (verbatim, for backup):

  Let `G = (J, V, E, L)` be a CDMG and `W ⊆ V` a subset of output
  nodes from `G`.  Then the CDMG that arises by first splitting the
  nodes on `W` and then marginalizing out the nodes from `W^o` can
  be identified with the CDMG that arises by hard intervention on
  `W`:
    `G_{doit(W)} ≅ (G_{swig(W)})^{∖ W^o}, w ↦ w^i`.
-/
-- ## Design choice
--
-- *`eqViaNodeMap` (carrier-relabelling equality), NOT literal `=` of
--   CDMGs.*  The LHS `G.hardInterventionOn W _` lives in `CDMG Node`;
--   the RHS `(G.nodeSplittingHard hG W hW).marginalize _ _` lives
--   in `CDMG (SplitNode Node)`.  These two carriers are not
--   Lean-equal as types, so a literal `LHS = RHS` is not
--   type-correct.  The LN's "$\cong$" is implicitly modulo the
--   canonical bijection `φ : Node → SplitNode Node` realised by
--   `toCopy1 W`; we render that bijection explicitly via the
--   `eqViaNodeMap` predicate from `claim_3_7`
--   (`TwoDisjointNode.lean`), asserting componentwise equality of
--   the four `Finset` data fields under `toCopy1 W`.  Same paradigm
--   as `claim_3_15` (`AddingInterventionNodesSwig`) and `claim_3_7`
--   (`TwoDisjointNode`).  A literal-`=` form would require either
--   (i) lifting the LHS to `CDMG (SplitNode Node)` via an extra
--   `Finset.image SplitNode.unsplit` wrapper on every field, or
--   (ii) introducing quotient types — both rejected at the
--   `claim_3_7` design stage in favour of `eqViaNodeMap`.
--
-- *Operand order `eqViaNodeMap LHS RHS (toCopy1 W)` — LHS on the
--   left, RHS on the right — matching the LN's explicit
--   `φ : G_{doit(W)} → (G_{swig(W)})^{∖ W^o}` direction.*  This is a
--   deliberate departure from `claim_3_15`'s "RHS on the left"
--   convention (which puts the side being relabelled on the left).
--   The reason is that `claim_3_15`'s LN does not specify a
--   bijection direction at all (its $=$ is over isomorphic
--   iterated-tagged-sum carriers, with no canonical orientation),
--   so `claim_3_15` picks one arbitrarily.  `claim_3_19`'s LN, by
--   contrast, displays the bijection as
--   `G_{doit(W)} ≅ (G_{swig(W)})^{∖ W^o}, w ↦ w^i` —
--   with `G_{doit(W)}` (= LHS) as the *domain* of $w \mapsto w^i$
--   and `(G_{swig(W)})^{∖ W^o}` (= RHS) as the *codomain*.  In our
--   Lean signature this orientation lands as: the side whose carrier
--   `Node` is *the source of `toCopy1 W`* sits on the left of
--   `eqViaNodeMap`, and the side whose carrier `SplitNode Node` is
--   *the target* sits on the right.  Preserving the LN's
--   bijection-direction faithfully is the deciding factor; the
--   reverse direction (`eqViaNodeMap RHS LHS f`) would require a
--   partial inverse of `toCopy1 W` that is awkward to state
--   (`SplitNode Node → Node`-style relabellings collide on the
--   `.copy0` constructor which never appears in the LHS but does
--   appear in the RHS carrier).
--
-- *`toCopy1 W : Node → SplitNode Node` as the bijection.*  This is
--   the literal Lean realisation of the LN's three-case `φ`:
--     • on `J ∪ (V ∖ W)`: `toCopy1 W v = .unsplit v` (the LN's
--       "identity on `J ∪ (V ∖ W)`" branch lifts through the
--       carrier-injection `Node ↪ SplitNode Node` via the `.unsplit`
--       constructor of `def_3_11`'s `SplitNode`);
--     • on `W`: `toCopy1 W w = .copy1 w` (the LN's "`w ↦ w^i`"
--       branch under the SWIG-side reading `.copy1 ↔ ^i` fixed by
--       `def_3_12` `NodeSplittingHard`'s design block).
--   The same helper `toCopy1` is *already* used inside
--   `nodeSplittingHard`'s `E_{swig}` clause
--   `G.E.image (fun e => (toCopy1 W e.1, toCopy0 W e.2))`, so the
--   bijection here lines up with the lift used by the operator
--   itself — a reader of the rendered statement sees the same
--   `toCopy1 W` shorthand on both the operator side and the
--   relabelling side.  Defining a fresh per-row `phi : Node →
--   SplitNode Node` was rejected because (i) it would diverge from
--   the chapter-wide `toCopy1` shorthand, and (ii) the LN's "implicit
--   identity on `J ∪ (V ∖ W)`" is *exactly* what `toCopy1`'s
--   `if v ∈ W then .copy1 v else .unsplit v` definition encodes.
--
-- *`hG : G.IsCADMG` on the signature, even though the rewritten tex
--   relaxes this to a CDMG-level reading.*  `def_3_12`
--   `nodeSplittingHard` requires `hG : G.IsCADMG` as a signature
--   binder (per its LN-faithful encoding — the LN's def_3_12 opens
--   with "Let $G$ be a CADMG").  The rewritten canonical statement
--   for this row explicitly notes that "the construction is
--   well-typed at the CDMG level using only the CDMG axioms, per
--   the 'Paradigm observation' paragraph of def_3_12" and reads the
--   RHS at the CDMG level — but at the Lean level we use the
--   existing `nodeSplittingHard` operator as-defined, which carries
--   the `hG` binder.  This is a *slight strengthening* of the
--   rewritten tex's hypothesis (`hG` is required here whereas the
--   tex reads at the bare CDMG level), but it does not change the
--   semantic content of the claim: the LN's $\cong$ holds for every
--   CDMG `G` and every `W ⊆ V`, and a fortiori for every CADMG `G`.
--   Downstream consumers always have `hG` available (the SWIG is
--   only ever constructed in contexts where `G.IsCADMG` is already
--   in scope), so the strengthening is harmless in practice.
--   Dropping `hG` would require either re-defining a CDMG-level
--   SWIG operator (a chapter-wide refactor, rejected) or duplicating
--   `nodeSplittingHard`'s four field assignments inline (rejected
--   for repetition / drift risk).  Matches the
--   `(G : CDMG Node) (hG : G.IsCADMG)` binder pattern of
--   `claim_3_15` (`AddingInterventionNodesSwig`).
--
-- *Hypotheses in the order `(G) (hG) (W) (hW)`.*  `G` comes first
--   (data); `hG : G.IsCADMG` is adjacent to `G` because it is a
--   side condition on `G` itself (per `claim_3_15`'s convention);
--   `W` follows (the parameter); `hW : W ⊆ G.V` is the standard
--   "subset of output nodes" precondition of the LN's "Let `W ⊆ V`",
--   matching `def_3_12`'s argument order
--   `(G) (hG) (W) (hW)` exactly.  Dot-notation
--   `G.marginalize_swig_eq_doit hG W hW` reads left-to-right like
--   the LN.
--
-- *No separate "output-node" predicate on `W` — `hW : W ⊆ G.V`
--   carries it.*  The LN's wording "Let `W ⊆ V` be a subset of
--   output nodes from `G`" qualifies `W` as a subset of *output*
--   nodes; one could imagine a richer encoding (e.g.\ a typeclass
--   or a `W ⊆ G.outputNodes` term) capturing the "output" aspect
--   separately from the subset relation.  None is needed: in
--   `def_3_1` (`CDMG.lean`), the field `G.V` *is* — by the LN's own
--   definition (def_3_1 names `V` the output-node set) — the
--   collection of output nodes of `G`.  Consequently `W ⊆ G.V` is
--   the literal Lean rendering of "subset of output nodes", and no
--   additional hypothesis is required at the signature level.  This
--   reading is the standing chapter-wide interpretation (cf.\ every
--   row in Section 3.2 that says "let `W ⊆ V` be …" — claim_3_15,
--   claim_3_17, claim_3_18 all share this collapse), and addresses
--   the LN-critic working-phase subtlety
--   `output_node_precondition_relies_on_external_definition`
--   raised against this row.  If a downstream chapter ever
--   re-partitioned `V` into output / something-else (none does
--   through chapter 16), this collapse would need revisiting.
--
-- *`W.image SplitNode.copy0` for the LN's `W^o`.*  The Lean
--   convention from `NodeSplittingHard.lean` (`def_3_12`): the
--   `^o` superscript is realised at the type level by the
--   `.copy0` constructor of `SplitNode`, and `W^o = {w^o | w ∈ W}`
--   lifts to `W.image SplitNode.copy0 : Finset (SplitNode Node)`.
--   No alternative considered — this is the chapter-wide encoding
--   of `W^o` (cf.\ the design block on `def_3_12`'s `J' :=
--   G.J.image .unsplit ∪ W.image .copy1`, `V' := (G.V \ W).image
--   .unsplit ∪ W.image .copy0`).
--
-- *Degenerate `W = ∅` case admitted.*  The quantifiers on `G` and
--   `W` are universal; `W = ∅` reduces both sides to (the
--   `.unsplit`-image of) `G` itself, with the bijection `toCopy1 ∅`
--   collapsing to `.unsplit` on all of `Node`.  `eqViaNodeMap`
--   reduces to "the four `Finset` fields of `G` lifted under
--   `.unsplit` equal the four fields of the doubly-trivial-operation
--   RHS", which holds for every `G`.  The signature does not
--   pre-emptively exclude this case (per the rewritten tex's
--   explicit admission of `W = ∅`).
--
-- *Conjunctive unpacking deferred to the proof.*  The rewritten
--   canonical tex enumerates four clauses (a)–(d):
--     (a) `φ` maps `J_{doit(W)} = J ∪ W` to
--         `J_{(G_{swig(W)})^{∖W^o}} = J ⊍ W^i` bijectively;
--     (b) `φ` maps `V_{doit(W)} = V ∖ W` to
--         `V_{(G_{swig(W)})^{∖W^o}} = V ∖ W` bijectively (identity);
--     (c) `φ` preserves directed edges (iff);
--     (d) `φ` preserves bidirected edges (iff).
--   These four clauses unpack into the four conjuncts of
--   `eqViaNodeMap LHS RHS (toCopy1 W)`:
--     `LHS.J.image (toCopy1 W) = RHS.J  ∧  LHS.V.image (toCopy1 W) = RHS.V`
--     `∧  LHS.E.image (Prod.map …) = RHS.E  ∧  LHS.L.image (Prod.map …) = RHS.L`.
--   The four-conjunct shape of `eqViaNodeMap` mirrors the four
--   clauses (a)–(d) of the rewrite literally, with the
--   field-by-field bijection / edge-preservation reasoning deferred
--   to the proof per the rewritten tex's closing remark.
set_option maxHeartbeats 800000 in
-- claim_3_19 -- start statement
theorem marginalize_swig_eq_doit (G : CDMG Node) (hG : G.IsCADMG)
    (W : Finset Node) (hW : W ⊆ G.V) :
    eqViaNodeMap
        (G.hardInterventionOn W (subset_J_union_V_of_subset_V hW))
        ((G.nodeSplittingHard hG W hW).marginalize
            (W.image SplitNode.copy0)
            image_copy0_subset_nodeSplittingHard_V)
        (toCopy1 W)
-- claim_3_19 -- end statement
:= by
  -- We prove the four conjuncts of `eqViaNodeMap` in turn, corresponding
  -- to clauses (a) `J`, (b) `V`, (c) `E`, (d) `L` of the verified tex
  -- proof.  Clauses (a) and (b) are pure `Finset.image` chasing; clauses
  -- (c) and (d) consume the structural-observation helpers above to
  -- collapse `Φ_E` / `Φ_L` to direct single-edge membership.
  --
  -- Throughout, we use that for `v ∉ W`, `toCopy1 W v = .unsplit v`
  -- (from `def_3_11`'s `toCopy1`), and that the LHS's `G.J` and
  -- `G.V \ W` are both disjoint from `W` (`G.hJV_disj` and the literal
  -- `\\ W` respectively).
  refine ⟨?_, ?_, ?_, ?_⟩
  -- ===== Clause (a): J equality =====
  -- `LHS.J = G.J ∪ W`, `RHS.J = swig.J = G.J.image .unsplit ∪ W.image .copy1`.
  -- `(G.J ∪ W).image (toCopy1 W) = G.J.image .unsplit ∪ W.image .copy1`,
  -- because `toCopy1 W` is `.unsplit` on `G.J` (G.J disjoint from W) and
  -- `.copy1` on `W`.
  · change (G.J ∪ W).image (toCopy1 W)
        = G.J.image SplitNode.unsplit ∪ W.image SplitNode.copy1
    rw [Finset.image_union]
    have hGJ : G.J.image (toCopy1 W) = G.J.image SplitNode.unsplit := by
      refine Finset.image_congr ?_
      intro j hj
      have hjJ : j ∈ G.J := Finset.mem_coe.mp hj
      have hj_notW : j ∉ W := by
        intro hjW
        exact Finset.disjoint_left.mp G.hJV_disj hjJ (hW hjW)
      show toCopy1 W j = SplitNode.unsplit j
      unfold toCopy1
      rw [if_neg hj_notW]
    have hW1 : W.image (toCopy1 W) = W.image SplitNode.copy1 := by
      refine Finset.image_congr ?_
      intro w hw
      have hwW : w ∈ W := Finset.mem_coe.mp hw
      show toCopy1 W w = SplitNode.copy1 w
      unfold toCopy1
      rw [if_pos hwW]
    rw [hGJ, hW1]
  -- ===== Clause (b): V equality =====
  -- `LHS.V = G.V \ W`, `RHS.V = swig.V \ W^o = (G.V \ W).image .unsplit`.
  -- `(G.V \ W).image (toCopy1 W) = (G.V \ W).image .unsplit` (since for
  -- `v ∈ G.V \ W`, `v ∉ W`, so `toCopy1 W v = .unsplit v`).
  · change (G.V \ W).image (toCopy1 W)
        = ((G.V \ W).image SplitNode.unsplit ∪ W.image SplitNode.copy0)
            \ (W.image SplitNode.copy0)
    -- Reduce LHS: `(G.V \ W).image (toCopy1 W) = (G.V \ W).image .unsplit`.
    have hLHS : (G.V \ W).image (toCopy1 W) = (G.V \ W).image SplitNode.unsplit := by
      refine Finset.image_congr ?_
      intro v hv
      have hvSdiff : v ∈ G.V \ W := Finset.mem_coe.mp hv
      have hv_notW : v ∉ W := (Finset.mem_sdiff.mp hvSdiff).2
      show toCopy1 W v = SplitNode.unsplit v
      unfold toCopy1
      rw [if_neg hv_notW]
    rw [hLHS]
    -- Reduce RHS: `(A ∪ B) \ B = A` when `A` is disjoint from `B`.
    -- Here `A = (G.V \ W).image .unsplit` and `B = W.image .copy0` are
    -- type-disjoint via constructor mismatch.
    apply Finset.ext
    intro x
    constructor
    · intro hx
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_union_left _ hx, ?_⟩
      intro hx_inW
      obtain ⟨v, _, hveq⟩ := Finset.mem_image.mp hx
      obtain ⟨_, _, hweq⟩ := Finset.mem_image.mp hx_inW
      rw [← hveq] at hweq
      cases hweq
    · intro hx
      obtain ⟨hx_union, hx_notC0⟩ := Finset.mem_sdiff.mp hx
      rcases Finset.mem_union.mp hx_union with hxA | hxB
      · exact hxA
      · exact absurd hxB hx_notC0
  -- ===== Clause (c): E directed-edge equality =====
  -- `LHS.E.image (Prod.map (toCopy1 W) (toCopy1 W))` equals `RHS.E`,
  -- where RHS.E is the marginalisation-filtered edge set of swig.E.
  -- We use `swig_marginalization_phi_E_W_copy0_iff` to collapse `Φ_E`.
  · change (G.E.filter (fun e => e.2 ∉ W)).image
            (Prod.map (toCopy1 W) (toCopy1 W))
        = (((G.nodeSplittingHard hG W hW).J
              ∪ ((G.nodeSplittingHard hG W hW).V \ (W.image SplitNode.copy0)))
              ×ˢ
              ((G.nodeSplittingHard hG W hW).V \ (W.image SplitNode.copy0))).filter
            (fun e => (G.nodeSplittingHard hG W hW).MarginalizationΦE
              (W.image SplitNode.copy0) e.1 e.2)
    -- Helper: when e.2 ∉ W, toCopy0 W e.2 = toCopy1 W e.2.
    have hC0eqC1 : ∀ {x : Node}, x ∉ W → toCopy0 W x = toCopy1 W x := by
      intro x hx
      unfold toCopy0 toCopy1
      rw [if_neg hx, if_neg hx]
    apply Finset.ext
    intro pair
    constructor
    · -- (⇒) Take a lifted LHS edge; show it lies in RHS.
      intro hpair
      obtain ⟨e, he, hPM⟩ := Finset.mem_image.mp hpair
      obtain ⟨he_E, he_notW⟩ := Finset.mem_filter.mp he
      obtain ⟨he1_in, he2_V⟩ := G.hE_subset he_E
      -- pair = Prod.map ... e = (toCopy1 W e.1, toCopy1 W e.2).
      have hPM_eq : pair = (toCopy1 W e.1, toCopy1 W e.2) := by
        rw [← hPM]; rfl
      -- Build swig.E membership of `pair` itself.
      have h_swig_E : pair ∈ (G.nodeSplittingHard hG W hW).E := by
        change pair ∈ G.E.image (fun e => (toCopy1 W e.1, toCopy0 W e.2))
        refine Finset.mem_image.mpr ⟨e, he_E, ?_⟩
        rw [hPM_eq]
        rw [hC0eqC1 he_notW]
      have hSub := (G.nodeSplittingHard hG W hW).hE_subset h_swig_E
      have hpair1_notC0 : pair.1 ∉ W.image SplitNode.copy0 :=
        swig_edge_source_notMem_W_copy0 hG hW h_swig_E
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · refine Finset.mem_product.mpr ⟨?_, ?_⟩
        · -- pair.1 ∈ swig.J ∪ (swig.V \ W^o).  Case-split on hSub.1.
          rcases Finset.mem_union.mp hSub.1 with hJ | hV
          · exact Finset.mem_union_left _ hJ
          · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hV, hpair1_notC0⟩)
        · refine Finset.mem_sdiff.mpr ⟨hSub.2, ?_⟩
          -- pair.2 = toCopy1 W e.2 = .unsplit e.2 since e.2 ∉ W.
          rw [hPM_eq]
          show toCopy1 W e.2 ∉ W.image SplitNode.copy0
          unfold toCopy1
          rw [if_neg he_notW]
          intro hContra
          obtain ⟨_, _, hweq⟩ := Finset.mem_image.mp hContra
          cases hweq
      · exact (swig_marginalization_phi_E_W_copy0_iff G hG W hW _ _).mpr h_swig_E
    · -- (⇐) Take a pair from RHS; show it's the lift of an LHS edge.
      intro hpair
      obtain ⟨hProd, hPhi⟩ := Finset.mem_filter.mp hpair
      have h_swig_E : pair ∈ (G.nodeSplittingHard hG W hW).E :=
        (swig_marginalization_phi_E_W_copy0_iff G hG W hW _ _).mp hPhi
      change pair ∈ G.E.image (fun e => (toCopy1 W e.1, toCopy0 W e.2)) at h_swig_E
      obtain ⟨e, he_E, hpair_eq⟩ := Finset.mem_image.mp h_swig_E
      obtain ⟨_, hv⟩ := Finset.mem_product.mp hProd
      obtain ⟨_, hv_notC0⟩ := Finset.mem_sdiff.mp hv
      have he2_notW : e.2 ∉ W := by
        intro he2W
        apply hv_notC0
        have h2 : pair.2 = toCopy0 W e.2 := by rw [← hpair_eq]
        rw [h2]
        show toCopy0 W e.2 ∈ W.image SplitNode.copy0
        unfold toCopy0
        rw [if_pos he2W]
        exact Finset.mem_image.mpr ⟨e.2, he2W, rfl⟩
      refine Finset.mem_image.mpr ⟨e, ?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨he_E, he2_notW⟩
      · -- Prod.map (toCopy1 W) (toCopy1 W) e = pair
        show Prod.map (toCopy1 W) (toCopy1 W) e = pair
        rw [← hpair_eq]
        show (toCopy1 W e.1, toCopy1 W e.2) = (toCopy1 W e.1, toCopy0 W e.2)
        rw [hC0eqC1 he2_notW]
  -- ===== Clause (d): L bidirected-edge equality =====
  -- Mirror of clause (c) for L.
  · change (G.L.filter (fun e => e.1 ∉ W ∧ e.2 ∉ W)).image
            (Prod.map (toCopy1 W) (toCopy1 W))
        = (((G.nodeSplittingHard hG W hW).V \ (W.image SplitNode.copy0))
              ×ˢ
              ((G.nodeSplittingHard hG W hW).V \ (W.image SplitNode.copy0))).filter
            (fun e => e.1 ≠ e.2
              ∧ (G.nodeSplittingHard hG W hW).MarginalizationΦL
                  (W.image SplitNode.copy0) e.1 e.2)
    -- Helper: when x ∉ W, toCopy0 W x = toCopy1 W x = .unsplit x.
    have hC0eqC1 : ∀ {x : Node}, x ∉ W → toCopy0 W x = toCopy1 W x := by
      intro x hx
      unfold toCopy0 toCopy1
      rw [if_neg hx, if_neg hx]
    have hToCopy1_unsplit : ∀ {x : Node}, x ∉ W → toCopy1 W x = SplitNode.unsplit x := by
      intro x hx
      unfold toCopy1
      rw [if_neg hx]
    apply Finset.ext
    intro pair
    constructor
    · -- (⇒)
      intro hpair
      obtain ⟨e, he, hPM⟩ := Finset.mem_image.mp hpair
      obtain ⟨he_L, he1_notW, he2_notW⟩ := Finset.mem_filter.mp he
      obtain ⟨he1_V, he2_V⟩ := G.hL_subset he_L
      have he_ne : e.1 ≠ e.2 := G.hL_irrefl he_L
      have hPM_eq : pair = (toCopy1 W e.1, toCopy1 W e.2) := by
        rw [← hPM]; rfl
      -- Build swig.L membership of `pair`.
      have h_swig_L : pair ∈ (G.nodeSplittingHard hG W hW).L := by
        change pair ∈ G.L.image (fun e => (toCopy0 W e.1, toCopy0 W e.2))
        refine Finset.mem_image.mpr ⟨e, he_L, ?_⟩
        rw [hPM_eq]
        rw [hC0eqC1 he1_notW, hC0eqC1 he2_notW]
      have hSub := (G.nodeSplittingHard hG W hW).hL_subset h_swig_L
      refine Finset.mem_filter.mpr ⟨?_, ?_, ?_⟩
      · refine Finset.mem_product.mpr ⟨?_, ?_⟩
        · refine Finset.mem_sdiff.mpr ⟨hSub.1, ?_⟩
          rw [hPM_eq]
          show toCopy1 W e.1 ∉ W.image SplitNode.copy0
          rw [hToCopy1_unsplit he1_notW]
          intro hContra
          obtain ⟨_, _, hweq⟩ := Finset.mem_image.mp hContra
          cases hweq
        · refine Finset.mem_sdiff.mpr ⟨hSub.2, ?_⟩
          rw [hPM_eq]
          show toCopy1 W e.2 ∉ W.image SplitNode.copy0
          rw [hToCopy1_unsplit he2_notW]
          intro hContra
          obtain ⟨_, _, hweq⟩ := Finset.mem_image.mp hContra
          cases hweq
      · -- pair.1 ≠ pair.2
        rw [hPM_eq]
        show toCopy1 W e.1 ≠ toCopy1 W e.2
        rw [hToCopy1_unsplit he1_notW, hToCopy1_unsplit he2_notW]
        intro h_eq
        injection h_eq with h_inj
        exact he_ne h_inj
      · exact (swig_marginalization_phi_L_W_copy0_iff G hG W hW _ _).mpr h_swig_L
    · -- (⇐)
      intro hpair
      obtain ⟨hProd, _, hPhi⟩ := Finset.mem_filter.mp hpair
      have h_swig_L : pair ∈ (G.nodeSplittingHard hG W hW).L :=
        (swig_marginalization_phi_L_W_copy0_iff G hG W hW _ _).mp hPhi
      change pair ∈ G.L.image (fun e => (toCopy0 W e.1, toCopy0 W e.2)) at h_swig_L
      obtain ⟨e, he_L, hpair_eq⟩ := Finset.mem_image.mp h_swig_L
      obtain ⟨hu, hv⟩ := Finset.mem_product.mp hProd
      obtain ⟨_, hu_notC0⟩ := Finset.mem_sdiff.mp hu
      obtain ⟨_, hv_notC0⟩ := Finset.mem_sdiff.mp hv
      have he1_notW : e.1 ∉ W := by
        intro he1W
        apply hu_notC0
        have h1 : pair.1 = toCopy0 W e.1 := by rw [← hpair_eq]
        rw [h1]
        show toCopy0 W e.1 ∈ W.image SplitNode.copy0
        unfold toCopy0
        rw [if_pos he1W]
        exact Finset.mem_image.mpr ⟨e.1, he1W, rfl⟩
      have he2_notW : e.2 ∉ W := by
        intro he2W
        apply hv_notC0
        have h2 : pair.2 = toCopy0 W e.2 := by rw [← hpair_eq]
        rw [h2]
        show toCopy0 W e.2 ∈ W.image SplitNode.copy0
        unfold toCopy0
        rw [if_pos he2W]
        exact Finset.mem_image.mpr ⟨e.2, he2W, rfl⟩
      refine Finset.mem_image.mpr ⟨e, ?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨he_L, he1_notW, he2_notW⟩
      · show Prod.map (toCopy1 W) (toCopy1 W) e = pair
        rw [← hpair_eq]
        show (toCopy1 W e.1, toCopy1 W e.2) = (toCopy0 W e.1, toCopy0 W e.2)
        rw [hC0eqC1 he1_notW, hC0eqC1 he2_notW]

end CDMG

end Causality
