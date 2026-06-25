import Chapter3_GraphTheory.Section3_1.CDMG
import Chapter3_GraphTheory.Section3_1.CDMGNotation
import Chapter3_GraphTheory.Section3_1.Walks
import Chapter3_GraphTheory.Section3_1.FamilyRelationships
import Chapter3_GraphTheory.Section3_1.Acyclicity
import Chapter3_GraphTheory.Section3_1.TopologicalOrder
import Chapter3_GraphTheory.Section3_2.MarginalizationAK

namespace Causality

/-!
# Marginalization preserves ancestors, bifurcations, and acyclicity
(`claim_3_16`)

This file formalises the LN remark `claim_3_16`
(`MargPreservesAncestors` in `graphs.tex`, section 3.2,
`\label{rem:marg_preserves_ancestors_bifurcations_acyclicity}`):

> Marginalization preserves ancestral relations, bifurcations and
> acyclicity:
>   i.   For `v_1, v_2 ∈ G` with `v_1, v_2 ∉ W`:
>        `v_1 ∈ Anc^G(v_2) ⟺ v_1 ∈ Anc^{G^{∖W}}(v_2)`.
>   ii.  For `v_1, v_2 ∈ G ∖ W` (and, optionally, `v_3 ∈ G ∖ W`):
>        there is a bifurcation between `v_1` and `v_2` (with source
>        `v_3`) in `G` iff there is one in `G^{∖W}`.
>   iii. If `G` is acyclic then so is `G^{∖W}`, and a topological
>        order of `G` induces a topological order of `G^{∖W}` (by
>        just ignoring the nodes from `W`).

The authoritative spec is the canonical tex statement at
`leanification/Chapter3_GraphTheory/Section3_2/tex/`
`claim_3_16_statement_MargPreservesAncestors.tex`, equivalent to
the LN block plus the `addition_to_the_LN` clarifications.  The
`addition_to_the_LN` clarifies the ambiguous "(and, optionally,
`v_3 ∈ G ∖ W`)" parenthetical of item ii as **two separate
biconditionals** — once with the parenthetical clauses omitted (the
sourceless form (a)) and once with them included (the sourced form
(b)).  Sub-claim iii is unfolded into two sub-assertions: (a)
preservation of acyclicity, and (b) restriction of any topological
order of `G` to a topological order of `G^{∖W}`.

Two subtleties in the LN's wording are made explicit by the
canonical tex:

* The "(and, optionally, `v_3 ∈ G ∖ W`)" parenthetical is resolved
  by the `addition_to_the_LN` clauses (a) and (b) above: the
  literal LN asserts two biconditionals, not one.
* Under the sourceless reading, the LHS's existential over the
  source ranges over `J ∪ V` (including `W`), while the RHS's
  ranges over `J ∪ (V ∖ W)`.  The biconditional silently relies on
  `Walk.IsBifurcation` admitting the `n = 1` direct bidirected edge
  case (so that a `Y`-fork through `W` collapses to a bidirected
  edge in `G^{∖W}`); this is exactly what the chapter-init addition
  `[bifurcation_index_boundary_excludes_natural_cases]` of
  `def_3_4` `IsBifurcation` admits.

The remark bundles five sub-assertions — three primary sub-claims,
two of which split further — under one `\begin{Rem}`.
This file states each as its **own top-level theorem**:

* `marginalize_preserves_ancestors` (sub-claim i): the ancestral-
  relation biconditional.
* `marginalize_preserves_bifurcation` (sub-claim ii(a),
  *sourceless* form per `addition_to_the_LN`): the
  "exists a bifurcation between `v_1` and `v_2`" biconditional.
* `marginalize_preserves_bifurcation_with_source` (sub-claim ii(b),
  *sourced* form per `addition_to_the_LN`): the
  "exists a bifurcation between `v_1` and `v_2` with source `v_3`"
  biconditional.
* `marginalize_preserves_acyclic` (sub-claim iii(a)): preservation
  of acyclicity.
* `marginalize_restricts_topological_order` (sub-claim iii(b)):
  the same `lt : Node → Node → Prop` that is a topological order of
  `G` is also a topological order of `G^{∖W}` (the restriction is
  invisible at the type level because marginalization keeps the
  original `Node` carrier; the `∀ v ∈ G^{∖W}, …` quantification
  inside `IsTopologicalOrder` already restricts the order's
  effective domain to `J ∪ (V ∖ W)`).

The proof bodies follow the TeX proof at
`tex/claim_3_16_proof_MargPreservesAncestors.tex`.
-/

namespace CDMG

-- ## Refactor replacements — Batch 1 (declarations 0–11) + net-new helper
--
-- Each replacement below is paired with the corresponding original above
-- via the same-file `REFACTOR-BLOCK-ORIGINAL` / `REFACTOR-BLOCK-REPLACEMENT`
-- marker convention.  Identifiers are prefixed `refactor_*` so the
-- replacements coexist with the originals during the refactor window; the
-- Phase 7 cleanup script renames `refactor_<Name>` → `<Name>` globally and
-- strips the markers.
--
-- The variable line, the Walk-algebra primitives (`comp`, `length_comp`,
-- `isDirectedWalk_comp`, the two vertex-list helpers, `vertices_comp`),
-- the per-step source-membership helper (`WalkStep.source_mem`), the
-- walk-level membership lemma (`Walk.mem_of_mem_vertices`), and the three
-- directed-walk-positivity lemmas (`source_in_G_of_directedWalk_pos`,
-- `target_in_GV_of_directedWalk_pos`, `target_in_G_of_directedWalk_pos`)
-- are pure structural ports against the typed `WalkStep`
-- constructors (`.forwardE`/`.backwardE`/`.bidir`) and the new
-- 3-arg `Walk.cons` cell.  `WalkStep.source_mem` is the only
-- structural rewrite: its proof case-splits on the typed constructor
-- instead of the original `Or` disjunction, and the `.bidir` branch uses
-- `Sym2.mem_mk_left` to discharge the `Sym2.Mem`-shaped `hL_subset`
-- obligation.
--
-- The net-new helper `marginalize_L_iff` at the bottom of this
-- block is the single source of truth for the Sym2-image membership
-- dance on the marginalised CDMG's `L` field; later batches (10, 11)
-- consume it at ~8 sites where the original code peeled
-- `Finset.mem_filter` / `Finset.mem_product` directly off `marg.L`.

-- claim_3_16 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- claim_3_16 --- end helper

/-- Concatenate two walks `p : u → v` and `q : v → w` into a walk
`u → w`.  Refactor twin of `Walk.comp` against the typed
`WalkStep`; the `cons`-cell pattern shifts from
`.cons v a h p` (4 args) to `.cons v s p` (3 args), reflecting
the dropped `(a : Node × Node)` field. -/
def Walk.comp {G : CDMG Node} :
    ∀ {u v w : Node}, Walk G u v → Walk G v w → Walk G u w
  | _, _, _, .nil _ _, q => q
  | _, _, _, .cons v s p, q => .cons v s (p.comp q)

lemma Walk.length_comp {G : CDMG Node} :
    ∀ {u v w : Node} (p : Walk G u v) (q : Walk G v w),
      (p.comp q).length = p.length + q.length
  | _, _, _, .nil _ _, _ => by
      simp [Walk.comp, Walk.length]
  | _, _, _, .cons _ _ p, q => by
      simp [Walk.comp, Walk.length,
            Walk.length_comp p q,
            Nat.add_comm, Nat.add_left_comm]

/-- Concatenation preserves the directed-walk property.  Refactor port:
under the typed `WalkStep`, `IsDirectedWalk` on
`.cons _ (.forwardE _) p` reduces *directly* to `p.IsDirectedWalk`
— no conjunctive destructuring needed.  The `.backwardE` / `.bidir`
branches are vacuous because `IsDirectedWalk` returns
`False` there. -/
lemma Walk.isDirectedWalk_comp {G : CDMG Node} :
    ∀ {u v w : Node} (p : Walk G u v) (q : Walk G v w),
      p.IsDirectedWalk → q.IsDirectedWalk →
        (p.comp q).IsDirectedWalk
  | _, _, _, .nil _ _, _, _, hq => hq
  | _, _, _, .cons _ (.forwardE _) p, q, hp, hq =>
      Walk.isDirectedWalk_comp p q hp hq
  | _, _, _, .cons _ (.backwardE _) _, _, hp, _ => hp.elim
  | _, _, _, .cons _ (.bidir _) _, _, hp, _ => hp.elim

/-- A walk's vertex list is non-empty (`nil` gives `[v]`, `cons`
prepends). -/
lemma Walk.vertices_ne_nil {G : CDMG Node} :
    ∀ {u v : Node} (p : Walk G u v), p.vertices ≠ []
  | _, _, .nil _ _ => by simp [Walk.vertices]
  | _, _, .cons _ _ _ => by simp [Walk.vertices]

/-- The source of a walk is in its vertex list. -/
lemma Walk.head_mem_vertices {G : CDMG Node} :
    ∀ {u v : Node} (p : Walk G u v), u ∈ p.vertices
  | _, _, .nil _ _ => by simp [Walk.vertices]
  | _, _, .cons _ _ _ => by simp [Walk.vertices]

lemma Walk.vertices_comp {G : CDMG Node} :
    ∀ {u v w : Node} (p : Walk G u v) (q : Walk G v w),
      (p.comp q).vertices =
        p.vertices.dropLast ++ q.vertices
  | _, _, _, .nil _ _, _ => rfl
  | _, _, _, .cons _ _ p, q => by
      have hne : p.vertices ≠ [] := Walk.vertices_ne_nil p
      simp [Walk.comp, Walk.vertices,
            Walk.vertices_comp p q,
            List.dropLast_cons_of_ne_nil hne]

/-- The source vertex of a `WalkStep` lies in `G`.

Refactor port of `WalkStep.source_mem`: signature now takes the
typed step `s : WalkStep G u v` directly (no stored
ordered pair `a` plus prop witness), and the body case-splits on
the constructor instead of the original `Or` disjunction.  The
`.bidir` branch uses `Sym2.mem_mk_left u v : u ∈ s(u, v)` to
discharge the `Sym2.Mem`-shaped `hL_subset` obligation. -/
lemma WalkStep.source_mem {G : CDMG Node}
    {u v : Node} (s : WalkStep G u v) : u ∈ G := by
  change u ∈ G.J ∪ G.V
  cases s with
  | forwardE h_E => exact (G.hE_subset h_E).1
  | backwardE h_E => exact Finset.mem_union_right _ (G.hE_subset h_E).2
  | bidir h_L =>
      exact Finset.mem_union_right _ (G.hL_subset h_L (Sym2.mem_mk_left u v))

/-- Every vertex of a walk lies in the underlying CDMG. -/
lemma Walk.mem_of_mem_vertices {G : CDMG Node} :
    ∀ {u v : Node} (p : Walk G u v) {x : Node},
      x ∈ p.vertices → x ∈ G
  | _, _, .nil v hv, x, hx => by
      change x ∈ [v] at hx
      rw [List.mem_singleton] at hx
      exact hx ▸ hv
  | _, _, .cons _ s p', x, hx => by
      change x ∈ _ :: p'.vertices at hx
      rcases List.mem_cons.mp hx with rfl | h_in
      · exact WalkStep.source_mem s
      · exact Walk.mem_of_mem_vertices p' h_in

/-- The source of a non-trivial directed walk lies in `G`.

Refactor port: under the typed `WalkStep`, the cons-cell's
WalkStep tag pins the edge directly — no `obtain ⟨ha_eq, ha_E, _⟩`
destructure needed.  The `.backwardE` / `.bidir` branches are
unreachable on a directed walk (`IsDirectedWalk` returns
`False` there). -/
lemma Walk.source_in_G_of_directedWalk_pos {G : CDMG Node} :
    ∀ {u v : Node} (p : Walk G u v),
      p.IsDirectedWalk → p.length ≥ 1 → u ∈ G
  | _, _, .nil _ _, _, hlen => by
      simp [Walk.length] at hlen
  | _, _, .cons _ (.forwardE h_E) _, _, _ => (G.hE_subset h_E).1
  | _, _, .cons _ (.backwardE _) _, hp, _ => hp.elim
  | _, _, .cons _ (.bidir _) _, hp, _ => hp.elim

/-- The target of a non-trivial directed walk lies in `G.V`.

Refactor port: equation-style pattern matching peels both the
`cons`-cell and its `WalkStep` constructor simultaneously, so the
elaborator refines the `IsDirectedWalk` hypothesis to
`q.IsDirectedWalk` on the `.forwardE` branch (and to
`False` on the `.backwardE` / `.bidir` branches).  The original's
inner `match q, hq_dir, hlen0 with | .nil _ _, _, _ => ...` is
preserved verbatim. -/
lemma Walk.target_in_GV_of_directedWalk_pos {G : CDMG Node} :
    ∀ {u v : Node} (p : Walk G u v),
      p.IsDirectedWalk → p.length ≥ 1 → v ∈ G.V
  | _, _, .nil _ _, _, hlen => by simp [Walk.length] at hlen
  | _, _, .cons _ (.forwardE h_E) q, hdir, _ => by
      by_cases hq_len : q.length ≥ 1
      · exact Walk.target_in_GV_of_directedWalk_pos q hdir hq_len
      · have hlen0 : q.length = 0 := by omega
        match q, hdir, hlen0 with
        | .nil _ _, _, _ => exact (G.hE_subset h_E).2
  | _, _, .cons _ (.backwardE _) _, hdir, _ => hdir.elim
  | _, _, .cons _ (.bidir _) _, hdir, _ => hdir.elim

lemma Walk.target_in_G_of_directedWalk_pos {G : CDMG Node} :
    ∀ {u v : Node} (p : Walk G u v),
      p.IsDirectedWalk → p.length ≥ 1 → v ∈ G := by
  intro u v p hdir hlen
  exact Finset.mem_union_right _
    (Walk.target_in_GV_of_directedWalk_pos p hdir hlen)

-- ## Net-new helper: Sym2-image membership on marg.L
--
-- The marginalised CDMG's `L` field is built via
--   `(((G.V \ W) ×ˢ (G.V \ W)).filter
--      (fun e => e.1 ≠ e.2 ∧ G.MarginalizationΦL W e.1 e.2)).image
--      (fun e => s(e.1, e.2))`,
-- so membership of an unordered pair `s : Sym2 Node` in `marg.L`
-- requires unwinding three Finset-API layers (`image`, `filter`,
-- `product`).  Later batches consume this iff at ~8 sites where the
-- original code peeled the membership chain inline; centralising the
-- unwrap here keeps the consumption sites short and unambiguous about
-- the Sym2 quotient.  Each consumer obtains an ordered-pair witness
-- `e : Node × Node` together with: `e.1, e.2 ∈ G.V \ W`,
-- `e.1 ≠ e.2`, `Φ_L W e.1 e.2`, and `s = s(e.1, e.2)`.
lemma marginalize_L_iff (G : CDMG Node) (W : Finset Node) (hW : W ⊆ G.V)
    {s : Sym2 Node} :
    s ∈ (G.marginalize W hW).L ↔
      ∃ e : Node × Node,
        e.1 ∈ G.V \ W ∧ e.2 ∈ G.V \ W ∧
        e.1 ≠ e.2 ∧ G.MarginalizationΦL W e.1 e.2 ∧
        s = s(e.1, e.2) := by
  constructor
  · intro hs
    obtain ⟨e, hFilter, hEq⟩ := Finset.mem_image.mp hs
    obtain ⟨hProd, hne, hΦ⟩ := Finset.mem_filter.mp hFilter
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp hProd
    exact ⟨e, h1, h2, hne, hΦ, hEq.symm⟩
  · rintro ⟨e, h1, h2, hne, hΦ, hs⟩
    refine Finset.mem_image.mpr ⟨e, ?_, hs.symm⟩
    refine Finset.mem_filter.mpr ⟨?_, hne, hΦ⟩
    exact Finset.mem_product.mpr ⟨h1, h2⟩

-- ## Batch 2: marg-membership lemmas + lt-of-directedWalk-pos +
-- vertex-list helpers (originals 12–16).  All five are mechanical
-- ports: the J/V fields of `marginalize` are unchanged
-- (only `E`/`L` shift to their refactor encodings), so the
-- marg-membership proofs read verbatim modulo the `marginalize` →
-- `marginalize` and `CDMG` → `CDMG` substitutions.
-- `lt_of_directedWalk_pos` shifts to equation-style structural
-- recursion: the cons-cell's `WalkStep` constructor pins the
-- direction directly (no `obtain ⟨ha_eq, ha_E, _⟩` destructure),
-- and the `.backwardE` / `.bidir` branches close via `hdir.elim`
-- because `IsDirectedWalk` returns `False` there.

/-- Lift node membership from the marginalized CDMG back to `G`.
Refactor port: marg's `J`/`V` fields are unchanged (J = G.J,
V = G.V \ W), so the body reads verbatim against the new
`marginalize`. -/
lemma mem_of_mem_marginalize {G : CDMG Node} {W : Finset Node}
    {hW : W ⊆ G.V} {v : Node} (h : v ∈ G.marginalize W hW) : v ∈ G := by
  change v ∈ G.J ∪ (G.V \ W) at h
  change v ∈ G.J ∪ G.V
  rcases Finset.mem_union.mp h with hJ | hVW
  · exact Finset.mem_union_left _ hJ
  · exact Finset.mem_union_right _ (Finset.mem_sdiff.mp hVW).1

/-- A node in `G.marginalize W hW` is outside `W`
(uses `hJV_disj` to handle the `J`-disjunct).  Refactor port:
marg's `J` is unchanged and `hJV_disj` is a field on
`CDMG` with the same signature, so the body reads
verbatim. -/
lemma notW_of_mem_marginalize {G : CDMG Node} {W : Finset Node}
    (hW : W ⊆ G.V) {v : Node} (h : v ∈ G.marginalize W hW) : v ∉ W := by
  intro hv_W
  change v ∈ G.J ∪ (G.V \ W) at h
  rcases Finset.mem_union.mp h with hJ | hVW
  · have hv_V : v ∈ G.V := hW hv_W
    exact Finset.disjoint_left.mp G.hJV_disj hJ hv_V
  · exact (Finset.mem_sdiff.mp hVW).2 hv_W

/-- Along a non-trivial directed walk in `G`, parent-precedence
plus transitivity force `lt` between source and target.  Refactor
port: pattern-match on the typed `WalkStep` instead of
destructuring an `Or`-shaped `hdir`.  The `.forwardE` branch
reduces `hdir` directly to `q.IsDirectedWalk` (no
`ha_eq ▸ ha_E` rewrite needed; the edge `(x, v) ∈ G.E` is the
constructor's payload `h_edge`).  The `.backwardE` / `.bidir`
branches close via `hdir.elim` because `IsDirectedWalk`
returns `False` there.  `G.Pa` shifts to `G.Pa`
(definition unchanged modulo CDMG type). -/
lemma Walk.lt_of_directedWalk_pos {G : CDMG Node}
    {lt : Node → Node → Prop}
    (h_trans : ∀ u ∈ G, ∀ v ∈ G, ∀ w ∈ G, lt u v → lt v w → lt u w)
    (h_parent : ∀ v w, v ∈ G.Pa w → lt v w) :
    ∀ {x y : Node} (p : Walk G x y),
      p.IsDirectedWalk → p.length ≥ 1 → lt x y
  | _, _, .nil _ _, _, hlen => by simp [Walk.length] at hlen
  | x, y, .cons v (.forwardE h_edge) q, hdir, _ => by
      have hx : x ∈ G := (G.hE_subset h_edge).1
      have hv : v ∈ G := Finset.mem_union_right _ (G.hE_subset h_edge).2
      have hlt_xv : lt x v := h_parent x v ⟨hx, h_edge⟩
      by_cases hq_len : q.length ≥ 1
      · have hy : y ∈ G :=
          Walk.target_in_G_of_directedWalk_pos q hdir hq_len
        have hlt_vy : lt v y :=
          Walk.lt_of_directedWalk_pos h_trans h_parent q hdir hq_len
        exact h_trans x hx v hv y hy hlt_xv hlt_vy
      · have hlen0 : q.length = 0 := by omega
        match q, hdir, hlen0 with
        | .nil _ _, _, _ => exact hlt_xv
  | _, _, .cons _ (.backwardE _) _, hdir, _ => hdir.elim
  | _, _, .cons _ (.bidir _) _, hdir, _ => hdir.elim

/-- Every walk's vertex list factors as `source :: tail`.
Refactor port: cons pattern arity drops from 4 to 3 (no stored
ordered pair `a`). -/
lemma Walk.vertices_eq_head_cons_tail {G : CDMG Node} :
    ∀ {u v : Node} (p : Walk G u v),
      p.vertices = u :: p.vertices.tail
  | _, _, .nil _ _ => rfl
  | _, _, .cons _ _ _ => rfl

/-- The vertex list's tail of a walk of length `≥ 1` is non-empty.
Refactor port: cons pattern arity drops from 4 to 3; the tail
walk `p'` is now the third argument of `.cons`. -/
lemma Walk.tail_vertices_ne_nil_of_pos {G : CDMG Node} :
    ∀ {u v : Node} (p : Walk G u v),
      p.length ≥ 1 → p.vertices.tail ≠ []
  | _, _, .nil _ _, h => by simp [Walk.length] at h
  | _, _, .cons _ _ p', _ => Walk.vertices_ne_nil p'

-- ## Batch 3: walk expansion through the marginalised CDMG (original 17).
--
-- `expand_directed_walk_marginalize` is the refactor port of
-- `expand_directed_walk_marginalize`: lift a directed walk in
-- `G.marginalize W hW` back to a directed walk in `G`, with
-- length at least the original AND four pointwise vertex-bound clauses
-- linking the lifted walk's vertices (and their dropLast / tail /
-- tail.dropLast slices) to the marg-walk's vertices plus `W`.
--
-- Mechanical port modulo two surface shifts:
-- (i) the `cons` cell now binds `s : WalkStep G u v` (no
--     ordered-pair `a`, no Prop witness `hStep`), and the case-split on
--     the cons-cell happens at the WalkStep level via `cases s` — the
--     `.backwardE` / `.bidir` branches close via `hp_dir.elim` because
--     `IsDirectedWalk` returns `False` there;
-- (ii) the `obtain ⟨ha_eq, ha_mem, hp'_dir⟩ := hp_dir` destructure
--     collapses: under `.forwardE h_edge`, `hp_dir` is *definitionally*
--     `p'.IsDirectedWalk`, and the edge witness
--     `h_edge : (u, vMid) ∈ (G.marginalize W hW).E` is the
--     constructor's payload (no `ha_eq ▸ ha_mem` rewrite needed).
--
-- All walk-algebra helpers (`comp`, `length_comp`,
-- `isDirectedWalk_comp`, `vertices_ne_nil`,
-- `vertices_comp`, `vertices_eq_head_cons_tail`,
-- `tail_vertices_ne_nil_of_pos`) and the marg-membership
-- helper (`mem_of_mem_marginalize`) come from Batches 1–2.

/-- Lift a directed walk in the marginalized CDMG to a directed walk
in the ambient `G`, with length at least the original AND vertex
bounds linking the expansion's vertices to the marg-walk's vertices
plus `W`.  Each marg-edge expands via the `Φ_E` witness (whose
intermediates lie in `W`); the concatenation of expansions preserves
directedness and is at least as long as the marg-walk.

Four symmetric bounds are provided: on `q.vertices`, on
`q.vertices.dropLast`, on `q.vertices.tail`, and
on the interior `q.vertices.tail.dropLast`.  The latter two
are load-bearing for `claim_3_17` (`MarginalizationsCommute.lean`),
which needs to refine `p.vertices.dropLast ∨ W` to
`p.vertices.tail.dropLast ∨ W` so that the source vertex `u`
(which is *not* assumed to lie in `W` ∪ the target marg-interior
set) does not leak into the bound.

Refactor port: signature retargets `Walk` / `CDMG` / `marginalize` /
`MarginalizationΦE` / `IsDirectedWalk` / `vertices` / `length` to
the `refactor_*` analogues; body case-splits on the typed
`WalkStep` constructor at the cons cell.  Only the
`.forwardE` branch survives; `.backwardE` / `.bidir` close via
`hp_dir.elim`.  The `obtain ⟨ha_eq, ha_mem, hp'_dir⟩ := hp_dir`
destructure collapses to a direct `hp_dir : p'.IsDirectedWalk`. -/
lemma expand_directed_walk_marginalize {G : CDMG Node}
    {W : Finset Node} {hW : W ⊆ G.V} :
    ∀ {u v : Node} (p : Walk (G.marginalize W hW) u v),
      p.IsDirectedWalk →
      ∃ (q : Walk G u v),
        q.IsDirectedWalk ∧ q.length ≥ p.length ∧
        (∀ x ∈ q.vertices, x ∈ p.vertices ∨ x ∈ W) ∧
        (∀ x ∈ q.vertices.dropLast,
          x ∈ p.vertices.dropLast ∨ x ∈ W) ∧
        (∀ x ∈ q.vertices.tail,
          x ∈ p.vertices.tail ∨ x ∈ W) ∧
        (∀ x ∈ q.vertices.tail.dropLast,
          x ∈ p.vertices.tail.dropLast ∨ x ∈ W) := by
  intro u v p
  induction p with
  | nil v hv =>
      intro _
      have hv_g : v ∈ G := mem_of_mem_marginalize hv
      refine ⟨Walk.nil v hv_g, trivial,
              by simp [Walk.length],
              ?_, ?_, ?_, ?_⟩
      · intro x hx
        change x ∈ [v] at hx
        change x ∈ [v] ∨ x ∈ W
        exact Or.inl hx
      · intro x hx
        change x ∈ ([v] : List Node).dropLast at hx
        simp [List.dropLast] at hx
      · intro x hx
        change x ∈ ([v] : List Node).tail at hx
        simp [List.tail] at hx
      · intro x hx
        change x ∈ ([v] : List Node).tail.dropLast at hx
        simp [List.tail, List.dropLast] at hx
  | @cons u v_end vMid s p' ih =>
      intro hp_dir
      cases s with
      | backwardE _ => exact hp_dir.elim
      | bidir _ => exact hp_dir.elim
      | forwardE h_edge =>
          have hp'_dir : p'.IsDirectedWalk := hp_dir
          have ha_filter : (u, vMid) ∈
                ((G.J ∪ (G.V \ W)) ×ˢ (G.V \ W)).filter
                  (fun e => G.MarginalizationΦE W e.1 e.2) := h_edge
          have ha_phi : G.MarginalizationΦE W u vMid :=
            (Finset.mem_filter.mp ha_filter).2
          obtain ⟨q_edge, hq_edge_dir, hq_edge_pos, hq_edge_inter⟩ := ha_phi
          obtain ⟨q_tail, hq_tail_dir, hq_tail_len, hq_tail_sub,
                  hq_tail_drop_sub, hq_tail_tail_sub, hq_tail_inter_sub⟩ :=
            ih hp'_dir
          have hq_edge_vs :
              q_edge.vertices = u :: q_edge.vertices.tail :=
            Walk.vertices_eq_head_cons_tail q_edge
          have h_qe_tail_ne : q_edge.vertices.tail ≠ [] :=
            Walk.tail_vertices_ne_nil_of_pos q_edge hq_edge_pos
          have h_qt_vs_ne : q_tail.vertices ≠ [] :=
            Walk.vertices_ne_nil q_tail
          have hp'_vs_ne : p'.vertices ≠ [] :=
            Walk.vertices_ne_nil p'
          -- q_edge.vertices.dropLast = u :: q_edge.vertices.tail.dropLast.
          have h_qe_drop : q_edge.vertices.dropLast
              = u :: q_edge.vertices.tail.dropLast := by
            rw [hq_edge_vs]
            exact List.dropLast_cons_of_ne_nil h_qe_tail_ne
          -- q_edge.vertices.dropLast is non-empty (its head is u).
          have h_qe_drop_ne : q_edge.vertices.dropLast ≠ [] := by
            rw [h_qe_drop]; exact List.cons_ne_nil _ _
          refine ⟨q_edge.comp q_tail,
                  Walk.isDirectedWalk_comp
                    q_edge q_tail hq_edge_dir hq_tail_dir,
                  ?_, ?_, ?_, ?_, ?_⟩
          · rw [Walk.length_comp]
            change q_edge.length + q_tail.length
                ≥ p'.length + 1
            omega
          · -- (q_edge.comp q_tail).vertices ⊆ p.vertices ∪ W.
            intro x hx
            rw [Walk.vertices_comp] at hx
            change x ∈ u :: p'.vertices ∨ x ∈ W
            rcases List.mem_append.mp hx with hx_edge | hx_tail
            · rw [hq_edge_vs] at hx_edge
              rw [List.dropLast_cons_of_ne_nil h_qe_tail_ne] at hx_edge
              rcases List.mem_cons.mp hx_edge with rfl | hx_in_qe_t_d
              · exact Or.inl List.mem_cons_self
              · exact Or.inr (hq_edge_inter x hx_in_qe_t_d)
            · rcases hq_tail_sub x hx_tail with h_p' | h_w
              · exact Or.inl (List.mem_cons.mpr (Or.inr h_p'))
              · exact Or.inr h_w
          · -- (q_edge.comp q_tail).vertices.dropLast ⊆ p.vertices.dropLast ∪ W.
            intro x hx
            have h_vs_comp : (q_edge.comp q_tail).vertices
                = q_edge.vertices.dropLast ++ q_tail.vertices :=
              Walk.vertices_comp q_edge q_tail
            rw [h_vs_comp] at hx
            rw [List.dropLast_append_of_ne_nil h_qt_vs_ne] at hx
            change x ∈ (u :: p'.vertices).dropLast ∨ x ∈ W
            rw [List.dropLast_cons_of_ne_nil hp'_vs_ne]
            rcases List.mem_append.mp hx with hx_edge | hx_tail_drop
            · rw [hq_edge_vs] at hx_edge
              rw [List.dropLast_cons_of_ne_nil h_qe_tail_ne] at hx_edge
              rcases List.mem_cons.mp hx_edge with rfl | hx_in_qe_t_d
              · exact Or.inl List.mem_cons_self
              · exact Or.inr (hq_edge_inter x hx_in_qe_t_d)
            · rcases hq_tail_drop_sub x hx_tail_drop with h_p' | h_w
              · exact Or.inl (List.mem_cons.mpr (Or.inr h_p'))
              · exact Or.inr h_w
          · -- (q_edge.comp q_tail).vertices.tail ⊆ p.vertices.tail ∪ W.
            intro x hx
            have h_vs_comp : (q_edge.comp q_tail).vertices
                = q_edge.vertices.dropLast ++ q_tail.vertices :=
              Walk.vertices_comp q_edge q_tail
            rw [h_vs_comp] at hx
            rw [List.tail_append_of_ne_nil h_qe_drop_ne] at hx
            -- q_edge.vertices.dropLast.tail = q_edge.vertices.tail.dropLast.
            have h_qe_drop_tail :
                q_edge.vertices.dropLast.tail
                  = q_edge.vertices.tail.dropLast := by
              rw [h_qe_drop]; rfl
            rw [h_qe_drop_tail] at hx
            -- p.vertices.tail = p'.vertices (since p = cons u _ p').
            change x ∈ p'.vertices ∨ x ∈ W
            rcases List.mem_append.mp hx with hx_qe_inter | hx_qt
            · exact Or.inr (hq_edge_inter x hx_qe_inter)
            · rcases hq_tail_sub x hx_qt with h_p' | h_w
              · exact Or.inl h_p'
              · exact Or.inr h_w
          · -- (q_edge.comp q_tail).vertices.tail.dropLast ⊆ p.vertices.tail.dropLast ∪ W.
            intro x hx
            have h_vs_comp : (q_edge.comp q_tail).vertices
                = q_edge.vertices.dropLast ++ q_tail.vertices :=
              Walk.vertices_comp q_edge q_tail
            rw [h_vs_comp] at hx
            rw [List.tail_append_of_ne_nil h_qe_drop_ne] at hx
            rw [List.dropLast_append_of_ne_nil h_qt_vs_ne] at hx
            have h_qe_drop_tail :
                q_edge.vertices.dropLast.tail
                  = q_edge.vertices.tail.dropLast := by
              rw [h_qe_drop]; rfl
            rw [h_qe_drop_tail] at hx
            change x ∈ p'.vertices.dropLast ∨ x ∈ W
            rcases List.mem_append.mp hx with hx_qe_inter | hx_qt_drop
            · exact Or.inr (hq_edge_inter x hx_qe_inter)
            · rcases hq_tail_drop_sub x hx_qt_drop with h_p' | h_w
              · exact Or.inl h_p'
              · exact Or.inr h_w

-- ## Batch 4: walk projection from `G` to the marginalised CDMG
-- (originals 18–22).  The dual to Batch 3 — given a directed walk in
-- the ambient `G` whose endpoints both lie in the marginalisation
-- carrier, produce a directed walk in `G.marginalize W hW`
-- between the same endpoints (possibly shorter, since each marg-edge
-- absorbs an arbitrary `W`-traversal).
--
-- The five declarations port mechanically against the typed
-- `WalkStep` constructors.  Only the `find_first_non_W_directed`
-- lemma's induction step (`@cons u v_end vMid s p' ih`) requires a
-- `cases s with | forwardE h_edge | backwardE _ | bidir _ => …`
-- destructure on the WalkStep; the `.backwardE` / `.bidir` branches
-- close via `hp_dir.elim` because `IsDirectedWalk` returns
-- `False` there.  The remaining four lemmas (`project_directed_walk_aux`,
-- its wrapper, the strong variant, and its wrapper) recurse on `n`
-- (the length bound) or wrap the aux lemma — no cons-cell pattern
-- matching is needed for them.
--
-- Marg-E construction sites: `(v₁, m) ∈ (G.marginalize W hW).E`
-- reads as `Finset.mem_filter` over the same product carrier as the
-- original (the E channel is unchanged — only L moved to `Sym2`), so
-- the membership chain `Finset.mem_filter ↔ Finset.mem_product ∧ Φ_E`
-- ports verbatim modulo the `Φ_E` rename.  Marg-L is *not* touched in
-- this batch (these are directed-walk lemmas); the Sym2 dance from R2
-- does not appear here.  The walk-step construction
-- `Or.inl ⟨rfl, Or.inl h_edge_marg⟩` collapses to `.forwardE h_edge_marg`,
-- and the IsDirectedWalk witness `⟨rfl, h_edge_marg, hq_tail_dir⟩`
-- collapses to `hq_tail_dir` (the cons-level `IsDirectedWalk`
-- on `.forwardE` is *definitionally* the tail's
-- `IsDirectedWalk`).

/-- Find the first non-`W` vertex strictly after the source of a
non-trivial directed walk whose target is outside `W`, and split the
walk at that vertex.  Additionally guarantees that
`p.vertices = head.vertices.dropLast ++ tail.vertices`,
i.e.\ the split factors `p` exactly as a `Walk.comp`.

Refactor port: signature retargets `Walk` / `CDMG` / `IsDirectedWalk` /
`vertices` / `length` to the `refactor_*` analogues; body case-splits
on the typed `WalkStep` constructor at the cons cell.  Only
the `.forwardE` branch survives; `.backwardE` / `.bidir` close via
`hp_dir.elim`.  The `obtain ⟨ha_eq, ha_mem, hp'_dir⟩ := hp_dir`
destructure collapses to a direct `hp_dir : p'.IsDirectedWalk`,
and the single-edge construction
`Walk.cons vMid a hStep (Walk.nil vMid hvMid_g)` becomes
`Walk.cons vMid (.forwardE h_edge) (Walk.nil vMid hvMid_g)`. -/
lemma find_first_non_W_directed {G : CDMG Node} (W : Finset Node) :
    ∀ {u v : Node} (p : Walk G u v),
      p.IsDirectedWalk → p.length ≥ 1 → v ∉ W →
      ∃ (m : Node) (head : Walk G u m) (tail : Walk G m v),
        head.IsDirectedWalk ∧ tail.IsDirectedWalk ∧
        head.length ≥ 1 ∧ m ∉ W ∧
        (∀ x ∈ head.vertices.tail.dropLast, x ∈ W) ∧
        head.length + tail.length = p.length ∧
        p.vertices =
          head.vertices.dropLast ++ tail.vertices := by
  intro u v p
  induction p with
  | nil v hv =>
      intros _ hp_pos _
      simp [Walk.length] at hp_pos
  | @cons u v_end vMid s p' ih =>
      intros hp_dir _ hv_notW
      cases s with
      | backwardE _ => exact hp_dir.elim
      | bidir _ => exact hp_dir.elim
      | forwardE h_edge =>
          have hp'_dir : p'.IsDirectedWalk := hp_dir
          by_cases hvMid_W : vMid ∈ W
          · -- vMid ∈ W: recurse on p'
            have hp'_pos : p'.length ≥ 1 := by
              by_contra hp'_nonpos
              have hp'_zero : p'.length = 0 := by omega
              match p', hp'_zero with
              | .nil _ _, _ => exact hv_notW hvMid_W
            obtain ⟨m, head_p', tail, h_head_p'_dir, h_tail_dir, h_head_p'_pos,
                    hm_notW, h_head_p'_inter, h_lens, h_p'_eq⟩ :=
              ih hp'_dir hp'_pos hv_notW
            refine ⟨m, Walk.cons vMid (.forwardE h_edge) head_p', tail,
                    h_head_p'_dir, h_tail_dir, ?_, hm_notW,
                    ?_, ?_, ?_⟩
            · change head_p'.length + 1 ≥ 1; omega
            · -- (cons u (.forwardE _) head_p').vertices.tail.dropLast ⊆ W
              intro x hx
              change x ∈ head_p'.vertices.dropLast at hx
              rw [Walk.vertices_eq_head_cons_tail head_p'] at hx
              have h_tail_ne : head_p'.vertices.tail ≠ [] :=
                Walk.tail_vertices_ne_nil_of_pos head_p' h_head_p'_pos
              rw [List.dropLast_cons_of_ne_nil h_tail_ne] at hx
              rcases List.mem_cons.mp hx with rfl | hx_rest
              · exact hvMid_W
              · exact h_head_p'_inter x hx_rest
            · change head_p'.length + 1 + tail.length
                  = p'.length + 1; omega
            · -- p.vertices
              -- = (cons _ _ head_p').vertices.dropLast ++ tail.vertices
              change u :: p'.vertices
                    = (u :: head_p'.vertices).dropLast
                        ++ tail.vertices
              have h_hp'_ne : head_p'.vertices ≠ [] :=
                Walk.vertices_ne_nil head_p'
              rw [List.dropLast_cons_of_ne_nil h_hp'_ne]
              rw [List.cons_append]
              rw [h_p'_eq]
          · -- vMid ∉ W: head := single-edge walk to vMid; tail := p'.
            have hvMid_g : vMid ∈ G :=
              Finset.mem_union_right _ (G.hE_subset h_edge).2
            refine ⟨vMid, Walk.cons vMid (.forwardE h_edge)
                    (Walk.nil vMid hvMid_g), p',
                    trivial, hp'_dir,
                    by simp [Walk.length],
                    hvMid_W, ?_, ?_, ?_⟩
            · intro x hx
              simp [Walk.vertices] at hx
            · change 1 + p'.length = p'.length + 1; omega
            · -- LHS: u :: p'.vertices; RHS: [u] ++ p'.vertices.
              change u :: p'.vertices = [u] ++ p'.vertices
              rfl

/-- Project a directed walk from `G` to the marginalized CDMG, given
both endpoints lie in `G.marginalize W hW`.  Constructed by
strong induction on walk length: iteratively peel off a head segment
from `v₁` to the first non-`W` vertex, witness the corresponding
`marg`-edge via the `Φ_E` predicate, and recurse on the tail.  The
projected walk is shorter than the original (a single `marg`-edge
absorbs an arbitrary `W`-traversal).

Refactor port: marg-E is *unchanged* in carrier shape
(`Finset (Node × Node)`); only the `Φ_E` reference renames.  The
walk-step construction `Or.inl ⟨rfl, Or.inl h_edge_marg⟩` becomes
`.forwardE h_edge_marg`, and the IsDirectedWalk witness
`⟨rfl, h_edge_marg, hq_tail_dir⟩` collapses to `hq_tail_dir`
(the cons-level `IsDirectedWalk` on `.forwardE` is
definitionally the tail's `IsDirectedWalk`). -/
lemma project_directed_walk_aux {G : CDMG Node} {W : Finset Node}
    {hW : W ⊆ G.V} :
    ∀ (n : ℕ) {v₁ v₂ : Node} (p : Walk G v₁ v₂),
      p.length ≤ n →
      p.IsDirectedWalk →
      v₁ ∈ G.marginalize W hW →
      v₂ ∈ G.marginalize W hW →
      ∃ (q : Walk (G.marginalize W hW) v₁ v₂),
        q.IsDirectedWalk := by
  intro n
  induction n with
  | zero =>
      intros v₁ v₂ p hp_len _ hv₁ _
      have hp_zero : p.length = 0 := by omega
      match p, hp_zero with
      | .nil v _, _ => exact ⟨Walk.nil v hv₁, trivial⟩
  | succ k ih =>
      intros v₁ v₂ p hp_len hp_dir hv₁ hv₂
      by_cases hp_zero : p.length = 0
      · match p, hp_zero with
        | .nil v _, _ => exact ⟨Walk.nil v hv₁, trivial⟩
      · have hp_pos : p.length ≥ 1 := Nat.one_le_iff_ne_zero.mpr hp_zero
        have hv₂_notW : v₂ ∉ W := notW_of_mem_marginalize hW hv₂
        obtain ⟨m, head, tail, h_head_dir, h_tail_dir, h_head_pos,
                hm_notW, h_head_inter, h_lens, _⟩ :=
          find_first_non_W_directed W p hp_dir hp_pos hv₂_notW
        -- m ∈ G.V (target of a directed walk of length ≥ 1).
        have hm_V : m ∈ G.V :=
          Walk.target_in_GV_of_directedWalk_pos
            head h_head_dir h_head_pos
        have hm_marg : m ∈ G.marginalize W hW := by
          change m ∈ G.J ∪ (G.V \ W)
          exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hm_V, hm_notW⟩)
        -- Project the tail.
        have h_tail_len : tail.length ≤ k := by omega
        obtain ⟨q_tail, hq_tail_dir⟩ :=
          ih tail h_tail_len h_tail_dir hm_marg hv₂
        by_cases hv₁_eq_m : v₁ = m
        · -- Self-loop / degenerate case: head is a `v₁ → ... → v₁` cycle
          -- through `W`.  Return `q_tail` directly (with `v₁ = m` on
          -- the type level).
          subst hv₁_eq_m
          exact ⟨q_tail, hq_tail_dir⟩
        · -- v₁ ≠ m: build a single `marg`-edge from v₁ to m, then
          -- prepend to the projected tail.
          have h_edge_marg : (v₁, m) ∈ (G.marginalize W hW).E := by
            change (v₁, m) ∈ ((G.J ∪ (G.V \ W)) ×ˢ (G.V \ W)).filter
                  (fun e => G.MarginalizationΦE W e.1 e.2)
            refine Finset.mem_filter.mpr ⟨?_, ?_⟩
            · refine Finset.mem_product.mpr ⟨hv₁, ?_⟩
              exact Finset.mem_sdiff.mpr ⟨hm_V, hm_notW⟩
            · -- `Φ_E W v₁ m`: the head walk itself witnesses it.
              exact ⟨head, h_head_dir, h_head_pos, h_head_inter⟩
          exact ⟨Walk.cons m (.forwardE h_edge_marg) q_tail,
                 hq_tail_dir⟩

/-- Convenience wrapper: project a directed walk from `G` to
`G.marginalize W hW`, with both endpoints in the marg-carrier.
Refactor port: pure name retarget. -/
lemma project_directed_walk_marginalize {G : CDMG Node}
    {W : Finset Node} {hW : W ⊆ G.V}
    {v₁ v₂ : Node} (p : Walk G v₁ v₂) (hp_dir : p.IsDirectedWalk)
    (hv₁ : v₁ ∈ G.marginalize W hW)
    (hv₂ : v₂ ∈ G.marginalize W hW) :
    ∃ (q : Walk (G.marginalize W hW) v₁ v₂),
      q.IsDirectedWalk :=
  project_directed_walk_aux
    (hW := hW) p.length p le_rfl hp_dir hv₁ hv₂

/-- Strengthened projection: project a directed walk in `G` (between
two marg-nodes of `G.marginalize W hW`) to a directed walk
in the same marg, with the additional guarantees:
  - every vertex of the projected walk appears in the original;
  - every vertex of the projected walk's `dropLast` appears in the
    original's `dropLast` (i.e.\ excluding-target sub-list);
  - every vertex of the projected walk's `tail` appears in the
    original's `tail` (i.e.\ excluding-source sub-list).
Used by sub-claim ii(b) `(⟹)`'s end-node uniqueness bookkeeping.

Refactor port: same shape as the unstrengthened projection above
(marg-E carrier unchanged, `.forwardE` for the typed WalkStep). -/
lemma project_directed_walk_with_vertex_subset_aux
    {G : CDMG Node} {W : Finset Node} {hW : W ⊆ G.V} :
    ∀ (n : ℕ) {v₁ v₂ : Node} (p : Walk G v₁ v₂),
      p.length ≤ n →
      p.IsDirectedWalk →
      v₁ ∈ G.marginalize W hW →
      v₂ ∈ G.marginalize W hW →
      ∃ (q : Walk (G.marginalize W hW) v₁ v₂),
        q.IsDirectedWalk ∧
        (∀ x ∈ q.vertices, x ∈ p.vertices) ∧
        (∀ x ∈ q.vertices.dropLast, x ∈ p.vertices.dropLast) ∧
        (∀ x ∈ q.vertices.tail, x ∈ p.vertices.tail) := by
  intro n
  induction n with
  | zero =>
      intros v₁ v₂ p hp_len _ hv₁ _
      have hp_zero : p.length = 0 := by omega
      match p, hp_zero with
      | .nil v _, _ =>
          refine ⟨Walk.nil v hv₁, trivial, ?_, ?_, ?_⟩
          · intro x hx
            change x ∈ [v] at hx
            change x ∈ [v]
            exact hx
          · intro x hx
            change x ∈ ([v] : List Node).dropLast at hx
            simp [List.dropLast] at hx
          · intro x hx
            change x ∈ ([v] : List Node).tail at hx
            simp [List.tail] at hx
  | succ k ih =>
      intros v₁ v₂ p hp_len hp_dir hv₁ hv₂
      by_cases hp_zero : p.length = 0
      · match p, hp_zero with
        | .nil v _, _ =>
            refine ⟨Walk.nil v hv₁, trivial, ?_, ?_, ?_⟩
            · intro x hx
              change x ∈ [v] at hx
              change x ∈ [v]
              exact hx
            · intro x hx
              change x ∈ ([v] : List Node).dropLast at hx
              simp [List.dropLast] at hx
            · intro x hx
              change x ∈ ([v] : List Node).tail at hx
              simp [List.tail] at hx
      · have hp_pos : p.length ≥ 1 := Nat.one_le_iff_ne_zero.mpr hp_zero
        have hv₂_notW : v₂ ∉ W := notW_of_mem_marginalize hW hv₂
        obtain ⟨m, head, tail, h_head_dir, h_tail_dir, h_head_pos,
                hm_notW, h_head_inter, h_lens, h_p_eq⟩ :=
          find_first_non_W_directed W p hp_dir hp_pos hv₂_notW
        have hm_V : m ∈ G.V :=
          Walk.target_in_GV_of_directedWalk_pos
            head h_head_dir h_head_pos
        have hm_marg : m ∈ G.marginalize W hW := by
          change m ∈ G.J ∪ (G.V \ W)
          exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hm_V, hm_notW⟩)
        have h_tail_len : tail.length ≤ k := by omega
        obtain ⟨q_tail, hq_tail_dir, hq_tail_sub, hq_tail_drop, hq_tail_tail⟩ :=
          ih tail h_tail_len h_tail_dir hm_marg hv₂
        -- Bookkeeping: head.vertices
        -- = v₁ :: head.vertices.tail, with non-empty tail.
        have h_head_drop_ne : head.vertices.tail ≠ [] :=
            Walk.tail_vertices_ne_nil_of_pos head h_head_pos
        have h_head_vs : head.vertices
            = v₁ :: head.vertices.tail :=
            Walk.vertices_eq_head_cons_tail head
        have h_v1_in_drop : v₁ ∈ head.vertices.dropLast := by
          rw [h_head_vs]
          rw [List.dropLast_cons_of_ne_nil h_head_drop_ne]
          exact List.mem_cons_self
        have h_head_drop_vs : head.vertices.dropLast =
            v₁ :: head.vertices.tail.dropLast := by
          rw [h_head_vs]
          exact List.dropLast_cons_of_ne_nil h_head_drop_ne
        -- p.vertices.dropLast: derived from
        -- p.vertices = head.dropLast ++ tail.
        have h_tail_vs_ne : tail.vertices ≠ [] :=
          Walk.vertices_ne_nil tail
        have h_p_drop : p.vertices.dropLast =
            head.vertices.dropLast ++ tail.vertices.dropLast := by
          rw [h_p_eq]
          exact List.dropLast_append_of_ne_nil h_tail_vs_ne
        have h_p_tail : p.vertices.tail =
            head.vertices.dropLast.tail ++ tail.vertices := by
          rw [h_p_eq, h_head_drop_vs]
          rfl
        by_cases hv₁_eq_m : v₁ = m
        · -- Self-loop case: return `q_tail` directly (with `v₁ = m` on
          -- the type level).
          subst hv₁_eq_m
          refine ⟨q_tail, hq_tail_dir, ?_, ?_, ?_⟩
          · -- q_tail.vertices ⊆ p.vertices.
            intro x hx
            rw [h_p_eq]
            exact List.mem_append.mpr (Or.inr (hq_tail_sub x hx))
          · -- q_tail.vertices.dropLast ⊆ p.vertices.dropLast.
            intro x hx
            rw [h_p_drop]
            exact List.mem_append.mpr (Or.inr (hq_tail_drop x hx))
          · -- q_tail.vertices.tail ⊆ p.vertices.tail.
            intro x hx
            rw [h_p_tail]
            have hx_t : x ∈ tail.vertices.tail := hq_tail_tail x hx
            exact List.mem_append.mpr (Or.inr (List.mem_of_mem_tail hx_t))
        · -- Non-self-loop case: build single marg-edge.
          have h_edge_marg : (v₁, m) ∈ (G.marginalize W hW).E := by
            change (v₁, m) ∈ ((G.J ∪ (G.V \ W)) ×ˢ (G.V \ W)).filter
                  (fun e => G.MarginalizationΦE W e.1 e.2)
            refine Finset.mem_filter.mpr ⟨?_, ?_⟩
            · refine Finset.mem_product.mpr ⟨hv₁, ?_⟩
              exact Finset.mem_sdiff.mpr ⟨hm_V, hm_notW⟩
            · -- `Φ_E W v₁ m`: the head walk itself witnesses it.
              exact ⟨head, h_head_dir, h_head_pos, h_head_inter⟩
          refine ⟨Walk.cons m (.forwardE h_edge_marg) q_tail,
                  hq_tail_dir, ?_, ?_, ?_⟩
          · -- q.vertices ⊆ p.vertices.
            intro x hx
            change x ∈ v₁ :: q_tail.vertices at hx
            rw [h_p_eq]
            rcases List.mem_cons.mp hx with hx_v1 | hx_tail
            · subst hx_v1
              exact List.mem_append.mpr (Or.inl h_v1_in_drop)
            · exact List.mem_append.mpr (Or.inr (hq_tail_sub x hx_tail))
          · -- q.vertices.dropLast ⊆ p.vertices.dropLast.
            -- q.vertices = v₁ :: q_tail.vertices.
            -- q_tail.vertices is non-empty, so
            -- q.vertices.dropLast = v₁ :: q_tail.vertices.dropLast.
            intro x hx
            have h_qt_vs_ne : q_tail.vertices ≠ [] :=
              Walk.vertices_ne_nil q_tail
            change x ∈ (v₁ :: q_tail.vertices).dropLast at hx
            rw [List.dropLast_cons_of_ne_nil h_qt_vs_ne] at hx
            rw [h_p_drop]
            rcases List.mem_cons.mp hx with hx_v1 | hx_qtl
            · subst hx_v1
              exact List.mem_append.mpr (Or.inl h_v1_in_drop)
            · exact List.mem_append.mpr (Or.inr (hq_tail_drop x hx_qtl))
          · -- q.vertices.tail ⊆ p.vertices.tail.
            -- q.vertices = v₁ :: q_tail.vertices.
            -- q.vertices.tail = q_tail.vertices.
            intro x hx
            change x ∈ q_tail.vertices at hx
            rw [h_p_tail]
            -- p.vertices.tail
            -- = head.vertices.dropLast.tail ++ tail.vertices.
            -- q_tail.vertices ⊆ tail.vertices ⊆ p.vertices.tail.
            exact List.mem_append.mpr (Or.inr (hq_tail_sub x hx))

/-- Convenience wrapper for the strong projection: project a directed
walk `p : Walk G v₁ v₂` (between marg-nodes of
`G.marginalize W hW`) to a directed walk
`q : Walk marg v₁ v₂` with the three vertex-subset
clauses.  Refactor port: pure name retarget. -/
lemma project_directed_walk_strong {G : CDMG Node}
    {W : Finset Node} {hW : W ⊆ G.V}
    {v₁ v₂ : Node} (p : Walk G v₁ v₂) (hp_dir : p.IsDirectedWalk)
    (hv₁ : v₁ ∈ G.marginalize W hW)
    (hv₂ : v₂ ∈ G.marginalize W hW) :
    ∃ (q : Walk (G.marginalize W hW) v₁ v₂),
      q.IsDirectedWalk ∧
      (∀ x ∈ q.vertices, x ∈ p.vertices) ∧
      (∀ x ∈ q.vertices.dropLast, x ∈ p.vertices.dropLast) ∧
      (∀ x ∈ q.vertices.tail, x ∈ p.vertices.tail) :=
  project_directed_walk_with_vertex_subset_aux
    (hW := hW) p.length p le_rfl hp_dir hv₁ hv₂

-- ## Refactor replacements — Batch 5 (declarations 23–33)
--
-- Walk reversal + mkBifurcation infrastructure, ported against the typed
-- `WalkStep` constructors.  The centerpiece is
-- `reverseDirected` (decl 24): under the refactor the cons-cell's
-- step IS the witness, so the `.backwardE h` constructor takes the same
-- `h : (c, vMid) ∈ G.E` extracted from the input `.forwardE h` step — no
-- separate `Or.inr ⟨ha_eq, ha_E⟩` proof tuple to assemble.  The two helper
-- aux lemmas (decls 32, 33) and the cons-backward-of-directed primitive
-- (decl 31) all benefit from the same simplification: predicates that
-- previously needed to discharge a triple conjunction (edge eq, edge
-- membership, tail directed/bifurcation) now hold by definitional unfolding
-- once the typed step is `.backwardE`, because
-- `IsBifurcationDirectedHingeWithSplit` and
-- `IsDirectedWalk` strip the conjunction structurally.
--
-- Vacuous `.backwardE` / `.bidir` branches discharge via `hqv_dir.elim`
-- (matching the pattern used in Batch 1's `isDirectedWalk_comp`
-- and `target_in_GV_of_directedWalk_pos`).

/-- A walk between distinct endpoints has length `≥ 1`. -/
lemma Walk.length_pos_of_ne {G : CDMG Node} {u v : Node}
    (p : Walk G u v) (h : u ≠ v) : p.length ≥ 1 := by
  cases p with
  | nil _ _ => exact absurd rfl h
  | cons _ _ _ => exact Nat.succ_le_succ (Nat.zero_le _)

/-- Reverse a directed walk.  Refactor port: case-split on the typed
step `s : WalkStep` instead of the original `Or`-disjunction
witness; only the `.forwardE h_E` constructor is reachable on a
directed walk, and the reversed cons-cell uses `.backwardE h_E` with
the same edge witness.  The `.backwardE` and `.bidir` branches are
discharged via `hqv_dir.elim` (`IsDirectedWalk` returns
`False` there). -/
def Walk.reverseDirected {G : CDMG Node} :
    ∀ {c v : Node} (qv : Walk G c v),
      qv.IsDirectedWalk → Walk G v c
  | _, _, .nil w hw, _ => Walk.nil w hw
  | c, _, .cons _ (.forwardE h_E) qv', hqv_dir =>
      (Walk.reverseDirected qv' hqv_dir).comp
        (Walk.cons c (.backwardE h_E)
          (Walk.nil c
            (WalkStep.source_mem (.forwardE h_E))))
  | _, _, .cons _ (.backwardE _) _, hqv_dir => hqv_dir.elim
  | _, _, .cons _ (.bidir _) _, hqv_dir => hqv_dir.elim

lemma Walk.length_reverseDirected {G : CDMG Node} :
    ∀ {c v : Node} (qv : Walk G c v) (hqv_dir : qv.IsDirectedWalk),
      (Walk.reverseDirected qv hqv_dir).length = qv.length
  | _, _, .nil _ _, _ => rfl
  | _, _, .cons _ (.forwardE _) qv', hqv_dir => by
      change ((Walk.reverseDirected qv' hqv_dir).comp _).length
            = qv'.length + 1
      rw [Walk.length_comp,
          Walk.length_reverseDirected qv' hqv_dir]
      rfl
  | _, _, .cons _ (.backwardE _) _, hqv_dir => hqv_dir.elim
  | _, _, .cons _ (.bidir _) _, hqv_dir => hqv_dir.elim

lemma Walk.vertices_reverseDirected {G : CDMG Node} :
    ∀ {c v : Node} (qv : Walk G c v) (hqv_dir : qv.IsDirectedWalk),
      (Walk.reverseDirected qv hqv_dir).vertices
        = qv.vertices.reverse
  | _, _, .nil _ _, _ => rfl
  | c, _, .cons vMid (.forwardE _) qv', hqv_dir => by
      have ih := Walk.vertices_reverseDirected qv' hqv_dir
      have h_head : qv'.vertices = vMid :: qv'.vertices.tail :=
        Walk.vertices_eq_head_cons_tail qv'
      change ((Walk.reverseDirected qv' hqv_dir).comp _).vertices
            = (c :: qv'.vertices).reverse
      rw [Walk.vertices_comp, ih]
      conv_lhs => rw [h_head]
      conv_rhs => rw [h_head]
      simp [Walk.vertices, List.reverse_cons]
  | _, _, .cons _ (.backwardE _) _, hqv_dir => hqv_dir.elim
  | _, _, .cons _ (.bidir _) _, hqv_dir => hqv_dir.elim

/-- The bifurcation-walk constructor.  Refactor port: wrapper around
`reverseDirected` + `comp`. -/
def Walk.mkBifurcation {G : CDMG Node} {c v w : Node}
    (qv : Walk G c v) (hqv_dir : qv.IsDirectedWalk)
    (_hqv_pos : qv.length ≥ 1) (qw : Walk G c w) : Walk G v w :=
  (Walk.reverseDirected qv hqv_dir).comp qw

lemma Walk.length_mkBifurcation {G : CDMG Node} {c v w : Node}
    (qv : Walk G c v) (hqv_dir : qv.IsDirectedWalk)
    (hqv_pos : qv.length ≥ 1) (qw : Walk G c w) :
    (Walk.mkBifurcation qv hqv_dir hqv_pos qw).length
      = qv.length + qw.length := by
  change ((Walk.reverseDirected qv hqv_dir).comp qw).length
        = qv.length + qw.length
  rw [Walk.length_comp,
      Walk.length_reverseDirected qv hqv_dir]

lemma Walk.vertices_mkBifurcation {G : CDMG Node} {c v w : Node}
    (qv : Walk G c v) (hqv_dir : qv.IsDirectedWalk)
    (hqv_pos : qv.length ≥ 1) (qw : Walk G c w) :
    (Walk.mkBifurcation qv hqv_dir hqv_pos qw).vertices
      = qv.vertices.reverse.dropLast ++ qw.vertices := by
  change ((Walk.reverseDirected qv hqv_dir).comp qw).vertices
        = qv.vertices.reverse.dropLast ++ qw.vertices
  rw [Walk.vertices_comp,
      Walk.vertices_reverseDirected qv hqv_dir]

lemma Walk.comp_assoc {G : CDMG Node} :
    ∀ {u₁ u₂ u₃ u₄ : Node} (p : Walk G u₁ u₂) (q : Walk G u₂ u₃)
      (r : Walk G u₃ u₄),
      (p.comp q).comp r = p.comp (q.comp r)
  | _, _, _, _, .nil _ _, _, _ => rfl
  | _, _, _, _, .cons _ s p, q, r => by
      change Walk.cons _ s ((p.comp q).comp r)
            = Walk.cons _ s (p.comp (q.comp r))
      rw [Walk.comp_assoc p q r]

/-- Refactor port: signature shrinks because the typed `.backwardE h`
constructor already pins the direction and edge witness — no
`(a : Node × Node)`, `ha_eq : a = (v, u)`, or `ha_mem : a ∈ G.E` field
to thread.  Under the new
`IsBifurcationDirectedHingeWithSplit`, the
`.cons _ (.backwardE _) (cons _ _ _), 0` arm reduces directly to
`p.IsDirectedWalk`, so the goal collapses to `hp_dir`. -/
lemma Walk.isBifurcationDirectedHinge_cons_backward_of_directed
    {G : CDMG Node} {u v w : Node}
    (h : (v, u) ∈ G.E) (p : Walk G v w)
    (hp_dir : p.IsDirectedWalk)
    (hp_nonempty : p.length ≥ 1) :
    (Walk.cons v (.backwardE h) p).IsBifurcationDirectedHingeWithSplit 0 := by
  cases p with
  | nil _ _ => simp [Walk.length] at hp_nonempty
  | cons _ _ _ => exact hp_dir

/-- Refactor port: same recursion shape as the original, but the cons-cell
destructure picks up the edge witness `h_E : (c, vMid) ∈ G.E` directly
from the `.forwardE h_E` step, and the backward step is `.backwardE h_E`
(with the same witness).  The `h_cons` intermediate that previously
needed `simp only [Walk.IsBifurcationDirectedHingeWithSplit]; exact ⟨...⟩`
to discharge a triple conjunction now equals `hrest` by definitional
unfolding of the `.cons _ (.backwardE _) p, k + 1` arm
(`p.IsBifurcationDirectedHingeWithSplit k`). -/
lemma Walk.isBifurcationDirectedHinge_comp_reverseDirected_aux
    {G : CDMG Node} :
    ∀ {c v : Node} (qv : Walk G c v) (hqv_dir : qv.IsDirectedWalk)
      {w : Node} (rest : Walk G c w) (k : ℕ)
      (_hrest : rest.IsBifurcationDirectedHingeWithSplit k),
      Walk.IsBifurcationDirectedHingeWithSplit
        ((Walk.reverseDirected qv hqv_dir).comp rest)
        (qv.length + k)
  | _, _, .nil w _, _, _, rest, k, hrest => by
      simp only [Walk.reverseDirected, Walk.comp,
                 Walk.length, Nat.zero_add]
      exact hrest
  | c, _, .cons vMid (.forwardE h_E) qv', hqv_dir, _, rest, k, hrest => by
      have h_cons : Walk.IsBifurcationDirectedHingeWithSplit
          (Walk.cons c (.backwardE h_E) rest) (k + 1) := by
        simp only [Walk.IsBifurcationDirectedHingeWithSplit]
        exact hrest
      have ih := Walk.isBifurcationDirectedHinge_comp_reverseDirected_aux
        qv' hqv_dir (Walk.cons c (.backwardE h_E) rest) (k + 1) h_cons
      change Walk.IsBifurcationDirectedHingeWithSplit
        (((Walk.reverseDirected qv' hqv_dir).comp
            (Walk.cons c (.backwardE h_E)
              (Walk.nil c
                (WalkStep.source_mem (.forwardE h_E))))).comp rest)
        (qv'.length + 1 + k)
      rw [Walk.comp_assoc]
      change Walk.IsBifurcationDirectedHingeWithSplit
        ((Walk.reverseDirected qv' hqv_dir).comp
          (Walk.cons c (.backwardE h_E) rest))
        (qv'.length + 1 + k)
      have hidx : qv'.length + 1 + k = qv'.length + (k + 1) := by omega
      rw [hidx]
      exact ih
  | _, _, .cons _ (.backwardE _) _, hqv_dir, _, _, _, _ => hqv_dir.elim
  | _, _, .cons _ (.bidir _) _, hqv_dir, _, _, _, _ => hqv_dir.elim

/-- Refactor port: structural simplifications mirror decl 32.  The
`backStep` construction `Or.inr ⟨hqv_dir.1, hqv_dir.2.1⟩` becomes the
typed `.backwardE h_E`, and the call to
`isBifurcationDirectedHinge_cons_backward_of_directed` drops
the `(a, ha_eq, ha_mem)` arguments. -/
lemma Walk.isBifurcationDirectedHinge_mkBifurcation
    {G : CDMG Node} {c v w : Node}
    (qv : Walk G c v) (hqv_dir : qv.IsDirectedWalk)
    (hqv_pos : qv.length ≥ 1)
    (qw : Walk G c w) (hqw_dir : qw.IsDirectedWalk)
    (hqw_pos : qw.length ≥ 1) :
    Walk.IsBifurcationDirectedHingeWithSplit
      (Walk.mkBifurcation qv hqv_dir hqv_pos qw)
      (qv.length - 1) := by
  change Walk.IsBifurcationDirectedHingeWithSplit
    ((Walk.reverseDirected qv hqv_dir).comp qw)
    (qv.length - 1)
  match qv, hqv_dir, hqv_pos with
  | .nil _ _, _, hpos => simp [Walk.length] at hpos
  | .cons _ (.forwardE h_E) qv', hqv_dir, _ =>
      have h_base : Walk.IsBifurcationDirectedHingeWithSplit
          (Walk.cons c (.backwardE h_E) qw) 0 :=
        Walk.isBifurcationDirectedHinge_cons_backward_of_directed
          h_E qw hqw_dir hqw_pos
      have ih := Walk.isBifurcationDirectedHinge_comp_reverseDirected_aux
        qv' hqv_dir (Walk.cons c (.backwardE h_E) qw) 0 h_base
      change Walk.IsBifurcationDirectedHingeWithSplit
        (((Walk.reverseDirected qv' hqv_dir).comp
            (Walk.cons c (.backwardE h_E)
              (Walk.nil c
                (WalkStep.source_mem (.forwardE h_E))))).comp qw)
        (qv'.length + 1 - 1)
      rw [Walk.comp_assoc]
      change Walk.IsBifurcationDirectedHingeWithSplit
        ((Walk.reverseDirected qv' hqv_dir).comp
          (Walk.cons c (.backwardE h_E) qw))
        (qv'.length + 1 - 1)
      have hidx : qv'.length + 1 - 1 = qv'.length + 0 := by omega
      rw [hidx]
      exact ih
  | .cons _ (.backwardE _) _, hqv_dir, _ => exact hqv_dir.elim
  | .cons _ (.bidir _) _, hqv_dir, _ => exact hqv_dir.elim

-- ## Refactor replacements — Batch 6 (declarations 34–41).
--
-- Bidirected-hinge mkBifurcation core + supporting bifurcation-split
-- lemmas.  All eight declarations port mechanically from the originals
-- with two structural shifts and two simplifications:
-- (i)  signature shift `(hLR : (vL, vR) ∈ G.L)` →
--      `(hLR : s(vL, vR) ∈ G.L)` reflecting the Sym2 encoding of `L`;
-- (ii) cons-cell construction shifts from
--      `Walk.cons vR (vL, vR) (Or.inl ⟨rfl, Or.inr hLR⟩) R` to
--      `Walk.cons vR (.bidir hLR) R` — significantly shorter.
-- Simplification (R3 in the workspace plan):
-- (a)  decl 40's nil-tail case in `h_base` collapses to `trivial`
--      under the new `IsBifurcationWithSplit`'s
--      `cons _ (.bidir _) (.nil _ _), 0` arm returning `True`
--      (originally `a = (u, v) ∧ a ∈ G.L`, discharged via `⟨rfl, hLR⟩`);
-- (b)  decl 41's IsBifurcationWithSplit existential pinning the
--      bidirected hinge inherits the simplification through the
--      `isBifurcationWithSplit_mkBifurcationBidir` call.

/-- Vertex-list re-expression: `p.vertices.reverse.dropLast =
p.vertices.tail.reverse`.  Refactor port: pure list-level identity
modulo `vertices` → `vertices`. -/
lemma Walk.vertices_reverse_dropLast {G : CDMG Node}
    {u v : Node} (p : Walk G u v) :
    p.vertices.reverse.dropLast = p.vertices.tail.reverse := by
  conv_lhs => rw [Walk.vertices_eq_head_cons_tail p]
  rw [List.reverse_cons]
  exact List.dropLast_concat

/-- The bidirected-hinge bifurcation walk constructor.  Refactor port:
the cons-cell witness `Or.inl ⟨rfl, Or.inr hLR⟩` carrying both the
ordered-pair equation and the channel choice collapses to the typed
constructor `.bidir hLR` — the channel is encoded in the constructor
name, no ordered-pair witness needed. -/
def Walk.mkBifurcationBidir {G : CDMG Node}
    {vL vR v1 v2 : Node}
    (L : Walk G vL v1) (hL_dir : L.IsDirectedWalk)
    (R : Walk G vR v2)
    (hLR : s(vL, vR) ∈ G.L) : Walk G v1 v2 :=
  (Walk.reverseDirected L hL_dir).comp
    (Walk.cons vR (.bidir hLR) R)

lemma Walk.length_mkBifurcationBidir
    {G : CDMG Node} {vL vR v1 v2 : Node}
    (L : Walk G vL v1) (hL_dir : L.IsDirectedWalk)
    (R : Walk G vR v2) (hLR : s(vL, vR) ∈ G.L) :
    (Walk.mkBifurcationBidir L hL_dir R hLR).length
      = L.length + R.length + 1 := by
  change ((Walk.reverseDirected L hL_dir).comp _).length = _
  rw [Walk.length_comp,
      Walk.length_reverseDirected]
  change L.length + (R.length + 1) = L.length + R.length + 1
  omega

lemma Walk.vertices_mkBifurcationBidir
    {G : CDMG Node} {vL vR v1 v2 : Node}
    (L : Walk G vL v1) (hL_dir : L.IsDirectedWalk)
    (R : Walk G vR v2) (hLR : s(vL, vR) ∈ G.L) :
    (Walk.mkBifurcationBidir L hL_dir R hLR).vertices
      = L.vertices.reverse.dropLast ++ (vL :: R.vertices) := by
  change ((Walk.reverseDirected L hL_dir).comp _).vertices = _
  rw [Walk.vertices_comp,
      Walk.vertices_reverseDirected]
  rfl

/-- Bidirected analog of
`isBifurcationDirectedHinge_comp_reverseDirected_aux`.
Refactor port: same recursion shape as Batch 5's decl 32, but with
`IsBifurcationDirectedHingeWithSplit` swapped for the broader
`IsBifurcationWithSplit`.  The `.backwardE` cons-cell at `k+1`
arm of `IsBifurcationWithSplit` reduces directly to
`p.IsBifurcationWithSplit k`, so the inner `h_cons`
intermediate degenerates to `hrest` (the original needed
`simp only [Walk.IsBifurcationWithSplit]; exact ⟨_, _, _⟩`
to discharge a triple conjunction). -/
lemma Walk.isBifurcationWithSplit_comp_reverseDirected_bidir_aux
    {G : CDMG Node} :
    ∀ {c v : Node} (qv : Walk G c v) (hqv_dir : qv.IsDirectedWalk)
      {w : Node} (rest : Walk G c w) (k : ℕ)
      (_hrest : rest.IsBifurcationWithSplit k),
      Walk.IsBifurcationWithSplit
        ((Walk.reverseDirected qv hqv_dir).comp rest)
        (qv.length + k)
  | _, _, .nil w _, _, _, rest, k, hrest => by
      simp only [Walk.reverseDirected, Walk.comp,
                 Walk.length, Nat.zero_add]
      exact hrest
  | c, _, .cons _ (.forwardE h_E) qv', hqv_dir, _, rest, k, hrest => by
      have h_cons : Walk.IsBifurcationWithSplit
          (Walk.cons c (.backwardE h_E) rest) (k + 1) := by
        simp only [Walk.IsBifurcationWithSplit]
        exact hrest
      have ih := Walk.isBifurcationWithSplit_comp_reverseDirected_bidir_aux
        qv' hqv_dir (Walk.cons c (.backwardE h_E) rest) (k + 1) h_cons
      change Walk.IsBifurcationWithSplit
        (((Walk.reverseDirected qv' hqv_dir).comp
            (Walk.cons c (.backwardE h_E)
              (Walk.nil c
                (WalkStep.source_mem (.forwardE h_E))))).comp rest)
        (qv'.length + 1 + k)
      rw [Walk.comp_assoc]
      change Walk.IsBifurcationWithSplit
        ((Walk.reverseDirected qv' hqv_dir).comp
          (Walk.cons c (.backwardE h_E) rest))
        (qv'.length + 1 + k)
      have hidx : qv'.length + 1 + k = qv'.length + (k + 1) := by omega
      rw [hidx]
      exact ih
  | _, _, .cons _ (.backwardE _) _, hqv_dir, _, _, _, _ => hqv_dir.elim
  | _, _, .cons _ (.bidir _) _, hqv_dir, _, _, _, _ => hqv_dir.elim

/-- Right-extension: appending a directed walk `D` to the right of a
bifurcation walk `M` preserves the `IsBifurcationWithSplit`
predicate at the same index.  Refactor port: the cons-cell's step
constructor now drives the case-split (no `Or`-shaped destructure).
Under the new `IsBifurcationWithSplit`, only `.backwardE _`
and `.bidir _` admit cons-cell-at-`k=0`, and only `.backwardE _`
admits `k+1`; the `.forwardE _` branches are uniformly vacuous and
close via `hM.elim`.  The original's k=0 case-split on `M'` also
collapses cleanly: `.nil` only realises the predicate for `.bidir`
(now `True`), and `.cons` realises `p.IsDirectedWalk`
for both `.backwardE` and `.bidir`, so the right-arm extension is a
direct call to `isDirectedWalk_comp`. -/
lemma Walk.isBifurcationWithSplit_comp_right_directed
    {G : CDMG Node} :
    ∀ {u v : Node} (M : Walk G u v) (k : ℕ),
      M.IsBifurcationWithSplit k →
      ∀ {w : Node} (D : Walk G v w), D.IsDirectedWalk →
      (M.comp D).IsBifurcationWithSplit k := by
  intro u v M
  induction M with
  | nil _ _ => intro k hM _ _ _; exact hM.elim
  | @cons _u _v_end _vMid s M' ih =>
      intro k hM _w D hD
      -- Drive the case-split through the step constructor, the index `k`, and
      -- (where needed) the shape of `M'` / `D`.  Each combination either
      -- unfolds the predicate to a usable hypothesis or to `False`, which we
      -- discharge with `hM.elim`.
      cases s with
      | forwardE _ =>
          -- `cons _ (.forwardE _) _` always returns `False`.
          cases k with
          | zero =>
              cases M' with
              | nil _ _ => exact hM.elim
              | cons _ _ _ => exact hM.elim
          | succ _ =>
              simp only [Walk.IsBifurcationWithSplit] at hM
      | backwardE h_E =>
          cases k with
          | zero =>
              -- `cons _ (.backwardE _) (.nil _ _), 0` is `False`;
              -- `cons _ (.backwardE _) (p@(.cons _ _ _)), 0` is
              -- `p.IsDirectedWalk`.
              cases M' with
              | nil _ _ => exact hM.elim
              | cons v' s' p =>
                  exact Walk.isDirectedWalk_comp
                    (Walk.cons v' s' p) D hM hD
          | succ k' =>
              -- `cons _ (.backwardE _) p, k+1` reduces to
              -- `p.IsBifurcationWithSplit k`; the goal reduces to
              -- `(p.comp D).IsBifurcationWithSplit k`.
              simp only [Walk.IsBifurcationWithSplit] at hM
              simp only [Walk.comp,
                         Walk.IsBifurcationWithSplit]
              exact ih k' hM D hD
      | bidir h_L =>
          cases k with
          | zero =>
              cases M' with
              | nil _ _ =>
                  -- `cons _ (.bidir _) (.nil _ _), 0` is `True`.
                  -- Goal:
                  -- `(cons _ (.bidir _) D).IsBifurcationWithSplit 0`
                  -- — `True` if `D = nil`, `D.IsDirectedWalk` if cons.
                  cases D with
                  | nil _ _ => trivial
                  | cons _ _ _ => exact hD
              | cons v' s' p =>
                  -- `cons _ (.bidir _) (p@(.cons _ _ _)), 0` reduces to
                  -- `p.IsDirectedWalk`.
                  exact Walk.isDirectedWalk_comp
                    (Walk.cons v' s' p) D hM hD
          | succ _ =>
              simp only [Walk.IsBifurcationWithSplit] at hM

/-- `mkBifurcationBidir L hL_dir R hLR` realises
`IsBifurcationWithSplit` at index `L.length`
(the position of the bidirected hinge).  Refactor port:
significant simplification on `h_base` — the original nil-tail case
discharged `a = (u, v) ∧ a ∈ G.L` via `⟨rfl, hLR⟩`; under the new
typed-step shape, `.cons _ (.bidir _) (.nil _ _), 0` reduces to
`True` (per the helper's arm), so `trivial` suffices.  The cons-tail
case also collapses: the original needed
`⟨Or.inr ⟨rfl, hLR⟩, hR_dir⟩` (channel-disjunction + directedness);
the new typed shape reduces `.cons _ (.bidir _) (p@(.cons _ _ _)), 0`
to `p.IsDirectedWalk`, so `hR_dir` alone suffices. -/
lemma Walk.isBifurcationWithSplit_mkBifurcationBidir
    {G : CDMG Node} {vL vR v1 v2 : Node}
    (L : Walk G vL v1) (hL_dir : L.IsDirectedWalk)
    (R : Walk G vR v2) (hR_dir : R.IsDirectedWalk)
    (hLR : s(vL, vR) ∈ G.L) :
    (Walk.mkBifurcationBidir L hL_dir R hLR).IsBifurcationWithSplit
      L.length := by
  change Walk.IsBifurcationWithSplit
    ((Walk.reverseDirected L hL_dir).comp _) L.length
  -- The cons-cell with the bidirected hinge at i = 0.
  have h_base : Walk.IsBifurcationWithSplit
      (Walk.cons vR (.bidir hLR) R) 0 := by
    cases R with
    | nil _ _ =>
        -- `cons _ (.bidir _) (.nil _ _), 0` reduces to `True`.
        trivial
    | cons _ _ _ =>
        -- `cons _ (.bidir _) (p@(.cons _ _ _)), 0` reduces to
        -- `p.IsDirectedWalk`.
        exact hR_dir
  have ih := Walk.isBifurcationWithSplit_comp_reverseDirected_bidir_aux
    L hL_dir _ 0 h_base
  have hidx : L.length + 0 = L.length := by omega
  rw [hidx] at ih
  exact ih

/-- Generic `IsBifurcation` lemma for `mkBifurcationBidir`.
Refactor port: signature swaps `(hLR : (vL, vR) ∈ G.L)` for
`(hLR : s(vL, vR) ∈ G.L)`; body is otherwise list-level manipulation
that ports verbatim modulo the standard `vertices` →
`vertices` retarget and helper-name prefix substitutions.
The IsBifurcation existential pinning the bidirected hinge no longer
needs the `a = (u, v) ∧ a ∈ G.L` discharge because the simplification
already happens inside `isBifurcationWithSplit_mkBifurcationBidir`. -/
lemma Walk.mkBifurcationBidir_isBifurcation
    {G : CDMG Node} {vL vR v1 v2 : Node}
    (L : Walk G vL v1) (hL_dir : L.IsDirectedWalk)
    (R : Walk G vR v2) (hR_dir : R.IsDirectedWalk)
    (hLR : s(vL, vR) ∈ G.L)
    (hv1v2_ne : v1 ≠ v2)
    (hv1_notin_L_drop : v1 ∉ L.vertices.dropLast)
    (hv1_notin_R : v1 ∉ R.vertices)
    (hv2_notin_L : v2 ∉ L.vertices)
    (hv2_notin_R_drop : v2 ∉ R.vertices.dropLast) :
    (Walk.mkBifurcationBidir L hL_dir R hLR).IsBifurcation := by
  have h_mk_vs := Walk.vertices_mkBifurcationBidir L hL_dir R hLR
  -- Auxiliary: l.reverse.tail = l.dropLast.reverse for any list `l`.
  have h_aux : ∀ (l : List Node), l.reverse.tail = l.dropLast.reverse := by
    intro l
    induction l with
    | nil => rfl
    | cons a rest ih =>
        by_cases h : rest = []
        · subst h; rfl
        · rw [List.reverse_cons, List.dropLast_cons_of_ne_nil h]
          rw [List.reverse_cons]
          rw [List.tail_append_of_ne_nil]
          · rw [ih]
          · intro hr_empty
            exact h (List.reverse_eq_nil_iff.mp hr_empty)
  -- Auxiliary: L.vertices.reverse.dropLast = L.vertices.tail.reverse.
  have h_L_rev_drop : L.vertices.reverse.dropLast = L.vertices.tail.reverse :=
    Walk.vertices_reverse_dropLast L
  -- R.vertices is non-empty (always).
  have h_R_vs_ne : R.vertices ≠ [] := Walk.vertices_ne_nil R
  -- vL is in L.vertices (always — it's the source).
  have h_vL_in_L_vs : vL ∈ L.vertices := Walk.head_mem_vertices L
  refine ⟨hv1v2_ne, ?_, ?_, L.length, ?_⟩
  · -- v1 ∉ walk.vertices.tail.
    intro hv1_in_tail
    rw [h_mk_vs] at hv1_in_tail
    by_cases hL_drop_empty : L.vertices.reverse.dropLast = []
    · -- L is trivial: L = nil, vL = v1.
      rw [hL_drop_empty, List.nil_append] at hv1_in_tail
      change v1 ∈ R.vertices at hv1_in_tail
      exact hv1_notin_R hv1_in_tail
    · -- L has length ≥ 1.
      rw [List.tail_append_of_ne_nil hL_drop_empty] at hv1_in_tail
      rcases List.mem_append.mp hv1_in_tail with hv1_L_drop_tail | hv1_vL_R
      · rw [h_L_rev_drop] at hv1_L_drop_tail
        rw [h_aux] at hv1_L_drop_tail
        have hv1_t_drop : v1 ∈ L.vertices.tail.dropLast :=
          List.mem_reverse.mp hv1_L_drop_tail
        have h_L_tail_ne : L.vertices.tail ≠ [] := by
          intro h
          apply hL_drop_empty
          rw [h_L_rev_drop, h]; rfl
        have h_t_drop_eq : L.vertices.tail.dropLast
            = L.vertices.dropLast.tail := by
          rw [Walk.vertices_eq_head_cons_tail L]
          simp only [List.tail_cons]
          rw [List.dropLast_cons_of_ne_nil h_L_tail_ne]
          rfl
        rw [h_t_drop_eq] at hv1_t_drop
        exact hv1_notin_L_drop (List.mem_of_mem_tail hv1_t_drop)
      · rcases List.mem_cons.mp hv1_vL_R with h_v1_eq_vL | hv1_R
        · -- v1 = vL. Derive vL ∈ L.vertices.dropLast.
          have h_L_tail_ne : L.vertices.tail ≠ [] := by
            intro h
            apply hL_drop_empty
            rw [h_L_rev_drop, h]
            rfl
          have hvL_in_drop : vL ∈ L.vertices.dropLast := by
            rw [Walk.vertices_eq_head_cons_tail L]
            rw [List.dropLast_cons_of_ne_nil h_L_tail_ne]
            exact List.mem_cons_self
          exact hv1_notin_L_drop (h_v1_eq_vL ▸ hvL_in_drop)
        · exact hv1_notin_R hv1_R
  · -- v2 ∉ walk.vertices.dropLast.
    intro hv2_in_drop
    rw [h_mk_vs] at hv2_in_drop
    have h_vLR_ne : (vL :: R.vertices) ≠ [] := by simp
    rw [List.dropLast_append_of_ne_nil h_vLR_ne] at hv2_in_drop
    rcases List.mem_append.mp hv2_in_drop with hv2_L_rev | hv2_vLR
    · rw [h_L_rev_drop] at hv2_L_rev
      have hv2_tail : v2 ∈ L.vertices.tail := List.mem_reverse.mp hv2_L_rev
      exact hv2_notin_L (List.mem_of_mem_tail hv2_tail)
    · rw [List.dropLast_cons_of_ne_nil h_R_vs_ne] at hv2_vLR
      rcases List.mem_cons.mp hv2_vLR with rfl | hv2_R_drop
      · exact hv2_notin_L h_vL_in_L_vs
      · exact hv2_notin_R_drop hv2_R_drop
  · -- IsBifurcationWithSplit at L.length.
    exact Walk.isBifurcationWithSplit_mkBifurcationBidir
      L hL_dir R hR_dir hLR

-- ## Refactor replacements — Batch 7 (declarations 42–46).
--
-- Bifurcation arm extractors + small support lemmas.  The two
-- "exists arms" lemmas (decl 42 + decl 47, the latter in Batch 8) are
-- central to all later bifurcation surgery (Batches 9–11 depend on
-- these).  Structural shifts in this batch:
-- (i)  the cons-cell destructure swaps `(a, hStep)` for the typed
--      `s : WalkStep`; we case-split on `s` *before* on
--      `i` / `p'` so each constructor's branch unfolds the
--      `IsBifurcation*` predicate cleanly;
-- (ii) the `let forwardStep := Or.inl ⟨ha_eq, Or.inl ha_mem⟩`
--      construction of the single-edge left arm becomes
--      `.forwardE h_E` (same edge witness, channel flips
--      orientation: input cell is `.backwardE h_E`, output single
--      step is `.forwardE h_E`);
-- (iii) the directed-hinge → generic-bifurcation conversion (decl 44)
--      collapses to `exact h` on the `.backwardE`-cons branch
--      because both `IsBifurcationDirectedHingeWithSplit`
--      and `IsBifurcationWithSplit` reduce to
--      `p.IsDirectedWalk` there (the original needed
--      `⟨Or.inl ⟨ha_eq, ha_E⟩, hp_dir⟩` to wrap the channel
--      disjunction);
-- (iv) the single-edge bidirected bifurcation witness (decl 46)
--      collapses to `trivial` because
--      `IsBifurcationWithSplit` on
--      `.cons _ (.bidir _) (.nil _ _), 0` is now `True` (the
--      original needed `⟨rfl, hLR⟩` for the
--      `a = (u, v) ∧ a ∈ G.L` disjunction-tag + L-membership).

set_option linter.style.longLine false in
/-- Refactor port of decl 42.  The typed-WalkStep refactor reshapes
the recursion: the cons-cell destructure drops the `(a, hStep)` pair
in favour of `s : WalkStep G u vMid`, and we case-split on
`s` before `i` / `p'`.  On `.forwardE _` and `.bidir _` arms the
hinge predicate uniformly reduces to `False`, dispatched with
`h_hinge.elim`.  On `.backwardE h_E`, the original
`let forwardStep := Or.inl ⟨ha_eq, Or.inl ha_mem⟩` building the
left-arm single-edge collapses to `.forwardE h_E` (same edge witness
`(vMid, u) ∈ G.E`; channel flips from backward-input to
forward-output).  The original's `obtain ⟨ha_eq, ha_mem, hp'_dir⟩
:= h_hinge` becomes `hp'_dir = h_hinge` directly at `i = 0`
(no destructure needed) and a no-op at `i = k + 1` (where
`h_hinge = p'.IsBifurcation...k` is passed straight to
`ih k h_hinge`). -/
lemma Walk.exists_arms_of_bifurcation_directed_hinge_strong
    {G : CDMG Node} {v w : Node} (p : Walk G v w) :
    ∀ (i : ℕ), p.IsBifurcationDirectedHingeWithSplit i →
      ∃ (c : Node) (L : Walk G c v) (R : Walk G c w),
        L.IsDirectedWalk ∧ R.IsDirectedWalk ∧
        L.length ≥ 1 ∧ R.length ≥ 1 ∧
        p.vertices[i + 1]? = some c ∧
        (∀ x ∈ L.vertices, x ∈ p.vertices.dropLast) ∧
        (∀ x ∈ R.vertices, x ∈ p.vertices.tail) ∧
        (∀ x ∈ L.vertices.dropLast, x ∈ p.vertices.tail) ∧
        (∀ x ∈ R.vertices.dropLast, x ∈ p.vertices.dropLast) := by
  induction p with
  | nil v hv =>
      intro i h_hinge
      exact h_hinge.elim
  | @cons u w vMid s p' ih =>
      intro i h_hinge
      cases s with
      | forwardE _ =>
          cases i with
          | zero =>
              cases p' with
              | nil _ _ => exact h_hinge.elim
              | cons _ _ _ => exact h_hinge.elim
          | succ _ =>
              cases p' with
              | nil _ _ => exact h_hinge.elim
              | cons _ _ _ => exact h_hinge.elim
      | bidir _ =>
          cases i with
          | zero =>
              cases p' with
              | nil _ _ => exact h_hinge.elim
              | cons _ _ _ => exact h_hinge.elim
          | succ _ =>
              cases p' with
              | nil _ _ => exact h_hinge.elim
              | cons _ _ _ => exact h_hinge.elim
      | backwardE h_E =>
          cases i with
          | zero =>
              cases p' with
              | nil _ _ => exact h_hinge.elim
              | cons vMid' s' p'' =>
                  -- h_hinge : (cons vMid' s' p'').IsDirectedWalk
                  have hp'_dir :
                      (Walk.cons vMid' s' p'').IsDirectedWalk := h_hinge
                  have hu_in_G : u ∈ G :=
                    WalkStep.source_mem (G := G)
                      (WalkStep.backwardE (u := u) (v := vMid) h_E)
                  refine ⟨vMid,
                          Walk.cons u (.forwardE h_E) (Walk.nil u hu_in_G),
                          Walk.cons vMid' s' p'',
                          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                  · -- L.IsDirectedWalk: the single forward-E
                    -- step then nil unfolds to (nil _ _).IsDirectedWalk = True.
                    trivial
                  · exact hp'_dir
                  · change 0 + 1 ≥ 1; exact Nat.le_refl 1
                  · change p''.length + 1 ≥ 1
                    exact Nat.succ_le_succ (Nat.zero_le _)
                  · rfl
                  · intro x hx
                    have hxv : x = vMid ∨ x = u := by
                      rcases List.mem_cons.mp hx with rfl | hx2
                      · exact Or.inl rfl
                      · rcases List.mem_cons.mp hx2 with rfl | hx3
                        · exact Or.inr rfl
                        · simp at hx3
                    have hp'_ne :
                        (Walk.cons vMid' s' p'').vertices ≠ [] :=
                      Walk.vertices_ne_nil _
                    have hp''_ne : p''.vertices ≠ [] :=
                      Walk.vertices_ne_nil _
                    change x ∈
                      (u :: (Walk.cons vMid' s' p'').vertices).dropLast
                    rw [List.dropLast_cons_of_ne_nil hp'_ne]
                    change x ∈ u :: (vMid :: p''.vertices).dropLast
                    rw [List.dropLast_cons_of_ne_nil hp''_ne]
                    rcases hxv with rfl | rfl
                    · exact List.mem_cons.mpr (Or.inr List.mem_cons_self)
                    · exact List.mem_cons_self
                  · intro x hx
                    change x ∈
                      (u :: (Walk.cons vMid' s' p'').vertices).tail
                    exact hx
                  · -- L.vertices.dropLast ⊆ p.vertices.tail
                    intro x hx
                    change x ∈ ([vMid, u] : List Node).dropLast at hx
                    change x ∈ vMid :: p''.vertices
                    simp [List.dropLast] at hx
                    subst hx
                    exact List.mem_cons_self
                  · -- R.vertices.dropLast ⊆ p.vertices.dropLast
                    intro x hx
                    have hp''_ne : p''.vertices ≠ [] :=
                      Walk.vertices_ne_nil _
                    change x ∈ (vMid :: p''.vertices).dropLast at hx
                    rw [List.dropLast_cons_of_ne_nil hp''_ne] at hx
                    have hp'_ne :
                        (Walk.cons vMid' s' p'').vertices ≠ [] :=
                      Walk.vertices_ne_nil _
                    change x ∈
                      (u :: (Walk.cons vMid' s' p'').vertices).dropLast
                    rw [List.dropLast_cons_of_ne_nil hp'_ne]
                    change x ∈ u :: (vMid :: p''.vertices).dropLast
                    rw [List.dropLast_cons_of_ne_nil hp''_ne]
                    exact List.mem_cons.mpr (Or.inr hx)
          | succ k =>
              cases p' with
              | nil _ _ => exact h_hinge.elim
              | cons vMid' s' p'' =>
                  -- h_hinge :
                  -- (cons vMid' s' p'').IsBifurcationDirectedHingeWithSplit k
                  have h_rec :
                      (Walk.cons vMid' s' p'').IsBifurcationDirectedHingeWithSplit k :=
                    h_hinge
                  obtain ⟨c, L', R, hL'_dir, hR_dir, _hL'_pos, hR_pos, h_idx_p',
                          hL'_sub, hR_sub, hL'_drop_sub, hR_drop_sub⟩ :=
                    ih k h_rec
                  have hu_in_G : u ∈ G :=
                    WalkStep.source_mem (G := G)
                      (WalkStep.backwardE (u := u) (v := vMid) h_E)
                  let single : Walk G vMid u :=
                    Walk.cons u (.forwardE h_E) (Walk.nil u hu_in_G)
                  have hsingle_dir : single.IsDirectedWalk := trivial
                  have hL_new_vs : (L'.comp single).vertices
                      = L'.vertices.dropLast ++ [vMid, u] := by
                    rw [Walk.vertices_comp]; rfl
                  have hp'_vs : (Walk.cons vMid' s' p'').vertices
                      = vMid :: p''.vertices := rfl
                  have hp'_ne :
                      (Walk.cons vMid' s' p'').vertices ≠ [] :=
                    Walk.vertices_ne_nil _
                  have hp''_ne : p''.vertices ≠ [] :=
                    Walk.vertices_ne_nil _
                  refine ⟨c, L'.comp single, R, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                  · exact Walk.isDirectedWalk_comp L' single hL'_dir hsingle_dir
                  · exact hR_dir
                  · rw [Walk.length_comp]
                    change L'.length + 1 ≥ 1
                    exact Nat.succ_le_succ (Nat.zero_le _)
                  · exact hR_pos
                  · change (u :: (Walk.cons vMid' s' p'').vertices)[k + 1 + 1]?
                          = some c
                    simpa using h_idx_p'
                  · intro x hx
                    rw [hL_new_vs] at hx
                    change x ∈
                      (u :: (Walk.cons vMid' s' p'').vertices).dropLast
                    rw [List.dropLast_cons_of_ne_nil hp'_ne]
                    change x ∈ u :: (vMid :: p''.vertices).dropLast
                    rw [List.dropLast_cons_of_ne_nil hp''_ne]
                    rcases List.mem_append.mp hx with hL'_drop | h_in_tail
                    · have hx_L'_vs : x ∈ L'.vertices :=
                        List.mem_of_mem_dropLast hL'_drop
                      have hx_p' : x ∈
                          (Walk.cons vMid' s' p'').vertices.dropLast :=
                        hL'_sub x hx_L'_vs
                      rw [hp'_vs] at hx_p'
                      rw [List.dropLast_cons_of_ne_nil hp''_ne] at hx_p'
                      exact List.mem_cons.mpr (Or.inr hx_p')
                    · rcases List.mem_cons.mp h_in_tail with rfl | hx_in2
                      · exact List.mem_cons.mpr (Or.inr List.mem_cons_self)
                      · rcases List.mem_cons.mp hx_in2 with rfl | hx_empty
                        · exact List.mem_cons_self
                        · simp at hx_empty
                  · intro x hx
                    have hx_p'_tail : x ∈
                        (Walk.cons vMid' s' p'').vertices.tail :=
                      hR_sub x hx
                    have hx_p' : x ∈ (Walk.cons vMid' s' p'').vertices :=
                      List.mem_of_mem_tail hx_p'_tail
                    change x ∈
                      (u :: (Walk.cons vMid' s' p'').vertices).tail
                    exact hx_p'
                  · -- L_new.vertices.dropLast ⊆ p.vertices.tail.
                    intro x hx
                    have hL_new_drop :
                        (L'.comp single).vertices.dropLast
                        = L'.vertices.dropLast ++ [vMid] := by
                      rw [hL_new_vs]
                      simp [List.dropLast]
                    rw [hL_new_drop] at hx
                    change x ∈
                      (u :: (Walk.cons vMid' s' p'').vertices).tail
                    change x ∈ (Walk.cons vMid' s' p'').vertices
                    rw [hp'_vs]
                    rcases List.mem_append.mp hx with hL'_drop | h_in_tail
                    · have hx_p'_tail : x ∈
                          (Walk.cons vMid' s' p'').vertices.tail :=
                        hL'_drop_sub x hL'_drop
                      exact List.mem_of_mem_tail hx_p'_tail
                    · rcases List.mem_cons.mp h_in_tail with rfl | hx_empty
                      · exact List.mem_cons_self
                      · simp at hx_empty
                  · intro x hx
                    have hx_p'_drop : x ∈
                        (Walk.cons vMid' s' p'').vertices.dropLast :=
                      hR_drop_sub x hx
                    rw [hp'_vs] at hx_p'_drop
                    rw [List.dropLast_cons_of_ne_nil hp''_ne] at hx_p'_drop
                    change x ∈
                      (u :: (Walk.cons vMid' s' p'').vertices).dropLast
                    rw [List.dropLast_cons_of_ne_nil hp'_ne]
                    change x ∈ u :: (vMid :: p''.vertices).dropLast
                    rw [List.dropLast_cons_of_ne_nil hp''_ne]
                    exact List.mem_cons.mpr (Or.inr hx_p'_drop)

set_option linter.style.longLine false in
/-- Refactor port of decl 43.  Body is mechanical: every walk-level
helper retargets to its `refactor_*` twin (`vertices`,
`length`, `vertices_mkBifurcation`,
`isBifurcationDirectedHinge_mkBifurcation`, etc.).  The
inner `induction qv with | @cons _ _ _ _ _ p' ih => ...` updates to
`| @cons _ _ _ _ p' ih => ...` (one fewer wildcard, reflecting the
dropped `a : Node × Node` field of `Walk.cons`). -/
lemma Walk.mkBifurcation_isBifurcationSource
    {G : CDMG Node} {c v w : Node}
    (qv : Walk G c v) (hqv_dir : qv.IsDirectedWalk)
    (hqv_pos : qv.length ≥ 1)
    (qw : Walk G c w) (hqw_dir : qw.IsDirectedWalk)
    (hqw_pos : qw.length ≥ 1)
    (hvw_ne : v ≠ w)
    (hv_qv_drop : v ∉ qv.vertices.dropLast)
    (hv_qw : v ∉ qw.vertices)
    (hw_qv : w ∉ qv.vertices)
    (hw_qw_drop : w ∉ qw.vertices.dropLast) :
    (Walk.mkBifurcation qv hqv_dir hqv_pos qw).IsBifurcationSource c := by
  have h_mk_vs :
      (Walk.mkBifurcation qv hqv_dir hqv_pos qw).vertices
        = qv.vertices.reverse.dropLast ++ qw.vertices :=
    Walk.vertices_mkBifurcation qv hqv_dir hqv_pos qw
  have h_qv_rev_drop :
      qv.vertices.reverse.dropLast = qv.vertices.tail.reverse :=
    Walk.vertices_reverse_dropLast qv
  have h_qv_tail_ne : qv.vertices.tail ≠ [] :=
    Walk.tail_vertices_ne_nil_of_pos qv hqv_pos
  have h_qv_rev_drop_ne : qv.vertices.reverse.dropLast ≠ [] := by
    rw [h_qv_rev_drop]
    intro hempty
    apply h_qv_tail_ne
    have : qv.vertices.tail = qv.vertices.tail.reverse.reverse := by
      rw [List.reverse_reverse]
    rw [this, hempty]; rfl
  have h_qw_vs_ne : qw.vertices ≠ [] := Walk.vertices_ne_nil qw
  have h_qw_drop_ne : qw.vertices.dropLast ≠ [] := by
    have h_qw_t_ne : qw.vertices.tail ≠ [] :=
      Walk.tail_vertices_ne_nil_of_pos qw hqw_pos
    intro hempty
    rw [Walk.vertices_eq_head_cons_tail qw] at hempty
    rw [List.dropLast_cons_of_ne_nil h_qw_t_ne] at hempty
    exact (List.cons_ne_nil _ _) hempty
  refine ⟨hvw_ne, ?_, ?_, ?_⟩
  · intro hv_in_tail
    rw [h_mk_vs] at hv_in_tail
    rw [List.tail_append_of_ne_nil h_qv_rev_drop_ne] at hv_in_tail
    rcases List.mem_append.mp hv_in_tail with hv_qv | hv_qw'
    · rw [h_qv_rev_drop] at hv_qv
      have h_aux : ∀ (l : List Node), l.reverse.tail = l.dropLast.reverse := by
        intro l
        induction l with
        | nil => rfl
        | cons a rest ih =>
            by_cases h : rest = []
            · subst h; rfl
            · rw [List.reverse_cons, List.dropLast_cons_of_ne_nil h]
              rw [List.reverse_cons]
              rw [List.tail_append_of_ne_nil]
              · rw [ih]
              · intro hr_empty
                exact h (List.reverse_eq_nil_iff.mp hr_empty)
      have h_t_rev_t : qv.vertices.tail.reverse.tail
          = qv.vertices.tail.dropLast.reverse :=
        h_aux qv.vertices.tail
      rw [h_t_rev_t] at hv_qv
      have hv_t_drop : v ∈ qv.vertices.tail.dropLast :=
        List.mem_reverse.mp hv_qv
      have h_t_drop_eq :
          qv.vertices.tail.dropLast = qv.vertices.dropLast.tail := by
        rw [Walk.vertices_eq_head_cons_tail qv]
        simp only [List.tail_cons]
        rw [List.dropLast_cons_of_ne_nil h_qv_tail_ne]
        rfl
      rw [h_t_drop_eq] at hv_t_drop
      exact hv_qv_drop (List.mem_of_mem_tail hv_t_drop)
    · exact hv_qw hv_qw'
  · intro hw_in_drop
    rw [h_mk_vs] at hw_in_drop
    rw [List.dropLast_append_of_ne_nil h_qw_vs_ne] at hw_in_drop
    rcases List.mem_append.mp hw_in_drop with hw_qv' | hw_qw_d
    · rw [h_qv_rev_drop] at hw_qv'
      have hw_t : w ∈ qv.vertices.tail := List.mem_reverse.mp hw_qv'
      exact hw_qv (List.mem_of_mem_tail hw_t)
    · exact hw_qw_drop hw_qw_d
  · refine ⟨qv.length - 1, ?_, ?_⟩
    · exact Walk.isBifurcationDirectedHinge_mkBifurcation
        qv hqv_dir hqv_pos qw hqw_dir hqw_pos
    · rw [h_mk_vs]
      have h_idx : qv.length - 1 + 1 = qv.length := by omega
      rw [h_idx]
      have h_rev_drop_len :
          qv.vertices.reverse.dropLast.length = qv.length := by
        rw [h_qv_rev_drop]
        rw [List.length_reverse]
        rw [Walk.vertices_eq_head_cons_tail qv]
        simp only [List.tail_cons]
        have h_len : qv.vertices.length = qv.length + 1 := by
          clear * -
          induction qv with
          | nil _ _ =>
              simp [Walk.vertices, Walk.length]
          | @cons _ _ _ _ p' ih =>
              simp [Walk.vertices, Walk.length]
              omega
        rw [Walk.vertices_eq_head_cons_tail qv] at h_len
        simp only [List.length_cons] at h_len
        omega
      rw [List.getElem?_append_right (by omega), h_rev_drop_len]
      simp
      rw [Walk.vertices_eq_head_cons_tail qw]
      simp

set_option linter.style.longLine false in
/-- A directed-hinge bifurcation walk is also a (generic, sourceless)
bifurcation walk at the same split index.

**Refactor port — significant simplification (R3 in the workspace
plan).**  Under the typed-WalkStep refactor, the `.backwardE`-cons
branch at `i = 0` reduces both
`IsBifurcationDirectedHingeWithSplit` and
`IsBifurcationWithSplit` to the SAME body
`p.IsDirectedWalk`, so the implication is just `exact h`
(the original needed `obtain ⟨ha_eq, ha_E, hp_dir⟩ := h` plus
`exact ⟨Or.inl ⟨ha_eq, ha_E⟩, hp_dir⟩` to dissolve the `Or`
channel-tag).  The `.backwardE`-cons branch at `i = k + 1`
similarly forwards directly to `ih k h` (the original's
`exact ⟨ha_eq, ha_E, ih k h_rest⟩` collapses).  All other
constructor / index combinations have both predicates equal to
`False`, dispatched via `h.elim`. -/
lemma Walk.isBifurcationDirectedHingeWithSplit_to_isBifurcationWithSplit
    {G : CDMG Node} {u v : Node} :
    ∀ (p : Walk G u v) (i : ℕ),
      p.IsBifurcationDirectedHingeWithSplit i →
      p.IsBifurcationWithSplit i := by
  intro p
  induction p with
  | nil _ _ => intro i h; exact h
  | @cons _ _ _ s p' ih =>
      intro i h
      cases s with
      | forwardE _ =>
          cases i with
          | zero =>
              cases p' with
              | nil _ _ => exact h.elim
              | cons _ _ _ => exact h.elim
          | succ _ =>
              cases p' with
              | nil _ _ => exact h.elim
              | cons _ _ _ => exact h.elim
      | bidir _ =>
          cases i with
          | zero =>
              cases p' with
              | nil _ _ => exact h.elim
              | cons _ _ _ => exact h.elim
          | succ _ =>
              cases p' with
              | nil _ _ => exact h.elim
              | cons _ _ _ => exact h.elim
      | backwardE _ =>
          cases i with
          | zero =>
              cases p' with
              | nil _ _ => exact h.elim
              | cons _ _ _ => exact h
          | succ k =>
              cases p' with
              | nil _ _ => exact h.elim
              | cons _ _ _ => exact ih k h

set_option linter.style.longLine false in
/-- `IsBifurcationSource` implies `IsBifurcation`:
just drop the source-tracking conjunct.  Refactor port: mechanical;
the inner forwarder is decl 44's `refactor_*` twin. -/
lemma Walk.isBifurcationSource_to_isBifurcation
    {G : CDMG Node} {u v : Node} (p : Walk G u v) (c : Node)
    (h : p.IsBifurcationSource c) : p.IsBifurcation := by
  obtain ⟨huv_ne, hu_tail, hv_drop, i, hh_dir, _⟩ := h
  refine ⟨huv_ne, hu_tail, hv_drop, i, ?_⟩
  exact Walk.isBifurcationDirectedHingeWithSplit_to_isBifurcationWithSplit
    p i hh_dir

set_option linter.style.longLine false in
/-- A single bidirected edge `s(u, v) ∈ G.L` gives a length-1 walk
`u → v` whose `IsBifurcation` predicate is satisfied (the
`n = 1` direct bidirected edge boundary case of `def_3_4` item~vi).

**Refactor port — significant simplification (R3 in the workspace
plan).**  Signature swaps `(hLR : (u, v) ∈ G.L)` for
`(hLR : s(u, v) ∈ G.L)` (Sym2 encoding of `L`).  The walk's
cons-cell witness `Or.inl ⟨rfl, Or.inr hLR⟩` of the original
collapses to the typed `.bidir hLR` constructor — no `let hStep`
ceremony, no `let`-bound binding needed at all.  The
`IsBifurcationWithSplit 0` witness on a single-edge bidir walk
used to be `⟨rfl, hLR⟩` (the `a = (u, v) ∧ a ∈ G.L`
disjunction-tag plus L-membership); under the refactor
`IsBifurcationWithSplit` on
`.cons _ (.bidir _) (.nil _ _), 0` reduces directly to `True`,
so `trivial` discharges the witness. -/
lemma Walk.singleEdge_isBifurcation_of_bidir
    {G : CDMG Node} {u v : Node} (_hu : u ∈ G) (hv : v ∈ G)
    (hLR : s(u, v) ∈ G.L) (huv : u ≠ v) :
    (Walk.cons v (.bidir hLR) (Walk.nil v hv)).IsBifurcation := by
  refine ⟨huv, ?_, ?_, 0, ?_⟩
  · intro h_in_tail
    change u ∈ [v] at h_in_tail
    rw [List.mem_singleton] at h_in_tail
    exact huv h_in_tail
  · intro h_in_drop
    change v ∈ ([u, v] : List Node).dropLast at h_in_drop
    simp [List.dropLast] at h_in_drop
    exact huv.symm h_in_drop
  · -- IsBifurcationWithSplit on `.cons _ (.bidir _) (.nil _ _), 0`
    -- reduces directly to `True`.
    trivial

set_option linter.style.longLine false in
/-- Refactor port of decl 47 (sourceless mirror of decl 42).  The
typed-WalkStep refactor restructures the original
`match i, p', h_bif, h_not_dir` 4-way pattern as a nested
`cases s` / `cases i` / `cases p'`.  The `.forwardE` arm
uniformly reduces `h_bif` to `False` (dispatched with
`h_bif.elim`).  The `.backwardE` arm at `i = 0`, `p' = cons`
collapses `h_bif` (which reduces to
`p'.IsDirectedWalk`) against `h_not_dir` (which
reduces to `¬ p'.IsDirectedWalk`) via `absurd`; at
`i = k + 1`, `p' = cons` it recurses with `h_bif` / `h_not_dir`
carried through directly, building the single forward edge via
`.forwardE h_E` (mirroring decl 42's backwardE-step → forwardE-arm
construction).  The `.bidir` arm at `i = 0`, `p' = nil` is the
new n=1 single-edge case: the original's
`obtain ⟨ha_eq, ha_L⟩ := h_bif` extracting `(u, v_nil) ∈ G.L`
collapses to the `.bidir h_L` constructor's stored witness
`h_L : s(u, v_nil) ∈ G.L` (R3/R5 simplification: `h_bif`
literally `True`).  The original's
`hv_nil_g : v_nil ∈ G := Finset.mem_union_right _ ((G.hL_subset _).2)`
detour disappears — the nil cell hands us `hv_nil : v_nil ∈ G`
directly.  The `.bidir` arm at `i = 0`, `p' = cons` is the
n≥2 hinge-at-index-0 case: the original's `rcases h_alt` to
pick the L-disjunct is replaced by the `.bidir` constructor
pinning the L-channel directly (the E-disjunct case is now
the `.backwardE` arm and is dispatched in its own branch).
The `.bidir` arm at `i = k + 1` is uniformly vacuous —
`IsBifurcationWithSplit` on `.cons _ (.bidir _) _, k + 1`
reduces to `False`. -/
lemma Walk.exists_arms_of_bifurcation_bidir_hinge_strong
    {G : CDMG Node} {v w : Node} (p : Walk G v w) :
    ∀ (i : ℕ), p.IsBifurcationWithSplit i →
      ¬ p.IsBifurcationDirectedHingeWithSplit i →
      ∃ (vL vR : Node) (L : Walk G vL v) (R : Walk G vR w),
        L.IsDirectedWalk ∧ R.IsDirectedWalk ∧
        s(vL, vR) ∈ G.L ∧
        p.vertices[i + 1]? = some vR ∧
        (∀ x ∈ L.vertices, x ∈ p.vertices.dropLast) ∧
        (∀ x ∈ R.vertices, x ∈ p.vertices.tail) ∧
        (∀ x ∈ L.vertices.dropLast, x ∈ p.vertices.tail) ∧
        (∀ x ∈ R.vertices.dropLast, x ∈ p.vertices.dropLast) := by
  induction p with
  | nil _ _ =>
      intro i h_bif _
      exact h_bif.elim
  | @cons u w vMid s p' ih =>
      intro i h_bif h_not_dir
      cases s with
      | forwardE _ =>
          cases i with
          | zero =>
              cases p' with
              | nil _ _ => exact h_bif.elim
              | cons _ _ _ => exact h_bif.elim
          | succ _ =>
              cases p' with
              | nil _ _ => exact h_bif.elim
              | cons _ _ _ => exact h_bif.elim
      | backwardE h_E =>
          cases i with
          | zero =>
              cases p' with
              | nil _ _ => exact h_bif.elim
              | cons vMid' s' p'' =>
                  -- h_bif : (cons vMid' s' p'').IsDirectedWalk
                  -- h_not_dir : ¬ (cons vMid' s' p'').IsDirectedWalk
                  -- (IsBifurcationDirectedHingeWithSplit on .cons _ (.backwardE _)
                  --  (p@(.cons _ _ _)), 0 reduces to p.IsDirectedWalk —
                  --  same as IsBifurcationWithSplit there.)
                  exact absurd h_bif h_not_dir
          | succ k =>
              cases p' with
              | nil _ _ => exact h_bif.elim
              | cons vMid' s' p'' =>
                  -- h_bif :
                  -- (cons vMid' s' p'').IsBifurcationWithSplit k
                  -- h_not_dir :
                  -- ¬ (cons vMid' s' p'').IsBifurcationDirectedHingeWithSplit k
                  have h_rec :
                      (Walk.cons vMid' s' p'').IsBifurcationWithSplit k :=
                    h_bif
                  have h_rec_not_dir :
                      ¬ (Walk.cons vMid' s' p'').IsBifurcationDirectedHingeWithSplit k :=
                    h_not_dir
                  obtain ⟨vL, vR, L', R, hL'_dir, hR_dir, hLR_L, h_idx_p',
                          hL'_sub, hR_sub, hL'_drop_sub, hR_drop_sub⟩ :=
                    ih k h_rec h_rec_not_dir
                  -- Build L = L'.comp (single forward-E from vMid to u).
                  have hu_in_G : u ∈ G :=
                    WalkStep.source_mem (G := G)
                      (WalkStep.backwardE (u := u) (v := vMid) h_E)
                  let single : Walk G vMid u :=
                    Walk.cons u (.forwardE h_E) (Walk.nil u hu_in_G)
                  have hsingle_dir : single.IsDirectedWalk := trivial
                  have hL_new_vs : (L'.comp single).vertices
                      = L'.vertices.dropLast ++ [vMid, u] := by
                    rw [Walk.vertices_comp]; rfl
                  have hp'_vs : (Walk.cons vMid' s' p'').vertices
                      = vMid :: p''.vertices := rfl
                  have hp'_ne :
                      (Walk.cons vMid' s' p'').vertices ≠ [] :=
                    Walk.vertices_ne_nil _
                  have hp''_ne : p''.vertices ≠ [] :=
                    Walk.vertices_ne_nil _
                  refine ⟨vL, vR, L'.comp single, R, ?_, hR_dir, hLR_L,
                          ?_, ?_, ?_, ?_, ?_⟩
                  · exact Walk.isDirectedWalk_comp L' single hL'_dir hsingle_dir
                  · -- p.vertices[k+1+1]? = some vR.
                    change (u :: (Walk.cons vMid' s' p'').vertices)[k + 1 + 1]?
                          = some vR
                    simpa using h_idx_p'
                  · -- L_new.vertices ⊆ p.vertices.dropLast.
                    intro x hx
                    rw [hL_new_vs] at hx
                    change x ∈
                      (u :: (Walk.cons vMid' s' p'').vertices).dropLast
                    rw [List.dropLast_cons_of_ne_nil hp'_ne]
                    change x ∈ u :: (vMid :: p''.vertices).dropLast
                    rw [List.dropLast_cons_of_ne_nil hp''_ne]
                    rcases List.mem_append.mp hx with hL'_drop | h_in_tail
                    · have hx_L'_vs : x ∈ L'.vertices :=
                        List.mem_of_mem_dropLast hL'_drop
                      have hx_p' : x ∈
                          (Walk.cons vMid' s' p'').vertices.dropLast :=
                        hL'_sub x hx_L'_vs
                      rw [hp'_vs] at hx_p'
                      rw [List.dropLast_cons_of_ne_nil hp''_ne] at hx_p'
                      exact List.mem_cons.mpr (Or.inr hx_p')
                    · rcases List.mem_cons.mp h_in_tail with rfl | hx_in2
                      · exact List.mem_cons.mpr (Or.inr List.mem_cons_self)
                      · rcases List.mem_cons.mp hx_in2 with rfl | hx_empty
                        · exact List.mem_cons_self
                        · simp at hx_empty
                  · -- R.vertices ⊆ p.vertices.tail.
                    intro x hx
                    have hx_p'_tail : x ∈
                        (Walk.cons vMid' s' p'').vertices.tail :=
                      hR_sub x hx
                    have hx_p' : x ∈ (Walk.cons vMid' s' p'').vertices :=
                      List.mem_of_mem_tail hx_p'_tail
                    change x ∈
                      (u :: (Walk.cons vMid' s' p'').vertices).tail
                    exact hx_p'
                  · -- L_new.vertices.dropLast ⊆ p.vertices.tail.
                    intro x hx
                    have hL_new_drop : (L'.comp single).vertices.dropLast
                        = L'.vertices.dropLast ++ [vMid] := by
                      rw [hL_new_vs]
                      simp [List.dropLast]
                    rw [hL_new_drop] at hx
                    change x ∈
                      (u :: (Walk.cons vMid' s' p'').vertices).tail
                    change x ∈ (Walk.cons vMid' s' p'').vertices
                    rw [hp'_vs]
                    rcases List.mem_append.mp hx with hL'_drop | h_in_tail
                    · have hx_p'_tail : x ∈
                          (Walk.cons vMid' s' p'').vertices.tail :=
                        hL'_drop_sub x hL'_drop
                      exact List.mem_of_mem_tail hx_p'_tail
                    · rcases List.mem_cons.mp h_in_tail with rfl | hx_empty
                      · exact List.mem_cons_self
                      · simp at hx_empty
                  · -- R.vertices.dropLast ⊆ p.vertices.dropLast.
                    intro x hx
                    have hx_p'_drop : x ∈
                        (Walk.cons vMid' s' p'').vertices.dropLast :=
                      hR_drop_sub x hx
                    rw [hp'_vs] at hx_p'_drop
                    rw [List.dropLast_cons_of_ne_nil hp''_ne] at hx_p'_drop
                    change x ∈
                      (u :: (Walk.cons vMid' s' p'').vertices).dropLast
                    rw [List.dropLast_cons_of_ne_nil hp'_ne]
                    change x ∈ u :: (vMid :: p''.vertices).dropLast
                    rw [List.dropLast_cons_of_ne_nil hp''_ne]
                    exact List.mem_cons.mpr (Or.inr hx_p'_drop)
      | bidir h_L =>
          cases i with
          | zero =>
              cases p' with
              | nil _ hv_w =>
                  -- n=1 bidirected single-edge case.
                  -- Lean's `cases p'` unifies the nil's endpoint with both
                  -- `vMid` and `w` (since `p' : Walk G vMid w`); the
                  -- surviving local is `w` (vMid substituted to w via Lean's
                  -- elimination preference for the cons-cell's existentials).
                  -- s = .bidir h_L, h_L : s(u, w) ∈ G.L (vMid := w substituted).
                  -- h_bif : True (IsBifurcationWithSplit on
                  --  .cons _ (.bidir _) (.nil _ _), 0 reduces to True).
                  -- — R3/R5 simplification: no h_bif destructure needed.
                  -- hv_w : w ∈ G (from nil's witness — no hL_subset dance).
                  have hu_g : u ∈ G :=
                    WalkStep.source_mem (G := G)
                      (WalkStep.bidir (u := u) (v := w) h_L)
                  refine ⟨u, w, Walk.nil u hu_g,
                          Walk.nil w hv_w,
                          trivial, trivial, h_L, ?_, ?_, ?_, ?_, ?_⟩
                  · -- p.vertices[1]? = some w.
                    -- p.vertices = [u, w].
                    rfl
                  · -- L.vertices = [u] ⊆ p.vertices.dropLast = [u].
                    intro x hx
                    change x ∈ [u] at hx
                    rw [List.mem_singleton] at hx
                    rw [hx]
                    change u ∈ ([u, w] : List Node).dropLast
                    simp [List.dropLast]
                  · -- R.vertices = [w] ⊆ p.vertices.tail = [w].
                    intro x hx
                    change x ∈ [w] at hx
                    rw [List.mem_singleton] at hx
                    rw [hx]
                    change w ∈ ([u, w] : List Node).tail
                    simp [List.tail]
                  · -- L.vertices.dropLast = [u].dropLast = [], vacuously ⊆.
                    intro x hx
                    change x ∈ ([u] : List Node).dropLast at hx
                    simp [List.dropLast] at hx
                  · -- R.vertices.dropLast = [w].dropLast = [], vacuously ⊆.
                    intro x hx
                    change x ∈ ([w] : List Node).dropLast at hx
                    simp [List.dropLast] at hx
              | cons vMid' s' p'' =>
                  -- n≥2 case, bidir hinge at index 0.
                  -- s = .bidir h_L, h_L : s(u, vMid) ∈ G.L
                  -- h_bif : (cons vMid' s' p'').IsDirectedWalk
                  -- — R5 simplification: the original's h_alt destructure
                  -- collapses because the .bidir constructor pins the L-channel
                  -- (the .backwardE branch is dispatched in its own arm above).
                  have hp'_dir :
                      (Walk.cons vMid' s' p'').IsDirectedWalk := h_bif
                  have hu_g : u ∈ G :=
                    WalkStep.source_mem (G := G)
                      (WalkStep.bidir (u := u) (v := vMid) h_L)
                  refine ⟨u, vMid, Walk.nil u hu_g,
                          Walk.cons vMid' s' p'',
                          trivial, hp'_dir, h_L, ?_, ?_, ?_, ?_, ?_⟩
                  · -- p.vertices[1]? = some vMid.
                    rfl
                  · -- L.vertices = [u] ⊆ p.vertices.dropLast.
                    intro x hx
                    change x ∈ [u] at hx
                    rw [List.mem_singleton] at hx
                    rw [hx]
                    have hp'_ne :
                        (Walk.cons vMid' s' p'').vertices ≠ [] :=
                      Walk.vertices_ne_nil _
                    change u ∈
                      (u :: (Walk.cons vMid' s' p'').vertices).dropLast
                    rw [List.dropLast_cons_of_ne_nil hp'_ne]
                    exact List.mem_cons_self
                  · -- R.vertices ⊆ p.vertices.tail
                    -- = (cons ...).vertices.
                    intro x hx
                    change x ∈
                      (u :: (Walk.cons vMid' s' p'').vertices).tail
                    exact hx
                  · -- L.vertices.dropLast = [u].dropLast = [], vacuously ⊆.
                    intro x hx
                    change x ∈ ([u] : List Node).dropLast at hx
                    simp [List.dropLast] at hx
                  · -- R.vertices.dropLast ⊆ p.vertices.dropLast.
                    intro x hx
                    have hp''_ne : p''.vertices ≠ [] :=
                      Walk.vertices_ne_nil _
                    change x ∈ (vMid :: p''.vertices).dropLast at hx
                    rw [List.dropLast_cons_of_ne_nil hp''_ne] at hx
                    have hp'_ne :
                        (Walk.cons vMid' s' p'').vertices ≠ [] :=
                      Walk.vertices_ne_nil _
                    change x ∈
                      (u :: (Walk.cons vMid' s' p'').vertices).dropLast
                    rw [List.dropLast_cons_of_ne_nil hp'_ne]
                    change x ∈ u :: (vMid :: p''.vertices).dropLast
                    rw [List.dropLast_cons_of_ne_nil hp''_ne]
                    exact List.mem_cons.mpr (Or.inr hx)
          | succ _ =>
              cases p' with
              | nil _ _ => exact h_bif.elim
              | cons _ _ _ => exact h_bif.elim

-- ## Refactor replacements — Batch 9 (declarations 48–55)
--
-- Two source-tracking forward / backward helpers for sub-claim ii(b)
-- (`marg_preserves_bifSource_forward` /
-- `marg_preserves_bifSource_backward`), two mechanical
-- wrappers `marg_bif_forward_dir_hinge_src_marg` /
-- `marg_bif_backward_dir_hinge` reducing sub-claim ii(a)
-- (directed-hinge case) to ii(b), and four list-/walk-bookkeeping
-- helpers (`Walk.vertices_getLast`,
-- `Walk.tail_getLast_of_pos`,
-- `Walk.length_pos_of_isBifurcation`,
-- `Walk.arm_dropLast_in_W`) used uniformly by the
-- backward-direction bidirected-hinge case (Batch 10) to discharge
-- the vertex-bound clauses on the extracted arms.
--
-- All eight are mechanical ports against the typed-`WalkStep`
-- + `Walk.cons _ s p` 3-arg cons cell.  The cons-skip pattern
-- `.cons _ _ _ _` collapses to `.cons _ _ _` everywhere, and every
-- helper retargets to its `refactor_*` twin.

/-- Refactor port of decl 48.  Mechanical: every walk-level helper
retargets to its `refactor_*` twin
(`Walk.exists_arms_of_bifurcation_directed_hinge_strong`,
`Walk.vertices_eq_head_cons_tail`,
`Walk.tail_vertices_ne_nil_of_pos`,
`project_directed_walk_strong`,
`Walk.length_pos_of_ne`,
`Walk.mkBifurcation`,
`Walk.mkBifurcation_isBifurcationSource`);
`G.marginalize` → `G.marginalize`;
`.vertices` → `.vertices`.  No structural changes. -/
lemma marg_preserves_bifSource_forward (G : CDMG Node)
    (W : Finset Node) (hW : W ⊆ G.V) {u w v₃ : Node}
    (hu : u ∈ G.marginalize W hW) (hw : w ∈ G.marginalize W hW)
    (hv₃ : v₃ ∈ G.marginalize W hW)
    (h : ∃ p : Walk G u w, p.IsBifurcationSource v₃) :
    ∃ q : Walk (G.marginalize W hW) u w,
      q.IsBifurcationSource v₃ := by
  obtain ⟨p, hp_src⟩ := h
  obtain ⟨huw_ne, hu_tail, hw_drop, i, hhinge, hsrc⟩ := hp_src
  obtain ⟨c, L, R, hL_dir, hR_dir, hL_pos, hR_pos, hidx,
          hL_sub, hR_sub, hL_drop_sub, hR_drop_sub⟩ :=
    Walk.exists_arms_of_bifurcation_directed_hinge_strong p i hhinge
  have hc_eq_v3 : c = v₃ := by
    rw [hidx] at hsrc
    exact Option.some.inj hsrc
  -- v₃ ≠ u via L.vertices.dropLast ⊆ p.vertices.tail + hu_tail.
  have hv3_ne_u : v₃ ≠ u := by
    intro heq
    have h_c_drop : c ∈ L.vertices.dropLast := by
      have hL_vs : L.vertices = c :: L.vertices.tail :=
        Walk.vertices_eq_head_cons_tail L
      have h_t_ne : L.vertices.tail ≠ [] :=
        Walk.tail_vertices_ne_nil_of_pos L hL_pos
      rw [hL_vs]
      rw [List.dropLast_cons_of_ne_nil h_t_ne]
      exact List.mem_cons_self
    have h_c_p_tail : c ∈ p.vertices.tail := hL_drop_sub c h_c_drop
    have hc_eq_u : c = u := hc_eq_v3.trans heq
    exact hu_tail (hc_eq_u ▸ h_c_p_tail)
  have hv3_ne_w : v₃ ≠ w := by
    intro heq
    have h_c_drop : c ∈ R.vertices.dropLast := by
      have hR_vs : R.vertices = c :: R.vertices.tail :=
        Walk.vertices_eq_head_cons_tail R
      have h_t_ne : R.vertices.tail ≠ [] :=
        Walk.tail_vertices_ne_nil_of_pos R hR_pos
      rw [hR_vs]
      rw [List.dropLast_cons_of_ne_nil h_t_ne]
      exact List.mem_cons_self
    have h_c_p_drop : c ∈ p.vertices.dropLast := hR_drop_sub c h_c_drop
    have hc_eq_w : c = w := hc_eq_v3.trans heq
    exact hw_drop (hc_eq_w ▸ h_c_p_drop)
  have hc_marg : c ∈ G.marginalize W hW := hc_eq_v3 ▸ hv₃
  obtain ⟨L', hL'_dir, hL'_sub, hL'_drop, _⟩ :=
    project_directed_walk_strong L hL_dir hc_marg hu
  obtain ⟨R', hR'_dir, hR'_sub, hR'_drop, _⟩ :=
    project_directed_walk_strong R hR_dir hc_marg hw
  have hL'_pos : L'.length ≥ 1 :=
    Walk.length_pos_of_ne L' (hc_eq_v3 ▸ hv3_ne_u)
  have hR'_pos : R'.length ≥ 1 :=
    Walk.length_pos_of_ne R' (hc_eq_v3 ▸ hv3_ne_w)
  -- Verify the four vertex-bound conditions for the generic mkBif lemma.
  have hu_notin_L'_drop : u ∉ L'.vertices.dropLast := fun h_u =>
    hu_tail (hL_drop_sub u (hL'_drop u h_u))
  have hu_notin_R' : u ∉ R'.vertices := fun h_u =>
    hu_tail (hR_sub u (hR'_sub u h_u))
  have hw_notin_L' : w ∉ L'.vertices := fun h_w =>
    hw_drop (hL_sub w (hL'_sub w h_w))
  have hw_notin_R'_drop : w ∉ R'.vertices.dropLast := fun h_w =>
    hw_drop (hR_drop_sub w (hR'_drop w h_w))
  refine ⟨Walk.mkBifurcation L' hL'_dir hL'_pos R', ?_⟩
  have h_bif_src :=
    Walk.mkBifurcation_isBifurcationSource
      L' hL'_dir hL'_pos R' hR'_dir hR'_pos
      huw_ne hu_notin_L'_drop hu_notin_R' hw_notin_L' hw_notin_R'_drop
  exact hc_eq_v3 ▸ h_bif_src

/-- Refactor port of decl 49.  Mirrors (48) on the backward direction:
expand `Lq` / `Rq` from the marg-walk into `L` / `R` in `G` via
`expand_directed_walk_marginalize`, then assemble via
`Walk.mkBifurcation`.  Mechanical port — same
retarget pattern as (48), plus
`expand_directed_walk_marginalize` → `expand_directed_walk_marginalize`
and `notW_of_mem_marginalize` → `notW_of_mem_marginalize`. -/
lemma marg_preserves_bifSource_backward (G : CDMG Node)
    (W : Finset Node) (hW : W ⊆ G.V) {u w v₃ : Node}
    (hu : u ∈ G.marginalize W hW) (hw : w ∈ G.marginalize W hW)
    (hv₃ : v₃ ∈ G.marginalize W hW)
    (h : ∃ q : Walk (G.marginalize W hW) u w,
            q.IsBifurcationSource v₃) :
    ∃ p : Walk G u w, p.IsBifurcationSource v₃ := by
  obtain ⟨q, hq_src⟩ := h
  obtain ⟨huw_ne, hu_tail, hw_drop, i, hhinge, hsrc⟩ := hq_src
  obtain ⟨c, Lq, Rq, hLq_dir, hRq_dir, hLq_pos, hRq_pos, hidx,
          hLq_sub, hRq_sub, hLq_drop_sub, hRq_drop_sub⟩ :=
    Walk.exists_arms_of_bifurcation_directed_hinge_strong q i hhinge
  have hc_eq_v3 : c = v₃ := by
    rw [hidx] at hsrc
    exact Option.some.inj hsrc
  -- v₃ ≠ u, v₃ ≠ w (analogous to forward direction).
  have hv3_ne_u : v₃ ≠ u := by
    intro heq
    have h_c_drop : c ∈ Lq.vertices.dropLast := by
      have hLq_vs : Lq.vertices = c :: Lq.vertices.tail :=
        Walk.vertices_eq_head_cons_tail Lq
      have h_t_ne : Lq.vertices.tail ≠ [] :=
        Walk.tail_vertices_ne_nil_of_pos Lq hLq_pos
      rw [hLq_vs]
      rw [List.dropLast_cons_of_ne_nil h_t_ne]
      exact List.mem_cons_self
    have h_c_q_tail : c ∈ q.vertices.tail := hLq_drop_sub c h_c_drop
    have hc_eq_u : c = u := hc_eq_v3.trans heq
    exact hu_tail (hc_eq_u ▸ h_c_q_tail)
  have hv3_ne_w : v₃ ≠ w := by
    intro heq
    have h_c_drop : c ∈ Rq.vertices.dropLast := by
      have hRq_vs : Rq.vertices = c :: Rq.vertices.tail :=
        Walk.vertices_eq_head_cons_tail Rq
      have h_t_ne : Rq.vertices.tail ≠ [] :=
        Walk.tail_vertices_ne_nil_of_pos Rq hRq_pos
      rw [hRq_vs]
      rw [List.dropLast_cons_of_ne_nil h_t_ne]
      exact List.mem_cons_self
    have h_c_q_drop : c ∈ q.vertices.dropLast := hRq_drop_sub c h_c_drop
    have hc_eq_w : c = w := hc_eq_v3.trans heq
    exact hw_drop (hc_eq_w ▸ h_c_q_drop)
  -- Expand Lq and Rq to walks in G.
  obtain ⟨L, hL_dir, hL_len, hL_sub_W, hL_drop_sub_W, _, _⟩ :=
    expand_directed_walk_marginalize Lq hLq_dir
  obtain ⟨R, hR_dir, hR_len, hR_sub_W, hR_drop_sub_W, _, _⟩ :=
    expand_directed_walk_marginalize Rq hRq_dir
  have hL_pos : L.length ≥ 1 := by omega
  have hR_pos : R.length ≥ 1 := by omega
  -- Auxiliary: c ∉ W (since c = v₃ ∈ marg).
  have hc_notW : c ∉ W := by
    rw [hc_eq_v3]
    exact notW_of_mem_marginalize hW hv₃
  have hu_notW : u ∉ W := notW_of_mem_marginalize hW hu
  have hw_notW : w ∉ W := notW_of_mem_marginalize hW hw
  -- Verify the four conditions.
  have hu_notin_L_drop : u ∉ L.vertices.dropLast := by
    intro h_u
    rcases hL_drop_sub_W u h_u with h_Lq_drop | h_u_W
    · exact hu_tail (hLq_drop_sub u h_Lq_drop)
    · exact hu_notW h_u_W
  have hu_notin_R : u ∉ R.vertices := by
    intro h_u
    rcases hR_sub_W u h_u with h_Rq | h_u_W
    · exact hu_tail (hRq_sub u h_Rq)
    · exact hu_notW h_u_W
  have hw_notin_L : w ∉ L.vertices := by
    intro h_w
    rcases hL_sub_W w h_w with h_Lq | h_w_W
    · exact hw_drop (hLq_sub w h_Lq)
    · exact hw_notW h_w_W
  have hw_notin_R_drop : w ∉ R.vertices.dropLast := by
    intro h_w
    rcases hR_drop_sub_W w h_w with h_Rq_drop | h_w_W
    · exact hw_drop (hRq_drop_sub w h_Rq_drop)
    · exact hw_notW h_w_W
  refine ⟨Walk.mkBifurcation L hL_dir hL_pos R, ?_⟩
  have h_bif_src :=
    Walk.mkBifurcation_isBifurcationSource
      L hL_dir hL_pos R hR_dir hR_pos
      huw_ne hu_notin_L_drop hu_notin_R hw_notin_L hw_notin_R_drop
  exact hc_eq_v3 ▸ h_bif_src

/-- Refactor port of decl 50.  Mechanical wrapper: assemble
`IsBifurcationSource c` from `IsBifurcation` + the directed-hinge
witness, dispatch to (48)'s `marg_preserves_bifSource_forward`,
then convert back via
`Walk.isBifurcationSource_to_isBifurcation`. -/
lemma marg_bif_forward_dir_hinge_src_marg
    (G : CDMG Node) (W : Finset Node) (hW : W ⊆ G.V) {u w : Node}
    (hu : u ∈ G.marginalize W hW) (hw : w ∈ G.marginalize W hW)
    {p : Walk G u w} (hp : p.IsBifurcation)
    {i : ℕ} (h_dir : p.IsBifurcationDirectedHingeWithSplit i)
    {c : Node} (hidx : p.vertices[i + 1]? = some c)
    (hc_marg : c ∈ G.marginalize W hW) :
    ∃ q : Walk (G.marginalize W hW) u w, q.IsBifurcation := by
  obtain ⟨huw_ne, hu_tail, hw_drop, _, _⟩ := hp
  have hp_src : p.IsBifurcationSource c :=
    ⟨huw_ne, hu_tail, hw_drop, i, h_dir, hidx⟩
  obtain ⟨q, hq_src⟩ :=
    marg_preserves_bifSource_forward G W hW hu hw hc_marg ⟨p, hp_src⟩
  exact ⟨q, Walk.isBifurcationSource_to_isBifurcation q c hq_src⟩

/-- Refactor port of decl 51.  Mechanical wrapper: extract the
hinge-source `c` from the directed-hinge witness via
`Walk.exists_arms_of_bifurcation_directed_hinge_strong`,
note `c ∈ marg` automatically (every vertex of a marg-walk lies in marg
via `Walk.mem_of_mem_vertices`), dispatch to (49)'s
`marg_preserves_bifSource_backward`, then convert back via
`Walk.isBifurcationSource_to_isBifurcation`. -/
lemma marg_bif_backward_dir_hinge
    (G : CDMG Node) (W : Finset Node) (hW : W ⊆ G.V) {u w : Node}
    (hu : u ∈ G.marginalize W hW) (hw : w ∈ G.marginalize W hW)
    {q : Walk (G.marginalize W hW) u w} (hq : q.IsBifurcation)
    {i : ℕ} (h_dir : q.IsBifurcationDirectedHingeWithSplit i) :
    ∃ p : Walk G u w, p.IsBifurcation := by
  obtain ⟨huw_ne, hu_tail, hw_drop, _, _⟩ := hq
  obtain ⟨c, _, _, _, _, _, _, hidx, _, _, _, _⟩ :=
    Walk.exists_arms_of_bifurcation_directed_hinge_strong q i h_dir
  have hc_in_q : c ∈ q.vertices := List.mem_of_getElem? hidx
  have hc_marg : c ∈ G.marginalize W hW :=
    Walk.mem_of_mem_vertices q hc_in_q
  have hq_src : q.IsBifurcationSource c :=
    ⟨huw_ne, hu_tail, hw_drop, i, h_dir, hidx⟩
  obtain ⟨p, hp_src⟩ :=
    marg_preserves_bifSource_backward G W hW hu hw hc_marg ⟨q, hq_src⟩
  exact ⟨p, Walk.isBifurcationSource_to_isBifurcation p c hp_src⟩

/-- The last vertex of any walk equals its target.  Refactor port:
cons-skip pattern shifts from `.cons _ _ _ p'` (4 args) to
`.cons _ _ p'` (3 args). -/
lemma Walk.vertices_getLast {G : CDMG Node} :
    ∀ {u v : Node} (p : Walk G u v),
      p.vertices.getLast (Walk.vertices_ne_nil p) = v
  | _, _, .nil _ _ => rfl
  | _, _, .cons _ _ p' => by
      simp only [Walk.vertices]
      rw [List.getLast_cons (Walk.vertices_ne_nil p')]
      exact Walk.vertices_getLast p'

/-- For a walk with `length ≥ 1`, its vertex list's tail
ends at the target.  Refactor port: the `@cons` constructor's
explicit-arg arity drops by one (no stored ordered pair `a` plus
prop witness `hStep`), and the body retargets to the
`refactor_*` twins of `vertices_getLast` and `length`. -/
lemma Walk.tail_getLast_of_pos {G : CDMG Node} {u v : Node}
    (p : Walk G u v) (hp_pos : p.length ≥ 1) :
    p.vertices.tail.getLast
        (Walk.tail_vertices_ne_nil_of_pos p hp_pos) = v := by
  cases p with
  | nil _ _ => simp [Walk.length] at hp_pos
  | @cons u' v' vMid s p' =>
      show p'.vertices.getLast _ = v
      exact Walk.vertices_getLast p'

/-- `M.IsBifurcation → M.length ≥ 1`.  Refactor port:
cons-skip pattern shifts from `.cons _ _ _ _` (4 wildcards) to
`.cons _ _ _` (3 wildcards). -/
lemma Walk.length_pos_of_isBifurcation
    {G : CDMG Node} {u v : Node}
    {M : Walk G u v} (hM : M.IsBifurcation) :
    M.length ≥ 1 := by
  obtain ⟨_, _, _, _, h_split⟩ := hM
  cases M with
  | nil _ _ => exact h_split.elim
  | cons _ _ _ => exact Nat.succ_le_succ (Nat.zero_le _)

/-- Helper for the backward bidirected case:
`arm.vertices.dropLast ⊆ W`, given direct bounds on
`arm.vertices.dropLast` into both `M.vertices.tail`
and `M.vertices.dropLast`.  Refactor port: mechanical retarget
of every walk-level helper to its `refactor_*` twin. -/
lemma Walk.arm_dropLast_in_W {G : CDMG Node} {a b : Node}
    {M : Walk G a b} (hM_bif : M.IsBifurcation)
    {W : Finset Node}
    (hM_W : ∀ x ∈ M.vertices.tail.dropLast, x ∈ W)
    {c d : Node} {arm : Walk G c d}
    (h_arm_drop_in_tail :
        ∀ x ∈ arm.vertices.dropLast, x ∈ M.vertices.tail)
    (h_arm_drop_in_drop :
        ∀ x ∈ arm.vertices.dropLast, x ∈ M.vertices.dropLast) :
    ∀ x ∈ arm.vertices.dropLast, x ∈ W := by
  intro x hx
  have hM_pos : M.length ≥ 1 :=
    Walk.length_pos_of_isBifurcation hM_bif
  have h_M_tail_ne : M.vertices.tail ≠ [] :=
    Walk.tail_vertices_ne_nil_of_pos M hM_pos
  have h_M_tail_last : M.vertices.tail.getLast h_M_tail_ne = b :=
    Walk.tail_getLast_of_pos M hM_pos
  have h_M_tail_decomp :
      M.vertices.tail = M.vertices.tail.dropLast ++ [b] := by
    have := List.dropLast_append_getLast h_M_tail_ne
    rw [h_M_tail_last] at this
    exact this.symm
  have h_M_vs_eq : M.vertices = a :: M.vertices.tail :=
    Walk.vertices_eq_head_cons_tail M
  have h_M_drop_decomp :
      M.vertices.dropLast = a :: M.vertices.tail.dropLast := by
    conv_lhs => rw [h_M_vs_eq]
    rw [List.dropLast_cons_of_ne_nil h_M_tail_ne]
  have hx_M_tail : x ∈ M.vertices.tail := h_arm_drop_in_tail x hx
  have hx_M_drop : x ∈ M.vertices.dropLast := h_arm_drop_in_drop x hx
  rw [h_M_tail_decomp] at hx_M_tail
  rcases List.mem_append.mp hx_M_tail with h_in_interior | h_eq_b
  · exact hM_W x h_in_interior
  · rw [List.mem_singleton] at h_eq_b
    rw [h_M_drop_decomp] at hx_M_drop
    rcases List.mem_cons.mp hx_M_drop with h_eq_a | h_in_interior
    · have : a = b := h_eq_a.symm.trans h_eq_b
      exact absurd this hM_bif.1
    · exact hM_W x h_in_interior

set_option linter.style.longLine false in
/-- Refactor port of decl 56 — the file's largest single lemma
(335 lines pre-refactor).  Mechanical port: every walk-level helper
retargets to its `refactor_*` twin, `(vL, vR) ∈ marg.L` opens via
`marginalize_L_iff` (Sym2-image unwrap, two-case Sym2.eq
dance for the orientation), and the bidirected hinge from
`exists_arms_of_bifurcation_bidir_hinge_strong` arrives as
`s(vL, vR) ∈ G.L` directly (no ordered-pair witness).  The original's
`G.hL_symm hMLR` invocation in the (Inr, bidir M-hinge) branch is
**deleted** — under `Sym2`, `s(vMR, vML) = s(vML, vMR)` definitionally,
so we just rewrite the carrier via `Sym2.eq_swap` to align the type
expected by `mkBifurcationBidir`.  No logic change. -/
lemma marg_bif_backward_bidir_hinge
    (G : CDMG Node) (W : Finset Node) (hW : W ⊆ G.V) {u w : Node}
    (hu : u ∈ G.marginalize W hW) (hw : w ∈ G.marginalize W hW)
    {q : Walk (G.marginalize W hW) u w} (hq : q.IsBifurcation)
    {i : ℕ} (h_split : q.IsBifurcationWithSplit i)
    (h_not_dir : ¬ q.IsBifurcationDirectedHingeWithSplit i) :
    ∃ p : Walk G u w, p.IsBifurcation := by
  obtain ⟨huw_ne, hu_tail, hw_drop, _, _⟩ := hq
  obtain ⟨vL, vR, L_marg, R_marg, hL_marg_dir, hR_marg_dir, hLR_marg, hidx,
          hL_marg_sub, hR_marg_sub, hL_marg_drop_sub, hR_marg_drop_sub⟩ :=
    Walk.exists_arms_of_bifurcation_bidir_hinge_strong
      q i h_split h_not_dir
  -- Unfold marg.L via the Sym2-image iff (Batch-1 net-new helper).
  obtain ⟨e, he1_VW, he2_VW, _he_ne, h_phi_L_e, hs_eq⟩ :=
    (marginalize_L_iff G W hW).mp hLR_marg
  -- `Sym2.eq_iff` case-split: `s(vL, vR) = s(e.1, e.2)` admits two
  -- orientations; in either we obtain `vL, vR ∈ G.V \ W` and the
  -- symmetric `Φ_L W vL vR` (via `Or.symm` in the swap case).
  have h_pack : vL ∈ G.V \ W ∧ vR ∈ G.V \ W ∧
                G.MarginalizationΦL W vL vR := by
    rcases Sym2.eq_iff.mp hs_eq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨he1_VW, he2_VW, h_phi_L_e⟩
    · exact ⟨he2_VW, he1_VW, h_phi_L_e.symm⟩
  obtain ⟨hvL_VW, hvR_VW, h_phi_L⟩ := h_pack
  have hvL_notW : vL ∉ W := (Finset.mem_sdiff.mp hvL_VW).2
  have hvR_notW : vR ∉ W := (Finset.mem_sdiff.mp hvR_VW).2
  have hu_notW : u ∉ W := notW_of_mem_marginalize hW hu
  have hw_notW : w ∉ W := notW_of_mem_marginalize hW hw
  -- Show vR ∈ q.vertices.tail (vR is at position i+1).
  have hvR_in_q_tail : vR ∈ q.vertices.tail := by
    have h_vs_eq : q.vertices = u :: q.vertices.tail :=
      Walk.vertices_eq_head_cons_tail q
    rw [h_vs_eq] at hidx
    have h_tail_idx : q.vertices.tail[i]? = some vR := by simpa using hidx
    exact List.mem_of_getElem? h_tail_idx
  have hu_ne_vR : u ≠ vR := fun heq => hu_tail (heq ▸ hvR_in_q_tail)
  -- Show w ≠ vL (since vL is at position i in q.vertices.dropLast).
  have hvL_in_q_drop : vL ∈ q.vertices.dropLast :=
    hL_marg_sub vL (Walk.head_mem_vertices L_marg)
  have hw_ne_vL : w ≠ vL := fun heq => hw_drop (heq ▸ hvL_in_q_drop)
  -- Expand L_marg, R_marg to G-walks.
  obtain ⟨L_g, hL_g_dir, _hL_g_len, hL_g_sub_W, hL_g_drop_sub_W, _, _⟩ :=
    expand_directed_walk_marginalize L_marg hL_marg_dir
  obtain ⟨R_g, hR_g_dir, _hR_g_len, hR_g_sub_W, hR_g_drop_sub_W, _, _⟩ :=
    expand_directed_walk_marginalize R_marg hR_marg_dir
  -- Vertex-bound facts for L_g and R_g.
  have hu_notin_L_g_drop : u ∉ L_g.vertices.dropLast := fun h_in =>
    (hL_g_drop_sub_W u h_in).elim
      (fun h_marg => hu_tail (hL_marg_drop_sub u h_marg)) hu_notW
  have hu_notin_R_g : u ∉ R_g.vertices := fun h_in =>
    (hR_g_sub_W u h_in).elim
      (fun h_marg => hu_tail (hR_marg_sub u h_marg)) hu_notW
  have hw_notin_L_g : w ∉ L_g.vertices := fun h_in =>
    (hL_g_sub_W w h_in).elim
      (fun h_marg => hw_drop (hL_marg_sub w h_marg)) hw_notW
  have hw_notin_R_g_drop : w ∉ R_g.vertices.dropLast := fun h_in =>
    (hR_g_drop_sub_W w h_in).elim
      (fun h_marg => hw_drop (hR_marg_drop_sub w h_marg)) hw_notW
  -- Case-split on Φ_L orientation.
  rcases h_phi_L with ⟨M, hM_bif, hM_W⟩ | ⟨M, hM_bif, hM_W⟩
  · -- inl case: M : Walk G vL vR.
    have hM_split_ex : ∃ i, M.IsBifurcationWithSplit i := hM_bif.2.2.2
    obtain ⟨k_M, hM_split⟩ := hM_split_ex
    by_cases h_M_dir : M.IsBifurcationDirectedHingeWithSplit k_M
    · -- Inl + directed M-hinge.
      obtain ⟨c_M, M_L, M_R, hM_L_dir, hM_R_dir, hM_L_pos, hM_R_pos, _,
              hM_L_sub, hM_R_sub, hM_L_drop_sub, hM_R_drop_sub⟩ :=
        Walk.exists_arms_of_bifurcation_directed_hinge_strong
          M k_M h_M_dir
      -- qv (c_M → u) = M_L.comp L_g, qw (c_M → w) = M_R.comp R_g.
      have hqv_dir : (M_L.comp L_g).IsDirectedWalk :=
        Walk.isDirectedWalk_comp M_L L_g hM_L_dir hL_g_dir
      have hqw_dir : (M_R.comp R_g).IsDirectedWalk :=
        Walk.isDirectedWalk_comp M_R R_g hM_R_dir hR_g_dir
      have hqv_len : (M_L.comp L_g).length
                       = M_L.length + L_g.length :=
        Walk.length_comp M_L L_g
      have hqw_len : (M_R.comp R_g).length
                       = M_R.length + R_g.length :=
        Walk.length_comp M_R R_g
      have hqv_pos : (M_L.comp L_g).length ≥ 1 := by
        rw [hqv_len]; omega
      have hqw_pos : (M_R.comp R_g).length ≥ 1 := by
        rw [hqw_len]; omega
      -- Vertex-bound checks via arm_dropLast_in_W + expansions.
      have hu_notin_M_L_drop : u ∉ M_L.vertices.dropLast := fun h_in =>
        hu_notW (Walk.arm_dropLast_in_W hM_bif hM_W hM_L_drop_sub
            (fun x hx => hM_L_sub x (List.mem_of_mem_dropLast hx)) u h_in)
      have hu_notin_M_R_drop : u ∉ M_R.vertices.dropLast := fun h_in =>
        hu_notW (Walk.arm_dropLast_in_W hM_bif hM_W
            (fun x hx => hM_R_sub x (List.mem_of_mem_dropLast hx)) hM_R_drop_sub u h_in)
      have hw_notin_M_L_drop : w ∉ M_L.vertices.dropLast := fun h_in =>
        hw_notW (Walk.arm_dropLast_in_W hM_bif hM_W hM_L_drop_sub
            (fun x hx => hM_L_sub x (List.mem_of_mem_dropLast hx)) w h_in)
      have hw_notin_M_R_drop : w ∉ M_R.vertices.dropLast := fun h_in =>
        hw_notW (Walk.arm_dropLast_in_W hM_bif hM_W
            (fun x hx => hM_R_sub x (List.mem_of_mem_dropLast hx)) hM_R_drop_sub w h_in)
      -- qv = M_L.comp L_g: vertices_comp.
      have h_qv_vs : (M_L.comp L_g).vertices
                       = M_L.vertices.dropLast ++ L_g.vertices :=
        Walk.vertices_comp M_L L_g
      have h_qw_vs : (M_R.comp R_g).vertices
                       = M_R.vertices.dropLast ++ R_g.vertices :=
        Walk.vertices_comp M_R R_g
      have h_L_g_ne : L_g.vertices ≠ [] :=
        Walk.vertices_ne_nil L_g
      have h_R_g_ne : R_g.vertices ≠ [] :=
        Walk.vertices_ne_nil R_g
      have h_qv_drop :
          (M_L.comp L_g).vertices.dropLast
            = M_L.vertices.dropLast ++ L_g.vertices.dropLast := by
        rw [h_qv_vs]; exact List.dropLast_append_of_ne_nil h_L_g_ne
      have h_qw_drop :
          (M_R.comp R_g).vertices.dropLast
            = M_R.vertices.dropLast ++ R_g.vertices.dropLast := by
        rw [h_qw_vs]; exact List.dropLast_append_of_ne_nil h_R_g_ne
      have hu_notin_qv_drop : u ∉ (M_L.comp L_g).vertices.dropLast := by
        rw [h_qv_drop]
        intro h_in
        rcases List.mem_append.mp h_in with h_M | h_L
        · exact hu_notin_M_L_drop h_M
        · exact hu_notin_L_g_drop h_L
      have hu_notin_qw : u ∉ (M_R.comp R_g).vertices := by
        rw [h_qw_vs]
        intro h_in
        rcases List.mem_append.mp h_in with h_M | h_R
        · exact hu_notin_M_R_drop h_M
        · exact hu_notin_R_g h_R
      have hw_notin_qv : w ∉ (M_L.comp L_g).vertices := by
        rw [h_qv_vs]
        intro h_in
        rcases List.mem_append.mp h_in with h_M | h_L
        · exact hw_notin_M_L_drop h_M
        · exact hw_notin_L_g h_L
      have hw_notin_qw_drop : w ∉ (M_R.comp R_g).vertices.dropLast := by
        rw [h_qw_drop]
        intro h_in
        rcases List.mem_append.mp h_in with h_M | h_R
        · exact hw_notin_M_R_drop h_M
        · exact hw_notin_R_g_drop h_R
      refine ⟨Walk.mkBifurcation (M_L.comp L_g)
                hqv_dir hqv_pos (M_R.comp R_g), ?_⟩
      have h_bif_src :=
        Walk.mkBifurcation_isBifurcationSource
          (M_L.comp L_g) hqv_dir hqv_pos
          (M_R.comp R_g) hqw_dir hqw_pos
          huw_ne hu_notin_qv_drop hu_notin_qw hw_notin_qv hw_notin_qw_drop
      exact Walk.isBifurcationSource_to_isBifurcation _ c_M h_bif_src
    · -- Inl + bidirected M-hinge.
      obtain ⟨vML, vMR, M_L, M_R, hM_L_dir, hM_R_dir, hMLR, _,
              hM_L_sub, hM_R_sub, hM_L_drop_sub, hM_R_drop_sub⟩ :=
        Walk.exists_arms_of_bifurcation_bidir_hinge_strong
          M k_M hM_split h_M_dir
      have hLc_dir : (M_L.comp L_g).IsDirectedWalk :=
        Walk.isDirectedWalk_comp M_L L_g hM_L_dir hL_g_dir
      have hRc_dir : (M_R.comp R_g).IsDirectedWalk :=
        Walk.isDirectedWalk_comp M_R R_g hM_R_dir hR_g_dir
      have hu_notin_M_L_drop : u ∉ M_L.vertices.dropLast := fun h_in =>
        hu_notW (Walk.arm_dropLast_in_W hM_bif hM_W hM_L_drop_sub
            (fun x hx => hM_L_sub x (List.mem_of_mem_dropLast hx)) u h_in)
      have hu_notin_M_R_drop : u ∉ M_R.vertices.dropLast := fun h_in =>
        hu_notW (Walk.arm_dropLast_in_W hM_bif hM_W
            (fun x hx => hM_R_sub x (List.mem_of_mem_dropLast hx)) hM_R_drop_sub u h_in)
      have hw_notin_M_L_drop : w ∉ M_L.vertices.dropLast := fun h_in =>
        hw_notW (Walk.arm_dropLast_in_W hM_bif hM_W hM_L_drop_sub
            (fun x hx => hM_L_sub x (List.mem_of_mem_dropLast hx)) w h_in)
      have hw_notin_M_R_drop : w ∉ M_R.vertices.dropLast := fun h_in =>
        hw_notW (Walk.arm_dropLast_in_W hM_bif hM_W
            (fun x hx => hM_R_sub x (List.mem_of_mem_dropLast hx)) hM_R_drop_sub w h_in)
      have h_Lc_vs : (M_L.comp L_g).vertices
                       = M_L.vertices.dropLast ++ L_g.vertices :=
        Walk.vertices_comp M_L L_g
      have h_Rc_vs : (M_R.comp R_g).vertices
                       = M_R.vertices.dropLast ++ R_g.vertices :=
        Walk.vertices_comp M_R R_g
      have h_L_g_ne : L_g.vertices ≠ [] :=
        Walk.vertices_ne_nil L_g
      have h_R_g_ne : R_g.vertices ≠ [] :=
        Walk.vertices_ne_nil R_g
      have h_Lc_drop :
          (M_L.comp L_g).vertices.dropLast
            = M_L.vertices.dropLast ++ L_g.vertices.dropLast := by
        rw [h_Lc_vs]; exact List.dropLast_append_of_ne_nil h_L_g_ne
      have h_Rc_drop :
          (M_R.comp R_g).vertices.dropLast
            = M_R.vertices.dropLast ++ R_g.vertices.dropLast := by
        rw [h_Rc_vs]; exact List.dropLast_append_of_ne_nil h_R_g_ne
      have hu_notin_Lc_drop : u ∉ (M_L.comp L_g).vertices.dropLast := by
        rw [h_Lc_drop]
        intro h_in
        rcases List.mem_append.mp h_in with h_M | h_L
        · exact hu_notin_M_L_drop h_M
        · exact hu_notin_L_g_drop h_L
      have hu_notin_Rc : u ∉ (M_R.comp R_g).vertices := by
        rw [h_Rc_vs]
        intro h_in
        rcases List.mem_append.mp h_in with h_M | h_R
        · exact hu_notin_M_R_drop h_M
        · exact hu_notin_R_g h_R
      have hw_notin_Lc : w ∉ (M_L.comp L_g).vertices := by
        rw [h_Lc_vs]
        intro h_in
        rcases List.mem_append.mp h_in with h_M | h_L
        · exact hw_notin_M_L_drop h_M
        · exact hw_notin_L_g h_L
      have hw_notin_Rc_drop : w ∉ (M_R.comp R_g).vertices.dropLast := by
        rw [h_Rc_drop]
        intro h_in
        rcases List.mem_append.mp h_in with h_M | h_R
        · exact hw_notin_M_R_drop h_M
        · exact hw_notin_R_g_drop h_R
      refine ⟨Walk.mkBifurcationBidir
                (M_L.comp L_g) hLc_dir (M_R.comp R_g) hMLR, ?_⟩
      exact Walk.mkBifurcationBidir_isBifurcation
        (M_L.comp L_g) hLc_dir
        (M_R.comp R_g) hRc_dir hMLR huw_ne hu_notin_Lc_drop hu_notin_Rc
        hw_notin_Lc hw_notin_Rc_drop
  · -- inr case: M : Walk G vR vL.
    have hM_split_ex : ∃ i, M.IsBifurcationWithSplit i := hM_bif.2.2.2
    obtain ⟨k_M, hM_split⟩ := hM_split_ex
    by_cases h_M_dir : M.IsBifurcationDirectedHingeWithSplit k_M
    · -- Inr + directed M-hinge.
      obtain ⟨c_M, M_L, M_R, hM_L_dir, hM_R_dir, hM_L_pos, hM_R_pos, _,
              hM_L_sub, hM_R_sub, hM_L_drop_sub, hM_R_drop_sub⟩ :=
        Walk.exists_arms_of_bifurcation_directed_hinge_strong
          M k_M h_M_dir
      have hqv_dir : (M_R.comp L_g).IsDirectedWalk :=
        Walk.isDirectedWalk_comp M_R L_g hM_R_dir hL_g_dir
      have hqw_dir : (M_L.comp R_g).IsDirectedWalk :=
        Walk.isDirectedWalk_comp M_L R_g hM_L_dir hR_g_dir
      have hqv_pos : (M_R.comp L_g).length ≥ 1 := by
        rw [Walk.length_comp]; omega
      have hqw_pos : (M_L.comp R_g).length ≥ 1 := by
        rw [Walk.length_comp]; omega
      have hu_notin_M_L_drop : u ∉ M_L.vertices.dropLast := fun h_in =>
        hu_notW (Walk.arm_dropLast_in_W hM_bif hM_W hM_L_drop_sub
            (fun x hx => hM_L_sub x (List.mem_of_mem_dropLast hx)) u h_in)
      have hu_notin_M_R_drop : u ∉ M_R.vertices.dropLast := fun h_in =>
        hu_notW (Walk.arm_dropLast_in_W hM_bif hM_W
            (fun x hx => hM_R_sub x (List.mem_of_mem_dropLast hx)) hM_R_drop_sub u h_in)
      have hw_notin_M_L_drop : w ∉ M_L.vertices.dropLast := fun h_in =>
        hw_notW (Walk.arm_dropLast_in_W hM_bif hM_W hM_L_drop_sub
            (fun x hx => hM_L_sub x (List.mem_of_mem_dropLast hx)) w h_in)
      have hw_notin_M_R_drop : w ∉ M_R.vertices.dropLast := fun h_in =>
        hw_notW (Walk.arm_dropLast_in_W hM_bif hM_W
            (fun x hx => hM_R_sub x (List.mem_of_mem_dropLast hx)) hM_R_drop_sub w h_in)
      have h_qv_vs : (M_R.comp L_g).vertices
                       = M_R.vertices.dropLast ++ L_g.vertices :=
        Walk.vertices_comp M_R L_g
      have h_qw_vs : (M_L.comp R_g).vertices
                       = M_L.vertices.dropLast ++ R_g.vertices :=
        Walk.vertices_comp M_L R_g
      have h_L_g_ne : L_g.vertices ≠ [] :=
        Walk.vertices_ne_nil L_g
      have h_R_g_ne : R_g.vertices ≠ [] :=
        Walk.vertices_ne_nil R_g
      have h_qv_drop :
          (M_R.comp L_g).vertices.dropLast
            = M_R.vertices.dropLast ++ L_g.vertices.dropLast := by
        rw [h_qv_vs]; exact List.dropLast_append_of_ne_nil h_L_g_ne
      have h_qw_drop :
          (M_L.comp R_g).vertices.dropLast
            = M_L.vertices.dropLast ++ R_g.vertices.dropLast := by
        rw [h_qw_vs]; exact List.dropLast_append_of_ne_nil h_R_g_ne
      have hu_notin_qv_drop : u ∉ (M_R.comp L_g).vertices.dropLast := by
        rw [h_qv_drop]
        intro h_in
        rcases List.mem_append.mp h_in with h_M | h_L
        · exact hu_notin_M_R_drop h_M
        · exact hu_notin_L_g_drop h_L
      have hu_notin_qw : u ∉ (M_L.comp R_g).vertices := by
        rw [h_qw_vs]
        intro h_in
        rcases List.mem_append.mp h_in with h_M | h_R
        · exact hu_notin_M_L_drop h_M
        · exact hu_notin_R_g h_R
      have hw_notin_qv : w ∉ (M_R.comp L_g).vertices := by
        rw [h_qv_vs]
        intro h_in
        rcases List.mem_append.mp h_in with h_M | h_L
        · exact hw_notin_M_R_drop h_M
        · exact hw_notin_L_g h_L
      have hw_notin_qw_drop : w ∉ (M_L.comp R_g).vertices.dropLast := by
        rw [h_qw_drop]
        intro h_in
        rcases List.mem_append.mp h_in with h_M | h_R
        · exact hw_notin_M_L_drop h_M
        · exact hw_notin_R_g_drop h_R
      refine ⟨Walk.mkBifurcation (M_R.comp L_g)
                hqv_dir hqv_pos (M_L.comp R_g), ?_⟩
      have h_bif_src :=
        Walk.mkBifurcation_isBifurcationSource
          (M_R.comp L_g) hqv_dir hqv_pos
          (M_L.comp R_g) hqw_dir hqw_pos
          huw_ne hu_notin_qv_drop hu_notin_qw hw_notin_qv hw_notin_qw_drop
      exact Walk.isBifurcationSource_to_isBifurcation _ c_M h_bif_src
    · -- Inr + bidirected M-hinge.
      obtain ⟨vML, vMR, M_L, M_R, hM_L_dir, hM_R_dir, hMLR, _,
              hM_L_sub, hM_R_sub, hM_L_drop_sub, hM_R_drop_sub⟩ :=
        Walk.exists_arms_of_bifurcation_bidir_hinge_strong
          M k_M hM_split h_M_dir
      -- Hinge: original used `G.hL_symm hMLR` to flip `(vML, vMR) ∈ G.L`
      -- to `(vMR, vML) ∈ G.L`.  Under `Sym2`, `s(vMR, vML) = s(vML, vMR)`
      -- definitionally; rewrite the carrier via `Sym2.eq_swap`.
      have hMLR_sym : s(vMR, vML) ∈ G.L := by rw [Sym2.eq_swap]; exact hMLR
      have hLc_dir : (M_R.comp L_g).IsDirectedWalk :=
        Walk.isDirectedWalk_comp M_R L_g hM_R_dir hL_g_dir
      have hRc_dir : (M_L.comp R_g).IsDirectedWalk :=
        Walk.isDirectedWalk_comp M_L R_g hM_L_dir hR_g_dir
      have hu_notin_M_L_drop : u ∉ M_L.vertices.dropLast := fun h_in =>
        hu_notW (Walk.arm_dropLast_in_W hM_bif hM_W hM_L_drop_sub
            (fun x hx => hM_L_sub x (List.mem_of_mem_dropLast hx)) u h_in)
      have hu_notin_M_R_drop : u ∉ M_R.vertices.dropLast := fun h_in =>
        hu_notW (Walk.arm_dropLast_in_W hM_bif hM_W
            (fun x hx => hM_R_sub x (List.mem_of_mem_dropLast hx)) hM_R_drop_sub u h_in)
      have hw_notin_M_L_drop : w ∉ M_L.vertices.dropLast := fun h_in =>
        hw_notW (Walk.arm_dropLast_in_W hM_bif hM_W hM_L_drop_sub
            (fun x hx => hM_L_sub x (List.mem_of_mem_dropLast hx)) w h_in)
      have hw_notin_M_R_drop : w ∉ M_R.vertices.dropLast := fun h_in =>
        hw_notW (Walk.arm_dropLast_in_W hM_bif hM_W
            (fun x hx => hM_R_sub x (List.mem_of_mem_dropLast hx)) hM_R_drop_sub w h_in)
      have h_Lc_vs : (M_R.comp L_g).vertices
                       = M_R.vertices.dropLast ++ L_g.vertices :=
        Walk.vertices_comp M_R L_g
      have h_Rc_vs : (M_L.comp R_g).vertices
                       = M_L.vertices.dropLast ++ R_g.vertices :=
        Walk.vertices_comp M_L R_g
      have h_L_g_ne : L_g.vertices ≠ [] :=
        Walk.vertices_ne_nil L_g
      have h_R_g_ne : R_g.vertices ≠ [] :=
        Walk.vertices_ne_nil R_g
      have h_Lc_drop :
          (M_R.comp L_g).vertices.dropLast
            = M_R.vertices.dropLast ++ L_g.vertices.dropLast := by
        rw [h_Lc_vs]; exact List.dropLast_append_of_ne_nil h_L_g_ne
      have h_Rc_drop :
          (M_L.comp R_g).vertices.dropLast
            = M_L.vertices.dropLast ++ R_g.vertices.dropLast := by
        rw [h_Rc_vs]; exact List.dropLast_append_of_ne_nil h_R_g_ne
      have hu_notin_Lc_drop : u ∉ (M_R.comp L_g).vertices.dropLast := by
        rw [h_Lc_drop]
        intro h_in
        rcases List.mem_append.mp h_in with h_M | h_L
        · exact hu_notin_M_R_drop h_M
        · exact hu_notin_L_g_drop h_L
      have hu_notin_Rc : u ∉ (M_L.comp R_g).vertices := by
        rw [h_Rc_vs]
        intro h_in
        rcases List.mem_append.mp h_in with h_M | h_R
        · exact hu_notin_M_L_drop h_M
        · exact hu_notin_R_g h_R
      have hw_notin_Lc : w ∉ (M_R.comp L_g).vertices := by
        rw [h_Lc_vs]
        intro h_in
        rcases List.mem_append.mp h_in with h_M | h_L
        · exact hw_notin_M_R_drop h_M
        · exact hw_notin_L_g h_L
      have hw_notin_Rc_drop : w ∉ (M_L.comp R_g).vertices.dropLast := by
        rw [h_Rc_drop]
        intro h_in
        rcases List.mem_append.mp h_in with h_M | h_R
        · exact hw_notin_M_L_drop h_M
        · exact hw_notin_R_g_drop h_R
      refine ⟨Walk.mkBifurcationBidir
                (M_R.comp L_g) hLc_dir (M_L.comp R_g) hMLR_sym, ?_⟩
      exact Walk.mkBifurcationBidir_isBifurcation
        (M_R.comp L_g) hLc_dir
        (M_L.comp R_g) hRc_dir hMLR_sym huw_ne hu_notin_Lc_drop hu_notin_Rc
        hw_notin_Lc hw_notin_Rc_drop

-- ## Refactor replacements — Batch 11 (declarations 57–63).
--
-- Forward-direction bidirected-case helpers + the two top-level
-- forward/backward bifurcation wrappers.  All seven are
-- structural/mechanical ports against the typed-`WalkStep`
-- + Sym2 encoding.  The two non-mechanical sites are:
-- * `hL_irrefl` rewrite (decls 57 and 61, original lines 2543 and 3187):
--   the original `G.hL_irrefl hLR : vL ≠ vR` becomes
--   `G.hL_irrefl hLR : ¬ s(vL, vR).IsDiag`; pull the inequality via
--   `fun h => G.hL_irrefl hLR (Sym2.mk_isDiag_iff.mpr h)`;
-- * `hL_subset` rewrite (decls 57 and 61, original lines 2529-2530 and
--   3183-3184): the original `(G.hL_subset hLR).1 / .2 : vL/vR ∈ G.V`
--   becomes `G.hL_subset hLR (Sym2.mem_mk_left vL vR) : vL ∈ G.V` and
--   `G.hL_subset hLR (Sym2.mem_mk_right vL vR) : vR ∈ G.V`.
-- The `s(vL, vR) ∈ marg.L` constructions go via
-- `marginalize_L_iff` (Batch 1 net-new helper); the bidirected
-- WalkStep witnesses are typed `.bidir hLR` rather than
-- `Or.inl ⟨rfl, Or.inr hLR⟩`.  Decls 62 and 63 are pure wrapper
-- by-name swaps.

/-- Refactor port of decl 57 — forward-direction bidirected hinge
where both hinge endpoints lie outside `W` (the `H.A` sub-case).
**Structural rewrites**:
* `hL_subset` returns membership-shaped: `(G.hL_subset hLR_G).1` / `.2`
  becomes `G.hL_subset hLR_G (Sym2.mem_mk_left/right vL vR)` to extract
  `vL, vR ∈ G.V` from `s(vL, vR) ∈ G.L`.
* `hL_irrefl` returns `¬ s(vL, vR).IsDiag` instead of `vL ≠ vR`; pull
  `vL ≠ vR` via `fun h => G.hL_irrefl hLR_G (Sym2.mk_isDiag_iff.mpr h)`.
* Single-edge witness `Walk.cons vR (vL, vR) (Or.inl ⟨rfl, Or.inr hLR⟩) (Walk.nil ...)`
  collapses to `Walk.cons vR (.bidir hLR_G) (Walk.nil vR hvR_g)`.
* `(vL, vR) ∈ marg.L` goes via `marginalize_L_iff` (Sym2-image
  unwrap); the Φ_L witness is `Or.inl ⟨single, h_single_bif, h_single_W⟩`
  per the unchanged Φ_L shape. -/
lemma marg_bif_forward_bidir_both_notW
    (G : CDMG Node) (W : Finset Node) (hW : W ⊆ G.V) {u w : Node}
    (hu : u ∈ G.marginalize W hW) (hw : w ∈ G.marginalize W hW)
    {p : Walk G u w} (hp : p.IsBifurcation)
    {vL vR : Node}
    (hvL_notW : vL ∉ W) (hvR_notW : vR ∉ W)
    (L_g : Walk G vL u) (R_g : Walk G vR w)
    (hL_dir : L_g.IsDirectedWalk) (hR_dir : R_g.IsDirectedWalk)
    (hLR_G : s(vL, vR) ∈ G.L)
    (hL_sub : ∀ x ∈ L_g.vertices, x ∈ p.vertices.dropLast)
    (hR_sub : ∀ x ∈ R_g.vertices, x ∈ p.vertices.tail)
    (hL_drop_sub : ∀ x ∈ L_g.vertices.dropLast, x ∈ p.vertices.tail)
    (hR_drop_sub : ∀ x ∈ R_g.vertices.dropLast, x ∈ p.vertices.dropLast) :
    ∃ q : Walk (G.marginalize W hW) u w,
      q.IsBifurcation := by
  obtain ⟨huw_ne, hu_tail, hw_drop, _, _⟩ := hp
  -- vL, vR ∈ G.V via hL_subset on the bidirected G-edge (Sym2.Mem-shaped).
  have hvL_GV : vL ∈ G.V := G.hL_subset hLR_G (Sym2.mem_mk_left vL vR)
  have hvR_GV : vR ∈ G.V := G.hL_subset hLR_G (Sym2.mem_mk_right vL vR)
  have hvL_g : vL ∈ G := Finset.mem_union_right _ hvL_GV
  have hvR_g : vR ∈ G := Finset.mem_union_right _ hvR_GV
  have hvL_VW : vL ∈ G.V \ W := Finset.mem_sdiff.mpr ⟨hvL_GV, hvL_notW⟩
  have hvR_VW : vR ∈ G.V \ W := Finset.mem_sdiff.mpr ⟨hvR_GV, hvR_notW⟩
  have hvL_marg : vL ∈ G.marginalize W hW := by
    change vL ∈ G.J ∪ (G.V \ W); exact Finset.mem_union_right _ hvL_VW
  have hvR_marg : vR ∈ G.marginalize W hW := by
    change vR ∈ G.J ∪ (G.V \ W); exact Finset.mem_union_right _ hvR_VW
  -- vL ≠ vR via Sym2.IsDiag.
  have hvLvR_ne : vL ≠ vR :=
    fun h => G.hL_irrefl hLR_G (Sym2.mk_isDiag_iff.mpr h)
  -- Construct single-edge witness for Φ_L using typed `.bidir`.
  let single : Walk G vL vR :=
    Walk.cons vR (.bidir hLR_G) (Walk.nil vR hvR_g)
  have h_single_bif : single.IsBifurcation :=
    Walk.singleEdge_isBifurcation_of_bidir hvL_g hvR_g hLR_G hvLvR_ne
  have h_single_W : ∀ x ∈ single.vertices.tail.dropLast, x ∈ W := by
    intro x hx
    change x ∈ ([vL, vR] : List Node).tail.dropLast at hx
    simp at hx
  -- s(vL, vR) ∈ marg.L via Φ_L (Sym2-image unwrap helper).
  have hLR_marg : s(vL, vR) ∈ (G.marginalize W hW).L :=
    (marginalize_L_iff G W hW).mpr
      ⟨(vL, vR), hvL_VW, hvR_VW, hvLvR_ne,
       Or.inl ⟨single, h_single_bif, h_single_W⟩, rfl⟩
  -- Project L_g, R_g to marg.
  obtain ⟨L_marg, hL_marg_dir, hL_marg_sub, hL_marg_drop_sub, _⟩ :=
    project_directed_walk_strong L_g hL_dir hvL_marg hu
  obtain ⟨R_marg, hR_marg_dir, hR_marg_sub, hR_marg_drop_sub, _⟩ :=
    project_directed_walk_strong R_g hR_dir hvR_marg hw
  -- Verify the four vertex-bound conditions for mkBifurcationBidir_isBifurcation.
  have hu_notin_L_drop : u ∉ L_marg.vertices.dropLast := fun h_in =>
    hu_tail (hL_drop_sub u (hL_marg_drop_sub u h_in))
  have hu_notin_R : u ∉ R_marg.vertices := fun h_in =>
    hu_tail (hR_sub u (hR_marg_sub u h_in))
  have hw_notin_L : w ∉ L_marg.vertices := fun h_in =>
    hw_drop (hL_sub w (hL_marg_sub w h_in))
  have hw_notin_R_drop : w ∉ R_marg.vertices.dropLast := fun h_in =>
    hw_drop (hR_drop_sub w (hR_marg_drop_sub w h_in))
  refine ⟨Walk.mkBifurcationBidir L_marg hL_marg_dir R_marg hLR_marg, ?_⟩
  exact Walk.mkBifurcationBidir_isBifurcation
    L_marg hL_marg_dir R_marg hR_marg_dir hLR_marg
    huw_ne hu_notin_L_drop hu_notin_R hw_notin_L hw_notin_R_drop

/-- Refactor port of decl 58 — assemble a marg bidirected-hinge
bifurcation from two marg-segment arms + a Φ_L witness.  Mechanical
port: same Sym2-image dance for `s(vL_exit, vR_exit) ∈ marg.L` via
`marginalize_L_iff`.  No `hL_irrefl` site here. -/
lemma marg_bif_forward_assemble_bidirected
    (G : CDMG Node) (W : Finset Node) (hW : W ⊆ G.V) {u w : Node}
    (hu : u ∈ G.marginalize W hW) (hw : w ∈ G.marginalize W hW)
    (huw_ne : u ≠ w)
    {vL_exit vR_exit : Node}
    (hvL_exit_VW : vL_exit ∈ G.V \ W) (hvR_exit_VW : vR_exit ∈ G.V \ W)
    (hvL_vR_exit_eq : vL_exit ≠ vR_exit)
    (hPhi_L : G.MarginalizationΦL W vL_exit vR_exit)
    {L_marg_seg : Walk G vL_exit u}
    (hL_marg_dir : L_marg_seg.IsDirectedWalk)
    {R_marg_seg : Walk G vR_exit w}
    (hR_marg_dir : R_marg_seg.IsDirectedWalk)
    (hu_notin_L_drop : u ∉ L_marg_seg.vertices.dropLast)
    (hu_notin_R : u ∉ R_marg_seg.vertices)
    (hw_notin_L : w ∉ L_marg_seg.vertices)
    (hw_notin_R_drop : w ∉ R_marg_seg.vertices.dropLast) :
    ∃ q : Walk (G.marginalize W hW) u w,
      q.IsBifurcation := by
  have hvL_marg : vL_exit ∈ G.marginalize W hW := by
    change vL_exit ∈ G.J ∪ (G.V \ W); exact Finset.mem_union_right _ hvL_exit_VW
  have hvR_marg : vR_exit ∈ G.marginalize W hW := by
    change vR_exit ∈ G.J ∪ (G.V \ W); exact Finset.mem_union_right _ hvR_exit_VW
  have hLR_marg : s(vL_exit, vR_exit) ∈ (G.marginalize W hW).L :=
    (marginalize_L_iff G W hW).mpr
      ⟨(vL_exit, vR_exit), hvL_exit_VW, hvR_exit_VW, hvL_vR_exit_eq, hPhi_L, rfl⟩
  obtain ⟨L_marg_proj, hL_marg_proj_dir, hL_marg_proj_sub,
          hL_marg_proj_drop_sub, _⟩ :=
    project_directed_walk_strong L_marg_seg hL_marg_dir hvL_marg hu
  obtain ⟨R_marg_proj, hR_marg_proj_dir, hR_marg_proj_sub,
          hR_marg_proj_drop_sub, _⟩ :=
    project_directed_walk_strong R_marg_seg hR_marg_dir hvR_marg hw
  have hu_notin_L_proj_drop : u ∉ L_marg_proj.vertices.dropLast := fun h_in =>
    hu_notin_L_drop (hL_marg_proj_drop_sub u h_in)
  have hu_notin_R_proj : u ∉ R_marg_proj.vertices := fun h_in =>
    hu_notin_R (hR_marg_proj_sub u h_in)
  have hw_notin_L_proj : w ∉ L_marg_proj.vertices := fun h_in =>
    hw_notin_L (hL_marg_proj_sub w h_in)
  have hw_notin_R_proj_drop : w ∉ R_marg_proj.vertices.dropLast := fun h_in =>
    hw_notin_R_drop (hR_marg_proj_drop_sub w h_in)
  refine ⟨Walk.mkBifurcationBidir L_marg_proj hL_marg_proj_dir
            R_marg_proj hLR_marg, ?_⟩
  exact Walk.mkBifurcationBidir_isBifurcation L_marg_proj hL_marg_proj_dir
    R_marg_proj hR_marg_proj_dir hLR_marg huw_ne
    hu_notin_L_proj_drop hu_notin_R_proj hw_notin_L_proj hw_notin_R_proj_drop

/-- Refactor port of decl 59 — forward-direction directed hinge with
source `c ∈ W`.  Heavy mechanical port: every walk-level helper
retargets to its `refactor_*` twin; vertex-list bookkeeping is
byte-identical modulo the `vertices` → `vertices` rename. -/
lemma marg_bif_forward_dir_hinge_src_W
    (G : CDMG Node) (W : Finset Node) (hW : W ⊆ G.V) {u w : Node}
    (hu : u ∈ G.marginalize W hW) (hw : w ∈ G.marginalize W hW)
    {p : Walk G u w} (hp : p.IsBifurcation)
    {i : ℕ} (h_dir : p.IsBifurcationDirectedHingeWithSplit i)
    {c : Node} (hidx : p.vertices[i + 1]? = some c)
    (hc_notin_marg : c ∉ G.marginalize W hW) :
    ∃ q : Walk (G.marginalize W hW) u w,
      q.IsBifurcation := by
  obtain ⟨huw_ne, hu_tail, hw_drop, _, _⟩ := hp
  obtain ⟨c', L_p, R_p, hL_p_dir, hR_p_dir, hL_p_pos, hR_p_pos, hidx',
          hL_p_sub, hR_p_sub, hL_p_drop_sub, hR_p_drop_sub⟩ :=
    Walk.exists_arms_of_bifurcation_directed_hinge_strong p i h_dir
  have hc_eq : c = c' := by
    rw [hidx] at hidx'; exact Option.some.inj hidx'
  subst hc_eq
  have hu_notW : u ∉ W := notW_of_mem_marginalize hW hu
  have hw_notW : w ∉ W := notW_of_mem_marginalize hW hw
  have hc_in_p : c ∈ p.vertices := List.mem_of_getElem? hidx
  have hc_g : c ∈ G := Walk.mem_of_mem_vertices p hc_in_p
  have hc_W : c ∈ W := by
    by_contra hc_notW
    apply hc_notin_marg
    change c ∈ G.J ∪ (G.V \ W)
    rcases Finset.mem_union.mp hc_g with hc_J | hc_V
    · exact Finset.mem_union_left _ hc_J
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hc_V, hc_notW⟩)
  obtain ⟨vL_exit, L_W_seg, L_marg_seg, hL_W_dir, hL_marg_dir, hL_W_pos,
          hvL_exit_notW, hL_W_inter, _hL_lens_eq, hL_p_vs_eq⟩ :=
    find_first_non_W_directed W L_p hL_p_dir hL_p_pos hu_notW
  obtain ⟨vR_exit, R_W_seg, R_marg_seg, hR_W_dir, hR_marg_dir, hR_W_pos,
          hvR_exit_notW, hR_W_inter, _hR_lens_eq, hR_p_vs_eq⟩ :=
    find_first_non_W_directed W R_p hR_p_dir hR_p_pos hw_notW
  have hvL_exit_GV : vL_exit ∈ G.V :=
    Walk.target_in_GV_of_directedWalk_pos L_W_seg hL_W_dir hL_W_pos
  have hvR_exit_GV : vR_exit ∈ G.V :=
    Walk.target_in_GV_of_directedWalk_pos R_W_seg hR_W_dir hR_W_pos
  have hvL_exit_VW : vL_exit ∈ G.V \ W :=
    Finset.mem_sdiff.mpr ⟨hvL_exit_GV, hvL_exit_notW⟩
  have hvR_exit_VW : vR_exit ∈ G.V \ W :=
    Finset.mem_sdiff.mpr ⟨hvR_exit_GV, hvR_exit_notW⟩
  have hL_marg_ne : L_marg_seg.vertices ≠ [] :=
    Walk.vertices_ne_nil L_marg_seg
  have hR_marg_ne : R_marg_seg.vertices ≠ [] :=
    Walk.vertices_ne_nil R_marg_seg
  -- L_marg_seg vertex bounds.
  have hL_marg_sub_L_p :
      ∀ x ∈ L_marg_seg.vertices, x ∈ L_p.vertices := by
    intro x hx; rw [hL_p_vs_eq]; exact List.mem_append.mpr (Or.inr hx)
  have hR_marg_sub_R_p :
      ∀ x ∈ R_marg_seg.vertices, x ∈ R_p.vertices := by
    intro x hx; rw [hR_p_vs_eq]; exact List.mem_append.mpr (Or.inr hx)
  have hL_marg_drop_sub_L_p_drop :
      ∀ x ∈ L_marg_seg.vertices.dropLast,
        x ∈ L_p.vertices.dropLast := by
    intro x hx
    rw [hL_p_vs_eq, List.dropLast_append_of_ne_nil hL_marg_ne]
    exact List.mem_append.mpr (Or.inr hx)
  have hR_marg_drop_sub_R_p_drop :
      ∀ x ∈ R_marg_seg.vertices.dropLast,
        x ∈ R_p.vertices.dropLast := by
    intro x hx
    rw [hR_p_vs_eq, List.dropLast_append_of_ne_nil hR_marg_ne]
    exact List.mem_append.mpr (Or.inr hx)
  have hu_notin_L_marg_drop : u ∉ L_marg_seg.vertices.dropLast := fun h_in =>
    hu_tail (hL_p_drop_sub u (hL_marg_drop_sub_L_p_drop u h_in))
  have hu_notin_R_marg : u ∉ R_marg_seg.vertices := fun h_in =>
    hu_tail (hR_p_sub u (hR_marg_sub_R_p u h_in))
  have hw_notin_L_marg : w ∉ L_marg_seg.vertices := fun h_in =>
    hw_drop (hL_p_sub w (hL_marg_sub_L_p w h_in))
  have hw_notin_R_marg_drop : w ∉ R_marg_seg.vertices.dropLast := fun h_in =>
    hw_drop (hR_p_drop_sub w (hR_marg_drop_sub_R_p_drop w h_in))
  -- L_W_seg vertex bounds.
  have hL_W_sub_L_p : ∀ x ∈ L_W_seg.vertices, x ∈ L_p.vertices := by
    intro x hx
    rw [hL_p_vs_eq]
    by_cases h_drop : x ∈ L_W_seg.vertices.dropLast
    · exact List.mem_append.mpr (Or.inl h_drop)
    · have h_x_last : x = vL_exit := by
        have h_W_seg_ne : L_W_seg.vertices ≠ [] :=
          Walk.vertices_ne_nil L_W_seg
        have h_W_seg_last :
            L_W_seg.vertices.getLast h_W_seg_ne = vL_exit :=
          Walk.vertices_getLast L_W_seg
        have := List.dropLast_append_getLast h_W_seg_ne
        rw [h_W_seg_last] at this
        have hx_in : x ∈ L_W_seg.vertices.dropLast ++ [vL_exit] := by
          rw [this]; exact hx
        rcases List.mem_append.mp hx_in with h | h
        · exact absurd h h_drop
        · exact List.mem_singleton.mp h
      rw [h_x_last]
      apply List.mem_append.mpr
      right
      exact Walk.head_mem_vertices L_marg_seg
  have hR_W_sub_R_p : ∀ x ∈ R_W_seg.vertices, x ∈ R_p.vertices := by
    intro x hx
    rw [hR_p_vs_eq]
    by_cases h_drop : x ∈ R_W_seg.vertices.dropLast
    · exact List.mem_append.mpr (Or.inl h_drop)
    · have h_x_last : x = vR_exit := by
        have h_W_seg_ne : R_W_seg.vertices ≠ [] :=
          Walk.vertices_ne_nil R_W_seg
        have h_W_seg_last :
            R_W_seg.vertices.getLast h_W_seg_ne = vR_exit :=
          Walk.vertices_getLast R_W_seg
        have := List.dropLast_append_getLast h_W_seg_ne
        rw [h_W_seg_last] at this
        have hx_in : x ∈ R_W_seg.vertices.dropLast ++ [vR_exit] := by
          rw [this]; exact hx
        rcases List.mem_append.mp hx_in with h | h
        · exact absurd h h_drop
        · exact List.mem_singleton.mp h
      rw [h_x_last]
      apply List.mem_append.mpr
      right
      exact Walk.head_mem_vertices R_marg_seg
  by_cases hvL_vR_exit_eq : vL_exit = vR_exit
  · -- Degenerate case: build sourced G-bifurcation.
    subst hvL_vR_exit_eq
    have hvL_exit_ne_u : vL_exit ≠ u := by
      intro h_eq
      have hvL_in_R_p_tail : vL_exit ∈ R_p.vertices := hR_marg_sub_R_p _
        (Walk.head_mem_vertices R_marg_seg)
      have hvL_in_p_tail : vL_exit ∈ p.vertices.tail :=
        hR_p_sub _ hvL_in_R_p_tail
      exact hu_tail (h_eq ▸ hvL_in_p_tail)
    have hvL_exit_ne_w : vL_exit ≠ w := by
      intro h_eq
      have hvL_in_L_p : vL_exit ∈ L_p.vertices := hL_marg_sub_L_p _
        (Walk.head_mem_vertices L_marg_seg)
      have hvL_in_p_drop : vL_exit ∈ p.vertices.dropLast :=
        hL_p_sub _ hvL_in_L_p
      exact hw_drop (h_eq ▸ hvL_in_p_drop)
    have hL_marg_pos : L_marg_seg.length ≥ 1 :=
      Walk.length_pos_of_ne L_marg_seg hvL_exit_ne_u
    have hR_marg_pos : R_marg_seg.length ≥ 1 :=
      Walk.length_pos_of_ne R_marg_seg hvL_exit_ne_w
    have hvL_marg : vL_exit ∈ G.marginalize W hW := by
      change vL_exit ∈ G.J ∪ (G.V \ W); exact Finset.mem_union_right _ hvL_exit_VW
    have h_src :
        (Walk.mkBifurcation L_marg_seg hL_marg_dir hL_marg_pos
            R_marg_seg).IsBifurcationSource vL_exit :=
      Walk.mkBifurcation_isBifurcationSource
        L_marg_seg hL_marg_dir hL_marg_pos
        R_marg_seg hR_marg_dir hR_marg_pos huw_ne
        hu_notin_L_marg_drop hu_notin_R_marg hw_notin_L_marg hw_notin_R_marg_drop
    obtain ⟨q, hq_src⟩ :=
      marg_preserves_bifSource_forward G W hW hu hw hvL_marg
        ⟨_, h_src⟩
    exact ⟨q, Walk.isBifurcationSource_to_isBifurcation
              q vL_exit hq_src⟩
  · -- Non-degenerate case: build Φ_L witness via mkBifurcation L_W_seg R_W_seg.
    have hvL_notin_L_W_drop : vL_exit ∉ L_W_seg.vertices.dropLast := by
      intro h_in
      have h_W_seg_tail_ne : L_W_seg.vertices.tail ≠ [] :=
        Walk.tail_vertices_ne_nil_of_pos L_W_seg hL_W_pos
      have h_vs_eq : L_W_seg.vertices = c :: L_W_seg.vertices.tail :=
        Walk.vertices_eq_head_cons_tail L_W_seg
      rw [h_vs_eq, List.dropLast_cons_of_ne_nil h_W_seg_tail_ne] at h_in
      rcases List.mem_cons.mp h_in with h_eq | h_rest
      · exact hvL_exit_notW (h_eq ▸ hc_W)
      · exact hvL_exit_notW (hL_W_inter vL_exit h_rest)
    have hvR_notin_R_W_drop : vR_exit ∉ R_W_seg.vertices.dropLast := by
      intro h_in
      have h_W_seg_tail_ne : R_W_seg.vertices.tail ≠ [] :=
        Walk.tail_vertices_ne_nil_of_pos R_W_seg hR_W_pos
      have h_vs_eq : R_W_seg.vertices = c :: R_W_seg.vertices.tail :=
        Walk.vertices_eq_head_cons_tail R_W_seg
      rw [h_vs_eq, List.dropLast_cons_of_ne_nil h_W_seg_tail_ne] at h_in
      rcases List.mem_cons.mp h_in with h_eq | h_rest
      · exact hvR_exit_notW (h_eq ▸ hc_W)
      · exact hvR_exit_notW (hR_W_inter vR_exit h_rest)
    have h_R_W_target : R_W_seg.vertices.tail.getLast
        (Walk.tail_vertices_ne_nil_of_pos R_W_seg hR_W_pos) = vR_exit :=
      Walk.tail_getLast_of_pos R_W_seg hR_W_pos
    have h_L_W_target : L_W_seg.vertices.tail.getLast
        (Walk.tail_vertices_ne_nil_of_pos L_W_seg hL_W_pos) = vL_exit :=
      Walk.tail_getLast_of_pos L_W_seg hL_W_pos
    have hvL_notin_R_W : vL_exit ∉ R_W_seg.vertices := by
      intro h_in
      have h_R_W_tail_ne : R_W_seg.vertices.tail ≠ [] :=
        Walk.tail_vertices_ne_nil_of_pos R_W_seg hR_W_pos
      have h_vs_eq : R_W_seg.vertices = c :: R_W_seg.vertices.tail :=
        Walk.vertices_eq_head_cons_tail R_W_seg
      rw [h_vs_eq] at h_in
      rcases List.mem_cons.mp h_in with h_eq | h_rest
      · exact hvL_exit_notW (h_eq ▸ hc_W)
      · have h_tail_decomp : R_W_seg.vertices.tail
            = R_W_seg.vertices.tail.dropLast ++ [vR_exit] := by
          have := List.dropLast_append_getLast h_R_W_tail_ne
          rw [h_R_W_target] at this
          exact this.symm
        rw [h_tail_decomp] at h_rest
        rcases List.mem_append.mp h_rest with h_W | h_eq2
        · exact hvL_exit_notW (hR_W_inter vL_exit h_W)
        · rw [List.mem_singleton] at h_eq2
          exact hvL_vR_exit_eq h_eq2
    have hvR_notin_L_W : vR_exit ∉ L_W_seg.vertices := by
      intro h_in
      have h_L_W_tail_ne : L_W_seg.vertices.tail ≠ [] :=
        Walk.tail_vertices_ne_nil_of_pos L_W_seg hL_W_pos
      have h_vs_eq : L_W_seg.vertices = c :: L_W_seg.vertices.tail :=
        Walk.vertices_eq_head_cons_tail L_W_seg
      rw [h_vs_eq] at h_in
      rcases List.mem_cons.mp h_in with h_eq | h_rest
      · exact hvR_exit_notW (h_eq ▸ hc_W)
      · have h_tail_decomp : L_W_seg.vertices.tail
            = L_W_seg.vertices.tail.dropLast ++ [vL_exit] := by
          have := List.dropLast_append_getLast h_L_W_tail_ne
          rw [h_L_W_target] at this
          exact this.symm
        rw [h_tail_decomp] at h_rest
        rcases List.mem_append.mp h_rest with h_W | h_eq2
        · exact hvR_exit_notW (hL_W_inter vR_exit h_W)
        · rw [List.mem_singleton] at h_eq2
          exact hvL_vR_exit_eq h_eq2.symm
    have h_phi_src :
        (Walk.mkBifurcation L_W_seg hL_W_dir hL_W_pos
            R_W_seg).IsBifurcationSource c :=
      Walk.mkBifurcation_isBifurcationSource
        L_W_seg hL_W_dir hL_W_pos
        R_W_seg hR_W_dir hR_W_pos hvL_vR_exit_eq
        hvL_notin_L_W_drop hvL_notin_R_W hvR_notin_L_W hvR_notin_R_W_drop
    have h_phi_bif :
        (Walk.mkBifurcation L_W_seg hL_W_dir hL_W_pos
            R_W_seg).IsBifurcation :=
      Walk.isBifurcationSource_to_isBifurcation _ c h_phi_src
    have h_phi_W :
        ∀ x ∈ (Walk.mkBifurcation L_W_seg hL_W_dir hL_W_pos
                  R_W_seg).vertices.tail.dropLast, x ∈ W := by
      intro x hx
      have h_vs : (Walk.mkBifurcation L_W_seg hL_W_dir hL_W_pos
                      R_W_seg).vertices
          = L_W_seg.vertices.reverse.dropLast ++ R_W_seg.vertices :=
        Walk.vertices_mkBifurcation L_W_seg hL_W_dir hL_W_pos R_W_seg
      have h_rev_drop : L_W_seg.vertices.reverse.dropLast
          = L_W_seg.vertices.tail.reverse :=
        Walk.vertices_reverse_dropLast L_W_seg
      have h_L_W_tail_decomp : L_W_seg.vertices.tail
          = L_W_seg.vertices.tail.dropLast ++ [vL_exit] := by
        have h_tail_ne : L_W_seg.vertices.tail ≠ [] :=
          Walk.tail_vertices_ne_nil_of_pos L_W_seg hL_W_pos
        have := List.dropLast_append_getLast h_tail_ne
        rw [h_L_W_target] at this
        exact this.symm
      have h_L_W_rev_eq : L_W_seg.vertices.tail.reverse
          = vL_exit :: L_W_seg.vertices.tail.dropLast.reverse := by
        conv_lhs => rw [h_L_W_tail_decomp]
        simp [List.reverse_append]
      rw [h_vs, h_rev_drop, h_L_W_rev_eq] at hx
      have h_R_W_ne : R_W_seg.vertices ≠ [] :=
        Walk.vertices_ne_nil R_W_seg
      rw [List.cons_append] at hx
      change x ∈ (L_W_seg.vertices.tail.dropLast.reverse
                    ++ R_W_seg.vertices).dropLast at hx
      rw [List.dropLast_append_of_ne_nil h_R_W_ne] at hx
      rcases List.mem_append.mp hx with h_L | h_R
      · rw [List.mem_reverse] at h_L
        exact hL_W_inter x h_L
      · have h_R_W_tail_ne : R_W_seg.vertices.tail ≠ [] :=
          Walk.tail_vertices_ne_nil_of_pos R_W_seg hR_W_pos
        have h_R_W_vs_eq : R_W_seg.vertices = c :: R_W_seg.vertices.tail :=
          Walk.vertices_eq_head_cons_tail R_W_seg
        rw [h_R_W_vs_eq, List.dropLast_cons_of_ne_nil h_R_W_tail_ne] at h_R
        rcases List.mem_cons.mp h_R with h_eq | h_rest
        · exact h_eq ▸ hc_W
        · exact hR_W_inter x h_rest
    have hPhi_L : G.MarginalizationΦL W vL_exit vR_exit := by
      left
      exact ⟨_, h_phi_bif, h_phi_W⟩
    exact marg_bif_forward_assemble_bidirected G W hW hu hw huw_ne
      hvL_exit_VW hvR_exit_VW hvL_vR_exit_eq hPhi_L hL_marg_dir hR_marg_dir
      hu_notin_L_marg_drop hu_notin_R_marg hw_notin_L_marg hw_notin_R_marg_drop

/-- Refactor port of decl 60 — finish forward Case 3.B by either
constructing a sourced G-bifurcation (degenerate `vL_exit = vR_exit`)
or assembling via `mkBifurcationBidir` + assembly helper.
Mechanical port: all `Walk.*` → `Walk.refactor_*`,
`marginalize` → `marginalize`, `IsBifurcation` →
`IsBifurcation`.  The `hLR_G : s(vL, vR) ∈ G.L` hypothesis is
Sym2-typed already at the use site, so no further conversion needed.
The cons-skip wildcards `.cons _ _ _ _` → `.cons _ _ _`. -/
lemma marg_bif_forward_bidir_finish
    (G : CDMG Node) (W : Finset Node) (hW : W ⊆ G.V) {u w : Node}
    (hu : u ∈ G.marginalize W hW) (hw : w ∈ G.marginalize W hW)
    (huw_ne : u ≠ w)
    {vL vR vL_exit vR_exit : Node}
    (hvL_g : vL ∈ G) (hvR_g : vR ∈ G)
    (hLR_G : s(vL, vR) ∈ G.L) (hvL_vR_ne : vL ≠ vR)
    (hvL_exit_VW : vL_exit ∈ G.V \ W) (hvR_exit_VW : vR_exit ∈ G.V \ W)
    (L_W_part : Walk G vL vL_exit)
    (hL_W_dir : L_W_part.IsDirectedWalk)
    (hL_W_inter : ∀ x ∈ L_W_part.vertices.tail.dropLast, x ∈ W)
    (hL_W_link : (L_W_part.length ≥ 1 ∧ vL ∈ W) ∨
                 (L_W_part.length = 0 ∧ vL = vL_exit))
    (R_W_part : Walk G vR vR_exit)
    (hR_W_dir : R_W_part.IsDirectedWalk)
    (hR_W_inter : ∀ x ∈ R_W_part.vertices.tail.dropLast, x ∈ W)
    (hR_W_link : (R_W_part.length ≥ 1 ∧ vR ∈ W) ∨
                 (R_W_part.length = 0 ∧ vR = vR_exit))
    (L_marg_part : Walk G vL_exit u)
    (hL_marg_dir : L_marg_part.IsDirectedWalk)
    (R_marg_part : Walk G vR_exit w)
    (hR_marg_dir : R_marg_part.IsDirectedWalk)
    (hu_notin_L_marg_drop : u ∉ L_marg_part.vertices.dropLast)
    (hu_notin_R_marg : u ∉ R_marg_part.vertices)
    (hw_notin_L_marg : w ∉ L_marg_part.vertices)
    (hw_notin_R_marg_drop : w ∉ R_marg_part.vertices.dropLast)
    (hvR_exit_ne_u : vR_exit ≠ u) (hvL_exit_ne_w : vL_exit ≠ w) :
    ∃ q : Walk (G.marginalize W hW) u w,
      q.IsBifurcation := by
  have hvL_exit_notW : vL_exit ∉ W := (Finset.mem_sdiff.mp hvL_exit_VW).2
  have hvR_exit_notW : vR_exit ∉ W := (Finset.mem_sdiff.mp hvR_exit_VW).2
  by_cases hvL_vR_exit_eq : vL_exit = vR_exit
  · -- Degenerate case: build sourced G-bifurcation.
    subst hvL_vR_exit_eq
    have hvL_exit_ne_u : vL_exit ≠ u := hvR_exit_ne_u
    have hL_marg_pos : L_marg_part.length ≥ 1 :=
      Walk.length_pos_of_ne L_marg_part hvL_exit_ne_u
    have hR_marg_pos : R_marg_part.length ≥ 1 :=
      Walk.length_pos_of_ne R_marg_part hvL_exit_ne_w
    have hvL_exit_marg : vL_exit ∈ G.marginalize W hW := by
      change vL_exit ∈ G.J ∪ (G.V \ W); exact Finset.mem_union_right _ hvL_exit_VW
    have h_src : (Walk.mkBifurcation L_marg_part hL_marg_dir
                    hL_marg_pos R_marg_part).IsBifurcationSource vL_exit :=
      Walk.mkBifurcation_isBifurcationSource L_marg_part hL_marg_dir
        hL_marg_pos R_marg_part hR_marg_dir hR_marg_pos huw_ne
        hu_notin_L_marg_drop hu_notin_R_marg hw_notin_L_marg hw_notin_R_marg_drop
    obtain ⟨q, hq_src⟩ := marg_preserves_bifSource_forward G W hW hu hw
      hvL_exit_marg ⟨_, h_src⟩
    exact ⟨q, Walk.isBifurcationSource_to_isBifurcation
              q vL_exit hq_src⟩
  · -- Non-degenerate case: build Φ_L witness via mkBifurcationBidir.
    have hvL_exit_notin_L_W_drop : vL_exit ∉ L_W_part.vertices.dropLast := by
      intro h_in
      rcases hL_W_link with ⟨hL_W_pos, hvL_W⟩ | ⟨hL_W_zero, _⟩
      · have h_tail_ne : L_W_part.vertices.tail ≠ [] :=
          Walk.tail_vertices_ne_nil_of_pos L_W_part hL_W_pos
        have h_vs_eq : L_W_part.vertices = vL :: L_W_part.vertices.tail :=
          Walk.vertices_eq_head_cons_tail L_W_part
        rw [h_vs_eq, List.dropLast_cons_of_ne_nil h_tail_ne] at h_in
        rcases List.mem_cons.mp h_in with h_eq | h_rest
        · exact hvL_exit_notW (h_eq ▸ hvL_W)
        · exact hvL_exit_notW (hL_W_inter vL_exit h_rest)
      · cases L_W_part with
        | nil _ _ => simp [Walk.vertices, List.dropLast] at h_in
        | cons _ _ _ => simp [Walk.length] at hL_W_zero
    have hvR_exit_notin_R_W_drop : vR_exit ∉ R_W_part.vertices.dropLast := by
      intro h_in
      rcases hR_W_link with ⟨hR_W_pos, hvR_W⟩ | ⟨hR_W_zero, _⟩
      · have h_tail_ne : R_W_part.vertices.tail ≠ [] :=
          Walk.tail_vertices_ne_nil_of_pos R_W_part hR_W_pos
        have h_vs_eq : R_W_part.vertices = vR :: R_W_part.vertices.tail :=
          Walk.vertices_eq_head_cons_tail R_W_part
        rw [h_vs_eq, List.dropLast_cons_of_ne_nil h_tail_ne] at h_in
        rcases List.mem_cons.mp h_in with h_eq | h_rest
        · exact hvR_exit_notW (h_eq ▸ hvR_W)
        · exact hvR_exit_notW (hR_W_inter vR_exit h_rest)
      · cases R_W_part with
        | nil _ _ => simp [Walk.vertices, List.dropLast] at h_in
        | cons _ _ _ => simp [Walk.length] at hR_W_zero
    have hvL_exit_notin_R_W : vL_exit ∉ R_W_part.vertices := by
      intro h_in
      have h_vs_eq : R_W_part.vertices = vR :: R_W_part.vertices.tail :=
        Walk.vertices_eq_head_cons_tail R_W_part
      rw [h_vs_eq] at h_in
      rcases List.mem_cons.mp h_in with h_eq | h_rest
      · rcases hR_W_link with ⟨_, hvR_W⟩ | ⟨_, hvR_eq⟩
        · exact hvL_exit_notW (h_eq ▸ hvR_W)
        · exact hvL_vR_exit_eq (h_eq.trans hvR_eq)
      · rcases hR_W_link with ⟨hR_W_pos, _⟩ | ⟨hR_W_zero, _⟩
        · have h_R_W_tail_ne : R_W_part.vertices.tail ≠ [] :=
            Walk.tail_vertices_ne_nil_of_pos R_W_part hR_W_pos
          have h_R_W_target : R_W_part.vertices.tail.getLast h_R_W_tail_ne
              = vR_exit :=
            Walk.tail_getLast_of_pos R_W_part hR_W_pos
          have h_tail_decomp : R_W_part.vertices.tail
              = R_W_part.vertices.tail.dropLast ++ [vR_exit] := by
            have := List.dropLast_append_getLast h_R_W_tail_ne
            rw [h_R_W_target] at this; exact this.symm
          rw [h_tail_decomp] at h_rest
          rcases List.mem_append.mp h_rest with h_W | h_eq2
          · exact hvL_exit_notW (hR_W_inter vL_exit h_W)
          · rw [List.mem_singleton] at h_eq2
            exact hvL_vR_exit_eq h_eq2
        · cases R_W_part with
          | nil _ _ => simp [Walk.vertices, List.tail] at h_rest
          | cons _ _ _ => simp [Walk.length] at hR_W_zero
    have hvR_exit_notin_L_W : vR_exit ∉ L_W_part.vertices := by
      intro h_in
      have h_vs_eq : L_W_part.vertices = vL :: L_W_part.vertices.tail :=
        Walk.vertices_eq_head_cons_tail L_W_part
      rw [h_vs_eq] at h_in
      rcases List.mem_cons.mp h_in with h_eq | h_rest
      · rcases hL_W_link with ⟨_, hvL_W⟩ | ⟨_, hvL_eq⟩
        · exact hvR_exit_notW (h_eq ▸ hvL_W)
        · exact hvL_vR_exit_eq (hvL_eq.symm.trans h_eq.symm)
      · rcases hL_W_link with ⟨hL_W_pos, _⟩ | ⟨hL_W_zero, _⟩
        · have h_L_W_tail_ne : L_W_part.vertices.tail ≠ [] :=
            Walk.tail_vertices_ne_nil_of_pos L_W_part hL_W_pos
          have h_L_W_target : L_W_part.vertices.tail.getLast h_L_W_tail_ne
              = vL_exit :=
            Walk.tail_getLast_of_pos L_W_part hL_W_pos
          have h_tail_decomp : L_W_part.vertices.tail
              = L_W_part.vertices.tail.dropLast ++ [vL_exit] := by
            have := List.dropLast_append_getLast h_L_W_tail_ne
            rw [h_L_W_target] at this; exact this.symm
          rw [h_tail_decomp] at h_rest
          rcases List.mem_append.mp h_rest with h_W | h_eq2
          · exact hvR_exit_notW (hL_W_inter vR_exit h_W)
          · rw [List.mem_singleton] at h_eq2
            exact hvL_vR_exit_eq h_eq2.symm
        · cases L_W_part with
          | nil _ _ => simp [Walk.vertices, List.tail] at h_rest
          | cons _ _ _ => simp [Walk.length] at hL_W_zero
    -- Construct Φ_L witness.
    have h_phi_bif :
        (Walk.mkBifurcationBidir L_W_part hL_W_dir
            R_W_part hLR_G).IsBifurcation :=
      Walk.mkBifurcationBidir_isBifurcation L_W_part hL_W_dir
        R_W_part hR_W_dir hLR_G hvL_vR_exit_eq
        hvL_exit_notin_L_W_drop hvL_exit_notin_R_W
        hvR_exit_notin_L_W hvR_exit_notin_R_W_drop
    have h_phi_W : ∀ x ∈ (Walk.mkBifurcationBidir L_W_part hL_W_dir
                            R_W_part hLR_G).vertices.tail.dropLast, x ∈ W := by
      intro x hx
      have h_vs : (Walk.mkBifurcationBidir L_W_part hL_W_dir
                      R_W_part hLR_G).vertices
          = L_W_part.vertices.reverse.dropLast
              ++ (vL :: R_W_part.vertices) :=
        Walk.vertices_mkBifurcationBidir L_W_part hL_W_dir R_W_part hLR_G
      rw [h_vs] at hx
      have h_R_W_cons_ne : (vL :: R_W_part.vertices) ≠ [] := by simp
      rcases hL_W_link with ⟨hL_W_pos, hvL_W⟩ | ⟨hL_W_zero, _⟩
      · have h_L_W_rev_drop : L_W_part.vertices.reverse.dropLast
            = L_W_part.vertices.tail.reverse :=
          Walk.vertices_reverse_dropLast L_W_part
        rw [h_L_W_rev_drop] at hx
        have h_L_W_tail_ne : L_W_part.vertices.tail ≠ [] :=
          Walk.tail_vertices_ne_nil_of_pos L_W_part hL_W_pos
        have h_L_W_rev_ne : L_W_part.vertices.tail.reverse ≠ [] := by
          intro h
          apply h_L_W_tail_ne
          have := List.reverse_eq_nil_iff.mp h
          exact this
        rw [List.tail_append_of_ne_nil h_L_W_rev_ne,
            List.dropLast_append_of_ne_nil h_R_W_cons_ne] at hx
        rcases List.mem_append.mp hx with h_L | h_R
        · have h_L_W_target : L_W_part.vertices.tail.getLast h_L_W_tail_ne
              = vL_exit :=
            Walk.tail_getLast_of_pos L_W_part hL_W_pos
          have h_L_W_tail_decomp : L_W_part.vertices.tail
              = L_W_part.vertices.tail.dropLast ++ [vL_exit] := by
            have := List.dropLast_append_getLast h_L_W_tail_ne
            rw [h_L_W_target] at this; exact this.symm
          have h_L_W_rev_eq : L_W_part.vertices.tail.reverse
              = vL_exit :: L_W_part.vertices.tail.dropLast.reverse := by
            conv_lhs => rw [h_L_W_tail_decomp]
            simp [List.reverse_append]
          rw [h_L_W_rev_eq, List.tail_cons] at h_L
          have h_in_dropLast : x ∈ L_W_part.vertices.tail.dropLast := by
            have := h_L
            rwa [List.mem_reverse] at this
          exact hL_W_inter x h_in_dropLast
        · rw [List.dropLast_cons_of_ne_nil
                (Walk.vertices_ne_nil R_W_part)] at h_R
          rcases List.mem_cons.mp h_R with h_eq | h_in_R_drop
          · exact h_eq ▸ hvL_W
          · rcases hR_W_link with ⟨hR_W_pos, hvR_W⟩ | ⟨hR_W_zero, _⟩
            · have h_R_tail_ne : R_W_part.vertices.tail ≠ [] :=
                Walk.tail_vertices_ne_nil_of_pos R_W_part hR_W_pos
              have h_R_vs_eq : R_W_part.vertices
                  = vR :: R_W_part.vertices.tail :=
                Walk.vertices_eq_head_cons_tail R_W_part
              rw [h_R_vs_eq, List.dropLast_cons_of_ne_nil h_R_tail_ne] at h_in_R_drop
              rcases List.mem_cons.mp h_in_R_drop with h_eq | h_rest
              · exact h_eq ▸ hvR_W
              · exact hR_W_inter x h_rest
            · cases R_W_part with
              | nil _ _ => simp [Walk.vertices, List.dropLast]
                              at h_in_R_drop
              | cons _ _ _ => simp [Walk.length] at hR_W_zero
      · have h_L_W_drop_empty : L_W_part.vertices.reverse.dropLast = [] := by
          cases L_W_part with
          | nil _ _ => rfl
          | cons _ _ _ => simp [Walk.length] at hL_W_zero
        rw [h_L_W_drop_empty, List.nil_append, List.tail_cons] at hx
        rcases hR_W_link with ⟨hR_W_pos, hvR_W⟩ | ⟨hR_W_zero, _⟩
        · have h_R_tail_ne : R_W_part.vertices.tail ≠ [] :=
            Walk.tail_vertices_ne_nil_of_pos R_W_part hR_W_pos
          have h_R_vs_eq : R_W_part.vertices
              = vR :: R_W_part.vertices.tail :=
            Walk.vertices_eq_head_cons_tail R_W_part
          rw [h_R_vs_eq, List.dropLast_cons_of_ne_nil h_R_tail_ne] at hx
          rcases List.mem_cons.mp hx with h_eq | h_rest
          · exact h_eq ▸ hvR_W
          · exact hR_W_inter x h_rest
        · cases R_W_part with
          | nil _ _ => simp [Walk.vertices, List.dropLast] at hx
          | cons _ _ _ => simp [Walk.length] at hR_W_zero
    have hPhi_L : G.MarginalizationΦL W vL_exit vR_exit := by
      left; exact ⟨_, h_phi_bif, h_phi_W⟩
    exact marg_bif_forward_assemble_bidirected G W hW hu hw huw_ne
      hvL_exit_VW hvR_exit_VW hvL_vR_exit_eq hPhi_L hL_marg_dir hR_marg_dir
      hu_notin_L_marg_drop hu_notin_R_marg hw_notin_L_marg hw_notin_R_marg_drop

/-- Refactor port of decl 61 — forward Case 3.B: bidirected hinge
with at least one endpoint in `W`.  Case-splits on `(vL ∈ W, vR ∈ W)`
and dispatches to `marg_bif_forward_bidir_finish`.  Same
`hL_irrefl` / `hL_subset` rewrites as decl 57 (original lines
3183-3184, 3187). -/
lemma marg_bif_forward_bidir_with_W
    (G : CDMG Node) (W : Finset Node) (hW : W ⊆ G.V) {u w : Node}
    (hu : u ∈ G.marginalize W hW) (hw : w ∈ G.marginalize W hW)
    {p : Walk G u w} (hp : p.IsBifurcation)
    {vL vR : Node}
    (hvL_or_vR_W : vL ∈ W ∨ vR ∈ W)
    (L_g : Walk G vL u) (R_g : Walk G vR w)
    (hL_dir : L_g.IsDirectedWalk) (hR_dir : R_g.IsDirectedWalk)
    (hLR_G : s(vL, vR) ∈ G.L)
    (hL_sub : ∀ x ∈ L_g.vertices, x ∈ p.vertices.dropLast)
    (hR_sub : ∀ x ∈ R_g.vertices, x ∈ p.vertices.tail)
    (hL_drop_sub : ∀ x ∈ L_g.vertices.dropLast, x ∈ p.vertices.tail)
    (hR_drop_sub : ∀ x ∈ R_g.vertices.dropLast, x ∈ p.vertices.dropLast) :
    ∃ q : Walk (G.marginalize W hW) u w,
      q.IsBifurcation := by
  obtain ⟨huw_ne, hu_tail, hw_drop, _, _⟩ := hp
  have hu_notW : u ∉ W := notW_of_mem_marginalize hW hu
  have hw_notW : w ∉ W := notW_of_mem_marginalize hW hw
  have hvL_GV : vL ∈ G.V := G.hL_subset hLR_G (Sym2.mem_mk_left vL vR)
  have hvR_GV : vR ∈ G.V := G.hL_subset hLR_G (Sym2.mem_mk_right vL vR)
  have hvL_g : vL ∈ G := Finset.mem_union_right _ hvL_GV
  have hvR_g : vR ∈ G := Finset.mem_union_right _ hvR_GV
  have hvL_vR_ne : vL ≠ vR :=
    fun h => G.hL_irrefl hLR_G (Sym2.mk_isDiag_iff.mpr h)
  by_cases hvL_W : vL ∈ W
  · -- vL ∈ W: find_first_non_W on L_g.
    have hL_g_pos : L_g.length ≥ 1 :=
      Walk.length_pos_of_ne L_g (fun heq => hu_notW (heq ▸ hvL_W))
    obtain ⟨vL_exit, L_W_part, L_marg_part, hL_W_dir, hL_marg_dir, hL_W_pos,
            hvL_exit_notW, hL_W_inter, _, hL_g_vs_eq⟩ :=
      find_first_non_W_directed W L_g hL_dir hL_g_pos hu_notW
    have hvL_exit_GV : vL_exit ∈ G.V :=
      Walk.target_in_GV_of_directedWalk_pos L_W_part hL_W_dir hL_W_pos
    have hvL_exit_VW : vL_exit ∈ G.V \ W :=
      Finset.mem_sdiff.mpr ⟨hvL_exit_GV, hvL_exit_notW⟩
    have hL_marg_ne : L_marg_part.vertices ≠ [] :=
      Walk.vertices_ne_nil L_marg_part
    have hL_marg_sub_L_g :
        ∀ x ∈ L_marg_part.vertices, x ∈ L_g.vertices := fun x hx =>
      by rw [hL_g_vs_eq]; exact List.mem_append.mpr (Or.inr hx)
    have hL_marg_drop_sub_L_g_drop :
        ∀ x ∈ L_marg_part.vertices.dropLast,
          x ∈ L_g.vertices.dropLast := fun x hx => by
      rw [hL_g_vs_eq, List.dropLast_append_of_ne_nil hL_marg_ne]
      exact List.mem_append.mpr (Or.inr hx)
    have hu_notin_L_marg_drop : u ∉ L_marg_part.vertices.dropLast := fun h_in =>
      hu_tail (hL_drop_sub u (hL_marg_drop_sub_L_g_drop u h_in))
    have hw_notin_L_marg : w ∉ L_marg_part.vertices := fun h_in =>
      hw_drop (hL_sub w (hL_marg_sub_L_g w h_in))
    by_cases hvR_W : vR ∈ W
    · -- Sub-case (C): vL ∈ W AND vR ∈ W.  find_first_non_W on R_g.
      have hR_g_pos : R_g.length ≥ 1 :=
        Walk.length_pos_of_ne R_g (fun heq => hw_notW (heq ▸ hvR_W))
      obtain ⟨vR_exit, R_W_part, R_marg_part, hR_W_dir, hR_marg_dir, hR_W_pos,
              hvR_exit_notW, hR_W_inter, _, hR_g_vs_eq⟩ :=
        find_first_non_W_directed W R_g hR_dir hR_g_pos hw_notW
      have hvR_exit_GV : vR_exit ∈ G.V :=
        Walk.target_in_GV_of_directedWalk_pos R_W_part hR_W_dir hR_W_pos
      have hvR_exit_VW : vR_exit ∈ G.V \ W :=
        Finset.mem_sdiff.mpr ⟨hvR_exit_GV, hvR_exit_notW⟩
      have hR_marg_ne : R_marg_part.vertices ≠ [] :=
        Walk.vertices_ne_nil R_marg_part
      have hR_marg_sub_R_g :
          ∀ x ∈ R_marg_part.vertices, x ∈ R_g.vertices := fun x hx =>
        by rw [hR_g_vs_eq]; exact List.mem_append.mpr (Or.inr hx)
      have hR_marg_drop_sub_R_g_drop :
          ∀ x ∈ R_marg_part.vertices.dropLast,
            x ∈ R_g.vertices.dropLast := fun x hx => by
        rw [hR_g_vs_eq, List.dropLast_append_of_ne_nil hR_marg_ne]
        exact List.mem_append.mpr (Or.inr hx)
      have hu_notin_R_marg : u ∉ R_marg_part.vertices := fun h_in =>
        hu_tail (hR_sub u (hR_marg_sub_R_g u h_in))
      have hw_notin_R_marg_drop : w ∉ R_marg_part.vertices.dropLast := fun h_in =>
        hw_drop (hR_drop_sub w (hR_marg_drop_sub_R_g_drop w h_in))
      have hvR_exit_ne_u : vR_exit ≠ u := fun heq =>
        hu_tail (hR_sub _ (hR_marg_sub_R_g _
          (heq ▸ Walk.head_mem_vertices R_marg_part)))
      have hvL_exit_ne_w : vL_exit ≠ w := fun heq =>
        hw_drop (hL_sub _ (hL_marg_sub_L_g _
          (heq ▸ Walk.head_mem_vertices L_marg_part)))
      exact marg_bif_forward_bidir_finish G W hW hu hw huw_ne
        hvL_g hvR_g hLR_G hvL_vR_ne hvL_exit_VW hvR_exit_VW
        L_W_part hL_W_dir hL_W_inter (Or.inl ⟨hL_W_pos, hvL_W⟩)
        R_W_part hR_W_dir hR_W_inter (Or.inl ⟨hR_W_pos, hvR_W⟩)
        L_marg_part hL_marg_dir R_marg_part hR_marg_dir
        hu_notin_L_marg_drop hu_notin_R_marg hw_notin_L_marg hw_notin_R_marg_drop
        hvR_exit_ne_u hvL_exit_ne_w
    · -- Sub-case (A): vL ∈ W, vR ∉ W.  R_W_part = nil at vR, vR_exit = vR.
      have hvR_exit_VW : vR ∈ G.V \ W := Finset.mem_sdiff.mpr ⟨hvR_GV, hvR_W⟩
      have hu_notin_R_g : u ∉ R_g.vertices := fun h_in =>
        hu_tail (hR_sub u h_in)
      have hw_notin_R_g_drop : w ∉ R_g.vertices.dropLast := fun h_in =>
        hw_drop (hR_drop_sub w h_in)
      have hvR_ne_u : vR ≠ u := fun heq =>
        hu_tail (hR_sub _ (heq ▸ Walk.head_mem_vertices R_g))
      have hvL_exit_ne_w : vL_exit ≠ w := fun heq =>
        hw_drop (hL_sub _ (hL_marg_sub_L_g _
          (heq ▸ Walk.head_mem_vertices L_marg_part)))
      have h_nil_R : (Walk.nil vR hvR_g
                        : Walk G vR vR).length = 0 := rfl
      exact marg_bif_forward_bidir_finish G W hW hu hw huw_ne
        hvL_g hvR_g hLR_G hvL_vR_ne hvL_exit_VW hvR_exit_VW
        L_W_part hL_W_dir hL_W_inter (Or.inl ⟨hL_W_pos, hvL_W⟩)
        (Walk.nil vR hvR_g) trivial
        (by intro x hx
            simp [Walk.vertices, List.tail, List.dropLast] at hx)
        (Or.inr ⟨h_nil_R, rfl⟩)
        L_marg_part hL_marg_dir R_g hR_dir
        hu_notin_L_marg_drop hu_notin_R_g hw_notin_L_marg hw_notin_R_g_drop
        hvR_ne_u hvL_exit_ne_w
  · -- vL ∉ W, so vR ∈ W.
    have hvR_W : vR ∈ W := hvL_or_vR_W.resolve_left hvL_W
    have hvL_VW : vL ∈ G.V \ W := Finset.mem_sdiff.mpr ⟨hvL_GV, hvL_W⟩
    have hR_g_pos : R_g.length ≥ 1 :=
      Walk.length_pos_of_ne R_g (fun heq => hw_notW (heq ▸ hvR_W))
    obtain ⟨vR_exit, R_W_part, R_marg_part, hR_W_dir, hR_marg_dir, hR_W_pos,
            hvR_exit_notW, hR_W_inter, _, hR_g_vs_eq⟩ :=
      find_first_non_W_directed W R_g hR_dir hR_g_pos hw_notW
    have hvR_exit_GV : vR_exit ∈ G.V :=
      Walk.target_in_GV_of_directedWalk_pos R_W_part hR_W_dir hR_W_pos
    have hvR_exit_VW : vR_exit ∈ G.V \ W :=
      Finset.mem_sdiff.mpr ⟨hvR_exit_GV, hvR_exit_notW⟩
    have hR_marg_ne : R_marg_part.vertices ≠ [] :=
      Walk.vertices_ne_nil R_marg_part
    have hR_marg_sub_R_g :
        ∀ x ∈ R_marg_part.vertices, x ∈ R_g.vertices := fun x hx =>
      by rw [hR_g_vs_eq]; exact List.mem_append.mpr (Or.inr hx)
    have hR_marg_drop_sub_R_g_drop :
        ∀ x ∈ R_marg_part.vertices.dropLast,
          x ∈ R_g.vertices.dropLast := fun x hx => by
      rw [hR_g_vs_eq, List.dropLast_append_of_ne_nil hR_marg_ne]
      exact List.mem_append.mpr (Or.inr hx)
    have hu_notin_R_marg : u ∉ R_marg_part.vertices := fun h_in =>
      hu_tail (hR_sub u (hR_marg_sub_R_g u h_in))
    have hw_notin_R_marg_drop : w ∉ R_marg_part.vertices.dropLast := fun h_in =>
      hw_drop (hR_drop_sub w (hR_marg_drop_sub_R_g_drop w h_in))
    have hu_notin_L_g_drop : u ∉ L_g.vertices.dropLast := fun h_in =>
      hu_tail (hL_drop_sub u h_in)
    have hw_notin_L_g : w ∉ L_g.vertices := fun h_in =>
      hw_drop (hL_sub w h_in)
    have hvR_exit_ne_u : vR_exit ≠ u := fun heq =>
      hu_tail (hR_sub _ (hR_marg_sub_R_g _
        (heq ▸ Walk.head_mem_vertices R_marg_part)))
    have hvL_ne_w : vL ≠ w := fun heq =>
      hw_drop (hL_sub _ (heq ▸ Walk.head_mem_vertices L_g))
    have h_nil_L : (Walk.nil vL hvL_g
                      : Walk G vL vL).length = 0 := rfl
    exact marg_bif_forward_bidir_finish G W hW hu hw huw_ne
      hvL_g hvR_g hLR_G hvL_vR_ne hvL_VW hvR_exit_VW
      (Walk.nil vL hvL_g) trivial
      (by intro x hx
          simp [Walk.vertices, List.tail, List.dropLast] at hx)
      (Or.inr ⟨h_nil_L, rfl⟩)
      R_W_part hR_W_dir hR_W_inter (Or.inl ⟨hR_W_pos, hvR_W⟩)
      L_g hL_dir R_marg_part hR_marg_dir
      hu_notin_L_g_drop hu_notin_R_marg hw_notin_L_g hw_notin_R_marg_drop
      hvR_exit_ne_u hvL_ne_w

/-- Refactor port of decl 62 — top-level wrapper for the forward
direction of sub-claim ii(a).  Mechanical wrapper that case-splits on
hinge type, dispatching to the relevant `refactor_*` helper. -/
lemma marg_preserves_bif_forward
    (G : CDMG Node) (W : Finset Node) (hW : W ⊆ G.V) {u w : Node}
    (hu : u ∈ G.marginalize W hW) (hw : w ∈ G.marginalize W hW)
    (h : ∃ p : Walk G u w, p.IsBifurcation) :
    ∃ q : Walk (G.marginalize W hW) u w,
      q.IsBifurcation := by
  obtain ⟨p, hp⟩ := h
  obtain ⟨i, hp_split⟩ := hp.2.2.2
  by_cases h_dir : p.IsBifurcationDirectedHingeWithSplit i
  · obtain ⟨c, _, _, _, _, _, _, hidx, _, _, _, _⟩ :=
      Walk.exists_arms_of_bifurcation_directed_hinge_strong p i h_dir
    by_cases hc_marg : c ∈ G.marginalize W hW
    · exact marg_bif_forward_dir_hinge_src_marg G W hW hu hw hp h_dir hidx hc_marg
    · exact marg_bif_forward_dir_hinge_src_W G W hW hu hw hp h_dir hidx hc_marg
  · obtain ⟨vL, vR, L_g, R_g, hL_dir, hR_dir, hLR_G, _,
            hL_sub, hR_sub, hL_drop_sub, hR_drop_sub⟩ :=
      Walk.exists_arms_of_bifurcation_bidir_hinge_strong p i hp_split h_dir
    by_cases hvL_W : vL ∈ W
    · exact marg_bif_forward_bidir_with_W G W hW hu hw hp (Or.inl hvL_W)
        L_g R_g hL_dir hR_dir hLR_G hL_sub hR_sub hL_drop_sub hR_drop_sub
    · by_cases hvR_W : vR ∈ W
      · exact marg_bif_forward_bidir_with_W G W hW hu hw hp (Or.inr hvR_W)
          L_g R_g hL_dir hR_dir hLR_G hL_sub hR_sub hL_drop_sub hR_drop_sub
      · exact marg_bif_forward_bidir_both_notW G W hW hu hw hp
          hvL_W hvR_W L_g R_g hL_dir hR_dir hLR_G
          hL_sub hR_sub hL_drop_sub hR_drop_sub

/-- Refactor port of decl 63 — top-level wrapper for the backward
direction of sub-claim ii(a).  Mechanical wrapper that case-splits on
hinge type. -/
lemma marg_preserves_bif_backward
    (G : CDMG Node) (W : Finset Node) (hW : W ⊆ G.V) {u w : Node}
    (hu : u ∈ G.marginalize W hW) (hw : w ∈ G.marginalize W hW)
    (h : ∃ q : Walk (G.marginalize W hW) u w,
            q.IsBifurcation) :
    ∃ p : Walk G u w, p.IsBifurcation := by
  obtain ⟨q, hq⟩ := h
  obtain ⟨i, hq_split⟩ := hq.2.2.2
  by_cases h_dir : q.IsBifurcationDirectedHingeWithSplit i
  · exact marg_bif_backward_dir_hinge G W hW hu hw hq h_dir
  · exact marg_bif_backward_bidir_hinge G W hW hu hw hq hq_split h_dir

-- ## Refactor replacements — Batch 12 (main theorems T1–T5)
--
-- The five top-level theorems of `claim_3_16`.  Each body is a thin
-- wrapper around the per-direction / per-case helpers ported in
-- Batches 1–11; the porting is a mechanical identifier rewrite
-- (`Walk → Walk`, `CDMG → CDMG`,
-- `marginalize → marginalize`, `Anc → Anc`,
-- `IsAcyclic → IsAcyclic`,
-- `IsTopologicalOrder → IsTopologicalOrder`,
-- `MarginalizationΦE → MarginalizationΦE`,
-- plus the local helper prefix swap).  No structural argument changes.

/-- Refactor port of T1 — sub-claim i (preservation of ancestral
relations).  The biconditional unfolds `Anc` to the
"exists a directed `Walk`" shape; the forward direction
calls `project_directed_walk_marginalize`, the backward
direction calls `expand_directed_walk_marginalize` and
discards its extra vertex-bound conjuncts.  Identifier swaps only;
the proof structure is unchanged. -/
-- claim_3_16 -- start statement
theorem marginalize_preserves_ancestors (G : CDMG Node) (W : Finset Node)
    (hW : W ⊆ G.V) (v₁ v₂ : Node)
    (hv₁ : v₁ ∈ G.marginalize W hW) (hv₂ : v₂ ∈ G.marginalize W hW) :
    v₁ ∈ G.Anc v₂ ↔ v₁ ∈ (G.marginalize W hW).Anc v₂
-- claim_3_16 -- end statement
  := by
  constructor
  · rintro ⟨_, p, hp_dir⟩
    refine ⟨hv₁, ?_⟩
    exact project_directed_walk_marginalize p hp_dir hv₁ hv₂
  · rintro ⟨_, p, hp_dir⟩
    refine ⟨mem_of_mem_marginalize hv₁, ?_⟩
    obtain ⟨q, hq_dir, _, _, _, _, _⟩ :=
      expand_directed_walk_marginalize p hp_dir
    exact ⟨q, hq_dir⟩

/-- Refactor port of T2 — sub-claim ii(a) (preservation of
bifurcations, sourceless).  Pure wrapper around the per-direction
helpers `marg_preserves_bif_forward` /
`marg_preserves_bif_backward` (Batch 11).  Identifier
swaps only. -/
-- claim_3_16 -- start statement
theorem marginalize_preserves_bifurcation (G : CDMG Node) (W : Finset Node)
    (hW : W ⊆ G.V) (v₁ v₂ : Node)
    (hv₁ : v₁ ∈ G.marginalize W hW) (hv₂ : v₂ ∈ G.marginalize W hW) :
    ((∃ p : Walk G v₁ v₂, p.IsBifurcation) ∨
        (∃ p : Walk G v₂ v₁, p.IsBifurcation))
      ↔
    ((∃ p : Walk (G.marginalize W hW) v₁ v₂, p.IsBifurcation) ∨
        (∃ p : Walk (G.marginalize W hW) v₂ v₁, p.IsBifurcation))
-- claim_3_16 -- end statement
  := by
  constructor
  · rintro (⟨p, hp⟩ | ⟨p, hp⟩)
    · exact Or.inl (marg_preserves_bif_forward G W hW hv₁ hv₂ ⟨p, hp⟩)
    · exact Or.inr (marg_preserves_bif_forward G W hW hv₂ hv₁ ⟨p, hp⟩)
  · rintro (⟨q, hq⟩ | ⟨q, hq⟩)
    · exact Or.inl (marg_preserves_bif_backward G W hW hv₁ hv₂ ⟨q, hq⟩)
    · exact Or.inr (marg_preserves_bif_backward G W hW hv₂ hv₁ ⟨q, hq⟩)

/-- Refactor port of T3 — sub-claim ii(b) (preservation of
bifurcations, sourced).  Pure wrapper around
`marg_preserves_bifSource_forward` /
`marg_preserves_bifSource_backward` (Batch 9).  Identifier
swaps only. -/
-- claim_3_16 -- start statement
theorem marginalize_preserves_bifurcation_with_source (G : CDMG Node)
    (W : Finset Node) (hW : W ⊆ G.V) (v₁ v₂ v₃ : Node)
    (hv₁ : v₁ ∈ G.marginalize W hW) (hv₂ : v₂ ∈ G.marginalize W hW)
    (hv₃ : v₃ ∈ G.marginalize W hW) :
    ((∃ p : Walk G v₁ v₂, p.IsBifurcationSource v₃) ∨
        (∃ p : Walk G v₂ v₁, p.IsBifurcationSource v₃))
      ↔
    ((∃ p : Walk (G.marginalize W hW) v₁ v₂,
        p.IsBifurcationSource v₃) ∨
        (∃ p : Walk (G.marginalize W hW) v₂ v₁,
          p.IsBifurcationSource v₃))
-- claim_3_16 -- end statement
  := by
  constructor
  · rintro (h12 | h21)
    · exact Or.inl (marg_preserves_bifSource_forward G W hW hv₁ hv₂ hv₃ h12)
    · exact Or.inr (marg_preserves_bifSource_forward G W hW hv₂ hv₁ hv₃ h21)
  · rintro (h12 | h21)
    · exact Or.inl (marg_preserves_bifSource_backward G W hW hv₁ hv₂ hv₃ h12)
    · exact Or.inr (marg_preserves_bifSource_backward G W hW hv₂ hv₁ hv₃ h21)

/-- Refactor port of T4 — sub-claim iii(a) (preservation of
acyclicity).  Expands a hypothetical non-trivial directed
marg-cycle back to a directed cycle in `G` via
`expand_directed_walk_marginalize`, contradicting
`G.IsAcyclic`.  Identifier swaps;
`q.length` → `q.length`. -/
-- claim_3_16 -- start statement
theorem marginalize_preserves_acyclic (G : CDMG Node) (W : Finset Node)
    (hW : W ⊆ G.V) (hAcyc : G.IsAcyclic) :
    (G.marginalize W hW).IsAcyclic
-- claim_3_16 -- end statement
  := by
  intro v hv_marg ⟨p, hp_dir, hp_pos⟩
  have hv_g : v ∈ G := mem_of_mem_marginalize hv_marg
  obtain ⟨q, hq_dir, hq_len, _, _, _, _⟩ :=
    expand_directed_walk_marginalize p hp_dir
  have hq_pos : q.length ≥ 1 := by omega
  exact hAcyc v hv_g ⟨q, hq_dir, hq_pos⟩

/-- Refactor port of T5 — sub-claim iii(b) (topological order
preserved by restriction).  Pointwise transport via
`mem_of_mem_marginalize` for irreflexivity / transitivity /
trichotomy; parent-precedence unfolds the marg-`E` `Finset.filter`
to a `MarginalizationΦE` witness, then chains `lt` along
the witnessing directed `G`-walk via
`Walk.lt_of_directedWalk_pos`.  The marg-`E`
filter shape is identical to the original modulo names. -/
-- claim_3_16 -- start statement
theorem marginalize_restricts_topological_order (G : CDMG Node)
    (W : Finset Node) (hW : W ⊆ G.V)
    (lt : Node → Node → Prop) (hlt : G.IsTopologicalOrder lt) :
    (G.marginalize W hW).IsTopologicalOrder lt
-- claim_3_16 -- end statement
  := by
  obtain ⟨⟨h_irrefl, h_trans, h_total⟩, h_parent⟩ := hlt
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro v hv
    exact h_irrefl v (mem_of_mem_marginalize hv)
  · intro u hu v hv w hw huv hvw
    exact h_trans u (mem_of_mem_marginalize hu)
                  v (mem_of_mem_marginalize hv)
                  w (mem_of_mem_marginalize hw) huv hvw
  · intro v hv w hw
    exact h_total v (mem_of_mem_marginalize hv)
                  w (mem_of_mem_marginalize hw)
  · intro v w hvw_parent
    obtain ⟨hv_marg, hvw_edge⟩ := hvw_parent
    have hvw_filter : (v, w) ∈ ((G.J ∪ (G.V \ W)) ×ˢ (G.V \ W)).filter
          (fun e => G.MarginalizationΦE W e.1 e.2) := hvw_edge
    have hvw_phi : G.MarginalizationΦE W v w :=
      (Finset.mem_filter.mp hvw_filter).2
    obtain ⟨p, hp_dir, hp_pos, _⟩ := hvw_phi
    exact Walk.lt_of_directedWalk_pos h_trans h_parent p hp_dir hp_pos

-- ## Set-level corollaries of `marginalize_preserves_ancestors`
-- (consumed by `claim_3_25` `ISigmaSeparationMarginalization`)
--
-- The four lemmas below are *set-level* repackagings of the
-- ancestor / descendant / SCC preservation content above,
-- shaped for direct consumption in the σ-blocking transport of
-- `claim_3_25` (Step 2(a) and 2(b) of the tex proof at
-- `Section3_3/tex/claim_3_25_proof_ISigmaSeparation.tex`,
-- lines 129-148).
--
-- * `marginalize_preserves_descendants` — mirror of
--   `marginalize_preserves_ancestors` (line 3830 above) with the
--   walk direction swapped.  Not in the codebase prior to this
--   subtask; proved here as a direct port of the ancestors proof
--   with the two endpoints `(v₁, v₂)` swapped at the
--   `project_directed_walk_marginalize` /
--   `expand_directed_walk_marginalize` call sites (since `Desc`
--   uses `Walk G v₂ v₁` where `Anc` uses `Walk G v₁ v₂`).
--
-- * `anc_set_marginalize_eq_inter_carrier` — for `C` disjoint
--   from `W` (and `C ⊆ J ∪ V`), `Anc^{G^{∖W}}(C) = Anc^G(C) ∩
--   (↑J ∪ ↑(V ∖ W))`.  Captures the LN's equation (★) of the
--   tex proof's Step 2(a).
--
-- * `subset_anc_set_marginalize_of_disjoint` —
--   `C ⊆ Anc^{G^{∖W}}(C)`, the reflexive self-membership
--   corollary used in Step 2(a)'s collider-clause transport
--   (every `c ∈ C` is its own ancestor in `G^{∖W}` via the
--   trivial walk).
--
-- * `sc_marginalize_eq_sdiff` — `Sc^{G^{∖W}}(v) = Sc^G(v) ∖ ↑W`
--   for `v ∈ V ∖ W`.  Captures the LN's equation (★★) of the
--   tex proof's Step 2(b); proved by `Anc ∩ Desc` unfolding plus
--   the two preservation theorems.

/-- Mirror of `marginalize_preserves_ancestors` for descendants:
`v₁ ∈ Desc^G(v₂) ↔ v₁ ∈ Desc^{G^{∖W}}(v₂)` for `v₁, v₂` in the
carrier of `G^{∖W}` (i.e.\ `J ∪ (V ∖ W)`).  Used as a building
block for the SCC preservation lemma `sc_marginalize_eq_sdiff`.
The proof structurally mirrors `marginalize_preserves_ancestors`:
the only delta is that `Desc` quantifies a walk `Walk G v₂ v₁`
(target-to-source) where `Anc` quantifies `Walk G v₁ v₂`, so the
two endpoint witnesses `hv₁, hv₂` are swapped at the
`project_directed_walk_marginalize` /
`expand_directed_walk_marginalize` call sites. -/
theorem marginalize_preserves_descendants (G : CDMG Node) (W : Finset Node)
    (hW : W ⊆ G.V) (v₁ v₂ : Node)
    (hv₁ : v₁ ∈ G.marginalize W hW) (hv₂ : v₂ ∈ G.marginalize W hW) :
    v₁ ∈ G.Desc v₂ ↔ v₁ ∈ (G.marginalize W hW).Desc v₂ := by
  constructor
  · rintro ⟨_, p, hp_dir⟩
    refine ⟨hv₁, ?_⟩
    exact project_directed_walk_marginalize p hp_dir hv₂ hv₁
  · rintro ⟨_, p, hp_dir⟩
    refine ⟨mem_of_mem_marginalize hv₁, ?_⟩
    obtain ⟨q, hq_dir, _, _, _, _, _⟩ :=
      expand_directed_walk_marginalize p hp_dir
    exact ⟨q, hq_dir⟩

/-- Set-level corollary of `marginalize_preserves_ancestors`:
the ancestor set of `C` in the marginalized CDMG equals the
intersection of the ambient ancestor set with the carrier of the
marginalized CDMG, provided `C` is well-typed in `G` and disjoint
from `W`.  Spec source: tex proof line 134-137 (the LN's equation
(★) of Step 2(a) of `claim_3_25`).  The carrier intersection is
`(↑G.J : Set Node) ∪ ↑(G.V \ W)`, the Set-level rendering of
`G^{∖W}`'s vertex set `J^{∖W} ∪ V^{∖W} = J ∪ (V ∖ W)`. -/
lemma anc_set_marginalize_eq_inter_carrier
    (G : CDMG Node) (W : Finset Node) (hW : W ⊆ G.V)
    (C : Set Node) (hC : C ⊆ (↑G.J : Set Node) ∪ ↑G.V)
    (hCW : Disjoint (↑W : Set Node) C) :
    (G.marginalize W hW).AncSet C
      = G.AncSet C ∩ ((↑G.J : Set Node) ∪ ↑(G.V \ W)) := by
  -- Every `c ∈ C` lifts to a node of the marginalized graph:
  -- `c ∈ J ∪ V` (from `hC`) and `c ∉ W` (from `hCW`) together
  -- give `c ∈ J ∪ (V ∖ W) = carrier(G^{∖W})`.
  have hC_marg : ∀ c ∈ C, c ∈ G.marginalize W hW := by
    intro c hc
    change c ∈ G.J ∪ (G.V \ W)
    have hc_G : c ∈ (↑G.J : Set Node) ∪ ↑G.V := hC hc
    have hc_notW : c ∉ (↑W : Set Node) := Set.disjoint_right.mp hCW hc
    rcases hc_G with hJ | hV
    · exact Finset.mem_union_left _ (Finset.mem_coe.mp hJ)
    · refine Finset.mem_union_right _
        (Finset.mem_sdiff.mpr ⟨Finset.mem_coe.mp hV, ?_⟩)
      intro hxW
      exact hc_notW (Finset.mem_coe.mpr hxW)
  ext v
  unfold CDMG.AncSet
  simp only [Set.mem_iUnion, Set.mem_inter_iff]
  constructor
  · rintro ⟨c, hc_C, hvc⟩
    have hc_marg : c ∈ G.marginalize W hW := hC_marg c hc_C
    have hv_marg : v ∈ G.marginalize W hW := hvc.1
    refine ⟨⟨c, hc_C, ?_⟩, ?_⟩
    · exact (marginalize_preserves_ancestors G W hW v c hv_marg hc_marg).mpr hvc
    · -- `v ∈ G.J ∪ (G.V \ W)` lifts to `v ∈ ↑G.J ∪ ↑(G.V \ W)`
      have hv_union : v ∈ G.J ∪ (G.V \ W) := hv_marg
      rcases Finset.mem_union.mp hv_union with hJ | hVW
      · exact Or.inl (Finset.mem_coe.mpr hJ)
      · exact Or.inr (Finset.mem_coe.mpr hVW)
  · rintro ⟨⟨c, hc_C, hvc⟩, hv_carrier⟩
    have hc_marg : c ∈ G.marginalize W hW := hC_marg c hc_C
    have hv_marg : v ∈ G.marginalize W hW := by
      change v ∈ G.J ∪ (G.V \ W)
      rcases hv_carrier with hJ | hVW
      · exact Finset.mem_union_left _ (Finset.mem_coe.mp hJ)
      · exact Finset.mem_union_right _ (Finset.mem_coe.mp hVW)
    exact ⟨c, hc_C,
      (marginalize_preserves_ancestors G W hW v c hv_marg hc_marg).mp hvc⟩

/-- Reflexive inclusion `C ⊆ Anc^{G^{∖W}}(C)`: each `c ∈ C` is its
own ancestor in `G^{∖W}` via the trivial walk `Walk.nil`, provided
`c ∉ W` (from disjointness) and `c ∈ J ∪ V` (well-typedness).
Spec source: tex proof line 138 (Step 2(a) of `claim_3_25`).  The
underlying mathematical fact is the LN's "$C \subseteq \Anc^G(C)$"
reflexivity clause of def_3_5, item iv, transported across
marginalization. -/
lemma subset_anc_set_marginalize_of_disjoint
    (G : CDMG Node) (W : Finset Node) (hW : W ⊆ G.V)
    (C : Set Node) (hC : C ⊆ (↑G.J : Set Node) ∪ ↑G.V)
    (hCW : Disjoint (↑W : Set Node) C) :
    C ⊆ (G.marginalize W hW).AncSet C := by
  intro c hc
  unfold CDMG.AncSet
  simp only [Set.mem_iUnion]
  have hc_G : c ∈ (↑G.J : Set Node) ∪ ↑G.V := hC hc
  have hc_notW : c ∉ (↑W : Set Node) := Set.disjoint_right.mp hCW hc
  have hc_marg : c ∈ G.marginalize W hW := by
    change c ∈ G.J ∪ (G.V \ W)
    rcases hc_G with hJ | hV
    · exact Finset.mem_union_left _ (Finset.mem_coe.mp hJ)
    · refine Finset.mem_union_right _
        (Finset.mem_sdiff.mpr ⟨Finset.mem_coe.mp hV, ?_⟩)
      intro hxW
      exact hc_notW (Finset.mem_coe.mpr hxW)
  exact ⟨c, hc, hc_marg, Walk.nil c hc_marg, trivial⟩

/-- Set-level SCC preservation: `Sc^{G^{∖W}}(v) = Sc^G(v) ∖ ↑W`
for `v ∈ V ∖ W`.  Spec source: tex proof lines 140-148 (the LN's
equation (★★) of Step 2(b) of `claim_3_25`).  The proof
unfolds `Sc = Anc ∩ Desc` (def_3_5, item vii) and chains
`marginalize_preserves_ancestors` with
`marginalize_preserves_descendants`; the `↑W` on the right is
the Set-coercion of the (Finset) marginalization set `W`. -/
lemma sc_marginalize_eq_sdiff
    (G : CDMG Node) (W : Finset Node) (hW : W ⊆ G.V)
    {v : Node} (hv : v ∈ G.V \ W) :
    (G.marginalize W hW).Sc v = G.Sc v \ (↑W : Set Node) := by
  have hv_marg : v ∈ G.marginalize W hW := by
    change v ∈ G.J ∪ (G.V \ W)
    exact Finset.mem_union_right _ hv
  ext x
  unfold CDMG.Sc
  simp only [Set.mem_inter_iff, Set.mem_diff]
  constructor
  · rintro ⟨hx_anc, hx_desc⟩
    have hx_marg : x ∈ G.marginalize W hW := hx_anc.1
    have hx_notW : x ∉ W := notW_of_mem_marginalize hW hx_marg
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact (marginalize_preserves_ancestors G W hW x v hx_marg hv_marg).mpr hx_anc
    · exact (marginalize_preserves_descendants G W hW x v hx_marg hv_marg).mpr hx_desc
    · intro hxW
      exact hx_notW (Finset.mem_coe.mp hxW)
  · rintro ⟨⟨hx_G_anc, hx_G_desc⟩, hx_notW⟩
    have hx_G : x ∈ G := hx_G_anc.1
    have hx_marg : x ∈ G.marginalize W hW := by
      change x ∈ G.J ∪ (G.V \ W)
      have hx_union : x ∈ G.J ∪ G.V := hx_G
      rcases Finset.mem_union.mp hx_union with hJ | hV
      · exact Finset.mem_union_left _ hJ
      · refine Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hV, ?_⟩)
        intro hxW
        exact hx_notW (Finset.mem_coe.mpr hxW)
    refine ⟨?_, ?_⟩
    · exact (marginalize_preserves_ancestors G W hW x v hx_marg hv_marg).mp hx_G_anc
    · exact (marginalize_preserves_descendants G W hW x v hx_marg hv_marg).mp hx_G_desc

end CDMG

end Causality
