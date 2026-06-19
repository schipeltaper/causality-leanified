import Chapter3_GraphTheory.Section3_1.CDMG
import Chapter3_GraphTheory.Section3_1.CDMGNotation
import Chapter3_GraphTheory.Section3_1.Acyclicity
import Chapter3_GraphTheory.Section3_1.TopologicalOrder
import Chapter3_GraphTheory.Section3_2.HardInterventionOn

namespace Causality

/-!
# Acyclicity and topological orders are preserved under hard
intervention (`claim_3_3`)

This file formalises the LN remark block `claim_3_3` (rendered as a
`\begin{Rem}` in `graphs.tex`, immediately after the hard-intervention
definition `def_3_10`):

> If `G` is acyclic then also `G_{\doit(W)}` is acyclic and a
> topological order for `G` is also one for `G_{\doit(W)}`.

The authoritative spec is the rewritten canonical tex statement at
`leanification/Chapter3_GraphTheory/Section3_2/tex/`
`claim_3_3_statement_AcyclicPreservedUnderDo.tex`, verified equivalent
to the LN block augmented with one operator clarification:

* `[w_is_free_unquantified_in_claim_body]` — `W` is universally
  quantified, ranging over all `W ⊆ J ∪ V` for which `G_{\doit(W)}`
  is defined per `def_3_10`.  The side condition `W ⊆ J ∪ V` is the
  one inherited verbatim from `def_3_10`, so `W` may overlap the
  input-node set `J`.

The claim packages two sub-conclusions under a single antecedent
`G.IsAcyclic`:

* (a) `(G.hardInterventionOn W hW).IsAcyclic` — the intervened CDMG
  is itself acyclic, in the sense of `def_3_6`.
* (b) `∀ lt, G.IsTopologicalOrder lt → (G.hardInterventionOn W hW).IsTopologicalOrder lt`
  — every topological order of `G` (in the sense of `def_3_8`) is a
  topological order of the intervened CDMG, where the same relation
  `lt : Node → Node → Prop` is reused without any re-indexing.

The label set `L` plays no role on either side: acyclicity (`def_3_6`)
is defined via directed walks built from `G.E` alone, and a
topological order (`def_3_8`) is defined via the parent set `Pa^G`
(also built from `G.E` alone).  The registered deviation
`hard_intervention_l_symmetrized_removal` for `def_3_10`
(`leanification/deviations.json`) only affects `L`, so it does not
propagate into this claim's signature or content.

The theorem body is filled in by `prove_claim_in_lean` (Manager B),
following the verified TeX proof at
`tex/claim_3_3_proof_AcyclicPreservedUnderDo.tex`.

-/

namespace CDMG

-- ## Design choice — statement context (refactor twin)
--
-- Three-dash `--- start helper` markers match the convention used
-- across `CDMG.lean`, `CDMGNotation.lean`, `Walks.lean`,
-- `EdgeRelations.lean`, `CDMGRestrictions.lean`, `Acyclicity.lean`,
-- `CDMGTypes.lean`, `TopologicalOrder.lean`, and
-- `FamilyRelationships.lean` for the `variable` line that binds the
-- implicit parameters into the five proof-only helpers and the main
-- theorem wrapped below.  Both `Node : Type*` and `[DecidableEq Node]`
-- are inherited verbatim from `def_3_1`'s refactor twin
-- (`CDMG`): the `Membership Node (CDMG Node)`
-- instance from `def_3_2`'s refactor twin (`instMembership`
-- in `CDMGNotation.lean`) reduces to `Finset.mem` on `G.J ∪ G.V` and
-- so needs `DecidableEq Node`; the `Walk` recursion in the
-- four walk-class helpers, the `IsDirectedWalk` Prop in the
-- main theorem body, and the `G.Pa w` set-builder in
-- `IsTopologicalOrder` all transitively rely on
-- `DecidableEq Node` for their `Finset` / `Sym2`-typed membership
-- checks.
-- claim_3_3 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- claim_3_3 --- end helper

-- ## Proof-only helpers (refactor twins)
--
-- The five helpers below are refactor twins of the corresponding
-- `private lemma / private def` declarations in the original
-- `namespace CDMG` block above; they are infrastructure for the proof
-- of `acyclic_preserved_under_do`.  They are deliberately
-- private and carry no marker comments other than the
-- REFACTOR-BLOCK-REPLACEMENT pairs — the markers are reserved for
-- declarations whose body is the formalised LN content of a row, and
-- these are just walk-level plumbing for step~(0) of the TeX proof
-- (carrier-matching membership lift, WalkStep lift, the recursive
-- walk-lift, and its preservation of `IsDirectedWalk` and
-- `length`).  See `tex/refactor_claim_3_3_proof_AcyclicPreservedUnderDo.tex`
-- for the TeX proof these helpers implement (unchanged by the
-- refactor; the mathematics is identical to the original twin).
--
-- *Mathematical content unchanged (TL;DR).*  The twins prove the
-- same lemmas as the originals; the refactor only swaps the upstream
-- `CDMG` / `Walk` / `WalkStep` shapes the helpers consume.
-- `CDMG.L` is retyped to `Finset (Sym2 Node)` (no
-- `hL_symm`), and `WalkStep` becomes a typed inductive
-- (`.forwardE` / `.backwardE` / `.bidir`) instead of the Prop-valued
-- disjunction.  But step~(0)'s edge-inclusion argument
-- (`E_{do(W)} ⊆ E` and `L_{do(W)} ⊆ L` follow from
-- `Finset.mem_filter`) is structurally unchanged, and so is the
-- walk-lift that uses it.

set_option linter.style.longLine false in
/-- Forward direction of the carrier-matching equality
`(G.J ∪ W) ∪ (G.V \ W) = G.J ∪ G.V` from the TeX statement block:
every node of the intervened CDMG is a node of `G`.  Consumes
`hW : W ⊆ G.J ∪ G.V` to fold the `W`-half of the left disjunct into
`G.J ∪ G.V`.  Body identical to the original — `G.J / G.V / W` are
unchanged by the `cdmg_typed_edges` refactor (only `L`'s type
changed), so the carrier-matching computation reads verbatim. -/
private lemma mem_of_mem_hardInterventionOn
    {G : CDMG Node} {W : Finset Node} {hW : W ⊆ G.J ∪ G.V}
    {v : Node}
    (h : v ∈ G.hardInterventionOn W hW) : v ∈ G := by
  -- `v ∈ G.hardInterventionOn W hW` reduces by the
  -- `instMembership` instance (`def_3_2`'s refactor twin,
  -- `CDMGNotation.lean`) to `v ∈ (G.J ∪ W) ∪ (G.V \ W)`.
  change v ∈ (G.J ∪ W) ∪ (G.V \ W) at h
  change v ∈ G.J ∪ G.V
  rcases Finset.mem_union.mp h with hJW | hVW
  · rcases Finset.mem_union.mp hJW with hJ | hWmem
    · exact Finset.mem_union_left _ hJ
    · exact hW hWmem
  · exact Finset.mem_union_right _ (Finset.mem_sdiff.mp hVW).1

set_option linter.style.longLine false in
/-- Per-edge content of step~(0): any typed `WalkStep` in
`G.hardInterventionOn W hW` is also a typed `WalkStep`
in `G`.  Under the refactor, `WalkStep` is a `Type _`-valued
inductive rather than a `Prop`, so this is a `def` (not a `lemma`)
that translates each constructor by stripping the `Finset.filter`
predicate via `Finset.mem_filter.mp`.

* `.forwardE h` and `.backwardE h` strip the `e.2 ∉ W` clause from
  the directed-edge filter and re-emit the same constructor.
* `.bidir h` strips the `∀ v ∈ s, v ∉ W` clause from the bidirected-
  edge filter and re-emits `.bidir`.  Under the `Sym2` encoding of
  `CDMG.L`, no symmetrisation step is needed — `s(u, v) =
  s(v, u)` is definitional, so the constructor preserves the
  unordered-pair identity verbatim. -/
private def Walk.refactor_liftWalkStep_of_hardInterventionOn
    {G : CDMG Node} {W : Finset Node} {hW : W ⊆ G.J ∪ G.V}
    {u v : Node} :
    WalkStep (G.hardInterventionOn W hW) u v →
      WalkStep G u v
  | .forwardE h  => .forwardE  ((Finset.mem_filter.mp h).1)
  | .backwardE h => .backwardE ((Finset.mem_filter.mp h).1)
  | .bidir h     => .bidir     ((Finset.mem_filter.mp h).1)

set_option linter.style.longLine false in
/-- Step~(0)'s walk-lift, as a recursive function on `Walk`s:
a walk in the intervened CDMG `G.hardInterventionOn W hW`
is *the same tuple* viewed as a walk in `G`.  Each `cons` cell keeps
its middle vertex `v`; the typed WalkStep witness is replaced by its
lift through `Walk.refactor_liftWalkStep_of_hardInterventionOn`.

The cons-cell signature change is structural: under
`Walk.cons` the cons cell takes three explicit args
(`v`, `s`, `p`) rather than the original four (`v`, `a`, `h`, `p`).
The `a : Node × Node` is gone (the WalkStep carries its endpoints in
its type indices), and the Prop witness `h` is replaced by the typed
data `s : WalkStep G u v`. -/
private def Walk.refactor_liftFromHardIntervention
    {G : CDMG Node} {W : Finset Node} {hW : W ⊆ G.J ∪ G.V} :
    ∀ {u v : Node},
      Walk (G.hardInterventionOn W hW) u v →
        Walk G u v
  | _, _, .nil w hw =>
      Walk.nil w (mem_of_mem_hardInterventionOn hw)
  | _, _, .cons vMid s p =>
      Walk.cons vMid
        (Walk.refactor_liftWalkStep_of_hardInterventionOn
          (hW := hW) s)
        (Walk.refactor_liftFromHardIntervention p)

set_option linter.style.longLine false in
/-- The walk-lift preserves `IsDirectedWalk`.

Under the refactor, `IsDirectedWalk` pattern-matches on the
typed WalkStep constructor: a `.forwardE` step advances the recursion
on the tail, while `.backwardE` and `.bidir` reduce to `False`
definitionally.  Consequently the proof simplifies from the
original's `obtain ⟨ha_eq, ha_E, hp_dir⟩ := hp` triple-conjunction
to a structural case-split on the typed step — the `.forwardE` case
recurses with no rewrite, and the other two close by `hp.elim`
(since `hp : False` for those constructors). -/
private lemma Walk.refactor_isDirectedWalk_liftFromHardIntervention
    {G : CDMG Node} {W : Finset Node} {hW : W ⊆ G.J ∪ G.V} :
    ∀ {u v : Node}
      (p : Walk (G.hardInterventionOn W hW) u v),
      p.IsDirectedWalk →
        (Walk.refactor_liftFromHardIntervention
          (hW := hW) p).IsDirectedWalk
  | _, _, .nil _ _, _ => trivial
  | _, _, .cons _ (.forwardE _) p, hp =>
      Walk.refactor_isDirectedWalk_liftFromHardIntervention p hp
  | _, _, .cons _ (.backwardE _) _, hp => hp.elim
  | _, _, .cons _ (.bidir _) _, hp => hp.elim

set_option linter.style.longLine false in
/-- The walk-lift preserves `length`: each `cons` cell of
the input walk produces exactly one `cons` cell of the output walk,
with the same middle vertex / typed WalkStep data.  Body is the
original with the cons-cell pattern shrunk from four args to three
(the `a : Node × Node` is gone — see the design block on
`Walk.cons` in `Walks.lean`). -/
private lemma Walk.refactor_length_liftFromHardIntervention
    {G : CDMG Node} {W : Finset Node} {hW : W ⊆ G.J ∪ G.V} :
    ∀ {u v : Node}
      (p : Walk (G.hardInterventionOn W hW) u v),
      (Walk.refactor_liftFromHardIntervention
        (hW := hW) p).length = p.length
  | _, _, .nil _ _ => rfl
  | _, _, .cons _ _ p =>
      congrArg (· + 1)
        (Walk.refactor_length_liftFromHardIntervention p)

-- ref: claim_3_3 — refactor twin
-- If `G : CDMG Node` is acyclic (in the sense of `def_3_6`'s
-- refactor twin `IsAcyclic`) and `W ⊆ G.J ∪ G.V`, then (a)
-- the intervened CDMG `G.hardInterventionOn W hW` is acyclic,
-- and (b) every topological order `lt` of `G` (in the sense of
-- `def_3_8`'s refactor twin `IsTopologicalOrder`) is a
-- topological order of `G.hardInterventionOn W hW`.
--
-- ## Design choice (refactor twin)
--
-- *Structural port of the original `acyclic_preserved_under_do`*
-- onto
--   the `cdmg_typed_edges` refactor's new upstream types (DEPENDENT
--   row; roots `def_3_1`, `def_3_4`).  The mathematical design — single
--   theorem returning a conjunction, sub-claim (b) universally
--   quantified over `lt`, same `lt` on both sides with no re-indexing,
--   shared `G.IsAcyclic` antecedent matching the LN packaging
--   even though (b) does not consume it, explicit `(W : Finset Node)`
--   `(hW : W ⊆ G.J ∪ G.V)` binders matching `hardInterventionOn`,
--   conjunction order (a) ∧ (b) following the rewrite's
--   `enumerate[label=(\alph*)]`, and `L` playing no role on either
--   side — is **unchanged**.  See the original block above for the
--   full rationale; the resolutions of the LN wording-check (which
--   returned `NO_SUBTLETIES`) and the operator clarification
--   `[w_is_free_unquantified_in_claim_body]` carry over verbatim.
--
-- *Mathematical content unchanged (TL;DR).*  The twin proves the same
--   theorem and runs the same argument as the original; the refactor
--   only swaps the upstream `CDMG` / `Walk` / `WalkStep` shapes the
--   proof consumes.  Step~(0) of the TeX proof (`E_{do(W)} ⊆ E` via
--   `Finset.mem_filter`) and the walk-lift it drives are structurally
--   unchanged.  No new mathematical commitment.
--
-- *The structural `hard_intervention_l_symmetrized_removal`
--   deviation, registered against the *pre-refactor* encoding of
--   `def_3_10`, does not affect this row in either encoding.*  Both
--   sub-claims read only the `(J, V, E)`-skeleton of `G`: acyclicity
--   is defined via directed walks (which build on `G.E` only), and
--   the topological-order predicate is defined via the parent set
--   `Pa^G` (also built from `G.E` only).  Under the post-refactor
--   `Sym2` encoding of `CDMG.L`, the deviation is
--   structurally resolved at the `def_3_10` row itself — the L-filter
--   reads "every endpoint of the unordered pair lies in `W`", which
--   is symmetric by construction.  But again: neither side of this
--   row's theorem touches `L`, so the deviation's resolution is
--   simply not visible here.
--
-- *Upstream-type shifts (and only those).*  The Lean translation
--   work is *mechanical* — each substitution maps one identifier:
--   - `CDMG Node                          → CDMG Node`
--   - `G.hardInterventionOn W hW          → G.hardInterventionOn W hW`
--   - `G.IsAcyclic                        → G.IsAcyclic`
--   - `G.IsTopologicalOrder lt            → G.IsTopologicalOrder lt`
--   - `G.IsTotalOrder lt`                 → unfolded as part of
--                                            `IsTopologicalOrder`'s
--                                            nested 2-conjunct shape
--                                            (irrefl / trans / tricho)
--   - `Walk G u v                         → Walk G u v`
--   - `Walk.nil w hw                      → Walk.nil w hw`
--   - `Walk.cons vMid a h p               → Walk.cons vMid s p`
--     (drops the `a : Node × Node` ordered pair and the
--     `h : G.WalkStep u a v` Prop witness; takes a typed
--     `s : WalkStep G u v` instead — see the `def_3_4`
--     refactor design block in `Walks.lean`)
--   - `p.IsDirectedWalk                   → p.IsDirectedWalk`
--   - `p.length                           → p.length`
--   - `G.WalkStep` (Prop disjunction)     → `WalkStep`
--     (typed inductive with `.forwardE` / `.backwardE` / `.bidir`)
--   - `G.Pa w                             → G.Pa w`
--   - Each `Walk.<helper>` / `Walk.<lemma>` → its
--     `Walk.refactor_<helper>` twin above.
--
-- *The single non-mechanical reshape (carried by the helpers, not
--   the theorem body).*  The WalkStep lift
--   (`Walk.refactor_liftWalkStep_of_hardInterventionOn`)
--   shifts from a `Prop`-recursion-on-disjunction to a structural
--   case-split on the typed `WalkStep` constructor; the
--   directedness-preservation lemma
--   (`Walk.refactor_isDirectedWalk_liftFromHardIntervention`)
--   shifts from `obtain ⟨ha_eq, ha_E, hp_dir⟩ := hp` to the typed
--   pattern `.cons _ (.forwardE _) p, hp`, with `.backwardE` and
--   `.bidir` closing by `hp.elim` (their `IsDirectedWalk`
--   is `False` definitionally).  Both reshapes are *fully contained
--   in the helpers* — the main theorem body reads near-verbatim
--   against the renamed helpers, because the sub-claim (a)
--   contradiction (a non-trivial directed walk in the intervened
--   CDMG lifts to a non-trivial directed walk in `G`) and the
--   sub-claim (b) parent-precedence transfer
--   (`Pa^{G_{do(W)}}(w) ⊆ Pa^G(w)` via `Finset.mem_filter`) are
--   stated at a level above the WalkStep recursion.
--
-- *Sub-claim (b)'s parent-precedence step.*  Under the refactor,
--   `G.Pa w : Set Node` unfolds to the literal set-builder
--   `{u | u ∈ G ∧ (u, w) ∈ G.E}` (see the `Pa` design block
--   in `FamilyRelationships.lean`).  Membership destructures via
--   `⟨hu, huw_E⟩` exactly as the original `Pa`-membership did,
--   because `G.E`'s `Finset (Node × Node)` carrier is unchanged by
--   the refactor.  The intervened parent set's directed-edge
--   filter `(G.hardInterventionOn W hW).E =
--   G.E.filter (fun e => e.2 ∉ W)` lifts to `G.E` via
--   `Finset.mem_filter.mp` — identical to the original.
--
-- *Conjunction packaging, anonymous-constructor destructuring,
--   acyclicity-shared-antecedent reading.*  All carry over verbatim:
--   `IsAcyclic` keeps the same `¬ ∃` over walks of length
--   ≥ 1 shape (`Acyclicity.lean`'s refactor twin), and
--   `IsTopologicalOrder` keeps the nested
--   2-conjunct shape `IsTotalOrder ∧ parent-precedence`
--   (`TopologicalOrder.lean`'s refactor twin).  Every `.1` / `.2`
--   projection and every `rintro ⟨…⟩` / anonymous-constructor
--   destructuring in the proof body therefore carries over
--   byte-for-byte modulo the `refactor_` renames above.
set_option linter.style.longLine false in
-- claim_3_3 -- start statement
theorem acyclic_preserved_under_do (G : CDMG Node)
    (W : Finset Node) (hW : W ⊆ G.J ∪ G.V) :
    G.IsAcyclic →
      (G.hardInterventionOn W hW).IsAcyclic ∧
        (∀ lt : Node → Node → Prop,
          G.IsTopologicalOrder lt →
            (G.hardInterventionOn W hW).IsTopologicalOrder lt)
-- claim_3_3 -- end statement
:= by
  intro hAcyclic
  refine ⟨?_, ?_⟩
  -- (a) Acyclicity preservation: if a non-trivial directed walk
  --     `v ⟶⋯⟶ v` existed in `G.hardInterventionOn W hW`,
  --     the walk-lift transfers it -- as the same tuple, by step~(0)
  --     of the TeX proof -- to a non-trivial directed walk in `G` at
  --     the same `v`, contradicting `G.IsAcyclic`.
  · intro v hv
    rintro ⟨p, hp_dir, hp_len⟩
    have hv_G : v ∈ G := mem_of_mem_hardInterventionOn hv
    apply hAcyclic v hv_G
    refine ⟨Walk.refactor_liftFromHardIntervention p,
            Walk.refactor_isDirectedWalk_liftFromHardIntervention
              p hp_dir, ?_⟩
    rw [Walk.refactor_length_liftFromHardIntervention p]
    exact hp_len
  -- (b) Topological-order preservation: each conjunct of
  --     `(G.hardInterventionOn W hW).IsTopologicalOrder lt`
  --     transfers from the corresponding conjunct of
  --     `G.IsTopologicalOrder lt` via the carrier-matching
  --     equality (for the strict-total-order conjuncts) and the
  --     edge-inclusion `(G.hardInterventionOn W hW).E ⊆ G.E`
  --     (for the parent-precedence conjunct).  `hAcyclic` is NOT used
  --     here.
  · intro lt hTop
    obtain ⟨⟨h_irrefl, h_trans, h_tricho⟩, h_parent⟩ := hTop
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · -- Irreflexivity on the intervened carrier
      intro v hv
      exact h_irrefl v (mem_of_mem_hardInterventionOn hv)
    · -- Transitivity on the intervened carrier
      intro u hu v hv w hw hluv hlvw
      exact h_trans u (mem_of_mem_hardInterventionOn hu)
                    v (mem_of_mem_hardInterventionOn hv)
                    w (mem_of_mem_hardInterventionOn hw)
                    hluv hlvw
    · -- Trichotomy on the intervened carrier
      intro v hv w hw
      exact h_tricho v (mem_of_mem_hardInterventionOn hv)
                     w (mem_of_mem_hardInterventionOn hw)
    · -- Parent-precedence on `G.hardInterventionOn W hW`:
      --   from `v ∈ (G.hardInterventionOn W hW).Pa w`
      --   we extract `v ∈ G.hardInterventionOn W hW` and
      --   `(v, w) ∈ (G.hardInterventionOn W hW).E`; the
      --   former lifts to `v ∈ G` via
      --   `mem_of_mem_hardInterventionOn` and the latter
      --   lifts to `(v, w) ∈ G.E` via `Finset.mem_filter`.  Together
      --   they give `v ∈ G.Pa w`, so `h_parent` yields
      --   `lt v w`.
      intro v w hvPa
      obtain ⟨hv_G', hvw_E'⟩ := hvPa
      have hvw_E_G : (v, w) ∈ G.E := (Finset.mem_filter.mp hvw_E').1
      have hv_G : v ∈ G := mem_of_mem_hardInterventionOn hv_G'
      exact h_parent v w ⟨hv_G, hvw_E_G⟩

end CDMG

end Causality
