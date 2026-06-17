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

-- ## Design choice — statement context
--
-- *`Node : Type*` with `[DecidableEq Node]`.*  Inherited verbatim from
--   `def_3_1` (`CDMG.lean`).  Both fixtures are load-bearing for this
--   row's statement because the signature references `CDMG Node`,
--   `G.hardInterventionOn` (`def_3_10`), `G.IsAcyclic` (`def_3_6`),
--   and `G.IsTopologicalOrder` (`def_3_8`); each of these depends on
--   `[DecidableEq Node]` through the `Finset`-backed membership and
--   filter operations on `G.J ∪ G.V` and `G.E`, and through the
--   `Membership Node (CDMG Node)` instance from `def_3_2` driving the
--   `v ∈ G` quantifier scope of `IsTotalOrder` / `IsTopologicalOrder`.
--   Stronger instances (`Fintype`, `LinearOrder`) are not needed at
--   the statement level and are deferred to the proof body's use
--   sites.
--
-- *Three-dash `--- start helper` marker (not the two-dash
--   `-- start statement`).*  Matches the convention in every sibling
--   file in this folder (`HardInterventionOn.lean`) and in the
--   upstream `Section3_1/` files
--   (`CDMG.lean`, `CDMGNotation.lean`, `Walks.lean`,
--   `EdgeRelations.lean`, `CDMGRestrictions.lean`, `Acyclicity.lean`,
--   `CDMGTypes.lean`, `TopologicalOrder.lean`, `Predecessors.lean`,
--   `AcyclicIffTopologicalOrder.lean`).  The two-dash marker is
--   reserved for declarations whose body is the formalised LN content
--   of the row; this `variable` line is statement-typing
--   infrastructure binding the implicit `Node` type and its
--   `DecidableEq` instance that the theorem's signature references.
-- claim_3_3 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- claim_3_3 --- end helper

-- ## Private helpers — verbatim translation of step (0) of the TeX
-- proof at `tex/claim_3_3_proof_AcyclicPreservedUnderDo.tex`.
--
-- The TeX proof rests on (i) the carrier-matching equality
-- `J_{\doit(W)} ∪ V_{\doit(W)} = J ∪ V` (used here as
-- `mem_of_mem_hardInterventionOn`, the forward direction), (ii) the
-- edge-inclusion lemma `E_{\doit(W)} ⊆ E` (used inline via
-- `Finset.mem_filter`), and (iii) the walk-lifting observation that
-- "the same tuple `p` in `G_{\doit(W)}` is a walk in `G`".  The walk
-- lift is realised as a recursive `Walk.liftFromHardIntervention`
-- function; `Walk.isDirectedWalk_liftFromHardIntervention` shows it
-- preserves `IsDirectedWalk` (because `E_{\doit(W)} ⊆ E` survives the
-- per-edge constraint) and `Walk.length_liftFromHardIntervention`
-- shows it preserves `length` (because the constructor structure is
-- copied verbatim).

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: mem_of_mem_hardInterventionOn
/-- Forward direction of the carrier-matching equality
`(G.J ∪ W) ∪ (G.V \ W) = G.J ∪ G.V` from the TeX statement block:
every node of the intervened CDMG is a node of `G`.  Consumes
`hW : W ⊆ G.J ∪ G.V` to fold the `W`-half of the left disjunct into
`G.J ∪ G.V`. -/
private lemma mem_of_mem_hardInterventionOn
    {G : CDMG Node} {W : Finset Node} {hW : W ⊆ G.J ∪ G.V} {v : Node}
    (h : v ∈ G.hardInterventionOn W hW) : v ∈ G := by
  -- `v ∈ G.hardInterventionOn W hW` reduces by the `Membership`
  -- instance from `def_3_2` to `v ∈ (G.J ∪ W) ∪ (G.V \ W)`.
  change v ∈ (G.J ∪ W) ∪ (G.V \ W) at h
  change v ∈ G.J ∪ G.V
  rcases Finset.mem_union.mp h with hJW | hVW
  · rcases Finset.mem_union.mp hJW with hJ | hWmem
    · exact Finset.mem_union_left _ hJ
    · exact hW hWmem
  · exact Finset.mem_union_right _ (Finset.mem_sdiff.mp hVW).1
-- REFACTOR-BLOCK-ORIGINAL-END: mem_of_mem_hardInterventionOn

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: Walk.liftWalkStep_of_hardInterventionOn
/-- Per-edge content of step (0): any walk-step in
`G.hardInterventionOn W hW` is also a walk-step in `G`.  Both
`E_{\doit(W)} ⊆ E` and `L_{\doit(W)} ⊆ L` follow from
`Finset.filter_subset`, applied pointwise. -/
private lemma Walk.liftWalkStep_of_hardInterventionOn
    {G : CDMG Node} {W : Finset Node} {hW : W ⊆ G.J ∪ G.V}
    {u v : Node} {a : Node × Node}
    (h : (G.hardInterventionOn W hW).WalkStep u a v) :
    G.WalkStep u a v := by
  rcases h with ⟨ha, hELor⟩ | ⟨ha, hE⟩
  · refine Or.inl ⟨ha, ?_⟩
    rcases hELor with hE | hL
    · exact Or.inl (Finset.mem_filter.mp hE).1
    · exact Or.inr (Finset.mem_filter.mp hL).1
  · exact Or.inr ⟨ha, (Finset.mem_filter.mp hE).1⟩
-- REFACTOR-BLOCK-ORIGINAL-END: Walk.liftWalkStep_of_hardInterventionOn

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: Walk.liftFromHardIntervention
/-- Step (0)'s walk-lift, as a recursive function on `Walk`s: a walk
in the intervened CDMG `G.hardInterventionOn W hW` is *the same tuple*
viewed as a walk in `G`.  Each `cons` cell keeps its vertex `v` and
its edge `a`; only the `WalkStep` witness is replaced by its lift
through `Walk.liftWalkStep_of_hardInterventionOn`. -/
private def Walk.liftFromHardIntervention
    {G : CDMG Node} {W : Finset Node} {hW : W ⊆ G.J ∪ G.V} :
    ∀ {u v : Node}, Walk (G.hardInterventionOn W hW) u v → Walk G u v
  | _, _, .nil w hw =>
      Walk.nil w (mem_of_mem_hardInterventionOn hw)
  | _, _, .cons vMid a h p =>
      Walk.cons vMid a
        (Walk.liftWalkStep_of_hardInterventionOn h)
        (Walk.liftFromHardIntervention p)
-- REFACTOR-BLOCK-ORIGINAL-END: Walk.liftFromHardIntervention

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: Walk.isDirectedWalk_liftFromHardIntervention
/-- The walk-lift preserves `IsDirectedWalk`: the per-edge
constraint `a = (u, v) ∧ a ∈ G.E` from `def_3_4` item ii survives
the lift because `(G.hardInterventionOn W hW).E ⊆ G.E` by
`Finset.mem_filter`. -/
private lemma Walk.isDirectedWalk_liftFromHardIntervention
    {G : CDMG Node} {W : Finset Node} {hW : W ⊆ G.J ∪ G.V} :
    ∀ {u v : Node} (p : Walk (G.hardInterventionOn W hW) u v),
      p.IsDirectedWalk →
        (Walk.liftFromHardIntervention (hW := hW) p).IsDirectedWalk
  | _, _, .nil _ _, _ => trivial
  | _, _, .cons _ _ _ p, hp => by
      obtain ⟨ha_eq, ha_E, hp_dir⟩ := hp
      refine ⟨ha_eq, (Finset.mem_filter.mp ha_E).1, ?_⟩
      exact isDirectedWalk_liftFromHardIntervention p hp_dir
-- REFACTOR-BLOCK-ORIGINAL-END: Walk.isDirectedWalk_liftFromHardIntervention

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: Walk.length_liftFromHardIntervention
/-- The walk-lift preserves `length`: each `cons` cell of the input
walk produces exactly one `cons` cell of the output walk, with the
same vertex / edge data. -/
private lemma Walk.length_liftFromHardIntervention
    {G : CDMG Node} {W : Finset Node} {hW : W ⊆ G.J ∪ G.V} :
    ∀ {u v : Node} (p : Walk (G.hardInterventionOn W hW) u v),
      (Walk.liftFromHardIntervention (hW := hW) p).length = p.length
  | _, _, .nil _ _ => rfl
  | _, _, .cons _ _ _ p =>
      congrArg (· + 1) (length_liftFromHardIntervention p)
-- REFACTOR-BLOCK-ORIGINAL-END: Walk.length_liftFromHardIntervention

-- ref: claim_3_3
-- If `G : CDMG Node` is acyclic (in the sense of `def_3_6`) and
-- `W ⊆ G.J ∪ G.V`, then (a) the intervened CDMG
-- `G.hardInterventionOn W hW` (`def_3_10`) is acyclic, and (b) every
-- topological order `lt` of `G` (in the sense of `def_3_8`) is a
-- topological order of `G.hardInterventionOn W hW`.  The two
-- sub-claims are packaged as a single conjunction under the shared
-- hypothesis `G.IsAcyclic`, mirroring the LN remark's "and"-join.
/-
LN tex (rewritten canonical statement for `claim_3_3`, in essence):

  Let `G = (J, V, E, L)` be a CDMG and `W ⊆ J ∪ V`, and let
  `G_{\doit(W)}` be the hard-intervention CDMG of `G` w.r.t. `W`
  (`def_3_10`).  If `G` is acyclic (`def_3_6`), then
  (a) `G_{\doit(W)}` is acyclic, and
  (b) for every strict total order `<` on `J ∪ V`,
      if `<` is a topological order of `G` then `<` is a topological
      order of `G_{\doit(W)}`.

LN block (verbatim, for backup):

  If `G` is acyclic then also `G_{\doit(W)}` is acyclic and a
  topological order for `G` is also one for `G_{\doit(W)}`.
-/
-- ## Design choice
--
-- *One theorem returning a conjunction, not two separate top-level
--   theorems.*  The LN's `\begin{Rem}` block is one remark joining
--   two clauses with "and"; the rewritten canonical statement file
--   explicitly licenses "the following conjunction of sub-claims
--   holds".  A single theorem returning `(a) ∧ (b)` is the literal
--   Lean rendering: consumers reach `.1` for the
--   acyclicity-preservation conclusion and `.2` for the
--   topological-order-preservation conclusion.  Splitting into two
--   named theorems was rejected because it would (i) duplicate the
--   antecedent `G.IsAcyclic` at the theorem-head level, (ii) hide the
--   LN's "and"-packaging behind two separate grep targets, and (iii)
--   diverge from the rewrite's explicit licensing.
--
-- *Sub-claim (b) is universally quantified over `lt`, not packed
--   under an existential.*  The LN's indefinite article in "a
--   topological order for `G` is also one for `G_{\doit(W)}`" is
--   read universally per the rewrite's closing remark — "every such
--   `<`, not merely some such `<`".  An existential reading
--   (`∃ lt : Node → Node → Prop, G.IsTopologicalOrder lt ∧
--   (G.hardInterventionOn W hW).IsTopologicalOrder lt`) would be
--   vacuous in context: any acyclic CDMG already admits *some*
--   topological order by `claim_3_2`
--   (`Section3_1/AcyclicIffTopologicalOrder.lean`), so once (a)
--   delivers acyclicity of `G_{\doit(W)}`, the same `claim_3_2`
--   produces *some* topological order on the intervened side too —
--   the existential would express nothing the chapter does not
--   already give for free.  The universal reading is the
--   load-bearing content: *every* `lt` that tops `G` continues to
--   top `G_{\doit(W)}`, with no need to re-pick.  The Lean
--   `∀ lt : Node → Node → Prop, G.IsTopologicalOrder lt → …`
--   matches this reading on the nose.
--
-- *Same `lt` on both sides of (b); no re-indexing function.*  The
--   rewrite's "Carrier matching" paragraph proves the set equality
--   `J_{\doit(W)} ∪ V_{\doit(W)} = J ∪ V` (using items i, ii of
--   `def_3_10` and the precondition `W ⊆ J ∪ V`), so a binary
--   relation on `J ∪ V` is the very same binary relation on the
--   carrier of `G_{\doit(W)}`, viewed from two CDMGs.  In Lean,
--   `lt : Node → Node → Prop` has a type independent of which CDMG
--   it is "for"; both `G.IsTopologicalOrder lt` and
--   `(G.hardInterventionOn W hW).IsTopologicalOrder lt` consume the
--   same `lt` directly, with the CDMG-dependence of the predicate
--   carried through its first argument.  No helper lemma is needed
--   at the *statement* level: `IsTopologicalOrder G lt` unfolds to
--   constraints quantified over `v ∈ G` (via `def_3_2`'s
--   `Membership Node (CDMG Node)` instance, dispatched by the CDMG
--   passed in), so the predicate is well-typed for *any* CDMG
--   without requiring the two carriers to be definitionally equal.
--   The set-equality
--     `(G.hardInterventionOn W hW).J ∪ (G.hardInterventionOn W hW).V
--        = G.J ∪ G.V`
--   (which holds when `W ⊆ G.J ∪ G.V`) is a *content* fact the
--   proof exploits — not a typing prerequisite.  Introducing a
--   carrier-translation function `lt' : Node → Node → Prop` with
--   `lt' u v := lt u v` would be a no-op wrapper adding noise to
--   every downstream consumer; the rewrite spec explicitly rules
--   that out ("Do not introduce a re-indexing / carrier-translation
--   function").
--
-- *Sub-claim (b)'s hypothesis matches the LN packaging.*  Sub-claim
--   (b) actually holds without acyclicity (the intervened parent set
--   is a subset of the original, so the parents-precede-children
--   clause is monotone in edge removal — see the proof workspace).
--   The LN nevertheless packages (a) and (b) under the same `If G
--   is acyclic` antecedent, and the rewritten canonical statement
--   file mirrors that packaging.  We mirror it too: the theorem
--   keeps the shared `G.IsAcyclic` hypothesis at the theorem head
--   rather than weakening (b)'s hypothesis at the signature level.
--   The downstream proof may exploit the stronger fact, but the
--   LN-faithful statement is what gets formalised here.
--
-- *`W` and `hW` quantified at the theorem head, matching
--   `hardInterventionOn`'s binder convention.*  `def_3_10`
--   (`HardInterventionOn.lean`) takes `(W : Finset Node) (hW : W ⊆
--   G.J ∪ G.V)` as explicit arguments to its `hardInterventionOn`
--   def; we reuse the same shape so call sites
--   `G.hardInterventionOn W hW` parse identically inside this
--   theorem and at every downstream consumer.  No subtype
--   `{W : Finset Node // W ⊆ G.J ∪ G.V}` is introduced — the
--   explicit hypothesis form is what every downstream consumer
--   (ch.\ 5 do-calculus, ch.\ 8+ iSCM intervention algebra) will
--   pattern-match against, and pushing `hW` into a subtype would
--   force a `Subtype.mk` / `Subtype.property` unpacking step at
--   every such site.
--
-- *Conjunction order (a) ∧ (b), matching the rewrite and the LN
--   reading order.*  The rewrite's `enumerate[label=(\alph*)]` block
--   lists (a) acyclicity preservation first, (b) topological-order
--   preservation second; we preserve that order in the Lean
--   conjunction so the natural `.1` / `.2` projections line up with
--   the (a) / (b) labels of the rewrite.
--
-- *`L` plays no role; the `hard_intervention_l_symmetrized_removal`
--   deviation does not propagate.*  Both sub-claims are about the
--   `(J, V, E)`-skeleton-derived structures: acyclicity is defined
--   via directed walks (`def_3_4`'s `Walk` built from `G.E`, see
--   `Walks.lean`) and a topological order is defined via the parent
--   set `Pa^G` (`def_3_5` item i, built from `G.E`, see
--   `FamilyRelationships.lean`).  Neither side reads `G.L`.  The
--   structural deviation `hard_intervention_l_symmetrized_removal`
--   registered for `def_3_10` (in `leanification/deviations.json`,
--   forced by `def_3_1`'s ordered-pair encoding of `L` with
--   `hL_symm`) only affects the `L`-component of the intervened
--   CDMG, so it does not propagate into this claim's signature or
--   content.  This is the same skeleton-only reading `claim_3_2`
--   (`AcyclicIffTopologicalOrder.lean`) adopts for "acyclic iff
--   topological order".
-- REFACTOR-BLOCK-ORIGINAL-BEGIN: acyclic_preserved_under_do
-- claim_3_3 -- start statement
theorem acyclic_preserved_under_do (G : CDMG Node) (W : Finset Node)
    (hW : W ⊆ G.J ∪ G.V) :
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
  --     `v ⟶⋯⟶ v` existed in `G.hardInterventionOn W hW`, the
  --     walk-lift transfers it -- as the same tuple, by step (0) of
  --     the TeX proof -- to a non-trivial directed walk in `G` at
  --     the same `v`, contradicting `G.IsAcyclic`.
  · intro v hv
    rintro ⟨p, hp_dir, hp_len⟩
    have hv_G : v ∈ G := mem_of_mem_hardInterventionOn hv
    apply hAcyclic v hv_G
    refine ⟨Walk.liftFromHardIntervention p,
            Walk.isDirectedWalk_liftFromHardIntervention p hp_dir, ?_⟩
    rw [Walk.length_liftFromHardIntervention p]
    exact hp_len
  -- (b) Topological-order preservation: each conjunct of
  --     `(G.hardInterventionOn W hW).IsTopologicalOrder lt` transfers
  --     from the corresponding conjunct of `G.IsTopologicalOrder lt`
  --     via the carrier-matching equality (for the strict-total-order
  --     conjuncts, which quantify over `v ∈ G`) and the edge-inclusion
  --     `(G.hardInterventionOn W hW).E ⊆ G.E` (for the
  --     parent-precedence conjunct, which gives
  --     `Pa^{G_{do(W)}}(w) ⊆ Pa^G(w)` pointwise).  The acyclicity
  --     hypothesis `hAcyclic` is NOT used in this branch -- sub-claim
  --     (b) holds without it (the proof in the TeX's closing remark);
  --     we keep `hAcyclic` bound at the theorem head purely for
  --     LN-faithfulness of the packaging.
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
    · -- Parent-precedence on `G.hardInterventionOn W hW`: from
      --   `v ∈ (G.hardInterventionOn W hW).Pa w` we extract
      --   `v ∈ G.hardInterventionOn W hW` and
      --   `(v, w) ∈ (G.hardInterventionOn W hW).E`; the former lifts
      --   to `v ∈ G` via `mem_of_mem_hardInterventionOn` and the
      --   latter lifts to `(v, w) ∈ G.E` via `Finset.mem_filter`.
      --   Together they give `v ∈ G.Pa w`, so `h_parent` yields
      --   `lt v w`.
      intro v w hvPa
      obtain ⟨hv_G', hvw_E'⟩ := hvPa
      have hvw_E_G : (v, w) ∈ G.E := (Finset.mem_filter.mp hvw_E').1
      have hv_G : v ∈ G := mem_of_mem_hardInterventionOn hv_G'
      exact h_parent v w ⟨hv_G, hvw_E_G⟩
-- REFACTOR-BLOCK-ORIGINAL-END: acyclic_preserved_under_do

end CDMG

namespace refactor_CDMG

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
-- (`refactor_CDMG`): the `Membership Node (refactor_CDMG Node)`
-- instance from `def_3_2`'s refactor twin (`refactor_instMembership`
-- in `CDMGNotation.lean`) reduces to `Finset.mem` on `G.J ∪ G.V` and
-- so needs `DecidableEq Node`; the `refactor_Walk` recursion in the
-- four walk-class helpers, the `refactor_IsDirectedWalk` Prop in the
-- main theorem body, and the `G.refactor_Pa w` set-builder in
-- `refactor_IsTopologicalOrder` all transitively rely on
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
-- of `refactor_acyclic_preserved_under_do`.  They are deliberately
-- private and carry no marker comments other than the
-- REFACTOR-BLOCK-REPLACEMENT pairs — the markers are reserved for
-- declarations whose body is the formalised LN content of a row, and
-- these are just walk-level plumbing for step~(0) of the TeX proof
-- (carrier-matching membership lift, WalkStep lift, the recursive
-- walk-lift, and its preservation of `refactor_IsDirectedWalk` and
-- `refactor_length`).  See `tex/refactor_claim_3_3_proof_AcyclicPreservedUnderDo.tex`
-- for the TeX proof these helpers implement (unchanged by the
-- refactor; the mathematics is identical to the original twin).
--
-- *Mathematical content unchanged (TL;DR).*  The twins prove the
-- same lemmas as the originals; the refactor only swaps the upstream
-- `CDMG` / `Walk` / `WalkStep` shapes the helpers consume.
-- `refactor_CDMG.L` is retyped to `Finset (Sym2 Node)` (no
-- `hL_symm`), and `refactor_WalkStep` becomes a typed inductive
-- (`.forwardE` / `.backwardE` / `.bidir`) instead of the Prop-valued
-- disjunction.  But step~(0)'s edge-inclusion argument
-- (`E_{do(W)} ⊆ E` and `L_{do(W)} ⊆ L` follow from
-- `Finset.mem_filter`) is structurally unchanged, and so is the
-- walk-lift that uses it.

set_option linter.style.longLine false in
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: mem_of_mem_hardInterventionOn (was: refactor_mem_of_mem_hardInterventionOn)
/-- Forward direction of the carrier-matching equality
`(G.J ∪ W) ∪ (G.V \ W) = G.J ∪ G.V` from the TeX statement block:
every node of the intervened CDMG is a node of `G`.  Consumes
`hW : W ⊆ G.J ∪ G.V` to fold the `W`-half of the left disjunct into
`G.J ∪ G.V`.  Body identical to the original — `G.J / G.V / W` are
unchanged by the `cdmg_typed_edges` refactor (only `L`'s type
changed), so the carrier-matching computation reads verbatim. -/
private lemma refactor_mem_of_mem_hardInterventionOn
    {G : refactor_CDMG Node} {W : Finset Node} {hW : W ⊆ G.J ∪ G.V}
    {v : Node}
    (h : v ∈ G.refactor_hardInterventionOn W hW) : v ∈ G := by
  -- `v ∈ G.refactor_hardInterventionOn W hW` reduces by the
  -- `refactor_instMembership` instance (`def_3_2`'s refactor twin,
  -- `CDMGNotation.lean`) to `v ∈ (G.J ∪ W) ∪ (G.V \ W)`.
  change v ∈ (G.J ∪ W) ∪ (G.V \ W) at h
  change v ∈ G.J ∪ G.V
  rcases Finset.mem_union.mp h with hJW | hVW
  · rcases Finset.mem_union.mp hJW with hJ | hWmem
    · exact Finset.mem_union_left _ hJ
    · exact hW hWmem
  · exact Finset.mem_union_right _ (Finset.mem_sdiff.mp hVW).1
-- REFACTOR-BLOCK-REPLACEMENT-END: mem_of_mem_hardInterventionOn

set_option linter.style.longLine false in
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: Walk.liftWalkStep_of_hardInterventionOn (was: refactor_Walk.refactor_liftWalkStep_of_hardInterventionOn)
/-- Per-edge content of step~(0): any typed `refactor_WalkStep` in
`G.refactor_hardInterventionOn W hW` is also a typed `refactor_WalkStep`
in `G`.  Under the refactor, `refactor_WalkStep` is a `Type _`-valued
inductive rather than a `Prop`, so this is a `def` (not a `lemma`)
that translates each constructor by stripping the `Finset.filter`
predicate via `Finset.mem_filter.mp`.

* `.forwardE h` and `.backwardE h` strip the `e.2 ∉ W` clause from
  the directed-edge filter and re-emit the same constructor.
* `.bidir h` strips the `∀ v ∈ s, v ∉ W` clause from the bidirected-
  edge filter and re-emits `.bidir`.  Under the `Sym2` encoding of
  `refactor_CDMG.L`, no symmetrisation step is needed — `s(u, v) =
  s(v, u)` is definitional, so the constructor preserves the
  unordered-pair identity verbatim. -/
private def refactor_Walk.refactor_liftWalkStep_of_hardInterventionOn
    {G : refactor_CDMG Node} {W : Finset Node} {hW : W ⊆ G.J ∪ G.V}
    {u v : Node} :
    refactor_WalkStep (G.refactor_hardInterventionOn W hW) u v →
      refactor_WalkStep G u v
  | .forwardE h  => .forwardE  ((Finset.mem_filter.mp h).1)
  | .backwardE h => .backwardE ((Finset.mem_filter.mp h).1)
  | .bidir h     => .bidir     ((Finset.mem_filter.mp h).1)
-- REFACTOR-BLOCK-REPLACEMENT-END: Walk.liftWalkStep_of_hardInterventionOn

set_option linter.style.longLine false in
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: Walk.liftFromHardIntervention (was: refactor_Walk.refactor_liftFromHardIntervention)
/-- Step~(0)'s walk-lift, as a recursive function on `refactor_Walk`s:
a walk in the intervened CDMG `G.refactor_hardInterventionOn W hW`
is *the same tuple* viewed as a walk in `G`.  Each `cons` cell keeps
its middle vertex `v`; the typed WalkStep witness is replaced by its
lift through `refactor_Walk.refactor_liftWalkStep_of_hardInterventionOn`.

The cons-cell signature change is structural: under
`refactor_Walk.cons` the cons cell takes three explicit args
(`v`, `s`, `p`) rather than the original four (`v`, `a`, `h`, `p`).
The `a : Node × Node` is gone (the WalkStep carries its endpoints in
its type indices), and the Prop witness `h` is replaced by the typed
data `s : refactor_WalkStep G u v`. -/
private def refactor_Walk.refactor_liftFromHardIntervention
    {G : refactor_CDMG Node} {W : Finset Node} {hW : W ⊆ G.J ∪ G.V} :
    ∀ {u v : Node},
      refactor_Walk (G.refactor_hardInterventionOn W hW) u v →
        refactor_Walk G u v
  | _, _, .nil w hw =>
      refactor_Walk.nil w (refactor_mem_of_mem_hardInterventionOn hw)
  | _, _, .cons vMid s p =>
      refactor_Walk.cons vMid
        (refactor_Walk.refactor_liftWalkStep_of_hardInterventionOn
          (hW := hW) s)
        (refactor_Walk.refactor_liftFromHardIntervention p)
-- REFACTOR-BLOCK-REPLACEMENT-END: Walk.liftFromHardIntervention

set_option linter.style.longLine false in
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: Walk.isDirectedWalk_liftFromHardIntervention (was: refactor_Walk.refactor_isDirectedWalk_liftFromHardIntervention)
/-- The walk-lift preserves `refactor_IsDirectedWalk`.

Under the refactor, `refactor_IsDirectedWalk` pattern-matches on the
typed WalkStep constructor: a `.forwardE` step advances the recursion
on the tail, while `.backwardE` and `.bidir` reduce to `False`
definitionally.  Consequently the proof simplifies from the
original's `obtain ⟨ha_eq, ha_E, hp_dir⟩ := hp` triple-conjunction
to a structural case-split on the typed step — the `.forwardE` case
recurses with no rewrite, and the other two close by `hp.elim`
(since `hp : False` for those constructors). -/
private lemma refactor_Walk.refactor_isDirectedWalk_liftFromHardIntervention
    {G : refactor_CDMG Node} {W : Finset Node} {hW : W ⊆ G.J ∪ G.V} :
    ∀ {u v : Node}
      (p : refactor_Walk (G.refactor_hardInterventionOn W hW) u v),
      p.refactor_IsDirectedWalk →
        (refactor_Walk.refactor_liftFromHardIntervention
          (hW := hW) p).refactor_IsDirectedWalk
  | _, _, .nil _ _, _ => trivial
  | _, _, .cons _ (.forwardE _) p, hp =>
      refactor_Walk.refactor_isDirectedWalk_liftFromHardIntervention p hp
  | _, _, .cons _ (.backwardE _) _, hp => hp.elim
  | _, _, .cons _ (.bidir _) _, hp => hp.elim
-- REFACTOR-BLOCK-REPLACEMENT-END: Walk.isDirectedWalk_liftFromHardIntervention

set_option linter.style.longLine false in
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: Walk.length_liftFromHardIntervention (was: refactor_Walk.refactor_length_liftFromHardIntervention)
/-- The walk-lift preserves `refactor_length`: each `cons` cell of
the input walk produces exactly one `cons` cell of the output walk,
with the same middle vertex / typed WalkStep data.  Body is the
original with the cons-cell pattern shrunk from four args to three
(the `a : Node × Node` is gone — see the design block on
`refactor_Walk.cons` in `Walks.lean`). -/
private lemma refactor_Walk.refactor_length_liftFromHardIntervention
    {G : refactor_CDMG Node} {W : Finset Node} {hW : W ⊆ G.J ∪ G.V} :
    ∀ {u v : Node}
      (p : refactor_Walk (G.refactor_hardInterventionOn W hW) u v),
      (refactor_Walk.refactor_liftFromHardIntervention
        (hW := hW) p).refactor_length = p.refactor_length
  | _, _, .nil _ _ => rfl
  | _, _, .cons _ _ p =>
      congrArg (· + 1)
        (refactor_Walk.refactor_length_liftFromHardIntervention p)
-- REFACTOR-BLOCK-REPLACEMENT-END: Walk.length_liftFromHardIntervention

-- ref: claim_3_3 — refactor twin
-- If `G : refactor_CDMG Node` is acyclic (in the sense of `def_3_6`'s
-- refactor twin `refactor_IsAcyclic`) and `W ⊆ G.J ∪ G.V`, then (a)
-- the intervened CDMG `G.refactor_hardInterventionOn W hW` is acyclic,
-- and (b) every topological order `lt` of `G` (in the sense of
-- `def_3_8`'s refactor twin `refactor_IsTopologicalOrder`) is a
-- topological order of `G.refactor_hardInterventionOn W hW`.
--
-- ## Design choice (refactor twin)
--
-- *Structural port of the original `acyclic_preserved_under_do`*
--   (`namespace CDMG`, the wrapped REFACTOR-BLOCK-ORIGINAL above) onto
--   the `cdmg_typed_edges` refactor's new upstream types (DEPENDENT
--   row; roots `def_3_1`, `def_3_4`).  The mathematical design — single
--   theorem returning a conjunction, sub-claim (b) universally
--   quantified over `lt`, same `lt` on both sides with no re-indexing,
--   shared `G.refactor_IsAcyclic` antecedent matching the LN packaging
--   even though (b) does not consume it, explicit `(W : Finset Node)`
--   `(hW : W ⊆ G.J ∪ G.V)` binders matching `refactor_hardInterventionOn`,
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
--   `Sym2` encoding of `refactor_CDMG.L`, the deviation is
--   structurally resolved at the `def_3_10` row itself — the L-filter
--   reads "every endpoint of the unordered pair lies in `W`", which
--   is symmetric by construction.  But again: neither side of this
--   row's theorem touches `L`, so the deviation's resolution is
--   simply not visible here.
--
-- *Upstream-type shifts (and only those).*  The Lean translation
--   work is *mechanical* — each substitution maps one identifier:
--   - `CDMG Node                          → refactor_CDMG Node`
--   - `G.hardInterventionOn W hW          → G.refactor_hardInterventionOn W hW`
--   - `G.IsAcyclic                        → G.refactor_IsAcyclic`
--   - `G.IsTopologicalOrder lt            → G.refactor_IsTopologicalOrder lt`
--   - `G.IsTotalOrder lt`                 → unfolded as part of
--                                            `refactor_IsTopologicalOrder`'s
--                                            nested 2-conjunct shape
--                                            (irrefl / trans / tricho)
--   - `Walk G u v                         → refactor_Walk G u v`
--   - `Walk.nil w hw                      → refactor_Walk.nil w hw`
--   - `Walk.cons vMid a h p               → refactor_Walk.cons vMid s p`
--     (drops the `a : Node × Node` ordered pair and the
--     `h : G.WalkStep u a v` Prop witness; takes a typed
--     `s : refactor_WalkStep G u v` instead — see the `def_3_4`
--     refactor design block in `Walks.lean`)
--   - `p.IsDirectedWalk                   → p.refactor_IsDirectedWalk`
--   - `p.length                           → p.refactor_length`
--   - `G.WalkStep` (Prop disjunction)     → `refactor_WalkStep`
--     (typed inductive with `.forwardE` / `.backwardE` / `.bidir`)
--   - `G.Pa w                             → G.refactor_Pa w`
--   - Each `Walk.<helper>` / `Walk.<lemma>` → its
--     `refactor_Walk.refactor_<helper>` twin above.
--
-- *The single non-mechanical reshape (carried by the helpers, not
--   the theorem body).*  The WalkStep lift
--   (`refactor_Walk.refactor_liftWalkStep_of_hardInterventionOn`)
--   shifts from a `Prop`-recursion-on-disjunction to a structural
--   case-split on the typed `refactor_WalkStep` constructor; the
--   directedness-preservation lemma
--   (`refactor_Walk.refactor_isDirectedWalk_liftFromHardIntervention`)
--   shifts from `obtain ⟨ha_eq, ha_E, hp_dir⟩ := hp` to the typed
--   pattern `.cons _ (.forwardE _) p, hp`, with `.backwardE` and
--   `.bidir` closing by `hp.elim` (their `refactor_IsDirectedWalk`
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
--   `G.refactor_Pa w : Set Node` unfolds to the literal set-builder
--   `{u | u ∈ G ∧ (u, w) ∈ G.E}` (see the `refactor_Pa` design block
--   in `FamilyRelationships.lean`).  Membership destructures via
--   `⟨hu, huw_E⟩` exactly as the original `Pa`-membership did,
--   because `G.E`'s `Finset (Node × Node)` carrier is unchanged by
--   the refactor.  The intervened parent set's directed-edge
--   filter `(G.refactor_hardInterventionOn W hW).E =
--   G.E.filter (fun e => e.2 ∉ W)` lifts to `G.E` via
--   `Finset.mem_filter.mp` — identical to the original.
--
-- *Conjunction packaging, anonymous-constructor destructuring,
--   acyclicity-shared-antecedent reading.*  All carry over verbatim:
--   `refactor_IsAcyclic` keeps the same `¬ ∃` over walks of length
--   ≥ 1 shape (`Acyclicity.lean`'s refactor twin), and
--   `refactor_IsTopologicalOrder` keeps the nested
--   2-conjunct shape `refactor_IsTotalOrder ∧ parent-precedence`
--   (`TopologicalOrder.lean`'s refactor twin).  Every `.1` / `.2`
--   projection and every `rintro ⟨…⟩` / anonymous-constructor
--   destructuring in the proof body therefore carries over
--   byte-for-byte modulo the `refactor_` renames above.
set_option linter.style.longLine false in
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: acyclic_preserved_under_do (was: refactor_acyclic_preserved_under_do)
-- claim_3_3 -- start statement
theorem refactor_acyclic_preserved_under_do (G : refactor_CDMG Node)
    (W : Finset Node) (hW : W ⊆ G.J ∪ G.V) :
    G.refactor_IsAcyclic →
      (G.refactor_hardInterventionOn W hW).refactor_IsAcyclic ∧
        (∀ lt : Node → Node → Prop,
          G.refactor_IsTopologicalOrder lt →
            (G.refactor_hardInterventionOn W hW).refactor_IsTopologicalOrder lt)
-- claim_3_3 -- end statement
:= by
  intro hAcyclic
  refine ⟨?_, ?_⟩
  -- (a) Acyclicity preservation: if a non-trivial directed walk
  --     `v ⟶⋯⟶ v` existed in `G.refactor_hardInterventionOn W hW`,
  --     the walk-lift transfers it -- as the same tuple, by step~(0)
  --     of the TeX proof -- to a non-trivial directed walk in `G` at
  --     the same `v`, contradicting `G.refactor_IsAcyclic`.
  · intro v hv
    rintro ⟨p, hp_dir, hp_len⟩
    have hv_G : v ∈ G := refactor_mem_of_mem_hardInterventionOn hv
    apply hAcyclic v hv_G
    refine ⟨refactor_Walk.refactor_liftFromHardIntervention p,
            refactor_Walk.refactor_isDirectedWalk_liftFromHardIntervention
              p hp_dir, ?_⟩
    rw [refactor_Walk.refactor_length_liftFromHardIntervention p]
    exact hp_len
  -- (b) Topological-order preservation: each conjunct of
  --     `(G.refactor_hardInterventionOn W hW).refactor_IsTopologicalOrder lt`
  --     transfers from the corresponding conjunct of
  --     `G.refactor_IsTopologicalOrder lt` via the carrier-matching
  --     equality (for the strict-total-order conjuncts) and the
  --     edge-inclusion `(G.refactor_hardInterventionOn W hW).E ⊆ G.E`
  --     (for the parent-precedence conjunct).  `hAcyclic` is NOT used
  --     here.
  · intro lt hTop
    obtain ⟨⟨h_irrefl, h_trans, h_tricho⟩, h_parent⟩ := hTop
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · -- Irreflexivity on the intervened carrier
      intro v hv
      exact h_irrefl v (refactor_mem_of_mem_hardInterventionOn hv)
    · -- Transitivity on the intervened carrier
      intro u hu v hv w hw hluv hlvw
      exact h_trans u (refactor_mem_of_mem_hardInterventionOn hu)
                    v (refactor_mem_of_mem_hardInterventionOn hv)
                    w (refactor_mem_of_mem_hardInterventionOn hw)
                    hluv hlvw
    · -- Trichotomy on the intervened carrier
      intro v hv w hw
      exact h_tricho v (refactor_mem_of_mem_hardInterventionOn hv)
                     w (refactor_mem_of_mem_hardInterventionOn hw)
    · -- Parent-precedence on `G.refactor_hardInterventionOn W hW`:
      --   from `v ∈ (G.refactor_hardInterventionOn W hW).refactor_Pa w`
      --   we extract `v ∈ G.refactor_hardInterventionOn W hW` and
      --   `(v, w) ∈ (G.refactor_hardInterventionOn W hW).E`; the
      --   former lifts to `v ∈ G` via
      --   `refactor_mem_of_mem_hardInterventionOn` and the latter
      --   lifts to `(v, w) ∈ G.E` via `Finset.mem_filter`.  Together
      --   they give `v ∈ G.refactor_Pa w`, so `h_parent` yields
      --   `lt v w`.
      intro v w hvPa
      obtain ⟨hv_G', hvw_E'⟩ := hvPa
      have hvw_E_G : (v, w) ∈ G.E := (Finset.mem_filter.mp hvw_E').1
      have hv_G : v ∈ G := refactor_mem_of_mem_hardInterventionOn hv_G'
      exact h_parent v w ⟨hv_G, hvw_E_G⟩
-- REFACTOR-BLOCK-REPLACEMENT-END: acyclic_preserved_under_do

end refactor_CDMG

end Causality
