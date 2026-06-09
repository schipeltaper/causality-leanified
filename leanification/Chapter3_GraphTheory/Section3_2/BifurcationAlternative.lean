import Chapter3_GraphTheory.Section3_1.CDMG
import Chapter3_GraphTheory.Section3_1.CDMGNotation
import Chapter3_GraphTheory.Section3_1.Walks
import Chapter3_GraphTheory.Section3_1.FamilyRelationships
import Chapter3_GraphTheory.Section3_2.HardInterventionOn

namespace Causality

/-!
# Bifurcation alternative (`claim_3_5`)

This file formalises the LN proposition `claim_3_5`
(`\label{prp:bifurcations_alternative}` in `graphs.tex`,
section 3.2):

> Let `G = (J, V, E, L)` be a CDMG.  For `v, w, c ∈ V ∪ J`:
> there exists a bifurcation between `v` and `w` in `G` with source
> `c` if and only if `v ≠ w` and `c ∈ Anc^{G_{do(w)}}(v) ∖ {v}` and
> `c ∈ Anc^{G_{do(v)}}(w) ∖ {w}`.

The authoritative spec is the rewritten canonical tex statement at
`leanification/Chapter3_GraphTheory/Section3_2/tex/`
`claim_3_5_statement_BifurcationAlternative.tex`, verified equivalent
to the LN block by `verify_tex_statement_only` and
`verify_tex_statement_equivalence`.  The rewritten tex spells out:

* the three universal quantifiers on `v, w, c ∈ J ∪ V`
  (rendered here as the three explicit membership hypotheses
  `hv : v ∈ G`, `hw : w ∈ G`, `hc : c ∈ G`, via the
  `Membership Node (CDMG Node)` instance of `def_3_2`);
* the singleton-set reading of the LN's `do(w)` / `do(v)` shorthand
  — `G_{do(w)}` is `G.hardInterventionOn ({w} : Finset Node) hw`
  in the sense of `def_3_10` (`HardInterventionOn.lean`);
* the literal set-difference shape `Anc^{...}(v) ∖ {v}` rather than
  the equivalent conjunction `c ∈ Anc ∧ c ≠ v`, matching the LN's
  notation verbatim;
* the LN-critic resolution
  `source_at_endpoint_w_when_right_arm_trivial`: under our
  `def_3_4` encoding's chapter-init addition
  `[bifurcation_right_chain_trivial_is_just_directed_walk]`,
  `IsBifurcationSource p c` already commits to the interior-source
  convention (the LN-critic's `k = n` directed-hinge corner case is
  excluded by `Walk.IsBifurcationDirectedHingeWithSplit`'s
  `.cons _ _ _ (.nil _ _), 0 => False` branch).  Consequently
  this proposition is provable as-stated, and no
  `addition_to_the_LN` clause was needed for `claim_3_5`
  (see `workspace_claim_3_5.md` and the comment block above the
  `\begin{Prp}` in the rewritten tex spec).

The body is filled in by `prove_claim_in_lean` (Manager B), following
the verified TeX proof at
`tex/claim_3_5_proof_BifurcationAlternative.tex`.

TeX proof: `claim_3_5_proof_BifurcationAlternative.tex`.

## Proof status / handoff note

The TeX proof has been verified by `verify_tex_statement_plus_proof`
and `verify_tex_proof`.  The Lean translation requires substantial
walk-level infrastructure beyond `def_3_4`/`def_3_5`/`def_3_10`:

* a walk concatenation `Walk.comp` (already mirrored in
  `AcyclicIffTopologicalOrder.lean` privately),
* a walk lift `Walk.liftFromHardIntervention` and its converse
  `Walk.liftTo_hardInterventionOn` between `G` and `G_{do(W)}`,
* a `Walk.truncateAtFirst` truncation function (for the minimum-
  length argument in the (⇐) direction),
* a `mkBifurcation` constructor that combines two directed arms
  into a bifurcation walk and the associated structure lemmas
  (`isBifurcationDirectedHinge_mkBifurcation_general`,
  `isBifurcationDirectedHinge_mkBifurcation`),
* an arm-extraction lemma `exists_arms_of_bifurcation_directed_hinge`
  that turns an `IsBifurcationDirectedHingeWithSplit p i` hypothesis
  into directed walks `qL : Walk G c u` and `qR : Walk G c w` with
  vertex-membership constraints lifting via the
  `vertices.dropLast` / `vertices.tail` clauses of
  `IsBifurcationSource`.

Detailed notes on the helpers' API surface and the open
vertex-uniqueness bookkeeping are recorded in
`workspace_claim_3_5.md`.  The Lean proof body is left as a `sorry`
pending completion of those helpers in a follow-up dispatch.
-/

namespace CDMG

-- ## Design choice — statement context
--
-- *`Node : Type*` with `[DecidableEq Node]`.*  Inherited verbatim from
--   `def_3_1` (`CDMG.lean`).  Both fixtures are load-bearing for this
--   row's statement because the signature references `CDMG Node`,
--   `Walk G v w` (`def_3_4`), `Walk.IsBifurcationSource` (`def_3_4`),
--   `G.Anc` (`def_3_5`), and `G.hardInterventionOn` (`def_3_10`); each
--   of these depends on `[DecidableEq Node]` through the `Finset`-backed
--   membership and filter operations on `G.J ∪ G.V`, `G.E`, and `G.L`,
--   and through the `Membership Node (CDMG Node)` instance from
--   `def_3_2` driving the `v ∈ G` membership hypotheses below.
--   Stronger instances (`Fintype`, `LinearOrder`) are not needed at
--   the statement level and are deferred to the proof body's use
--   sites.
--
-- *Three-dash `--- start helper` marker (not the two-dash
--   `-- start statement`).*  Matches the convention in every sibling
--   file in this folder (`HardInterventionOn.lean`,
--   `AcyclicPreservedUnderDo.lean`, `HardInterventionsCommute.lean`)
--   and in the upstream `Section3_1/` files.  The two-dash marker is
--   reserved for declarations whose body is the formalised LN content
--   of the row; this `variable` line is statement-typing
--   infrastructure binding the implicit `Node` type and its
--   `DecidableEq` instance that the theorem's signature references.
-- claim_3_5 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- claim_3_5 --- end helper

-- ## Private helpers — `HardInterventionOn` walk-lift infrastructure
--
-- Subtask 1 of the proof of `claim_3_5` builds the `G_{do(W)} → G`
-- walk-lift infrastructure that the (⇐) direction of the proof uses
-- to upgrade the minimum-length directed walks `q_v : Walk
-- (G.hardInterventionOn {w} _) c v` and `q_w : Walk
-- (G.hardInterventionOn {v} _) c w` to walks in the ambient CDMG `G`
-- before assembling them into a candidate bifurcation walk.
--
-- The first five helpers below mirror `claim_3_3`'s
-- `AcyclicPreservedUnderDo.lean` lines 104–177 verbatim; the sixth,
-- `Walk.vertices_liftFromHardIntervention`, is new infrastructure
-- needed for the (⇐) direction's clause~(a) end-node-uniqueness
-- bookkeeping in step 5 of the TeX proof (the lift preserves the
-- underlying vertex list because each `cons` cell keeps its vertex
-- data verbatim).
--
-- ## Design choice
--
-- *Localised verbatim copy rather than cross-file `import`.*  The
--   sibling `AcyclicPreservedUnderDo.lean` already declares these
--   five lemmas `private`, so they are not accessible from this
--   file.  Re-declaring `private` here matches the explicit
--   workspace plan instruction ("the previous private mirrors are
--   TEMPLATES, not imports") and the chapter precedent of localising
--   walk-level plumbing to the consuming row.  A future chapter-wide
--   refactor can hoist these into `Walks.lean`; until then, the
--   local copy keeps the consuming file self-contained.
-- claim_3_5 --- start helper

/-- Forward direction of the carrier-matching equality
`(G.J ∪ W) ∪ (G.V \ W) = G.J ∪ G.V`: every node of the intervened
CDMG is a node of `G`.  Consumes `hW : W ⊆ G.J ∪ G.V` to fold the
`W`-half of the left disjunct into `G.J ∪ G.V`.  Verbatim copy of
`AcyclicPreservedUnderDo.lean`'s lemma of the same name; localised
here because the sibling copy is `private`. -/
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

/-- Per-edge content of the (⇐) direction's walk lift: any walk-step
in `G.hardInterventionOn W hW` is also a walk-step in `G`.  Both
`E_{do(W)} ⊆ E` and `L_{do(W)} ⊆ L` follow from `Finset.filter_subset`,
applied pointwise.  Verbatim copy of `AcyclicPreservedUnderDo.lean`'s
lemma of the same name. -/
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

/-- The walk-lift, as a recursive function on `Walk`s: a walk in the
intervened CDMG `G.hardInterventionOn W hW` is *the same tuple*
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

/-- The walk-lift preserves `IsDirectedWalk`: the per-edge constraint
`a = (u, v) ∧ a ∈ G.E` from `def_3_4` item ii survives the lift
because `(G.hardInterventionOn W hW).E ⊆ G.E` by
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

/-- **New (subtask 1 of `claim_3_5`):** the walk-lift preserves the
underlying `vertices` list.  Each `cons` cell of the input keeps its
vertex data verbatim under the lift, so the induced list of vertices
is byte-identical.  The `nil` case reduces to `[v] = [v]` definitionally;
the `cons` case is `u :: (lift p).vertices = u :: p.vertices` via
`congrArg (u :: ·) ih`.  Used by the (⇐) direction's clause~(a) /
clause~(e) end-node-uniqueness bookkeeping when lifting the minimum-
length directed arms `q_v`, `q_w` back to `G`. -/
private lemma Walk.vertices_liftFromHardIntervention
    {G : CDMG Node} {W : Finset Node} {hW : W ⊆ G.J ∪ G.V} :
    ∀ {u v : Node} (p : Walk (G.hardInterventionOn W hW) u v),
      (Walk.liftFromHardIntervention (hW := hW) p).vertices = p.vertices
  | _, _, .nil _ _ => rfl
  | u, _, .cons _ _ _ p =>
      congrArg (u :: ·) (vertices_liftFromHardIntervention p)
-- claim_3_5 --- end helper

-- ref: claim_3_5
-- For any CDMG `G : CDMG Node` and any three (not necessarily
-- distinct) nodes `v, w, c ∈ G` (i.e. `v, w, c ∈ G.J ∪ G.V`), the
-- following are equivalent:
--
-- (a) *Existence of a bifurcation between `v` and `w` with source
--     `c`.*  There exists a walk `p : Walk G v w` such that
--     `p.IsBifurcationSource c` (in the sense of `def_3_4`'s
--     trailing `IsBifurcationSource` predicate).  This single
--     existential packages both the LN's "`p` is a bifurcation
--     between `v` and `w`" (clauses (a)–(e) of `def_3_4` item~vi,
--     including the `v ≠ w` first-half of clause (a) and the
--     end-node-uniqueness clause), and the LN's "the bifurcation
--     has source `c`" (the closing paragraph of `def_3_4`
--     item~vi).  Under our `def_3_4` encoding's chapter-init
--     addition `[bifurcation_right_chain_trivial_is_just_directed_walk]`,
--     `IsBifurcationSource p c` automatically commits to the
--     interior-source convention `1 ≤ k ≤ n - 1` (`0 ≤ i ≤ n - 2`
--     in the Lean encoding), so `c ≠ v` and `c ≠ w` are
--     consequences of (a), not extra hypotheses.
--
-- (b) *Set-theoretic ancestral characterisation.*
--     The conjunction of:
--       (i)   `v ≠ w`;
--       (ii)  `c ∈ (G.hardInterventionOn {w} _).Anc v \ {v}`,
--             i.e. `c` is an ancestor of `v` in the
--             do-on-`{w}` intervened CDMG (`def_3_10` +
--             `def_3_5`'s `Anc`), and `c ≠ v`;
--       (iii) `c ∈ (G.hardInterventionOn {v} _).Anc w \ {w}`,
--             i.e. `c` is an ancestor of `w` in the
--             do-on-`{v}` intervened CDMG, and `c ≠ w`.
--
-- The `_` in (ii) and (iii) is the singleton-subset witness
-- `{w} ⊆ G.J ∪ G.V` / `{v} ⊆ G.J ∪ G.V`, supplied here by
-- `Finset.singleton_subset_iff.mpr hw` / `… hv` (recovering the
-- LN's "the lowercase `w` / `v` inside the `do(·)` slot is
-- shorthand for the singleton sets `{w}` / `{v}`" reading of
-- `def_3_10`'s `W` argument).
/-
LN tex (verbatim, from `graphs.tex`,
`\label{prp:bifurcations_alternative}`):

  \begin{Prp}\label{prp:bifurcations_alternative}
    Let $G = \lt J, V, E, L \rt$ be a CDMG.  For $v, w, c \in V
    \cup J$: there exists a bifurcation between $v$ and $w$ in
    $G$ with source $c$ if and only if $v \ne w$ and $c \in
    \Anc^{G_{\doit(w)}}(v) \sm \{v\}$ and $c \in
    \Anc^{G_{\doit(v)}}(w) \sm \{w\}$.
  \end{Prp}

Rewritten canonical tex (`claim_3_5_statement_BifurcationAlternative.tex`,
sketch):

  Universal quantification over `(G, v, w, c)` with
  `v, w, c ∈ J ∪ V`.  Equivalence:
    (a) ∃ walk `p` from `v` to `w` in `G` with split index `k`
        (`1 ≤ k ≤ n`) such that `p` is a bifurcation between
        `v` and `w` at `k` and `c` is the source (directed
        hinge, `c = v_k`).  Clause (e) of `def_3_4` item~vi
        forces `1 ≤ k ≤ n - 1`, so `c ≠ v ≠ w`.
    (b) `v ≠ w` ∧ `c ∈ Anc^{G_{do({w})}}(v) ∖ {v}`
              ∧ `c ∈ Anc^{G_{do({v})}}(w) ∖ {w}`,
        with the singleton-set reading of `do(·)` made explicit.
-/
-- ## Design choice
--
-- *One theorem, biconditional `↔` between (a) and (b).*  The LN
--   block writes a single "if and only if" between two propositions;
--   the rewritten tex preserves that single-statement shape; we
--   render it as one Lean `theorem` returning an `Iff`.  Splitting
--   into two named theorems (forward / backward) was rejected
--   because (i) the LN treats this as one proposition with a single
--   reference label `\label{prp:bifurcations_alternative}`, and
--   (ii) downstream consumers wanting either direction reach `.mp` /
--   `.mpr` on the `Iff` for free.
--
-- *Binder shape `(G : CDMG Node) (v w c : Node) (hv hw hc : … ∈ G)`,
--   in that order.*  Mirrors `def_3_10`'s `(G : CDMG Node) (W : …)
--   (hW : W ⊆ G.J ∪ G.V)` shape (graph first, then the relevant
--   nodes/sets, then the membership/subset preconditions).  The
--   three membership hypotheses are explicit, matching the rewritten
--   tex's `v, w, c ∈ J ∪ V` quantifier scope (rendered via the
--   `Membership Node (CDMG Node)` instance of `def_3_2`).  `hc` is
--   technically not needed to type-check the RHS (the `c ∈ Anc …`
--   conjunct already requires `c ∈ G` via `def_3_5`'s `Anc` body),
--   but we carry it explicitly to match the LN's literal universal
--   scope and to keep the binder block parallel to `hv` / `hw`.
--
-- *LHS as `∃ p : Walk G v w, p.IsBifurcationSource c`.*  The
--   rewritten tex spec decomposes the LN's "exists a bifurcation
--   between `v` and `w` with source `c`" into:
--     (1) a walk `p` from `v` to `w`,
--     (2) `p` is a bifurcation between `v` and `w` at some index `k`,
--     (3) `c` is the source of this bifurcation.
--   Our `Walk.IsBifurcationSource p c` (in
--   `Section3_1/Walks.lean`) is a single `Prop` packaging all three
--   ingredients — it requires (i) `u ≠ v` (the LN's "v ≠ w"
--   conjunct at clause (a) first-half), (ii) `u ∉ p.vertices.tail`
--   and `v ∉ p.vertices.dropLast` (the end-node uniqueness clause
--   (a) second-half), and (iii) `∃ i,
--   p.IsBifurcationDirectedHingeWithSplit i ∧
--   p.vertices[i + 1]? = some c` (the bifurcation split and
--   directed-hinge source identification).  Existential
--   quantification over the index `k` (here `i`) is internal to
--   `IsBifurcationSource`, so the outer existential is over `p`
--   alone, matching the LN's surface reading "there exists a
--   bifurcation (which is a walk) ...".  Building the LHS via an
--   ad-hoc tuple type `(p, k, h_bif, h_src)` was rejected because
--   it would duplicate the `def_3_4`-encoded constraints at the
--   theorem boundary, lose the LN-faithful "exists a bifurcation"
--   surface phrasing, and force every downstream consumer to
--   re-derive what `def_3_4` has already packaged.
--
-- *RHS as a three-way conjunction `v ≠ w ∧ … ∧ …`, mirroring the
--   LN's literal `v ≠ w and … and …` reading.*  The LN writes the
--   right-hand side as three separate conjuncts joined by "and";
--   we follow the LN literally rather than collapsing into, say,
--   `v ≠ w ∧ c ∈ A ∩ B \ {v, w}` (which would obscure the
--   `def_3_10` singleton interventions and the asymmetry between
--   `\ {v}` and `\ {w}`).  Conjunction order matches the LN.
--
-- *Asymmetric pairing `Anc^{G_{do(w)}}(v) \ {v}` and
--   `Anc^{G_{do(v)}}(w) \ {w}` preserved verbatim (not the
--   "natural-looking" alternatives).*  The LN pairs each
--   *intervention end-node* with the *opposite ancestor target* —
--   the source `c` is an ancestor of `v` in the graph where the
--   other end-node `w` has been do-intervened, and vice versa.
--   This pairing encodes the "bifurcation arms avoid the opposite
--   end-node" semantic content: by `def_3_10` items iii.–iv. the
--   `do` cuts all incoming edges to the intervened node, so any
--   ancestor path from `c` to `v` in `G_{do(w)}` automatically
--   avoids `w` — exactly the directed-walk-to-`v` arm of the
--   bifurcation (`def_3_4` item~vi.(b)).  The natural-looking
--   "matched" alternative `Anc^{G_{do(v)}}(v) \ {v}` is vacuously
--   empty (the intervened node has no incoming edges, so
--   `Anc^{G_{do(v)}}(v) = {v}` and the set-minus is `∅`); the
--   uninterventioned alternative `Anc^G(v) ∩ Anc^G(w)` would
--   conflate "common ancestor" with "bifurcation source" and lose
--   the "arms avoid the opposite end" content.  Preserving the LN's
--   exact orientation is load-bearing for downstream rows: chapter
--   4+ d-separation, identification, and the do-calculus rules all
--   pattern-match `claim_3_5` in this orientation, so any
--   rearrangement here would force every consumer to re-derive the
--   equivalence under permuted conjuncts.
--
-- *`G.hardInterventionOn ({w} : Finset Node)
--   (Finset.singleton_subset_iff.mpr hw)`*, with the singleton
--   subset proof inlined.  The LN writes `G_{do(w)}` with a
--   bare `w` inside `do(·)`; the rewritten tex makes the
--   singleton-set reading explicit ("`G_{do(w)}` is shorthand
--   for `G_{do({w})}`").  We inline the proof
--   `Finset.singleton_subset_iff.mpr hw` (one-liner taking
--   `w ∈ G.J ∪ G.V` to `{w} ⊆ G.J ∪ G.V`, where `hw : w ∈ G` is
--   definitionally `w ∈ G.J ∪ G.V` via the `Membership Node
--   (CDMG Node)` instance of `def_3_2`).  A named helper lemma
--   was rejected as overkill — the inline form is a single mathlib
--   call and adds no friction at the statement level; if a
--   downstream row finds itself repeating this pattern, the helper
--   can be promoted later.
--
-- *Set-difference shape `\ {v}` (`Set.diff` with a singleton
--   `Set Node`), not the equivalent conjunction `… ∧ c ≠ v`.*
--   The rewritten tex spec preserves the LN's literal `\ {v}` /
--   `\ {w}` notation; we mirror that in Lean.  `Anc` returns
--   `Set Node`, so `\ {v}` elaborates as `Set.diff (G.Anc v) ({v}
--   : Set Node)` and `c ∈ … \ {v}` unfolds to `c ∈ … ∧ c ∉ {v}`
--   i.e. `c ∈ … ∧ c ≠ v`.  Writing `c ∈ … ∧ c ≠ v` directly
--   would be content-equivalent but diverge stylistically from
--   the rewritten tex.  The set-difference reading also makes
--   downstream lemmas about ancestor sets transport directly
--   (`Set.mem_diff`, `Set.mem_singleton_iff`).
--
-- *Universal `c ∈ G` is carried even though the LN-faithful (b)
--   already implies it via `Anc`'s body.*  The rewritten tex's
--   quantifier scope is `v, w, c ∈ J ∪ V`; if we dropped `hc`,
--   the theorem would still be true (the RHS's `Anc` conjunct
--   would force `c ∈ G` whenever (b) holds; the LHS's
--   `IsBifurcationSource p c` would force `c ∈ G` via
--   `p.vertices[i + 1]? = some c` and the walk's vertex
--   membership in `G`), but the statement would no longer
--   literally mirror the LN's universal scope.  Carrying `hc`
--   keeps the contract LN-faithful and gives the proof a free
--   `c ∈ G` to start from.
--
-- *No additional `IsBifurcation`-vs-`IsBifurcationSource`
--   disambiguation hypothesis.*  Subtle point: the LN's "exists
--   a bifurcation between `v` and `w` with source `c`" is *one*
--   existential; the LN-critic's `source_at_endpoint_w_when_right_arm_trivial`
--   wording check flagged that a literal reading of `def 3.4`
--   would let the source coincide with `w` in the degenerate
--   `k = n` case.  Our `def_3_4` encoding's `IsBifurcationSource`
--   predicate already excludes that case (via
--   `IsBifurcationDirectedHingeWithSplit`'s
--   `.cons _ _ _ (.nil _ _), 0 => False` branch implementing the
--   chapter-init addition
--   `[bifurcation_right_chain_trivial_is_just_directed_walk]`),
--   so no extra hypothesis or disjunct is needed here.  See the
--   long comment block above `\begin{Prp}` in the rewritten tex
--   spec and the workspace note in
--   `workspace_claim_3_5.md` for the full LN-critic resolution.
-- claim_3_5 -- start statement
theorem bifurcationAlternative (G : CDMG Node) (v w c : Node)
    (hv : v ∈ G) (hw : w ∈ G) (hc : c ∈ G) :
    (∃ p : Walk G v w, p.IsBifurcationSource c)
      ↔
        v ≠ w
      ∧ c ∈ (G.hardInterventionOn {w}
              (Finset.singleton_subset_iff.mpr hw)).Anc v \ {v}
      ∧ c ∈ (G.hardInterventionOn {v}
              (Finset.singleton_subset_iff.mpr hv)).Anc w \ {w}
-- claim_3_5 -- end statement
  := by
  -- `hc` is part of the universal scope `v, w, c ∈ J ∪ V` per
  -- `def_3_2`; the RHS's `Anc` conjunct independently forces
  -- `c ∈ G`, but we carry `hc` for LN-faithfulness of the binder
  -- block (see the "Universal `c ∈ G` is carried …" design-choice
  -- bullet above).  The `let _` pin mirrors the unused-LN-faithful
  -- convention used in `HardInterventionOn.lean`'s `hardInterventionOn`
  -- definition.
  let _ := hc
  sorry

end CDMG

end Causality
