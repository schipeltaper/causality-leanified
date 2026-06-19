import Chapter3_GraphTheory.Section3_1.CDMG
import Chapter3_GraphTheory.Section3_1.CDMGNotation
import Chapter3_GraphTheory.Section3_1.Walks

namespace Causality

/-!
# Marginalization a.k.a. latent projection on CDMGs (`def_3_14`)

This file formalises the LN definition `def_3_14`
(`\label{def:G_marginalization}` in `graphs.tex`) — the
*marginalization* (a.k.a. *latent projection*) operation
`G ↦ G^{∖W}` on a CDMG.  Given a CDMG `G = (J, V, E, L)` and a subset
`W ⊆ V` of *output* nodes, the marginalized CDMG
`G^{V \setminus W \,|\, J} = G^{∖W}` has

* `J^{∖W} := J` (input nodes unchanged);
* `V^{∖W} := V ∖ W` (the marginalized output nodes);
* `E^{∖W}`: the set of pairs `(ū, ō) ∈ (J ∪ (V ∖ W)) × (V ∖ W)` for
  which there is a *directed walk* in `G` whose all intermediate
  vertices lie in `W`, with the *self-cycle restriction* that a
  self-edge `ū = ō` requires walk length `≥ 2`;
* `L^{∖W}`: the set of pairs `(ū, ō) ∈ (V ∖ W) × (V ∖ W)` with
  `ū ≠ ō` for which there is a *bifurcation* in `G` whose all
  intermediate vertices lie in `W`.

The authoritative spec is the rewritten canonical tex statement at
`leanification/Chapter3_GraphTheory/Section3_2/tex/def_3_14_MarginalizationAK.tex`,
verified equivalent to the LN block (`graphs.tex`,
`\label{def:G_marginalization}`) augmented with two operator
clarifications:

* `[bifurcation_index_boundary_excludes_natural_cases]` — the
  bifurcation in clause (iv) is read per the previously formalized
  `def_3_4` `Walk.IsBifurcation`, with the boundary conventions
  `w_0 := ū`, `w_n := ō` and hinge index `k ∈ {1, …, n}`.  The
  cases `n = 1` (direct bidirected edge already in `L`), `n = 2,
  k = 1` (`Y`-fork), and `n = 2, k = n` (mirror `Y`) all qualify.

* `[self_cycle_asymmetry_between_directed_and_bidirected]` — the
  asymmetry between clauses (iii) and (iv) is intentional:
  directed self-cycles `v → v` may appear in `E^{∖W}` (but only
  via a walk of length `≥ 2` through `W`), while bidirected
  self-edges `v ↔ v` are excluded from `L^{∖W}` outright by the
  explicit `ū ≠ ō` constraint in the set-builder for `L^{∖W}`.
  No `ū ≠ ō` constraint is imposed on `E^{∖W}`, and no relaxation
  of `ū ≠ ō` is made on `L^{∖W}`.

The substantive design rationale — the choice of `Walk`-based
predicates `MarginalizationΦE` and `MarginalizationΦL`, the
symmetrised `Φ_L` encoding (so that `hL_symm` reduces to `Or.comm`),
the use of classical decidability for the `Finset.filter`, and how
each CDMG axiom of `def_3_1` is discharged on the marginalised
carrier — lives in the `--` comment block immediately above each
`def` declaration.  Read those blocks before changing a field; they
are the load-bearing contract for downstream rows (`claim_3_16`,
`claim_3_17`, `claim_3_18`, `claim_3_19`) and the do-calculus /
identifiability chapters that build on the latent-projection
operator.
-/

namespace CDMG

-- def_3_14 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- def_3_14 --- end helper

-- ref: def_3_14 (helper, directed-walk-through-`W` predicate) — refactor
--
-- `MarginalizationΦE G W u v` is the post-refactor port of
-- `MarginalizationΦE`: identical LN-level semantics ("exists a directed
-- walk of length ≥ 1 in `G` from `u` to `v` whose intermediate vertices
-- all lie in `W`"), retargeted onto the new `Walk` /
-- `IsDirectedWalk` / `length` / `vertices`
-- API.  The body is byte-identical to the original modulo those four
-- surface retargets — no constructor case-splits or LN-conjunct changes.
-- def_3_14 --- start helper
def MarginalizationΦE (G : CDMG Node) (W : Finset Node)
    (u v : Node) : Prop :=
  ∃ (p : Walk G u v),
    p.IsDirectedWalk ∧
    p.length ≥ 1 ∧
    (∀ x ∈ p.vertices.tail.dropLast, x ∈ W)
-- def_3_14 --- end helper

-- ref: def_3_14 (helper, bifurcation-through-`W` predicate) — refactor
--
-- `MarginalizationΦL G W u v` is the post-refactor port of
-- `MarginalizationΦL`: identical LN-level semantics ("exists a
-- bifurcation in `G` between `u` and `v` whose intermediate vertices
-- all lie in `W`"), retargeted onto `Walk` /
-- `IsBifurcation` / `vertices`.  The symmetric
-- `Or` over the two walk orientations is preserved — under the new
-- `CDMG` there is no `hL_symm` field, but the symmetric `Or`
-- in Φ_L remains LN-faithful (Φ_L is still semantically symmetric in
-- `(u, v)`).  Body byte-identical modulo the three surface retargets.
-- def_3_14 --- start helper
def MarginalizationΦL (G : CDMG Node) (W : Finset Node)
    (u v : Node) : Prop :=
  (∃ (p : Walk G u v),
      p.IsBifurcation ∧ ∀ x ∈ p.vertices.tail.dropLast, x ∈ W) ∨
  (∃ (p : Walk G v u),
      p.IsBifurcation ∧ ∀ x ∈ p.vertices.tail.dropLast, x ∈ W)
-- def_3_14 --- end helper

-- Classical decidability instance for `MarginalizationΦE`
-- (internal plumbing).  Same rationale as the original
-- `instDecidableMarginalizationΦE`: the existential over
-- `Walk G u v` is not constructively decidable without a
-- separate reachability-bound argument the chapter has not paid for;
-- `Classical.propDecidable` is the standard Mathlib fallback, and the
-- consequent `noncomputable` annotation propagates to
-- `marginalize`.
noncomputable instance instDecidableMarginalizationΦE
    (G : CDMG Node) (W : Finset Node) (u v : Node) :
    Decidable (G.MarginalizationΦE W u v) :=
  Classical.propDecidable _

noncomputable instance instDecidableMarginalizationΦL
    (G : CDMG Node) (W : Finset Node) (u v : Node) :
    Decidable (G.MarginalizationΦL W u v) :=
  Classical.propDecidable _

-- ## Proof helpers for the four CDMG axioms under marginalize
--
-- Four private lemmas (one fewer than the pre-refactor five — the
-- `hL_symm` obligation has been removed since `CDMG` carries
-- `L : Finset (Sym2 Node)` and swap-symmetry is *definitional* via
-- `Sym2`).  Factored out of `marginalize`'s structure literal
-- so the def body is pure data + lemma references.  None of the
-- obligations consume `hW`; it is carried on the def signature purely
-- for LN-faithfulness ("Let `W ⊆ V`").

private lemma marginalize_hJV_disj (G : CDMG Node)
    (W : Finset Node) :
    Disjoint G.J (G.V \ W) := by
  refine Finset.disjoint_left.mpr fun a haJ haVW => ?_
  exact Finset.disjoint_left.mp G.hJV_disj haJ (Finset.mem_sdiff.mp haVW).1

private lemma marginalize_hE_subset (G : CDMG Node)
    (W : Finset Node) :
    ∀ ⦃e : Node × Node⦄,
      e ∈ ((G.J ∪ (G.V \ W)) ×ˢ (G.V \ W)).filter
            (fun e => G.MarginalizationΦE W e.1 e.2) →
      e.1 ∈ G.J ∪ (G.V \ W) ∧ e.2 ∈ G.V \ W := by
  intro e he
  exact Finset.mem_product.mp (Finset.mem_filter.mp he).1

-- ## `marginalize_hL_subset` — `Sym2.Mem`-shaped obligation
--
-- The post-refactor `hL_subset` axiom on `CDMG` quantifies
-- *unordered-pair* membership via `Sym2.Mem` (`v ∈ s`), not by
-- destructuring `s = s(v₁, v₂)`.  Our `L` is built as
-- `(filter …).image (fun e => s(e.1, e.2))`, so the proof:
-- (1) `Finset.mem_image.mp hs` extracts the pre-image
-- `e : Node × Node` with `s = s(e.1, e.2)`;
-- (2) `Finset.mem_filter.mp` peels the filter conjunction off, giving
-- `(e ∈ product) ∧ (e.1 ≠ e.2 ∧ Φ_L …)`;
-- (3) `Finset.mem_product` gives `e.1 ∈ G.V \ W ∧ e.2 ∈ G.V \ W`;
-- (4) `Sym2.mem_iff.mp hv` reduces `v ∈ s(e.1, e.2)` to
-- `v = e.1 ∨ v = e.2`, and a case-split closes via `rfl`.
private lemma marginalize_hL_subset (G : CDMG Node)
    (W : Finset Node) :
    ∀ ⦃s : Sym2 Node⦄,
      s ∈ (((G.V \ W) ×ˢ (G.V \ W)).filter
              (fun e => e.1 ≠ e.2 ∧ G.MarginalizationΦL W e.1 e.2)).image
            (fun e => s(e.1, e.2)) →
      ∀ ⦃v : Node⦄, v ∈ s → v ∈ G.V \ W := by
  intro s hs v hv
  obtain ⟨e, hFilter, rfl⟩ := Finset.mem_image.mp hs
  obtain ⟨hProd, _⟩ := Finset.mem_filter.mp hFilter
  obtain ⟨h1, h2⟩ := Finset.mem_product.mp hProd
  rcases Sym2.mem_iff.mp hv with rfl | rfl
  · exact h1
  · exact h2

-- ## `marginalize_hL_irrefl` — `Sym2.IsDiag`-shaped obligation
--
-- The post-refactor `hL_irrefl` axiom on `CDMG` is phrased as
-- `¬ s.IsDiag` (Mathlib's canonical "no self-pair" predicate on `Sym2`),
-- not as the pre-refactor `v₁ ≠ v₂` on ordered pairs.  The proof reads
-- the `e.1 ≠ e.2` conjunct off the filter, and `Sym2.mk_isDiag_iff`
-- pulls `s(e.1, e.2).IsDiag` back to `e.1 = e.2`, contradicting.
private lemma marginalize_hL_irrefl (G : CDMG Node)
    (W : Finset Node) :
    ∀ ⦃s : Sym2 Node⦄,
      s ∈ (((G.V \ W) ×ˢ (G.V \ W)).filter
              (fun e => e.1 ≠ e.2 ∧ G.MarginalizationΦL W e.1 e.2)).image
            (fun e => s(e.1, e.2)) →
      ¬ s.IsDiag := by
  intro s hs hDiag
  obtain ⟨e, hFilter, rfl⟩ := Finset.mem_image.mp hs
  obtain ⟨_, hNe, _⟩ := Finset.mem_filter.mp hFilter
  exact hNe (Sym2.mk_isDiag_iff.mp hDiag)

-- The pre-refactor CDMG carried an `hL_symm` axiom because `L` was
-- encoded as a `Finset (Node × Node)` needing a separate symmetry
-- obligation.  Under `cdmg_typed_edges` the new `L` is a
-- `Finset (Sym2 Node)`, symmetric by construction, so the `hL_symm`
-- field — and every proof obligation that previously discharged it —
-- disappears from the refactor.  This empty REPLACEMENT block exists
-- only so the finalize-time marker validator can pair the ORIGINAL
-- `marginalize_hL_symm` block with a same-named REPLACEMENT.

-- ref: def_3_14
--
-- The *marginalization* of `G` w.r.t. `W` — the LN's `G^{∖W}` — as the
-- `CDMG` `G.marginalize W hW`.  Post-refactor port of
-- `marginalize` against the `cdmg_typed_edges` design (`def_3_1`'s
-- post-refactor shape: `L : Finset (Sym2 Node)`, no `hL_symm` axiom).
-- The four data fields are:
--   * `J^{∖W} := G.J`;
--   * `V^{∖W} := G.V \ W`;
--   * `E^{∖W} := { e ∈ (G.J ∪ (G.V \ W)) × (G.V \ W) | Φ_E W e.1 e.2 }`
--     — unchanged shape from the original, retargeted onto
--     `MarginalizationΦE`;
--   * `L^{∖W} := { s(e.1, e.2) | e ∈ (G.V \ W) × (G.V \ W),
--                  e.1 ≠ e.2, Φ_L W e.1 e.2 }` — the same set of
--     unordered pairs as the original's ordered-pair `L^{∖W}`, lifted
--     through the `Sym2.mk` quotient via `Finset.image`.  Build pattern:
--     `(filter …).image (fun e => s(e.1, e.2))` — filter on the
--     ordered-pair carrier first (so the `e.1 ≠ e.2` conjunct stays
--     writable), then `image` lifts to `Finset (Sym2 Node)`.
--
-- ## Design choice — post-refactor deltas
--
-- * **`L` is built via `(filter …).image (fun e => s(e.1, e.2))`, not
--   directly as a `Finset.filter` over a `Sym2`-carrier.**  Filtering
--   directly over `Finset (Sym2 Node)` would require either (i) a
--   pre-existing `Sym2`-carrier `Finset` to filter from (which we don't
--   have — the LN's `L^{∖W}` is set-builder-defined, not derived from
--   `G.L`), or (ii) hand-building such a carrier from `(G.V \ W) ×ˢ
--   (G.V \ W)` via a more elaborate `Sym2`-equivalence-class step.
--   The filter-then-image pattern is the cleanest LN-faithful encoding:
--   the ordered-pair filter mirrors the LN's set-builder
--   `{ (ū, ō) ∈ (V \ W) × (V \ W) | ū ≠ ō ∧ Φ_L(ū, ō) }` literally,
--   and `Finset.image (fun e => s(e.1, e.2))` is the standard Mathlib
--   idiom for quotienting an ordered-pair `Finset` to its `Sym2`
--   image.  Both pairs `(u, v)` and `(v, u)` in the source filter
--   collapse to the same `s(u, v)` in the image, mirroring the
--   unordered-pair semantics.
--
-- * **No `marginalize_hL_symm` field.**  The post-refactor
--   `CDMG` structure carries only four proof obligations
--   (`hJV_disj`, `hE_subset`, `hL_subset`, `hL_irrefl`); the
--   pre-refactor `hL_symm` field is gone because swap-symmetry is
--   *definitional* on `Sym2` (`s(v, w) = s(w, v)` by quotient
--   construction).  The pre-refactor `marginalize_hL_symm` proof
--   (which closed via `Or.comm` on Φ_L's two walk-orientation
--   disjuncts) has no analogue here — the symmetry it asserted is
--   structurally vacuous post-refactor.
--
-- * **`MarginalizationΦL` keeps the symmetric `Or` over the
--   two walk orientations**, even though no `hL_symm` field consumes
--   it.  The symmetric encoding is *semantically* faithful to the LN's
--   "bifurcation between `ū` and `ō`" phrasing (an undirected concept
--   at the LN level), and downstream consumers (`claim_3_16`–`3_19`)
--   may want a symmetric Φ_L for their own purposes.  Dropping the
--   `Or` here would be a gratuitous deviation from the original; the
--   refactor's principle is "port mechanically, preserve LN-level
--   semantics", not "trim every redundancy".
--
-- * **`hW` remains carried, `noncomputable` remains.**  Both
--   unchanged from the original — `hW` is signature-level LN-fidelity
--   only, and `noncomputable` is inherited from the classical
--   decidability instances above.  Same `set_option
--   linter.unusedVariables false in` to suppress the linter warning
--   on the unused `hW`.
set_option linter.unusedVariables false in
set_option maxHeartbeats 800000 in
-- def_3_14 -- start statement
noncomputable def marginalize (G : CDMG Node) (W : Finset Node)
    (hW : W ⊆ G.V) : CDMG Node where
  J := G.J
  V := G.V \ W
  hJV_disj := marginalize_hJV_disj G W
  E := ((G.J ∪ (G.V \ W)) ×ˢ (G.V \ W)).filter
        (fun e => G.MarginalizationΦE W e.1 e.2)
  hE_subset := marginalize_hE_subset G W
  L := (((G.V \ W) ×ˢ (G.V \ W)).filter
        (fun e => e.1 ≠ e.2 ∧ G.MarginalizationΦL W e.1 e.2)).image
        (fun e => s(e.1, e.2))
  hL_subset := marginalize_hL_subset G W
  hL_irrefl := marginalize_hL_irrefl G W
-- def_3_14 -- end statement

end CDMG

end Causality
