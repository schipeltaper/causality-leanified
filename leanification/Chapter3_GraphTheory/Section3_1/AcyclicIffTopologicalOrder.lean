import Chapter3_GraphTheory.Section3_1.Acyclicity
import Chapter3_GraphTheory.Section3_1.TopologicalOrder
import Chapter3_GraphTheory.Section3_1.CDMGTypes

namespace Causality

/-!
# Acyclicity is equivalent to existence of a topological order (`claim_3_2`)

This file formalises the LN lemma block `claim_3_2` from `graphs.tex`,
immediately following `def-topological-order`:

> A CDMG `G = (J, V, E, L)` is acyclic if and only if it has a
> topological order.

The authoritative spec is the rewritten canonical tex statement at
`leanification/Chapter3_GraphTheory/Section3_1/tex/`
`claim_3_2_statement_AcyclicIffTopologicalOrder.tex`, verified
equivalent to the LN block.  The row carries an empty
`addition_to_the_LN`; the LN-critic wording-check returned
`NO_SUBTLETIES`.  The literal LN sentence is authoritative.

Both sides of the biconditional refer to upstream chapter-3 predicates
already in this folder:

* `G.IsAcyclic` from `def_3_6` (`Acyclicity.lean`) — there does not
  exist a non-trivial directed walk from any node `v ∈ J ∪ V` back to
  itself.
* `G.IsTopologicalOrder lt` from `def_3_8` (`TopologicalOrder.lean`) —
  the four-conjunct `Prop` predicate on an external relation
  `lt : Node → Node → Prop` asserting (i) irreflexivity on `J ∪ V`,
  (ii) transitivity on `J ∪ V`, (iii) trichotomy on `J ∪ V`, and (iv)
  `v ∈ Pa^G(w) → lt v w` (parents precede their children).

Because `def_3_8` characterises *which* relations qualify as a
topological order (rather than asserting one exists), "G has a
topological order" reads in Lean as the existential
`∃ lt : Node → Node → Prop, G.IsTopologicalOrder lt` — exactly the
shape that `def_3_8`'s "Downstream consumers" design block
anticipates.  The label set `L` of `def_3_1` plays no role on either
side of the biconditional; the result is a property of the
`(J, V, E)`-skeleton of `G` only.

The theorem body is filled in by `prove_claim_in_lean` (Manager B),
following the verified TeX proof at
`tex/claim_3_2_proof_AcyclicIffTopologicalOrder.tex`.  Proof-only
helpers (walk concatenation, source/target-in-`G` for non-trivial
directed walks, single-edge directed walk, walk-induction on `lt`)
live just below the `variable` block, outside the marker zones
because they are not statement content.

-/

namespace CDMG

-- ## Design choice — statement context (refactor twin)
--
-- Three-dash `--- start helper` markers match the convention used
-- across `CDMG.lean`, `CDMGNotation.lean`, `Walks.lean`,
-- `EdgeRelations.lean`, `CDMGRestrictions.lean`, `Acyclicity.lean`,
-- `CDMGTypes.lean`, `TopologicalOrder.lean`, and
-- `FamilyRelationships.lean` for the `variable` line that binds the
-- implicit parameters into the theorem and proof-only helpers wrapped
-- below.  Both `Node : Type*` and `[DecidableEq Node]` are inherited
-- verbatim from `def_3_1`'s refactor twin (`CDMG`): the
-- `Membership Node (CDMG Node)` instance from `def_3_2`'s
-- refactor twin (`instMembership` in `CDMGNotation.lean`) —
-- driving the `v ∈ G` quantifier scope throughout — reduces to
-- `Finset.mem` on `G.J ∪ G.V`, which needs `DecidableEq Node`; the
-- `Walk G u v` recursion in every walk-class helper, the
-- `IsDirectedWalk` Prop in the proof body, and the
-- `G.Pa w` set-builder in `IsTopologicalOrder` all
-- transitively rely on `DecidableEq Node` for their `Finset` /
-- `Sym2`-typed membership checks.
-- claim_3_2 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- claim_3_2 --- end helper

-- ## Proof-only helpers (refactor twins)
--
-- The seven helpers below are refactor twins of the corresponding
-- `private def Walk.* / private lemma Walk.*` declarations in the
-- original `namespace CDMG` block above; they are infrastructure for
-- the proof of `acyclic_iff_topological_order`.  They are
-- deliberately private and carry no marker comments other than the
-- REFACTOR-BLOCK-REPLACEMENT pairs — the markers are reserved for
-- declarations whose body is the formalised LN content of a row, and
-- these are just walk-level plumbing (concatenation, length /
-- directedness preservation under concatenation, source / target-
-- membership for a non-trivial directed walk, the single-edge
-- directed walk witnessing the parent → child step, and the
-- walk-induced `lt` propagation under transitivity + parent-precedes).
-- See `tex/refactor_claim_3_2_proof_AcyclicIffTopologicalOrder.tex`
-- for the TeX proof these helpers implement (unchanged by the
-- refactor; the mathematics is identical to the original twin).

-- *Why this helper exists.*  The (⇒) direction reads walk
-- reachability as a partial order on `J ∪ V`; `comp` is
-- the engine for both `htrans` (concatenate two `le₀`-witnesses)
-- and `hantisymm` (concatenate two opposing non-trivial directed
-- walks into the self-loop that refutes acyclicity).  Required
-- input to `extend_partialOrder`.
--
-- *Typed-WalkStep shape: structure-agnostic.*  Concatenation does
-- not inspect the channel, so the cons recursion passes the typed
-- `s` through verbatim — one-for-one field rename `a, h ↦ s`, body
-- otherwise identical to the original.
/-- Concatenate two refactor_Walks `p : u → v` and `q : v → w` into a
walk `u → w`. -/
private def Walk.comp {G : CDMG Node} :
    ∀ {u v w : Node}, Walk G u v → Walk G v w →
      Walk G u w
  | _, _, _, .nil _ _, q => q
  | _, _, _, .cons v s p, q => .cons v s (p.comp q)

-- *Why this helper exists.*  The `omega`-discharged
-- `(p.comp q).length ≥ 1` step in `htrans` and `hantisymm` needs
-- length's additivity under concatenation as a `simp` lemma; this
-- is that lemma.
--
-- *Typed-WalkStep shape: structure-agnostic.*  Pure structural
-- recursion on the walk spine plus `Nat` arithmetic — the typed
-- step never enters the case split.  Body is the original with
-- `length` / `comp` swapped for `length` / `comp`.
/-- The `length` of `p.comp q` is `p.length
+ q.length`. -/
private lemma Walk.length_comp {G : CDMG Node} :
    ∀ {u v w : Node} (p : Walk G u v) (q : Walk G v w),
      (p.comp q).length =
        p.length + q.length
  | _, _, _, .nil _ _, q => by
      simp [Walk.comp, Walk.length]
  | _, _, _, .cons _ _ p, q => by
      simp [Walk.comp, Walk.length,
            Walk.length_comp p q,
            Nat.add_comm, Nat.add_left_comm]

-- *Why this helper exists.*  `htrans`'s `Or.inr ⟨p.comp q, …⟩`
-- and `hantisymm`'s opposing-walks self-loop both construct the
-- concatenated walk; they need a witness that directedness
-- survives the concatenation — this lemma supplies it inductively.
--
-- *Typed-WalkStep shape: simplifies.*  The original's
-- `obtain ⟨ha_eq, ha_E, hq_dir⟩ := hp` plus `⟨h1, h2, recurse⟩`
-- reassembly is replaced by a structural recursion on the typed
-- step `s`: `.forwardE _` recurses on the tail's witness, while
-- `.backwardE _` / `.bidir _` close by `hp.elim` (their
-- `IsDirectedWalk` is `False` definitionally — discharged
-- by structural impossibility, not by hand).
set_option linter.style.longLine false in
/-- Directedness is preserved under `comp`: concatenating
two directed walks produces a directed walk. -/
private lemma Walk.isDirectedWalk_comp {G : CDMG Node} :
    ∀ {u v w : Node} (p : Walk G u v) (q : Walk G v w),
      p.IsDirectedWalk → q.IsDirectedWalk →
        (p.comp q).IsDirectedWalk
  | _, _, _, .nil _ _, _, _, hq => hq
  | _, _, _, .cons _ (.forwardE _) p, q, hp, hq =>
      Walk.isDirectedWalk_comp p q hp hq
  | _, _, _, .cons _ (.backwardE _) _, _, hp, _ => hp.elim
  | _, _, _, .cons _ (.bidir _) _, _, hp, _ => hp.elim

-- *Why this helper exists.*  `hantisymm` needs `a ∈ G` to invoke
-- `hac a ha (…)` on the acyclicity hypothesis; the source of a
-- non-trivial directed walk is the source of its first edge,
-- which sits in `G.J ∪ G.V = G` by `hE_subset.1`.
--
-- *Typed-WalkStep shape: simplifies.*  The original's
-- `obtain ⟨ha_eq, ha_E, _⟩ := hp` then
-- `(G.hE_subset (ha_eq ▸ ha_E)).1` collapses to a single
-- `.forwardE h ↦ (G.hE_subset h).1` clause: `h : (u, v) ∈ G.E` is
-- the constructor argument, no rewrite step.  `.backwardE _` /
-- `.bidir _` close by `hp.elim`.
set_option linter.style.longLine false in
/-- The source of a non-trivial directed walk lies in `G`. -/
private lemma Walk.source_in_G_of_directedWalk_pos
    {G : CDMG Node} :
    ∀ {u v : Node} (p : Walk G u v),
      p.IsDirectedWalk → p.length ≥ 1 → u ∈ G
  | _, _, .nil _ _, _, hlen => by
      simp [Walk.length] at hlen
  | _, _, .cons _ (.forwardE h) _, _, _ => (G.hE_subset h).1
  | _, _, .cons _ (.backwardE _) _, hp, _ => hp.elim
  | _, _, .cons _ (.bidir _) _, hp, _ => hp.elim

-- *Why this helper exists.*  `lt_of_directedWalk_pos`'s
-- transitivity step needs `w ∈ G` to invoke `h_trans u … w …` on
-- a non-trivial directed tail; combined with `hE_subset.2` on the
-- trivial-tail base case (forced `v = w` under `nil`), this gives
-- `w ∈ G` uniformly.
--
-- *Typed-WalkStep shape: simplifies.*  The original's
-- `obtain ⟨ha_eq, ha_E, hq_dir⟩ := hdir` then `ha_eq ▸ ha_E` to
-- recover `(u, v) ∈ G.E` collapses to a `cases s`: `.forwardE h`
-- exposes `h : (u, v) ∈ G.E` directly, while `.backwardE _` /
-- `.bidir _` close by `hdir.elim`.  The recursive-tail vs trivial-
-- tail `match` is otherwise unchanged.
set_option linter.style.longLine false in
/-- The target of a non-trivial directed walk lies in `G`. -/
private lemma Walk.target_in_G_of_directedWalk_pos
    {G : CDMG Node} :
    ∀ {u v : Node} (p : Walk G u v),
      p.IsDirectedWalk → p.length ≥ 1 → v ∈ G := by
  intro u v p
  induction p with
  | nil _ _ => intro _ hlen; simp [Walk.length] at hlen
  | @cons u w v s q ih =>
      intro hdir _
      cases s with
      | forwardE h =>
          by_cases hq_len : q.length ≥ 1
          · exact ih hdir hq_len
          · -- `q` is the trivial walk; `q : Walk G v w` with
            -- `v = w` forced by `Walk.nil`.
            have hlen0 : q.length = 0 := by omega
            match q, hdir, hlen0 with
            | .nil _ _, _, _ =>
                exact Finset.mem_union_right _ (G.hE_subset h).2
      | backwardE _ => exact hdir.elim
      | bidir _ => exact hdir.elim

-- *Why this helper exists.*  Two consumer sites in (⇒): (i) the
-- parent-precedes step needs `le₀ u w` from `u ∈ Pa^G(w)`,
-- packaged as the length-1 walk on the edge `(u, w) ∈ G.E`; (ii)
-- the self-loop contradiction at `u = w` reuses the same length-1
-- walk on `(u, u) ∈ G.E` to refute acyclicity.
--
-- *Typed-WalkStep shape: simplifies, and the constructor must be
-- `.forwardE`.*  A directed edge `(u, v) ∈ G.E` only fits
-- `.forwardE` (its argument type is exactly `(u, v) ∈ G.E`); the
-- typed channel forbids landing it in `.bidir` (wrong carrier —
-- `Sym2`-valued, would need `s(u, v) ∈ G.L`) or `.backwardE`
-- (wrong direction — would need `(v, u) ∈ G.E`).  The original's
-- `G.WalkStep u (u, v) v` witness `Or.inl ⟨rfl, Or.inl huv⟩` and
-- the cons-head directedness witness `⟨rfl, huv, trivial⟩`
-- collapse to constructor arguments: the WalkStep is just
-- `.forwardE huv`, and the directedness reduces to `trivial`
-- (the nil case of `IsDirectedWalk` under `.forwardE`).
set_option linter.style.longLine false in
/-- A single edge `(u, v) ∈ G.E` (with `v ∈ G`) is witnessed by a
length-1 directed `Walk` from `u` to `v`. -/
private lemma Walk.refactor_singleEdge_directedWalk
    {G : CDMG Node}
    {u v : Node} (hv : v ∈ G) (huv : (u, v) ∈ G.E) :
    ∃ p : Walk G u v,
      p.IsDirectedWalk ∧ p.length ≥ 1 := by
  refine ⟨Walk.cons v (.forwardE huv) (Walk.nil v hv),
          ?_, ?_⟩
  · -- `IsDirectedWalk` on `cons _ (.forwardE _) (nil _ _)`
    -- reduces to `(nil _ _).IsDirectedWalk = True`.
    trivial
  · simp [Walk.length]

-- *Why this helper exists.*  The (⇐) direction Leanifies the LN's
-- `v = v_0 < v_1 < ⋯ < v_n = v_0` chain as a single inductive
-- walk-walk: under transitivity + parent-precedes, a non-trivial
-- directed walk `x → ⋯ → y` forces `lt x y`.  Specialised at
-- `x = y = v` (a hypothetical directed self-loop), this
-- contradicts irreflexivity — the engine of the (⇐) contradiction.
--
-- *Typed-WalkStep shape: simplifies.*  The original's
-- `obtain ⟨ha_eq, ha_E, hq_dir⟩ := hdir` is replaced by `cases s`:
-- `.forwardE h` exposes `h : (u, v) ∈ G.E` directly (driving
-- `hu`, `hv`, `hlt_uv := h_parent u v ⟨hu, h⟩` without the rewrite
-- step), while `.backwardE _` / `.bidir _` close by `hdir.elim`.
-- The recursive-tail vs trivial-tail split inside `.forwardE` is
-- unchanged from the original.
set_option linter.style.longLine false in
/-- Along a non-trivial directed walk, a topological order forces
`lt` between source and target.  Used in the (⇐) direction of
`acyclic_iff_topological_order`: a hypothetical directed
self-loop `v → … → v` would contradict irreflexivity of any
topological order. -/
private lemma Walk.lt_of_directedWalk_pos
    {G : CDMG Node}
    {lt : Node → Node → Prop}
    (h_trans : ∀ u ∈ G, ∀ v ∈ G, ∀ w ∈ G, lt u v → lt v w → lt u w)
    (h_parent : ∀ v w, v ∈ G.Pa w → lt v w) :
    ∀ {x y : Node} (p : Walk G x y),
      p.IsDirectedWalk → p.length ≥ 1 → lt x y := by
  intro x y p
  induction p with
  | nil _ _ => intro _ hlen; simp [Walk.length] at hlen
  | @cons u w v s q ih =>
      intro hdir _
      cases s with
      | forwardE h =>
          have hu : u ∈ G := (G.hE_subset h).1
          have hv : v ∈ G :=
            Finset.mem_union_right _ (G.hE_subset h).2
          have hlt_uv : lt u v := h_parent u v ⟨hu, h⟩
          by_cases hq_len : q.length ≥ 1
          · -- recurse on `q`
            have hw : w ∈ G :=
              Walk.target_in_G_of_directedWalk_pos q
                hdir hq_len
            have hlt_vw : lt v w := ih hdir hq_len
            exact h_trans u hu v hv w hw hlt_uv hlt_vw
          · -- `q` is the trivial walk; `v = w`.
            have hlen0 : q.length = 0 := by omega
            match q, hdir, hlen0 with
            | .nil _ _, _, _ => exact hlt_uv
      | backwardE _ => exact hdir.elim
      | bidir _ => exact hdir.elim

-- ref: claim_3_2 — refactor twin
-- A CDMG `G = (J, V, E, L)` is acyclic (in the sense of `def_3_6`)
-- iff there exists a topological order of `G` (in the sense of
-- `def_3_8`).  The biconditional has shape
--   `G.IsAcyclic ↔
--    ∃ lt, G.IsTopologicalOrder lt`.
/-
LN tex (rewritten canonical statement for `claim_3_2`, unchanged by
the refactor):

  Let `G = (J, V, E, L)` be a CDMG.  Then `G` is acyclic (in the sense
  of def_3_6) iff there exists a topological order of `G` (in the
  sense of def_3_8); equivalently, `G` is acyclic iff there exists a
  strict total order `<` on `J ∪ V` — i.e.\ a binary relation `<` on
  `J ∪ V` that is irreflexive, transitive, and trichotomous — such
  that, for every `v, w ∈ J ∪ V`, `v ∈ Pa^G(w) ⟹ v < w`.  The label
  set `L` plays no role on either side of the biconditional.
-/
-- ## Design choice (refactor twin)
--
-- *Structural port of the original `acyclic_iff_topological_order`*
--
--   onto the `cdmg_typed_edges` refactor's new upstream types
--   (DEPENDENT row; roots `def_3_1`, `def_3_4`).  The mathematical
--   design — biconditional shape, nested topological-order encoding
--   (`IsTotalOrder ∧ parent-precedence`), walk-reachability-then-
--   Szpilrajn for the (⇒) direction (refl/trans via walk
--   concatenation, antisymm via acyclicity ruling out the cycle
--   formed by opposing non-trivial walks), parent-precedes-plus-
--   irreflexivity contradiction for the (⇐) direction, the seven
--   proof-only helpers (concatenation, length-additivity,
--   directedness preservation, source / target in `G`, single-edge
--   directed walk, walk-induced `lt`) — is **unchanged**.  See the
--   original block above for the full rationale (shape of the
--   biconditional, nested 2-conjunct shape, `∃ lt : Node → Node →
--   Prop` over bundled order, witness-assembly via the nested
--   encoding, surface signature minimal, labels `L` absent from both
--   sides, known limitation of non-canonical witness).  All
--   `addition_to_the_LN` clauses are empty and the LN-critic
--   wording-check returned `NO_SUBTLETIES`; both carry over verbatim.
--
-- *Mathematical content unchanged (TL;DR).*  The twin proves the
--   same theorem and runs the same argument as the original; the
--   refactor only swaps the upstream `Walk` / `CDMG` shapes the
--   proof consumes (typed `WalkStep` constructors in
--   place of the `WalkStep`-Prop disjunction; `CDMG.L`
--   retyped to `Finset (Sym2 Node)`, but neither side of this
--   biconditional reads `L`).  No new mathematical commitment.
--
-- *Why `∃ lt : Node → Node → Prop` (rather than a bundled order).*
--   The right-hand side `∃ lt, G.IsTopologicalOrder lt`
--   passes the relation as a bare `Node → Node → Prop` —
--   consistent with `IsTopologicalOrder`'s signature,
--   which itself takes `lt` unbundled (see `TopologicalOrder.lean`'s
--   refactor twin design block).  Threading a bundled
--   `LinearOrder Node` / `IsTotalOrder Node lt` through the
--   existential would force decidability on `lt` at every use
--   site, which neither the LN nor any chapter-3 consumer asks
--   for.  Empty `addition_to_the_LN` confirms the literal LN's
--   "has a topological order" is the spec: *pure existence*, no
--   uniqueness, no constructive choice; any linear refinement of
--   the parent-precedence partial order qualifies.
--
-- *Why `[DecidableEq Node]` alone (no `[Fintype Node]`).*
--   Finiteness of `J ∪ V` — the only domain on which the order
--   must be total — is already carried by the `Finset`-valued
--   fields `CDMG.J` / `CDMG.V` from `def_3_1`'s
--   refactor twin; the finiteness witness comes from the
--   structure, not from a typeclass over the ambient `Node`.
--   `[DecidableEq Node]` is the *minimal* binder that lets the
--   chapter-3 chain kernel-reduce: `Finset` membership in
--   `G.J ∪ G.V`, the `Membership Node (CDMG Node)`
--   instance from `def_3_2`'s twin (resolving `v ∈ G`), and the
--   `IsDirectedWalk` recursion all reach through it.
--   `[Fintype Node]` was considered (a constructive variant of
--   (⇒) could enumerate `(G.J ∪ G.V).toList` to pick the order by
--   hand) and rejected at the signature level: the
--   classical-Szpilrajn construction in the proof body never
--   enumerates, so leaking the typeclass would over-constrain
--   consumers for no statement-level gain.
--
-- *Upstream-type shifts (and only those).*  The Lean translation
--   work is *mechanical* — each substitution maps one identifier:
--   - `CDMG Node                   → CDMG Node`
--   - `G.IsAcyclic                 → G.IsAcyclic`
--   - `G.IsTopologicalOrder lt     → G.IsTopologicalOrder lt`
--   - `G.IsTotalOrder lt           → G.IsTotalOrder lt`
--   - `Walk G u v                  → Walk G u v`
--   - `Walk.nil v hv               → Walk.nil v hv`
--   - `Walk.cons v a h p           → Walk.cons v s p`
--     (drops the `a : Node × Node` ordered pair and the
--     `h : G.WalkStep u a v` Prop witness; takes a typed
--     `s : WalkStep G u v` instead — see the `def_3_4`
--     refactor design block at `Walks.lean:1400-1462`)
--   - `p.IsDirectedWalk            → p.IsDirectedWalk`
--   - `p.length                    → p.length`
--   - `G.WalkStep` (Prop disjunction) → `WalkStep` (typed
--     inductive with `.forwardE` / `.backwardE` / `.bidir`)
--   - `G.Pa w                      → G.Pa w`
--   - Each `Walk.<helper>` / `Walk.<lemma>` → its
--     `Walk.refactor_<helper>` twin in this namespace.
--
-- *The single non-mechanical reshape.*  The directed-walk
--   destructuring in three of the helpers
--   (`isDirectedWalk_comp`,
--   `source_in_G_of_directedWalk_pos`,
--   `target_in_G_of_directedWalk_pos`,
--   `lt_of_directedWalk_pos`) and inline in the proof body
--   shifts from
--     `obtain ⟨ha_eq, ha_E, hq_dir⟩ := hp`
--   (a triple-conjunction `Prop` recursion on the original
--   `IsDirectedWalk (cons _ a _ p) = a = (u, v) ∧ a ∈ G.E ∧
--   p.IsDirectedWalk`) to a *structural match on the typed
--   `WalkStep` constructor*: under `.forwardE h` the
--   directed-walk predicate reduces to `p.IsDirectedWalk`
--   and the `(u, v) ∈ G.E` witness is the constructor argument `h`
--   directly (no `ha_eq ▸ ha_E` rewrite); under `.backwardE _` or
--   `.bidir _` the predicate is `False`, so those cases close by
--   `hp.elim`.  This is *still a port* — the LN's "directed walk"
--   argument is unchanged; only the Lean encoding of "this step is a
--   directed step" shifts from a Prop witness to a constructor tag.
--   The shape transposition is fully captured in the helper twins;
--   the theorem body itself reads near-verbatim against the renamed
--   helpers.
--
-- *Constructor-witness collapse for `refactor_singleEdge_directedWalk`.*
--   The original needed an explicit `G.WalkStep u (u, v) v` witness
--   `Or.inl ⟨rfl, Or.inl huv⟩` (the LN's `(u, v) ∈ G.E` case under
--   the `WalkStep`-disjunction's first branch); the refactor twin's
--   witness is *just* `WalkStep.forwardE huv`, with the
--   `(u, v)` indices recovered from the WalkStep's type indices and
--   the `huv : (u, v) ∈ G.E` membership stored directly as the
--   constructor argument.  The directedness witness on the resulting
--   length-1 walk collapses correspondingly: the original needed
--   `⟨rfl, huv, trivial⟩` (matching the triple-conjunction recursion
--   on the cons head), the refactor twin needs just `trivial` (the
--   `nil` case of `IsDirectedWalk`, since `.forwardE`'s
--   `IsDirectedWalk` recursion bottoms out at the trivial
--   tail).  This is a *simplification the refactor buys* at this
--   row — a strictly smaller proof obligation per use site.
--
-- *Acyclicity / topological-order packaging preserved.*
--   `IsAcyclic` keeps the same shape as the original
--   (a `¬ ∃` over walks of length ≥ 1; see `Acyclicity.lean`'s
--   refactor twin), and `IsTopologicalOrder` keeps the
--   nested 2-conjunct shape `IsTotalOrder ∧
--   parent-precedence` (see `TopologicalOrder.lean`'s refactor twin).
--   Consequently every `.1` / `.2` projection and every
--   `rintro ⟨lt, ⟨hi, htr, htri⟩, hp⟩` / anonymous-constructor
--   destructuring in the proof body carries over verbatim — this is
--   what makes the port mechanical.  The (⇒) direction's final
--   `refine ⟨fun u v => s u v ∧ u ≠ v, ⟨?_, ?_, ?_⟩, ?_⟩` reads the
--   `IsTopologicalOrder` shape exactly as the original read
--   `IsTopologicalOrder`; the (⇐) direction's
--   `rintro ⟨lt, ⟨hi, htr, htri⟩, hp⟩` destructures the existential
--   with the matching nested pattern, putting the four hypotheses
--   needed for the contradiction in scope under their natural names
--   without adjustment.
--
-- *Labels `L` absent from both sides.*  Neither
--   `IsAcyclic` (only inspects `Walk` +
--   `IsDirectedWalk`, neither of which reads `G.L`) nor
--   `IsTopologicalOrder` (only references `Pa`,
--   a `G.E`-only construct) touches the `L` field.  The
--   `Finset (Node × Node) → Finset (Sym2 Node)` retyping at root
--   `def_3_1` does not propagate here.  This is a property of the
--   `(J, V, E)`-skeleton of `G` only — exactly as in the original.
set_option linter.style.longLine false in
-- claim_3_2 -- start statement
theorem acyclic_iff_topological_order (G : CDMG Node) :
    G.IsAcyclic ↔
      ∃ lt : Node → Node → Prop, G.IsTopologicalOrder lt
-- claim_3_2 -- end statement
:= by
  -- TeX proof: tex/refactor_claim_3_2_proof_AcyclicIffTopologicalOrder.tex
  constructor
  · -- (⇒) Acyclic ⇒ a topological order exists.
    --
    -- Following the LN proof: define the reflexive walk-reachability
    -- relation `le₀ u v := u = v ∨ ∃ directed walk u → v of length
    -- ≥ 1`, show it is a partial order (refl/trans via walk
    -- concatenation, antisymm via acyclicity), then apply Mathlib's
    -- Szpilrajn extension (`extend_partialOrder`) to obtain a linear
    -- order `s` extending `le₀`.  Reading `lt u v := s u v ∧ u ≠ v`
    -- gives the strict total order witnessing
    -- `IsTopologicalOrder`.
    intro hac
    let le₀ : Node → Node → Prop := fun u v =>
      u = v ∨ ∃ p : Walk G u v,
        p.IsDirectedWalk ∧ p.length ≥ 1
    -- Reflexivity, transitivity, antisymmetry of `le₀`.
    have hrefl : ∀ a, le₀ a a := fun _ => Or.inl rfl
    have htrans : ∀ a b c, le₀ a b → le₀ b c → le₀ a c := by
      intros a b c hab hbc
      rcases hab with heq | ⟨p, hp_dir, hp_len⟩
      · subst heq; exact hbc
      rcases hbc with heq | ⟨q, hq_dir, hq_len⟩
      · subst heq; exact Or.inr ⟨p, hp_dir, hp_len⟩
      · refine Or.inr ⟨p.comp q,
          Walk.isDirectedWalk_comp p q hp_dir hq_dir, ?_⟩
        rw [Walk.length_comp]; omega
    have hantisymm : ∀ a b, le₀ a b → le₀ b a → a = b := by
      intros a b hab hba
      rcases hab with heq | ⟨p, hp_dir, hp_len⟩
      · exact heq
      rcases hba with heq | ⟨q, hq_dir, hq_len⟩
      · exact heq.symm
      · -- Both `p : a → b` and `q : b → a` non-trivial directed
        -- walks.  Concatenate to a non-trivial directed walk `a →
        -- a`, contradict acyclicity at `a` (`a ∈ G` from the source
        -- of `p`).
        exfalso
        have ha : a ∈ G :=
          Walk.source_in_G_of_directedWalk_pos p
            hp_dir hp_len
        refine hac a ha ⟨p.comp q,
          Walk.isDirectedWalk_comp p q hp_dir hq_dir, ?_⟩
        rw [Walk.length_comp]; omega
    haveI : Std.Refl le₀ := ⟨hrefl⟩
    haveI : IsTrans Node le₀ := ⟨htrans⟩
    haveI : Std.Antisymm le₀ := ⟨hantisymm⟩
    haveI : IsPreorder Node le₀ := {}
    haveI : IsPartialOrder Node le₀ := {}
    -- Szpilrajn extension: a linear order `s` with `le₀ ≤ s`.
    obtain ⟨s, hs_lo, h_sub⟩ := extend_partialOrder le₀
    -- Promote `hs_lo` to an active typeclass instance so the
    -- inherited `IsTrans` / `Std.Total` / `Std.Antisymm` are
    -- resolvable by name (without `haveI` they sit as a regular
    -- hypothesis, invisible to typeclass synthesis — hence the
    -- unification failures otherwise triggered by
    -- `Std.Total.total v w`).
    haveI : IsLinearOrder Node s := hs_lo
    -- The strict version of `s` is our topological order.
    refine ⟨fun u v => s u v ∧ u ≠ v, ⟨?_, ?_, ?_⟩, ?_⟩
    · -- Irreflexivity on `G`: `¬ (s v v ∧ v ≠ v)` from `v ≠ v`.
      intro v _ hlt
      exact hlt.2 rfl
    · -- Transitivity on `G`.
      intros u _ v _ w _ huv hvw
      obtain ⟨hsuv, hne_uv⟩ := huv
      obtain ⟨hsvw, hne_vw⟩ := hvw
      refine ⟨IsTrans.trans u v w hsuv hsvw, ?_⟩
      intro huw
      subst huw
      -- `s u v` and `s v u` with antisymm gives `u = v`,
      -- contradicting `hne_uv`.
      exact hne_uv (Std.Antisymm.antisymm u v hsuv hsvw)
    · -- Trichotomy on `G`: from totality of `s`.
      intros v _ w _
      by_cases h : v = w
      · right; left; exact h
      · rcases (Std.Total.total (r := s) v w) with hvw | hwv
        · left; exact ⟨hvw, h⟩
        · right; right; exact ⟨hwv, fun heq => h heq.symm⟩
    · -- Parent precedes: `u ∈ Pa^G(w) → lt u w`.
      intros u w hu_in_Pa
      obtain ⟨hu, huw_E⟩ := hu_in_Pa
      have hw : w ∈ G :=
        Finset.mem_union_right _ (G.hE_subset huw_E).2
      have hle₀_uw : le₀ u w :=
        Or.inr (Walk.refactor_singleEdge_directedWalk hw huw_E)
      have hsuw : s u w := h_sub _ _ hle₀_uw
      refine ⟨hsuw, ?_⟩
      intro heq
      subst heq
      -- A self-loop `(u, u) ∈ G.E` would give a length-1 directed
      -- walk `u → u`, contradicting acyclicity at `u`.
      exact hac u hu
        (Walk.refactor_singleEdge_directedWalk hu huw_E)
  · -- (⇐) A topological order ⇒ acyclic.
    --
    -- LN argument: a non-trivial directed walk `v = v_0 → v_1 → ⋯ →
    -- v_n = v` with `n ≥ 1` would give a chain
    -- `v_0 < v_1 < ⋯ < v_n = v_0` under any topological order,
    -- contradicting irreflexivity.  Encoded as
    -- `Walk.lt_of_directedWalk_pos` above (which
    -- uses parent-precedes and transitivity to walk along edges) and
    -- combined with the topological order's irreflexivity field.
    rintro ⟨lt, ⟨hi, htr, htri⟩, hp⟩
    intro v hv ⟨p, hp_dir, hp_len⟩
    exact hi v hv
      (Walk.lt_of_directedWalk_pos htr hp p hp_dir hp_len)

end CDMG

end Causality
