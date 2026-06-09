# Workspace for claim_3_5 — BifurcationAlternative

## The claim
Iff between "there exists a bifurcation between $v$ and $w$ with source $c$" and
"$v \ne w$ and $c \in \Anc^{G_{\doit(w)}}(v) \sm \{v\}$ and $c \in \Anc^{G_{\doit(v)}}(w) \sm \{w\}$".

## Key context from upstream encoding (def_3_4 in Section3_1/Walks.lean)
- `IsBifurcation`: existential over a split index $i$ with `IsBifurcationWithSplit`.
- `IsBifurcationSource p x`: requires `IsBifurcationDirectedHingeWithSplit i` AND `x = v_{i+1}`.
- The helper `IsBifurcationDirectedHingeWithSplit` **excludes** the degenerate `k = n`
  (right arm trivial) case via the `.cons _ _ _ (.nil _ _), 0 => False` branch.
  This is the chapter-init addition `[bifurcation_right_chain_trivial_is_just_directed_walk]`.
- Consequence: in our Lean encoding, whenever `IsBifurcationSource p c` holds, `c` is an
  **interior** vertex of the bifurcation walk, so `c ≠ v` and `c ≠ w` automatically.

## Wording-check resolution
The LN-critic flagged that literal def 3.4 permits `c = w` in a degenerate single-edge
case. **Our def_3_4 encoding already commits to the "interior source" convention** via
the chapter-init addition, so the proposition is correct (and provable) as stated under
our chosen encoding. No new addition_to_the_LN needed for claim_3_5.

## Plan
1. `formalize_claim_in_tex` — rewrite statement file: spell out quantifiers (∃ a walk `p`
   between `v` and `w` with `IsBifurcationSource p c`), translate `\Anc^{G_{\doit(w)}}(v)`
   to set-theoretic phrasing, surface that source is interior.
2. `verify_tex_statement_only` (structural) → `verify_tex_statement_equivalence` (semantic).
3. `formalize_claim_in_lean` — Lean theorem signature; will need to reference upstream
   `IsBifurcationSource` (def_3_4) and `Anc` / `HardInterventionOn` (def_3_10).
4. `review_design` + `verify_equivalence` (+ `verify_equivalence_strict` recommended since
   this is a non-trivial iff over a multi-piece predicate).
5. `add_design_choice_comments` → handoff via `new_manager` for Manager B (the proof).

## Run log
- t=0 (this turn): first run. Wording check reviewed; analysis above. Dispatching tex formalizer.

## Manager B (proof phase) — handoff state
- Statement phase complete; rewritten canonical statement tex at
  `tex/claim_3_5_statement_BifurcationAlternative.tex` (PASS structural + semantic).
- Lean statement at `Section3_2/BifurcationAlternative.lean`
  (`theorem bifurcationAlternative`, body = `let _ := hc; sorry`) — PASSed
  `review_design` + `verify_equivalence` + `add_design_choice_comments`.
- Proof tex stub at `tex/claim_3_5_proof_BifurcationAlternative.tex` (still TODO).
- **LN proof exists** at `lecture-notes/lecture_notes/graphs.tex:366–371` (4 lines).
  Brief; both directions need expansion:
  - `⇒`: LN just describes the shape of a bifurcation walk. Needs explicit
    extraction of the two directed sub-walks `v ← ... ← c` and `c → ... → w`,
    arguing each lies in the do-intervened graph on the *opposite* end-node.
    Key lift: the directed-edge form `c → v_{k-1}` (i.e. `v_{k-1} ← c`) at the
    hinge means `v` is not the head of the hinge edge; the left arm
    `v ← v_1 ← ... ← v_{k-1} ← c` is a directed walk from `c` to `v`.  Since
    none of the interior vertices is `w` (clause (e) end-node-uniqueness in
    def_3_4), the walk persists in `G_{do({w})}` (do removes only incoming
    edges to `w`; this directed walk has no incoming edge to `w`).
  - `⇐`: LN's concatenation idea. Need to argue (i) `v ≠ w` (given);
    (ii) both directed paths exist by ancestor definition; (iii) why the
    concatenated walk is a bifurcation in the LN sense, including
    end-node-uniqueness — `v` cannot appear on the `c → ... → w` arm (it's
    in the do-on-`{v}` graph, where `v` has no incoming edges, so any
    directed walk reaching a node other than `v` from `c ≠ v` cannot pass
    through `v`). Symmetric argument for `w`.

## Manager B plan
1. `spawn_agent_sub_task` → `write_tex_proof.md`: sync at-the-top statement block
   from the canonical statement file; rewrite the LN's brief proof at
   `graphs.tex:366–371` into a self-contained, formal proof that:
   - explicitly cites the bifurcation form (def_3_4 item vi clauses (a)–(e)),
   - explicitly invokes `Anc` (def_3_5 item iv) and `hardInterventionOn` (def_3_10),
   - in both directions, justifies the end-node-uniqueness via the
     "do removes incoming edges to the intervened node" property
     (def_3_10 items iii.–iv.).
2. `verify_tex_statement_plus_proof` (structural).
3. `verify_tex_proof` (mathematical).
4. `spawn_agent_sub_task` → `prove_claim_in_lean.md`.
5. `solved`.

## Lean prover progress notes (2026-06-09)

### Helpers added in `BifurcationAlternative.lean` (all `-- claim_3_5 --- helper`)

The proof requires substantial walk-level infrastructure not present in
`Walks.lean` / `HardInterventionOn.lean`.  Helpers added:

* `Walk.vertices_eq_cons_tail_self`: every walk's vertices begin with its
  start vertex.
* `Walk.start_mem_self`: start vertex lies in `G`.
* `mem_of_mem_hardInterventionOn`, `mem_hardInterventionOn_of_mem_not_W`:
  carrier transports between `G` and `G_{do(W)}`.
* `Walk.liftWalkStep_of_hardInterventionOn`: walk-step lift.
* `Walk.liftFromHardIntervention` (+ directedness + vertices preserved):
  lifts a walk from `G_{do(W)}` to `G`.  Mirrors the same-named private
  lemma in `AcyclicPreservedUnderDo.lean`.
* `Walk.vertices_directed_avoid_of_hardInterventionOn`: directed walks
  in `G_{do(W)}` avoid `W` along all their vertices.
* `Walk.liftTo_hardInterventionOn` (+ directedness): lifts a walk from
  `G` to `G_{do(W)}` given vertex avoidance.
* `Walk.comp` (+ length + vertices + directedness): walk concatenation
  (mirrors the same-named private def in `AcyclicIffTopologicalOrder.lean`).
* `Walk.truncateAtFirst` (+ length ≤ + isDirectedWalk + length < under
  dropLast): truncates a walk at the first occurrence of a vertex.
* `exists_directed_walk_v_not_in_dropLast`: minimum-length argument
  (uses `Nat.find` on directed-walk lengths).
* `mkBifurcation` (+ length + vertices): constructor that combines a
  directed `qv : Walk G c v` and a directed `qw : Walk G c w` into a
  bifurcation walk `Walk G v w` (tail-recursive prepending of backward
  `E`-edges).
* `isBifurcationDirectedHinge_mkBifurcation_general`: the predicate
  composition lemma for `mkBifurcation` (any prepended backward chain
  shifts the bifurcation index by the chain length).
* `isBifurcationDirectedHinge_cons_backward_of_directed`: bases the
  composition at split index 0.
* `isBifurcationDirectedHinge_mkBifurcation`: the main predicate result
  on `mkBifurcation qv hqv qw` at index `qv.length - 1`.
* `exists_arms_of_bifurcation_directed_hinge`: extracts the source
  vertex + left arm (Walk G c u, directed) + right arm (Walk G c w,
  directed) from `IsBifurcationDirectedHingeWithSplit p i`, with vertex
  membership claims that the arms' vertices are contained in
  `p.vertices.dropLast` / `p.vertices.tail` respectively.

### State / outstanding issues

The Lean infrastructure for both directions is in place, but several
helpers still have compile errors that surfaced after the bulk
restructure (Mathlib lemma-name drift for `List.mem_cons_self`, omega
not seeing the truncate-bound hypothesis through pattern matching,
`show` vs `change` linter complaints in the helper bodies, and the
arm-extraction lemma's vertex-membership case analysis is not closing
under Lean's pattern-match unfolding).  The MAIN theorem proof
(both directions) has been written but currently relies on the helper
section building cleanly, plus a small number of inline `sorry`s for
the final vertex-uniqueness clauses `v ∉ vertices.tail` and
`w ∉ vertices.dropLast` of the bifurcation predicate on
`mkBifurcation qv qw` — these need lemmas

* `(mkBifurcation qv hqv qw).vertices.tail = qv.vertices.tail.reverse.tail
  ++ qw.vertices` (or an equivalent splitting),
* `v ∉ qv.vertices.tail` (from `v ∉ qv.vertices.dropLast` via the
  min-length argument, plus `qv` ends at `v`),
* `w ∉ qw.vertices.dropLast` (similar),
* `v ∉ qw.vertices` (from `qw_int : Walk G_{do(v)} c w` directed +
  `c ≠ v` ⇒ all qw vertices ≠ v, via
  `Walk.vertices_directed_avoid_of_hardInterventionOn` BEFORE the lift),
* `w ∉ qv.vertices` (symmetric).

The infrastructure works conceptually but the proof's bookkeeping of
vertex memberships across `mkBifurcation` + reverse + tail/dropLast is
exacting.

### Lemmas I wish existed in `Walks.lean`

Several of these helpers feel like they should be at the chapter-level
(in `Section3_1/Walks.lean` rather than copies in every consumer):

* `Walk.comp` (concatenation) — currently duplicated in
  `AcyclicIffTopologicalOrder.lean` and this file.
* `Walk.liftFromHardIntervention` + variants — currently duplicated in
  `AcyclicPreservedUnderDo.lean` and this file.
* `Walk.length_pos_of_endpoints_ne` (or equivalent): `c ≠ v` ⇒
  `Walk G c v` has length ≥ 1 — needed in `mkBifurcation`'s use sites
  for the positivity hypotheses.
* `Walk.vertices_directed_avoid_of_hardInterventionOn` (or a more
  general "edges-into avoidance" lemma).

A future refactor of the chapter should hoist these into `Walks.lean`
or a new `WalkLifts.lean` shared by `Section3_2/`.

### Handoff state
This row's `BifurcationAlternative.lean` is *not yet building clean*.
The TeX proof is verified correct; the Lean translation is in
progress but blocked on (a) the trailing vertex-uniqueness clauses,
(b) a handful of helper-level compile errors that need careful Lean
tactic adjustments rather than mathematical insight.

## Lean proof completion plan (drafted 2026-06-09 by plan_subtasks)

### State on entry
The previous monolithic Lean translation pass added ~10 helpers plus
the both-directions main proof in a single `spawn_agent_sub_task`
dispatch.  Compile errors accumulated in the helper layer (Mathlib
name drift on `List.mem_cons_self`, `omega` failing to see the
truncate-bound through pattern matches, `change` vs `show` linter
complaints, arm-extraction case analysis not closing under Lean's
pattern-match unfolding) plus inline `sorry`s for vertex-uniqueness
bookkeeping in the main proof.  The file was reverted to a clean
`let _ := hc; sorry` so `lake build` stays green while we replan.

This plan **decomposes the work into 8 small, build-verifiable
subtasks**, each closing at a clean `lake build` (with a single
tracked `sorry` in the *next* helper or the main theorem, marked
`-- TODO(claim_3_5): closed in subtask N+1`).

All helpers live inside the `namespace CDMG ... end CDMG` block of
`Section3_2/BifurcationAlternative.lean`, under the **three-dash
helper marker** convention `-- claim_3_5 --- start helper` /
`-- claim_3_5 --- end helper` (matching the existing
`variable {Node : Type*} [DecidableEq Node]` marker block at the
top of the file).  Helpers should be `private` where they would
duplicate a name elsewhere in the chapter (`Walk.comp`,
`Walk.liftFromHardIntervention`, etc.) — `private` scoping is fine
for proof-only plumbing per the precedent in
`AcyclicIffTopologicalOrder.lean` and `AcyclicPreservedUnderDo.lean`.

### Subtask sequence

#### 1. HardInterventionOn lift `G_{do(W)} → G` infrastructure
   **Worker dispatch:** `spawn_agent_sub_task` (custom brief).
   **Files touched:**
   - `leanification/Chapter3_GraphTheory/Section3_2/BifurcationAlternative.lean`
   **Helpers/lemmas added:** (all `private`, all under one
     `-- claim_3_5 --- start helper` block)
   - `mem_of_mem_hardInterventionOn :
        v ∈ G.hardInterventionOn W hW → v ∈ G`
   - `Walk.liftWalkStep_of_hardInterventionOn :
        (G.hardInterventionOn W hW).WalkStep u a v →
          G.WalkStep u a v`
   - `Walk.liftFromHardIntervention :
        Walk (G.hardInterventionOn W hW) u v → Walk G u v`
   - `Walk.isDirectedWalk_liftFromHardIntervention :
        p.IsDirectedWalk →
          (Walk.liftFromHardIntervention (hW := hW) p).IsDirectedWalk`
   - `Walk.length_liftFromHardIntervention :
        (Walk.liftFromHardIntervention (hW := hW) p).length = p.length`
   - **New:** `Walk.vertices_liftFromHardIntervention :
        (Walk.liftFromHardIntervention (hW := hW) p).vertices = p.vertices`
     (the lift preserves the underlying `vertices` list because each
      `cons` cell keeps its `vMid` data verbatim — induction over `p`,
      `nil`/`cons` cases both close with `rfl` / `congrArg`).
   **Templates to copy from:**
   - `AcyclicPreservedUnderDo.lean` lines 104–177 — first five
     declarations are literal copies (rename to drop `private` →
     keep `private`; structure unchanged).  Only the new
     `vertices_liftFromHardIntervention` lemma is fresh.
   **Build checkpoint:** `lake build` clean; main theorem still
     `let _ := hc; sorry`.
   **Risk / subtlety:** the `vertices` lemma needs `cons` recursion
     to match the `.cons vMid a h p` shape; the conclusion is
     definitionally `vMid :: p'.vertices = vMid :: p.vertices`, so
     `rfl` should suffice (the `lift` recursion keeps `vMid` and
     `a` unchanged).  No name-drift risk.
   **Rationale:** the (⇐) direction of the proof (Step 2) needs
     these lifts to upgrade the directed walks `q_v`, `q_w` from
     `G_{do(w)}` / `G_{do(v)}` to `G` before the bifurcation walk
     is assembled.

#### 2. Walk concatenation `Walk.comp` infrastructure
   **Worker dispatch:** `spawn_agent_sub_task` (custom brief).
   **Files touched:**
   - `leanification/Chapter3_GraphTheory/Section3_2/BifurcationAlternative.lean`
   **Helpers/lemmas added:** (all `private`, one helper-marker
     block)
   - `Walk.comp : Walk G u v → Walk G v w → Walk G u w`
   - `Walk.length_comp :
        (p.comp q).length = p.length + q.length`
   - `Walk.isDirectedWalk_comp :
        p.IsDirectedWalk → q.IsDirectedWalk → (p.comp q).IsDirectedWalk`
   - **New:** `Walk.vertices_comp :
        (p.comp q).vertices = p.vertices.dropLast ++ q.vertices`
     (proof: `nil` case `p = .nil v _`: `p.comp q = q`,
      `p.vertices.dropLast = [v].dropLast = []`, ✓;
      `cons` case: `(p.cons _ _ _).comp q = .cons _ _ _ (p.comp q)`
      and `(u :: p.vertices).dropLast = u :: p.vertices.dropLast`
      since `p.vertices` is non-empty by structural induction).
   **Templates to copy from:**
   - `Section3_1/AcyclicIffTopologicalOrder.lean` lines 96–116 —
     `Walk.comp`, `Walk.length_comp`, `Walk.isDirectedWalk_comp`
     are literal copies.  Only `Walk.vertices_comp` is fresh.
   **Build checkpoint:** `lake build` clean; main theorem still
     `sorry`.
   **Risk / subtlety:** `Walk.vertices_comp`'s `cons` case needs
     `List.dropLast_cons_of_ne_nil` (Mathlib: yes, this exists
     under that name; verify with `Grep`) and an auxiliary fact
     that `p.vertices ≠ []` (true by induction: `nil` gives `[v]`,
     `cons` gives `u :: …`).  If the linter complains about the
     non-empty side condition, add a tiny `private lemma
     Walk.vertices_ne_nil` first.
   **Rationale:** the (⇐) direction of the proof (Step 4) builds
     the bifurcation walk by reversing the left arm and
     concatenating; `Walk.comp` is the concatenation primitive,
     and `vertices_comp` is the bookkeeping needed by clause~(a)
     end-node-uniqueness verification in Step 5.

#### 3. Vertex-avoidance + lift `G → G_{do(W)}` infrastructure
   **Worker dispatch:** `spawn_agent_sub_task` (custom brief).
   **Files touched:**
   - `leanification/Chapter3_GraphTheory/Section3_2/BifurcationAlternative.lean`
   **Helpers/lemmas added:** (all `private`)
   - `Walk.vertices_directed_avoid_of_hardInterventionOn :
        p.IsDirectedWalk → ∀ x ∈ p.vertices.tail, x ∉ W`
     where `p : Walk (G.hardInterventionOn W hW) u v`.  The
     `.tail` carve-out is load-bearing: the source `u = u_0` is
     unconstrained (it may or may not be in `W`); only the
     **heads** of the edges (positions `1, 2, …, n`) must avoid
     `W`, because `(u, v) ∈ E_{do(W)}` forces `v ∉ W` via the
     `filter`-clause of `def_3_10` item iv.  Proof: induction on
     `p`, `cons` case unfolds `IsDirectedWalk` (the head
     constraint `a = (u, vMid) ∈ E_{do(W)} → vMid ∉ W` follows
     from `Finset.mem_filter`) and recurses.
   - `Walk.liftTo_hardInterventionOn :
        ∀ (p : Walk G u v) (hu : u ∈ G.hardInterventionOn W hW),
          p.IsDirectedWalk →
          (∀ x ∈ p.vertices.tail, x ∉ W) →
          Walk (G.hardInterventionOn W hW) u v`
     (rebuilds the walk cell-by-cell, witnessing each step via
      `Or.inl ⟨rfl, Or.inl _⟩` with `mem_filter` packaging the
      `e.2 ∉ W` clause).
   - `Walk.isDirectedWalk_liftTo_hardInterventionOn`: lift
     preserves `IsDirectedWalk`.
   **Templates to copy from:** no direct sibling; this is fresh
     content but mirrors the structural pattern of
     `Walk.liftFromHardIntervention` in subtask 1 (in reverse).
   **Build checkpoint:** `lake build` clean; main theorem still
     `sorry`.
   **Risk / subtlety:** the `liftTo` signature carries the source
     membership `u ∈ G.hardInterventionOn W hW` as an explicit
     hypothesis (the `Walk.nil` base case needs it).  In the
     `cons` recursion, the recursive call's source membership
     comes from `WalkStep` decomposition: the head of the current
     edge is the source of the recursive walk.  The avoidance
     hypothesis transports because `tail` of `u :: p.vertices` is
     `p.vertices`, so the universal statement directly restricts
     to `p`.
   **Rationale:** the (⇒) direction of the proof needs to take
     the left arm `L : Walk G c v` (from arm-extraction, subtask
     7) and lift it to `Walk (G.hardInterventionOn {w} _) c v`
     after establishing that no vertex of `L` equals `w` (this
     uses the bifurcation walk's clause (a) end-node-uniqueness
     applied to the arm extraction).  Symmetric for the right
     arm.

#### 4. Truncation `Walk.truncateAtFirst` + minimum-length extraction
   **Worker dispatch:** `spawn_agent_sub_task` (custom brief).
   **Files touched:**
   - `leanification/Chapter3_GraphTheory/Section3_2/BifurcationAlternative.lean`
   **Helpers/lemmas added:** (all `private`)
   - `Walk.truncateAtFirst {G : CDMG Node} :
        ∀ {u v : Node} (p : Walk G u v) (t : Node)
          (h : t ∈ p.vertices),
          Σ' (v' : Node), Walk G u v'`
     (returns a walk truncated at the first occurrence of `t`; the
      target `v'` is `t` when `t ≠ u`, else `u` with the
      length-0 walk).  Cleaner alternative: parameterise the
      output by `Walk G u t` and prove it terminates at the first
      `t` — either shape is fine, pick whichever closes more
      neatly under the structural induction.
   - `Walk.length_truncateAtFirst_le :
        (p.truncateAtFirst t h).2.length ≤ p.length`
   - `Walk.isDirectedWalk_truncateAtFirst :
        p.IsDirectedWalk → (p.truncateAtFirst t h).2.IsDirectedWalk`
   - `Walk.length_truncateAtFirst_lt_of_mem_dropLast :
        t ∈ p.vertices.dropLast →
          (p.truncateAtFirst t (… mem promotion …)).2.length < p.length`
     (this is the load-bearing strict inequality for the
      minimality argument: if `t` appears before the last position,
      truncating drops at least one cell).
   - `exists_directed_walk_v_not_in_dropLast {G : CDMG Node}
        {c v : Node} :
        c ∈ G.Anc v → c ≠ v →
        ∃ (p : Walk G c v), p.IsDirectedWalk ∧
          v ∉ p.vertices.dropLast`
     (uses `Nat.find` over the predicate "exists a directed walk
      from `c` to `v` of length `n`" to pick a minimum-length
      representative; if `v` appeared in `dropLast`,
      `truncateAtFirst v` would yield a strictly-shorter directed
      walk from `c` to `v`, contradicting minimality).
   **Templates to copy from:** no direct sibling.  The
     `Nat.find` idiom appears in mathlib's `Nat.find_min` /
     `Nat.find_spec` API; consult `Mathlib.Order.Basic` for the
     standard pattern.
   **Build checkpoint:** `lake build` clean; main theorem still
     `sorry`.
   **Risk / subtlety:** structural recursion termination on
     `truncateAtFirst` may need `decreasing_by` or an explicit
     match on whether the current cell's vertex equals `t`.  An
     alternative formulation: `Walk.takeUntil p t h : Walk G u t`
     by case analysis on the head — this might compose more
     cleanly.  The exact signature shape can be the worker's
     judgment call as long as the resulting four lemmas are
     consumable.
   **Rationale:** Step 1 of (⇐) in the TeX proof picks
     **minimum-length** directed walks `q_v`, `q_w`; their
     minimality is used in Step 3 (3.2) and (3.3) to argue that
     `v` (resp.\ `w`) does not appear in their `vertices.dropLast`.
     This is exactly the conclusion of
     `exists_directed_walk_v_not_in_dropLast`.

#### 5. `mkBifurcation` constructor + length + vertices
   **Worker dispatch:** `spawn_agent_sub_task` (custom brief).
   **Files touched:**
   - `leanification/Chapter3_GraphTheory/Section3_2/BifurcationAlternative.lean`
   **Helpers/lemmas added:** (all `private`)
   - `Walk.mkBifurcation {G : CDMG Node} {c v w : Node} :
        ∀ (qv : Walk G c v) (hqv_dir : qv.IsDirectedWalk)
          (hqv_pos : qv.length ≥ 1) (qw : Walk G c w),
          Walk G v w`
     (recursion on `qv`: each `.cons vMid a h qv'` becomes a
      prepended *backward* edge cell `Walk.cons vMid a' h' …`
      where the new edge `a' = (vMid, prev_vertex)` is the
      reversed orientation of `a = (prev_vertex, vMid) ∈ G.E`,
      and the base case `qv = .cons vMid a h (.nil c hc)` returns
      `Walk.cons vMid a' h' qw` — i.e.\ the right arm `qw`
      becomes the right arm of the bifurcation, prefixed by the
      single backward edge from `vMid = v` to `c`).
   - `Walk.length_mkBifurcation :
        (Walk.mkBifurcation qv hqv_dir hqv_pos qw).length =
          qv.length + qw.length`
   - `Walk.vertices_mkBifurcation :
        (Walk.mkBifurcation qv hqv_dir hqv_pos qw).vertices =
          qv.vertices.reverse.dropLast ++ qw.vertices`
     (this is the load-bearing splitting formula for clause~(a)
      end-node-uniqueness in Step 5; verify it matches the TeX
      proof's vertex enumeration `v_0 = u_r, …, v_r = u_0 = c,
      v_{r+1} = x_1, …`).
   **Templates to copy from:** no direct sibling; the previous
     attempt had a working sketch — re-derive from the TeX proof
     Step 4 vertex / edge formulas.
   **Build checkpoint:** `lake build` clean; main theorem still
     `sorry`.
   **Risk / subtlety:** the recursion direction matters.  Easiest
     is "build by structural recursion on `qv` from the end
     (peeling off the last cell)" rather than "from the front" —
     each peeled cell becomes a prepended backward edge.  But
     "from the end" is awkward in Lean's `cons` representation, so
     a cleaner approach is: define an auxiliary
     `Walk.reverseDirected qv hqv_dir : Walk G v c` (reversing a
     directed walk reverses its edge orientations to land in `G`
     as a directed walk in the opposite direction), then
     `mkBifurcation qv hqv_dir hqv_pos qw :=
       (Walk.reverseDirected qv hqv_dir).comp qw`.  This
     factors the work cleanly and makes both `length` and
     `vertices` follow from `length_comp` /
     `vertices_comp` from subtask 2.  **The worker should pick
     this two-step factoring**.  Then `vertices_reverseDirected`
     becomes a separate small lemma:
     `(Walk.reverseDirected qv hqv_dir).vertices =
        qv.vertices.reverse`.
   **Rationale:** Step 4 of (⇐) constructs the candidate
     bifurcation walk `p` by reversing `q_v` and concatenating
     with `q_w` at the common endpoint `c`.  `mkBifurcation` is
     the Lean rendering of that construction; the vertex /
     length formulas pin down Step 5's clause-by-clause
     verification.

#### 6. `mkBifurcation` realises `IsBifurcationDirectedHingeWithSplit`
   **Worker dispatch:** `spawn_agent_sub_task` (custom brief).
   **Files touched:**
   - `leanification/Chapter3_GraphTheory/Section3_2/BifurcationAlternative.lean`
   **Helpers/lemmas added:** (all `private`)
   - `Walk.isBifurcationDirectedHinge_cons_backward_of_directed
        {G : CDMG Node} {u v w : Node} (a : Node × Node)
        (h : G.WalkStep v a u) (p : Walk G v w)
        (hp_dir : p.IsDirectedWalk) (ha : a = (v, u) ∧ a ∈ G.E)
        (hp_nonempty : p.length ≥ 1) :
        (Walk.cons v a h p).IsBifurcationDirectedHingeWithSplit 0`
     (the base case: a single backward edge `(v, u)` followed by
      a non-trivial directed walk `p` realises the
      directed-hinge predicate at index 0; this corresponds to
      the `cons _ _ _ (p@(.cons _ _ _ _)), 0` branch of
      `Walks.lean:1045-1046`).
   - `Walk.isBifurcationDirectedHinge_mkBifurcation_general
        {G : CDMG Node} {u v w : Node}
        (backward : Walk G u v) (hbw : backward.IsDirectedWalk)
        (a : Node × Node) (rest : Walk G _ w) (hrest_hinge :
        rest.IsBifurcationDirectedHingeWithSplit k) :
        (… composition …).IsBifurcationDirectedHingeWithSplit
          (k + backward.length)`
     (the inductive step: prepending a `backward.length`-many
      backward-edge chain to an existing
      `IsBifurcationDirectedHingeWithSplit k` walk shifts the
      index by `backward.length`; the exact statement depends on
      the chosen reverse / `comp` factoring from subtask 5 —
      adapt to that).
   - `Walk.isBifurcationDirectedHinge_mkBifurcation :
        (Walk.mkBifurcation qv hqv_dir hqv_pos qw)
          .IsBifurcationDirectedHingeWithSplit (qv.length - 1)`
     (combining the previous two by induction on `qv.length`).
   **Build checkpoint:** `lake build` clean; main theorem still
     `sorry`.
   **Risk / subtlety:** the predicate
     `IsBifurcationDirectedHingeWithSplit`'s recursion pattern
     (`Walks.lean:1042–1048`) splits on three cases at index 0
     and one at index `k+1` — the `nil → False` case, the
     `cons _ _ _ (.nil _ _), 0 → False` case (degenerate single
     edge), and the `cons _ _ _ (p@(.cons _ _ _ _)), 0` case.
     The base lemma needs `p.length ≥ 1` to land in the third
     case.  This is exactly `qw.length ≥ 1`, which follows from
     `c ≠ w` in the (⇐) hypothesis.  Make sure the
     `mkBifurcation` signature carries enough hypotheses
     (`hqw_pos : qw.length ≥ 1`).
   **Rationale:** Step 5 of (⇐) needs all five clauses (a)–(e)
     of `def_3_4` item~vi to hold on the constructed walk at
     index `k = qv.length - 1`.  This subtask's main lemma
     `isBifurcationDirectedHinge_mkBifurcation` packages
     clauses (b), (c), (d) (the directed-hinge predicate covers
     these).  Clauses (a) and (e) are left to the main proof
     (subtask 8) since they involve vertex-uniqueness bookkeeping
     using `vertices_mkBifurcation` from subtask 5.

#### 7. Arm-extraction lemma `exists_arms_of_bifurcation_directed_hinge`
   **Worker dispatch:** `spawn_agent_sub_task` (custom brief).
   **Files touched:**
   - `leanification/Chapter3_GraphTheory/Section3_2/BifurcationAlternative.lean`
   **Helpers/lemmas added:** (all `private`)
   - `Walk.exists_arms_of_bifurcation_directed_hinge
        {G : CDMG Node} {v w : Node} (p : Walk G v w)
        {i : ℕ} (h_hinge : p.IsBifurcationDirectedHingeWithSplit i) :
        ∃ (c : Node) (L : Walk G c v) (R : Walk G c w),
          L.IsDirectedWalk ∧ R.IsDirectedWalk ∧
          L.length ≥ 1 ∧ R.length ≥ 1 ∧
          p.vertices[i + 1]? = some c ∧
          (∀ x ∈ L.vertices, x ∈ p.vertices.dropLast.reverse) ∧
          (∀ x ∈ R.vertices, x ∈ p.vertices.drop i)`
     (extract from a bifurcation-with-directed-hinge walk: the
      source vertex `c = v_k`, the left arm `L : Walk G c v` (a
      directed walk consisting of reversed backward edges
      `v_k → v_{k-1} → … → v_0`), and the right arm `R : Walk G
      c w` (directly the forward directed sub-walk
      `v_k → v_{k+1} → … → v_n`).  The two vertex-containment
      clauses are the load-bearing facts used in the (⇒) lift
      step: `L`'s vertices are among
      `{v_0, v_1, …, v_k} = p.vertices` first `k+1` elements,
      which is a subset of `p.vertices.dropLast` (since `k ≤ n-1`
      from the directed-hinge constraint, so `v_k` is interior);
      `R`'s vertices are among
      `{v_k, v_{k+1}, …, v_n}`, a subset of `p.vertices.drop i`
      where `i = k - 1`).
   - Refine the exact vertex-containment statements as the
     worker discovers what the (⇒) lift step actually needs.
     The shape above is approximate; the lifting in subtask 8
     uses these via the bifurcation-walk's clause~(a)
     end-node-uniqueness to argue `w ∉ L.vertices` and
     `v ∉ R.vertices`.
   **Build checkpoint:** `lake build` clean; main theorem still
     `sorry`.
   **Risk / subtlety:** **highest-risk subtask of the plan.**  The
     previous attempt's pattern-match case analysis "did not
     close under Lean's pattern-match unfolding" (workspace note
     line 126).  Plan A: use structural recursion on `p`
     simultaneously with structural recursion on `i`, returning
     the arms by accumulator.  Plan B: prove a parametric
     `forall i, IsBifurcationDirectedHingeWithSplit p i → …`
     by induction on `i` first, then by cases on `p` inside each
     `i` branch.  The two-arm vertex-containment claims should be
     left a bit loose — the exact `dropLast` / `drop` indices can
     be tuned to whatever closes the main proof in subtask 8.
     If the worker finds the unified
     `∃ c L R, …` shape too brittle, **factor into three lemmas**:
     `exists_source_of_bifurcation_directed_hinge`,
     `exists_left_arm_of_…`, `exists_right_arm_of_…`, each
     returning its own existential with vertex-containment.
   **Rationale:** the (⇒) direction of the proof decomposes the
     bifurcation walk `p` at the directed hinge into the left and
     right directed arms, which is exactly this lemma.  The
     vertex-containment clauses transport to "no vertex of `L`
     equals `w`" and "no vertex of `R` equals `v`" via clause~(a)
     end-node-uniqueness, supplying the avoidance hypothesis of
     `Walk.liftTo_hardInterventionOn` (subtask 3).

#### 8. Main theorem `bifurcationAlternative` — both directions
   **Worker dispatch:** `spawn_agent_sub_task` (custom brief).
   **Files touched:**
   - `leanification/Chapter3_GraphTheory/Section3_2/BifurcationAlternative.lean`
     (the body `let _ := hc; sorry` becomes the full proof).
   **Helpers/lemmas added:** none — just the main theorem body.
   **Templates to copy from:** the TeX proof at
     `tex/claim_3_5_proof_BifurcationAlternative.tex`
     (lines 152–424); each `⟹` step has a 1-to-1 mapping to a
     Lean tactic combining helpers from subtasks 1–7.
   **Build checkpoint:** `lake build` clean; **no `sorry`s
     anywhere** in the file (subtask completes the row's proof).
   **Risk / subtlety:** the workspace notes (lines 132–146)
     enumerate the vertex-uniqueness clauses that previously
     required inline `sorry`s.  With `vertices_mkBifurcation`
     (subtask 5), `vertices_directed_avoid_of_hardInterventionOn`
     (subtask 3), and `exists_directed_walk_v_not_in_dropLast`
     (subtask 4) all in place, these should close by direct
     application — no extra inline plumbing should be needed.
     Each direction is ~25 lines of tactic script.  If the
     worker still hits stuck spots, **fall back to splitting into
     8a (⇒ only) and 8b (⇐ only)** — but only if necessary; the
     helpers are designed so a single dispatch should suffice.
     Use `Anc`'s definition `{w | w ∈ G ∧ ∃ p, p.IsDirectedWalk}`
     directly — there is no `Anc_iff_exists_directed_walk` lemma
     (the def unfolds by `Set.mem_setOf_eq`).
   **Rationale:** with all helper infrastructure in place, the
     LN proof translates directly: (⇒) uses subtask 7 +
     subtask 3 + the `Anc` unfolding; (⇐) uses the `Anc`
     unfolding + subtask 1 + subtask 4 + subtask 5 + subtask 6 +
     `vertices_mkBifurcation` for clause~(a)/(e) bookkeeping.

### Cross-cutting notes for the manager dispatching these subtasks

* **Each subtask is `spawn_agent_sub_task` with a custom brief**,
  not `prove_claim_in_lean.md` (which assumes helpers are in
  place).  The brief should quote the TeX proof section the
  subtask supports, point at the template file/lines listed
  above, and pin the exact lemma signatures the next subtask
  will consume.
* **The previous private mirrors are TEMPLATES, not imports.**
  Don't try to `import` `AcyclicIffTopologicalOrder.lean` into
  `BifurcationAlternative.lean` and lift `private` definitions —
  the `private` scoping was deliberate.  Copy the lemma bodies
  into `BifurcationAlternative.lean`'s private helper block.
  A future chapter-level refactor (noted in workspace lines
  148–164) can hoist these into `Walks.lean`.
* **Commit after each subtask.**  Use
  `scaffold/build_and_commit.sh "claim_3_5 subtask N: <one-liner>"`
  to land each clean checkpoint, so a failed subsequent subtask
  can be rolled back without losing the earlier infrastructure.
* **If subtask 7 stalls**, recursively re-dispatch
  `plan_subtasks` on it alone — the arm-extraction lemma is the
  one with the highest pattern-match-bookkeeping risk and may
  warrant its own sub-decomposition into "extract source",
  "extract left arm", "extract right arm" if the unified form
  proves brittle.
* **No new files should be created.**  All work lives inside
  `Section3_2/BifurcationAlternative.lean`.  The chapter
  aggregator `Chapter3_GraphTheory.lean` already imports this
  file (no changes needed there).
* **TeX files are frozen.**  The statement and proof TeX files
  have passed `verify_tex_statement_only`,
  `verify_tex_statement_equivalence`,
  `verify_tex_statement_plus_proof`, and `verify_tex_proof`.
  Subtasks 1–8 do not edit them.
