# Workspace for def_3_4 — Walks

## What this row is

A **foundational, 6-part definition** that the rest of chapters 3–16 quietly
depend on. Five subordinate concepts (`directed walk`, `bidirected walk`,
`collider walk`, `path`, `bifurcation`) are introduced as variants/predicates
of the umbrella concept "walk":

| LN concept       | Shape                                              | Downstream first use      |
|------------------|----------------------------------------------------|---------------------------|
| walk             | `v=v_0 a_0 v_1 ... a_{n-1} v_n=w`, any `a_k`       | def_3_15/16/17 (σ-blocking) carry a named walk π |
| directed walk    | every `a_k = v_k \tuh v_{k+1}`                     | def_3_5 (ancestors/desc.) |
| bidirected walk  | every `a_k = v_k \huh v_{k+1}`                     | def_3_5 (district)        |
| collider walk    | `v_0 \suh v_1 \huh ... \huh v_{n-1} \hus v_n`      | commented in def_3_5 (Markov blanket) — used in later chapters |
| path             | walk with no repeated nodes                        | def_3_18 (σ-separation), fci.tex Ch 16 (heavy) |
| bifurcation      | `v_0 \hut ... \hut v_{k-1} \hus v_k \tuh ... \tuh v_n`  | def_3_14 (marginalisation), claim_3_5 (source), Ch 15-16 |
| into/out of v_0/v_n | predicates determined by first/last step      | def_3_15 (colliders), Ch 16 |

**Two distinct usage patterns** across the LN:

1. **Existential** — `\exists \text{ directed walk: } w \tuh \cdots \tuh v`.
   Most uses in chapter 3 (def_3_5 family relationships, def_3_6 acyclicity)
   are of this form: walks appear only inside `∃`.
2. **As named data** — "Let `π` be a walk in `G`" with subsequent reasoning
   about π's colliders, sub-walks, concatenations. This appears starting in
   **def_3_15/16/17** (σ-blocking definitions still in chapter 3, lines
   1218+, 1264+), continues through **claim_3_16/3_18** (marginalisation
   proofs on `graphs.tex` lines 977–1108), then becomes pervasive in
   **chapter 15** (minimal_sep_sets, Prop 29 composes sub-walks) and
   **chapter 16** (fci.tex, ~130 walk references with concatenation,
   sub-walk extraction, walk-vs-path equivalences).

The "named data" usage is decisive: walks must be **data** (a `Type`-valued
inductive), not merely an existential proposition. The kinds (directed /
bidirected / collider / path / bifurcation) sit on top as predicates.

## Key design decisions

### 1. Walk is data; kinds are predicates

A `Walk G v w : Type` inductive carrying the alternating vertex/edge
sequence. Existential phrasings ("there exists a directed walk from `v` to
`w`") become `∃ π : Walk G v w, π.IsDirected`. Named-walk reasoning ("let π
be a walk in `G`") becomes `(π : Walk G v w)`. **Rationale**: fci.tex
(chapter 16) explicitly concatenates, extracts sub-walks, and inducts on
walk structure (Lemmas 270–334, ~130 walk references) — none of that is
possible if walks are only `Prop`. Mathlib's `SimpleGraph.Walk` is precedent
for the data-walk shape.

### 2. Per-step edge: an inductive `WalkStep` with three constructors

The LN says a step is either `(v_k, v_{k+1}) ∈ E` (forward directed), or
`(v_k, v_{k+1}) ∈ L` (bidirected), or `(v_{k+1}, v_k) ∈ E` (backward
directed). Three constructors, each carrying the adjacency proof:

```
inductive WalkStep (G : CDMG α) : α → α → Type _
  | forward  {v w : α} (h : v ⟶[G] w) : WalkStep G v w   -- tuh
  | backward {v w : α} (h : v ⟵[G] w) : WalkStep G v w   -- hut
  | bidir    {v w : α} (h : v ⟷[G] w) : WalkStep G v w   -- huh
```

**Rationale**: matches LN's three explicit orientation cases; pattern
matches cleanly; carries the adjacency proof inline so that the existence
of a walk implies its edges are real (mirrors `SimpleGraph.Adj`-valued
walks). Rejected the alternative ("single constructor + `Orientation`
enum") because it forces a layer of indirection at every pattern match.

### 3. `Walk` inductive: left-cons (Mathlib style)

```
inductive Walk (G : CDMG α) : α → α → Type _
  | nil  (v : α)                                                : Walk G v v
  | cons {v w u : α} (s : WalkStep G v w) (p : Walk G w u)      : Walk G v u
```

**Rationale**: left-cons matches Mathlib's `SimpleGraph.Walk` and makes "the
first step / first edge" trivially accessible via pattern match. "Into / out
of `v_0`" reads off the first step's constructor (`backward`/`bidir` vs.
`forward`). The trivial walk `nil v` covers the LN's "trivial walk
consisting of a single node `v_0 ∈ G`".

**Sub-decision: `nil` does NOT require `v ∈ G` membership.** Adding `(h : v
∈ G.J ∪ G.V)` to `nil` would force a proof obligation at every nil
construction site. The LN's "v ∈ G" precondition is best handled at the
call site (e.g. inside the `Anc^G(v) := { w ∈ G | ... }` set comprehension,
membership is part of the comprehension, not the walk). Every walk of
length ≥ 1 automatically constrains its endpoints to `J ∪ V` via the edge
inclusions `E ⊆ (J ∪ V) × V` and `L ⊆ V × V`.

### 4. Directed / bidirected / collider walks: predicates, not separate types

```
def Walk.IsDirected   : Walk G v w → Prop  -- every step is `forward`
def Walk.IsBidirected : Walk G v w → Prop  -- every step is `bidir`
def Walk.IsCollider   : Walk G v w → Prop  -- first step `suh`, last `hus`, middle all `bidir`
```

**Rationale**: the LN uses the same word "walk" for all four (directed,
bidirected, collider, generic), with the kind as a modifier. The predicate
shape mirrors this — callers think of a directed walk as "a walk that is
directed". Mathlib's `IsTrail` / `IsPath` use exactly this shape.

Rejected separate `DirectedWalk G v w`, `BidirectedWalk G v w` inductive
types because (a) they would duplicate the inductive structure of `Walk`
three times, and (b) downstream lemmas like "concatenation of two directed
walks is a directed walk" would have to be re-proved on each separate
inductive. Predicates compose naturally.

Trivial walks: `nil.IsDirected = nil.IsBidirected = True` (LN explicitly
allows `n = 0` for directed walks; bidirected walks parallel that).
`nil.IsCollider = True` vacuously (no internal nodes to check). The
formalizer should confirm and document.

### 5. Path predicate via `Walk.support`

```
def Walk.support : Walk G v w → List α   -- vertex sequence v_0, v_1, ..., v_n
def Walk.IsPath  (π : Walk G v w) : Prop := π.support.Nodup
```

**Rationale**: directly mirrors Mathlib's `Walk.support` / `Walk.IsPath`.
`support` is defined recursively: `(nil v).support = [v]`, `(cons s p).support
= v :: p.support` (where `v` is the start vertex of `s`). `Nodup` from
`List` gives the no-repeats condition exactly.

### 6. Bifurcation as a predicate, with a separate `source` definition

The trickiest case. I recommend:

```
def Walk.IsBifurcation (π : Walk G v w) : Prop :=
  v ≠ w ∧
  π.support.count v = 1 ∧
  π.support.count w = 1 ∧
  ∃ k, 1 ≤ k ∧ k ≤ π.length ∧
    π.takeStep k    -- left subwalk v_0 ... v_{k-1}
       satisfies: all steps `backward` (i.e. `hut`),
       equivalent to: read backwards, it is a directed walk from v_{k-1} to v_0
    ∧ (π.stepAt (k-1)).hingeIsHusEdge   -- the v_{k-1} \hus v_k edge
    ∧ π.dropStep k                       -- right subwalk v_k ... v_n
       satisfies: all steps `forward` (i.e. `tuh`),
       equivalent to: directed walk from v_k to v_n
```

**Concretely**, the predicate is "the walk has the shape `(hut)^{k-1} (hus) (tuh)^{n-k}` for some valid `k`, and the endpoints v, w each appear exactly once".

Edge cases:
- $k = 1$: left subwalk is just `nil v_0`, hinge edge is `v_0 \hus v_1`, right subwalk has length `n-1` of all-`forward` steps. The LN's left-subwalk "is a directed walk from v_{k-1} to v_0" — with k=1 this is the trivial directed walk from $v_0$ to itself. Valid.
- $k = n$: right subwalk is just `nil v_n`, hinge edge is `v_{n-1} \hus v_n`. Valid.
- $n = 0$ (trivial walk): no hinge possible, so a trivial walk is never a bifurcation. Combined with the `v ≠ w` clause this is automatic.

The **source** sub-definition (when the hinge is specifically `hut`, not
`huh`):

```
def Walk.bifurcationSource (π : Walk G v w) (hb : π.IsBifurcation) : Option α
```

returns `some v_k` if the hinge edge `(stepAt (k-1))` is a `backward`
constructor, else `none`. (The witness `k` is `Classical.choose` from the
existential in `IsBifurcation`; uniqueness of `k` is *not* claimed by the
LN — though in practice the proof of claim_3_5 picks a specific `k`. The
formalizer should document this.)

**Rationale for predicate over `Bifurcation` structure**: matches LN's "a
bifurcation is a walk of the form ..." — the bifurcation IS a walk, with
extra structure on top. Claim_3_5 reads "there exists a bifurcation between
v and w with source c" — naturally `∃ π : Walk G v w, π.IsBifurcation ∧
π.bifurcationSource = some c`.

### 7. "Into / out of v_0 / v_n" — read off `firstStep` / `lastStep`

```
def Walk.IntoStart  (π : Walk G v w) : Prop  -- π = cons s _ with s : backward _ ∨ bidir _
def Walk.OutOfStart (π : Walk G v w) : Prop  -- π = cons s _ with s : forward _
def Walk.IntoEnd    (π : Walk G v w) : Prop  -- last step has arrowhead at w
def Walk.OutOfEnd   (π : Walk G v w) : Prop  -- last step is backward
```

Trivial walk (`nil`) has neither a first nor a last step, so all four
predicates return `False` on `nil`. Document this — the LN only uses these
predicates on non-trivial walks.

**Reuse def_3_3**: phrase the predicates via `CDMG.EdgeInto G v₀ v₁`
(matches `backward ∨ bidir` per def_3_3 item 2) and `CDMG.EdgeOutOf G v₀
v₁` (matches `forward` per def_3_3 item 3). This keeps the def_3_3 prose
names load-bearing instead of duplicating their content.

### 8. File layout: 3 files, split at natural boundaries

| File                           | Contents                                                            | Est. size |
|--------------------------------|---------------------------------------------------------------------|-----------|
| `Walks.lean`                   | `WalkStep`, `Walk`, `support`, `length`, `firstStep`, `lastStep`, plus `append`/`reverse` API (will be needed by chapter 15-16) | ~450 lines |
| `WalkPredicates.lean`          | `IsDirected`, `IsBidirected`, `IsCollider`, `IsPath`, `IntoStart`, `OutOfStart`, `IntoEnd`, `OutOfEnd`     | ~300 lines |
| `Bifurcation.lean`             | `IsBifurcation`, `bifurcationSource`                                | ~200 lines |

A single ~1000-line `Walks.lean` would violate the project's 700-line
guideline (claude.md rule 5). Splitting at the kind-predicates / bifurcation
boundary is natural: `Bifurcation.lean` will accumulate its own machinery
(left/right subwalk extraction, source lemmas) over chapters 3.2 and 15.

Note: `append` and `reverse` are not strictly required for def_3_4 itself,
but chapter-16 walks heavily on them (fci.tex Lemmas 270–334 use both
explicitly). Including them now means we don't have to reopen `Walks.lean`
when those rows are reached. The formalizer may decide to defer them if
they want a tighter PR scope.

### 9. Notation: minimal, no new walk arrows

The LN displays walks as `v_0 \tuh v_1 \hut v_2 \huh v_3` — purely
def_3_2 arrow notation between consecutive vertices. We do **not** add new
notation for walks themselves. Walks are constructed via named
constructors (`Walk.nil v`, `Walk.cons step walk`) and pattern-matched the
same way. Adding a `::ʷ` for `cons` is possible but doesn't help
readability enough to justify the complexity at this stage. **Recommend:
no walk notation.**

## Plan

1. **Formalize `WalkStep` + `Walk` + basic API in `Walks.lean`.**
   - worker: `formalize_definition_in_lean`
   - inputs:
     - `def_3_4_Walks.tex` (item 1 only — the walk umbrella concept)
     - prerequisite imports: `CDMGNotation` for `tuh`/`hut`/`huh` notations,
       `EdgeRelations` for `EdgeInto`/`EdgeOutOf`
   - contents to deliver:
     - `inductive WalkStep (G : CDMG α) : α → α → Type _` with three
       constructors (`forward`, `backward`, `bidir`)
     - `inductive Walk (G : CDMG α) : α → α → Type _` with `nil` and `cons`
     - `def Walk.length : Walk G v w → ℕ`
     - `def Walk.support : Walk G v w → List α` (vertex sequence)
     - `def Walk.firstStep? : Walk G v w → Option (Σ' v' w', WalkStep G v' w')`
       (or its equivalent — used by Into/OutOf predicates)
     - `def Walk.lastStep? : Walk G v w → Option (Σ' v' w', WalkStep G v' w')`
     - `def Walk.append : Walk G u v → Walk G v w → Walk G u w` (recommended,
       since chapter 15-16 needs it; formalizer may defer)
     - `def Walk.reverse : Walk G v w → Walk G w v` (likewise; needs the
       per-orientation flip of `WalkStep`)
     - design comments explaining all of the above
   - rationale: foundational data layer that every other walk concept
     depends on. No predicates yet — they live in the next file.
   - difficulty: medium. The `WalkStep.reverse` flip (forward ↔ backward,
     bidir ↔ bidir) is the only delicate piece, and that uses `G.L_symm`
     from def_3_1.

2. **Formalize walk-kind predicates in `WalkPredicates.lean`.**
   - worker: `formalize_definition_in_lean`
   - inputs:
     - `def_3_4_Walks.tex` (items 2, 3, 4, 5 — directed, bidirected,
       collider, path)
     - imports: `Walks.lean` from step 1, `EdgeRelations.lean` from def_3_3
   - contents to deliver:
     - `def Walk.IsDirected   : Walk G v w → Prop`
     - `def Walk.IsBidirected : Walk G v w → Prop`
     - `def Walk.IsCollider   : Walk G v w → Prop`
     - `def Walk.IsPath       : Walk G v w → Prop`
     - `def Walk.IntoStart    : Walk G v w → Prop`
     - `def Walk.OutOfStart   : Walk G v w → Prop`
     - `def Walk.IntoEnd      : Walk G v w → Prop`
     - `def Walk.OutOfEnd     : Walk G v w → Prop`
     - basic `simp` characterisation lemmas (e.g.
       `IsDirected_nil : (nil v).IsDirected ↔ True`,
       `IsDirected_cons : (cons s p).IsDirected ↔ ∃ h, s = .forward h ∧ p.IsDirected`)
   - rationale: separating the kind predicates keeps `Walks.lean` focused on
     the data structure. Predicates here are short (each ~3-line recursive
     definitions or single `support.Nodup` for `IsPath`).
   - difficulty: low-medium. `IsCollider` is the only one with non-trivial
     case analysis (endpoint vs. middle).

3. **Formalize `IsBifurcation` and `bifurcationSource` in `Bifurcation.lean`.**
   - worker: `formalize_definition_in_lean`
   - inputs:
     - `def_3_4_Walks.tex` (item 6 — bifurcation)
     - imports: `Walks.lean`, `WalkPredicates.lean`
   - contents to deliver:
     - helper: a way to extract the left subwalk and right subwalk at a
       chosen position `k` (probably `Walk.takeSteps : (k : ℕ) → Walk G v w →
       Option (∃ v', Walk G v v' × Walk G v' w)` or two functions
       `takeFirst k` / `dropFirst k`)
     - `def Walk.IsBifurcation : Walk G v w → Prop`
     - `def Walk.bifurcationSource : (π : Walk G v w) → π.IsBifurcation → Option α`
     - design comments justifying the chosen encoding of the existential `k`
   - rationale: bifurcation is structurally complex (decomposition at a
     hinge), and the `source` is conditional on the hinge type — best kept
     isolated from the simpler kinds.
   - difficulty: medium-high. The subwalk extraction is the part most
     likely to require iteration. Suggest the formalizer write a brief
     LaTeX sketch in this file's comments before the Lean code.

4. **`review_design`** — full-chapter context check.
   - Confirm: does `Walk.IsDirected` compose cleanly into `def_3_5`'s
     `Anc^G(v) := { w | ∃ π : Walk G w v, π.IsDirected }`? Does
     `Walk.IsBidirected` slot into `Dist^G(v)` similarly? Does
     `Walk.IsBifurcation` fit `def_3_14`'s marginalisation rule and
     `claim_3_5`'s ancestor-characterisation?
   - Confirm: σ-blocking definitions (def_3_15/16/17) want to read off
     collider positions on a walk and check ancestral relations — does
     `Walk.support` give the vertex list those need?
   - Confirm: walk-vs-path equivalences (claim_3_23 — `prp:sigma_opens`
     equivalence) need `IsPath`. Is the chosen encoding amenable to the
     standard "shortest-walk-is-a-path" argument?

5. **`verify_equivalence`** — focused LN-block-vs-Lean correspondence
   check, item by item (walk umbrella, directed, bidirected, collider,
   path, bifurcation, source).

6. **`solved` → `verify_row_solved`** — finalise.

## Notes for downstream rows

- **def_3_5 (Family Relationships)** will define ancestors as
  `{ w ∈ G | ∃ π : Walk G w v, π.IsDirected }`. Similarly children, district
  (uses `IsBidirected`), and the (commented-out) Markov blanket (uses
  `IsCollider`). The existential-over-Walk pattern is the convention.

- **def_3_6 (Acyclicity)** uses "non-trivial directed walk from v to v".
  In Lean: `∃ π : Walk G v v, π.length ≥ 1 ∧ π.IsDirected`. So
  `Walk.length` is a load-bearing function — make sure it exists and has
  good simp lemmas.

- **def_3_15 (Colliders / non-colliders)** takes a walk π and queries each
  position `k`. The choice to expose `Walk.support` (vertex list) and a
  way to inspect consecutive `WalkStep`s at position `k` matters here.
  Expect to add a `Walk.stepAt : Walk G v w → ℕ → Option ...` helper later.

- **def_3_17 (σ-blocked walks)** combines collider/non-collider position
  analysis with the existence of an ancestral directed walk. So the
  `IsDirected` predicate + `Anc^G` from def_3_5 must compose well.

- **claim_3_5 (`prp:bifurcations_alternative`)** is the first user of
  `bifurcationSource` — it states existence of a bifurcation with source c
  is equivalent to two ancestral conditions. Once def_3_4 lands, this row
  should be one of the first to exercise the API.

- **Chapter 15 (minimal_sep_sets) and chapter 16 (fci)** will use walk
  concatenation, subwalk extraction, walk reversal, and the
  walk-vs-path-equivalence (claim_3_23). Investing in a good `append` /
  `reverse` / `takeSteps` API now will pay back many chapters later. Worth
  including in `Walks.lean` immediately (step 1 above).

- **Convention this row sets**: **walks are data; kinds are predicates;
  existential phrasings use `∃ π : Walk G ..., π.IsXxx`; named-walk
  reasoning uses `(π : Walk G v w)` directly.** All downstream rows should
  follow this pattern.

## Risks / open questions

1. **Should `nil` carry a `v ∈ G` membership proof?** My recommendation:
   **no**, push the membership constraint to the call site (set
   comprehensions / hypotheses). Alternative: require it, accepting the
   bookkeeping cost. Manager should confirm before step 1.

2. **Should `IsCollider` on `nil` be `True` (vacuous) or `False`?** The LN
   is silent on `n = 0` collider walks. `True` seems more defensible
   (vacuously all internal nodes are colliders), but it may surprise
   readers. The formalizer should pick and document.

3. **Should `append` / `reverse` be in step 1 or deferred?** They're not
   strictly needed for def_3_4 *itself*, but chapters 15-16 will need
   them. Include them now (recommended) for one-pass design, or defer to a
   later "extend Walks.lean" task. Manager call.

4. **Bifurcation hinge: how to encode the existential `k` cleanly?** Two
   options for `IsBifurcation`: (a) define a `Walk.takeSteps k` helper
   and state the condition on the resulting left/right subwalks; (b)
   define inductively. Option (a) is more direct; (b) may be cleaner for
   later induction-on-bifurcation proofs (chapter 16 has these). The
   formalizer in step 3 should pick after sketching both.

5. **Uniqueness of the hinge `k`?** The LN does not claim the bifurcation
   shape determines a unique `k`. In edge cases (e.g. a walk that is *both*
   a left-arm-only and a right-arm-only directed walk against itself —
   shouldn't happen given the `v ≠ w` clause and "endpoints exactly
   once") the value of `bifurcationSource` could be ambiguous. The
   formalizer should sanity-check this before settling on the encoding.

6. **Walk equality / decidability.** Two walks with the same vertex/edge
   sequence but constructed via different `WalkStep` proofs (different
   `(v, w) ∈ G.E` witnesses) — are they equal? In Lean's `Prop`-irrelevant
   setting this should be automatic since adjacency is `Prop`-valued, but
   the formalizer should confirm via `Subsingleton` or by checking that
   `WalkStep` equality reduces to vertex equality + orientation.
