import Chapter3_GraphTheory.Section3_1.EdgeRelations

/-!
# Walks in a CDMG (def 3.4, item 1)

This file formalises *item 1* of definition 3.4 of the lecture notes
(Forré & Mooij, `lecture-notes/lecture_notes/graphs.tex`): the umbrella
*walk* concept in a Conditional Directed Mixed Graph (CDMG), together
with the supporting data API (`length`, `support`, `firstStep?`,
`lastStep?`, `append`, `reverse`) needed by every later walk-using row
of the project.

Items 2 -- 6 of LN def 3.4 (directed walks, bidirected walks, collider
walks, paths, bifurcations) sit on top of this data layer and are
formalised in sibling files:

  * `WalkPredicates.lean` -- `IsDirected`, `IsBidirected`,
    `IsCollider`, `IsPath`, plus the "into / out of $v_0$" and
    "into / out of $v_n$" prose predicates of item 1 (LN def 3.4
    items 2 -- 5 plus item 1's "into / out of" sentences).
  * `Bifurcation.lean` -- `IsBifurcation` and `bifurcationSource`
    (LN def 3.4 item 6).

## Top-level shapes

* `WalkStep G v w : Type _` -- a single edge in a walk between two
  adjacent vertices `v` and `w` of `G`, with three constructors
  `forward` / `backward` / `bidir` carrying the underlying adjacency
  proof. Mirrors the LN's three explicit orientation cases verbatim:
  `v \tuh w` (forward), `v \hut w` (backward), `v \huh w` (bidirected).
* `Walk G v w : Type _` -- a walk in `G` from `v` to `w`, built as a
  left-cons list of `WalkStep`s with a trivial `nil v : Walk G v v`
  base case (the LN's "trivial walk consisting of a single node
  $v_0 \in G$").

Walks are *data*, not propositions. Existential phrasings like "there
exists a directed walk from $v$ to $w$" become `∃ π : Walk G v w,
π.IsDirected`; named-walk reasoning ("let $π$ be a walk in $G$ ...")
becomes `(π : Walk G v w)`. This shape is forced by chapter 16
(fci.tex Lemmas 270 -- 334) which concatenates, reverses, and extracts
sub-walks of named walks; none of that is possible if walks are merely
`Prop`-valued.

## Provided API

* `Walk.length : Walk G v w → ℕ` -- the LN's parameter `n` in
  `v = v_0, …, v_n = w`.
* `Walk.support : Walk G v w → List α` -- the visited-vertex sequence
  `v_0, v_1, …, v_n`; satisfies `support.length = length + 1`
  (`Walk.support_length`).
* `Walk.firstStep?` / `Walk.lastStep?` -- `Option`-valued accessors
  for the head and tail steps, packaged as dependent pairs so the
  step's endpoints remain inspectable. Used by `WalkPredicates.lean`
  to phrase the "into / out of $v_0$" and "into / out of $v_n$"
  predicates from item 1 of the LN definition.
* `Walk.append : Walk G u v → Walk G v w → Walk G u w` -- walk
  concatenation, needed by chapters 15 -- 16 for composition of
  sub-walks (`SimpleGraph.Walk.append` is the structural precedent).
* `WalkStep.reverse : WalkStep G v w → WalkStep G w v` -- flips the
  orientation of a step. The `forward ↔ backward` swap is a definitional
  identity (both unfold to `(v, w) ∈ G.E`, see
  `EdgeRelations.edgeOutOf_iff_hut`); the `bidir ↔ bidir` case uses
  `G.L_symm` from def 3.1.
* `Walk.reverse : Walk G v w → Walk G w v` -- the reversed walk.
  Defined by appending the per-step reverses in reverse order.

Mathlib's `SimpleGraph.Walk` (in `Combinatorics.SimpleGraph.Walks.Basic`
and `…Operations`) is the structural precedent for the
`nil` / `cons` / `length` / `support` / `append` / `reverse` pattern;
we deliberately reuse the same names so a reader familiar with
Mathlib's walk API can carry intuition over.
-/

namespace Causality

open scoped Causality.CDMG

variable {α : Type*}

-- def_3_4 (item 1, per-step edge)
-- title: Walks -- per-step edge with explicit orientation
--
-- A single step of a walk between adjacent vertices `v` and `w` is one of:
--   * `forward`: a directed edge `v ⟶[G] w` (LN's `\tuh`),
--   * `backward`: a directed edge `v ⟵[G] w` (LN's `\hut`,
--     equivalent to `(w, v) ∈ G.E`),
--   * `bidir`: a bidirected edge `v ⟷[G] w` (LN's `\huh`).
-- The LN's text "$a_k = (v_k, v_{k+1}) \in E \cup L$ or
-- $a_k = (v_{k+1}, v_k) \in E$" enumerates exactly these three cases.
-- Each constructor carries the adjacency proof inline so that the
-- existence of a walk certifies the existence of its edges.
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` (def 3.4, item 1
-- the per-step requirement):

  ... for every $k=0,\dots,n-1$ we have that
  $a_k = (v_k, v_{k+1}) \in E \cup L$ or
  $a_k = (v_{k+1}, v_k) \in E$ ...
-/
--
-- ## Design choice
--
-- * **Three constructors, not a single constructor with an
--   `Orientation` enum.** The LN explicitly enumerates three cases
--   (`v_k \tuh v_{k+1}` directed, `v_k \hut v_{k+1}` reverse-directed,
--   `v_k \huh v_{k+1}` bidirected); a single-constructor "step +
--   orientation enum" encoding would force a `match` on the enum at
--   every use site -- which is exactly the case-split the LN prose
--   itself does. Mirroring the LN here lets every downstream pattern
--   match read like the LN's own case analysis. It also means
--   `WalkStep.reverse` (below) can pattern-match on the three cases
--   directly, with two cases collapsing to `rfl`.
--
-- * **Each constructor carries the adjacency proof.** Just like
--   Mathlib's `SimpleGraph.Walk` constructor `cons (h : G.Adj u v) p`,
--   embedding the proof of `v ⟶[G] w` (or its variants) into the
--   `WalkStep` itself means *the existence of a walk certifies the
--   existence of its edges*. Existential phrasings later
--   (e.g. `∃ π : Walk G u v, ...`) cannot be vacuously satisfied by
--   inventing walks whose edges are not actually in `G`.
--
-- * **Notation in the constructor signatures.** The constructor types
--   read `v ⟶[G] w` (and friends) instead of raw `(v, w) ∈ G.E`. This
--   keeps the inductive's definition aligned with the LN's atoms and
--   means callers can pattern-match against `forward (h : v ⟶[G] w)`
--   directly.
/-- A single edge in a walk in the CDMG `G`, between two adjacent
vertices `v` and `w`, with explicit orientation. The three constructors
mirror the three cases in `lecture-notes/lecture_notes/graphs.tex`
def 3.4 item 1: `forward` for `v ⟶[G] w` (`\tuh`), `backward` for
`v ⟵[G] w` (`\hut`, equivalent to `(w, v) ∈ G.E`), and `bidir` for
`v ⟷[G] w` (`\huh`). Each constructor carries the underlying
adjacency proof inline. -/
inductive WalkStep (G : CDMG α) : α → α → Type _ where
  /-- A directed forward step `v → w`, witnessing `(v, w) ∈ G.E`.
  Mirrors LN's `\tuh`. -/
  | forward {v w : α} (h : v ⟶[G] w) : WalkStep G v w
  /-- A directed backward step `v ← w`, witnessing `(w, v) ∈ G.E`.
  Mirrors LN's `\hut`. -/
  | backward {v w : α} (h : v ⟵[G] w) : WalkStep G v w
  /-- A bidirected step `v ↔ w`, witnessing `(v, w) ∈ G.L`. Mirrors
  LN's `\huh`. -/
  | bidir {v w : α} (h : v ⟷[G] w) : WalkStep G v w

-- def_3_4 (item 1, walks themselves)
-- title: Walks -- the umbrella walk inductive
--
-- A walk in `G` is built by extending a trivial walk `nil v` (the LN's
-- "trivial walk consisting of a single node $v_0 \in G$") with
-- successive `WalkStep`s via the left-cons constructor. The endpoints
-- of the resulting walk are the start vertex of the first step (or the
-- `nil` vertex) and the end vertex of the walk.
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` (def 3.4, item 1
-- the walk itself):

  A \emph{walk} from $v$ to $w$ in $G$ is a finite alternating sequence
  of adjacent nodes and edges
    $v=v_0, a_0,  v_1, \dots v_{n-1}, a_{n-1}, v_n=w$
  in $G$ for some $n \ge 0$, ...
  The same node may appear multiple times in a walk.
  Also the \emph{trivial walk} consisting of a single node
  $v_0 \in G$ is allowed (if $v=w$).
-/
--
-- ## Design choice
--
-- * **`Type _`, not `Prop`.** See the module docstring -- walks are
--   *data* because chapter 16 (fci.tex) concatenates, reverses, and
--   inducts on named walks. A `Prop`-valued definition would support
--   only existential reasoning and rule out all of that. We do
--   support existential reasoning too (downstream rows use
--   `∃ π : Walk G v w, ...`), but it requires walk-as-data
--   underneath.
--
-- * **Left-cons (Mathlib `SimpleGraph.Walk` style), not right-cons or
--   list-of-steps.** Left-cons makes "the first step of a walk" a
--   trivial pattern-match away (the head step is just `cons s _`),
--   which is exactly what the LN's "into / out of $v_0$" prose
--   predicates read off. A right-cons (or `concat`) shape would
--   invert that and make `firstStep` recursive. A flat
--   `List (WalkStep G _ _)` would require an external endpoint-
--   matching invariant; the indexed inductive shape bakes it in.
--
-- * **`nil` takes `v` as an *explicit* argument; no membership
--   proof.** The LN's "trivial walk consisting of a single node
--   $v_0 \in G$" suggests `v ∈ G` should be a side condition of the
--   trivial walk. We deliberately drop it from the constructor: most
--   existential phrasings downstream (e.g. `Anc^G(v) := {w ∈ G |
--   ∃ π : Walk G w v, π.IsDirected}` in def 3.5) already constrain
--   the endpoints via set-comprehension membership, so requiring it
--   in the constructor would force a redundant proof obligation at
--   every `nil` construction site with no compensating gain. Walks
--   of length ≥ 1 automatically force their endpoints into
--   `G.J ∪ G.V` via `CDMG.E_subset` and `CDMG.L_subset`. Making `v`
--   explicit (rather than implicit) means `Walk.nil v` reads clearly
--   at construction sites, paralleling Mathlib's `Walk.nil' (u : V)`
--   pattern abbreviation.
--
-- * **Endpoints in the constructor's type indices, not in fields.**
--   Indexing the inductive by the endpoint pair `(v, w)` is what
--   lets the `cons` constructor's typing rule
--   `cons : WalkStep G v w → Walk G w u → Walk G v u`
--   enforce vertex-matching at compile time -- the second-to-last
--   vertex of the head step must coincide with the start of the
--   tail walk. This is the same trick `SimpleGraph.Walk` uses.
/-- A walk in the CDMG `G` from `v` to `w`. Inductively built from a
trivial walk `nil v : Walk G v v` (the LN's trivial single-vertex walk)
by left-consing `WalkStep`s onto a tail walk. See
`lecture-notes/lecture_notes/graphs.tex` def 3.4 item 1. The same
node may appear multiple times in the support; see `Walk.support` for
the visited-vertex list. -/
inductive Walk (G : CDMG α) : α → α → Type _ where
  /-- The trivial walk on a single vertex `v` (LN's "trivial walk
  consisting of a single node $v_0 \in G$"). -/
  | nil (v : α) : Walk G v v
  /-- Extend a walk by left-consing a leading edge step. -/
  | cons {v w u : α} (s : WalkStep G v w) (p : Walk G w u) : Walk G v u

namespace WalkStep

variable {G : CDMG α}

-- def_3_4 (item 1, supporting API on `WalkStep`)
-- title: Walks -- reverse a single step
--
-- Flips the orientation of a step:
--   * `forward h` (with `h : v ⟶[G] w`) becomes `backward h`
--     (where `h : w ⟵[G] v`); these are *definitionally* the same
--     proof because both unfold to `(v, w) ∈ G.E` -- see
--     `EdgeRelations.edgeOutOf_iff_hut`.
--   * `backward h` likewise becomes `forward h` definitionally.
--   * `bidir h` (with `h : v ⟷[G] w`) becomes `bidir (G.L_symm h)`
--     (where `G.L_symm h : w ⟷[G] v`); the symmetry of bidirected
--     edges is one of the structural fields of `def_3_1.CDMG`
--     (`L_symm`).
-- This function is the only delicate piece of the walk data layer:
-- everything else is structural, but this one needs `G.L_symm` to
-- exist as a *field* on `CDMG`, which is exactly what def_3_1 set up.
--
-- ## Design choice
--
-- * **Output type is the literal index swap.** We produce
--   `WalkStep G w v` from `WalkStep G v w` rather than something
--   modulo equality of vertex pairs. This is what `Walk.reverse`
--   downstream needs in order to build a walk of the swapped endpoint
--   type by structural recursion -- the indices must literally swap.
--
-- * **Two of three cases are `rfl`.** Both `forward h ↦ backward h`
--   and `backward h ↦ forward h` are `rfl` because the underlying
--   `Prop`s are definitionally equal up to argument swap: `tuh G v w`
--   and `hut G w v` both unfold to `(v, w) ∈ G.E`. Only `bidir`
--   actually needs `G.L_symm`. The three `@[simp]` characterisation
--   lemmas below make this transparent.
/-- The orientation-reversed version of a `WalkStep`. Swaps `forward
↔ backward` (a definitional identity on the underlying `G.E`
membership) and conjugates `bidir` by `G.L_symm` from def 3.1. Used by
`Walk.reverse`. -/
def reverse : {v w : α} → WalkStep G v w → WalkStep G w v
  | _, _, .forward h  => .backward h
  | _, _, .backward h => .forward h
  | _, _, .bidir h    => .bidir (G.L_symm h)

/-- Reversing a `forward` step gives a `backward` step on the same
underlying `G.E` membership. Holds by `rfl` since `tuh G v w` and
`hut G w v` are definitionally equal (both `(v, w) ∈ G.E`). -/
@[simp] theorem reverse_forward {v w : α} (h : v ⟶[G] w) :
    (WalkStep.forward h).reverse = WalkStep.backward h := rfl

/-- Reversing a `backward` step gives a `forward` step on the same
underlying `G.E` membership. Holds by `rfl` for the same reason as
`reverse_forward`. -/
@[simp] theorem reverse_backward {v w : α} (h : v ⟵[G] w) :
    (WalkStep.backward h).reverse = WalkStep.forward h := rfl

/-- Reversing a `bidir` step keeps it `bidir`, but conjugates the
adjacency proof via `G.L_symm` (the symmetry field of `CDMG`,
def 3.1). -/
@[simp] theorem reverse_bidir {v w : α} (h : v ⟷[G] w) :
    (WalkStep.bidir h).reverse = WalkStep.bidir (G.L_symm h) := rfl

end WalkStep

namespace Walk

variable {G : CDMG α}

-- def_3_4 (item 1, length)
-- title: Walks -- number of steps in a walk
--
-- The LN parameterises walks by `n ≥ 0` -- the trivial walk has
-- `n = 0`, a one-step walk has `n = 1`, etc. We expose this `n` as
-- `Walk.length`, defined by structural recursion: `(nil _).length = 0`
-- and `(cons _ p).length = p.length + 1`. Used in def_3_6 (acyclicity:
-- "non-trivial directed walk" means `length ≥ 1`) and pervasively in
-- chapters 15 -- 16 (induction on walk length).
/-- The *length* of a walk: the number of edges (`WalkStep`s) it
contains. This is the LN's parameter `n` in `v = v_0, …, v_n = w`. -/
def length : {v w : α} → Walk G v w → ℕ
  | _, _, .nil _    => 0
  | _, _, .cons _ p => p.length + 1

/-- The trivial walk has length `0`. -/
@[simp] theorem length_nil (v : α) : (nil v : Walk G v v).length = 0 := rfl

/-- A `cons`-extended walk has length one more than the tail walk. -/
@[simp] theorem length_cons {v w u : α} (s : WalkStep G v w) (p : Walk G w u) :
    (cons s p).length = p.length + 1 := rfl

-- def_3_4 (item 1, support)
-- title: Walks -- visited-vertex list
--
-- The list `v_0, v_1, …, v_n` of vertices visited by a walk, in
-- order. Definitionally: `(nil v).support = [v]` and
-- `(cons (s : WalkStep G v w) p).support = v :: p.support`. This is
-- the standard "support" of a walk, lifted from Mathlib's
-- `SimpleGraph.Walk.support`. Used by `Walk.IsPath` (no repeats) in
-- `WalkPredicates.lean` and by σ-blocking definitions
-- (def_3_15/16/17) which scan the support for collider positions.
/-- The list of vertices visited by a walk, in order
(`v_0, v_1, …, v_n` in the LN's notation). It has length
`p.length + 1`; see `Walk.support_length`. -/
def support : {v w : α} → Walk G v w → List α
  | _, _, .nil v    => [v]
  | v, _, .cons _ p => v :: p.support

/-- The support of the trivial walk on `v` is the single-element list
`[v]`. -/
@[simp] theorem support_nil (v : α) : (nil v : Walk G v v).support = [v] := rfl

/-- The support of a `cons`-extended walk is the start vertex followed
by the support of the tail walk. -/
@[simp] theorem support_cons {v w u : α} (s : WalkStep G v w) (p : Walk G w u) :
    (cons s p).support = v :: p.support := rfl

/-- The support list of a walk has length `p.length + 1`: there is
one more vertex than there are edges. Step 2 of the def_3_4 plan
(`WalkPredicates.lean`) uses this to phrase the `IsPath` predicate
via `List.Nodup`. -/
theorem support_length {v w : α} (p : Walk G v w) :
    p.support.length = p.length + 1 := by
  induction p with
  | nil _      => rfl
  | cons _ _ ih => simp [ih]

-- def_3_4 (item 1, first step accessor)
-- title: Walks -- head step (optional)
--
-- Returns the head `WalkStep` of a walk if it has one, packaged as a
-- dependent pair so that the step's endpoints remain inspectable.
-- The trivial walk has no first step; a `cons s _` walk has first
-- step `s`. Used by `WalkPredicates.lean` to phrase the
-- "into $v_0$" / "out of $v_0$" predicates of item 1 of the LN
-- definition, which depend on the constructor of the first step.
--
-- ## Design choice
--
-- * **Dependent-pair packaging `Σ' (v' w' : α), WalkStep G v' w'`.**
--   The step's endpoints are not fixed by the walk's endpoint pair
--   (the walk goes from `v` to `w`, but the *first step* goes from
--   `v` to some intermediate `w'`). Packaging the step with both of
--   its endpoints lets callers inspect them without re-pattern-
--   matching on the walk. `Σ'` is `PSigma`, which works for both
--   `Prop`- and `Type`-valued payloads -- here we need it because
--   `WalkStep` is `Type _`-valued.
--
-- * **`Option`-valued, not a partial function.** The trivial walk
--   genuinely has no first step; encoding this with `Option` keeps
--   the accessor total and avoids the bookkeeping of a proof-carrying
--   `head` (which would force every caller to discharge a "walk is
--   non-trivial" obligation just to inspect the head).
--
-- * **Alternative considered.** Step-2 predicates may also choose to
--   pattern-match directly on the walk's constructor rather than
--   route through `firstStep?`. Both APIs are exposed: `firstStep?`
--   for callers who want a value back; direct pattern matching for
--   callers who want a `Prop`-level test. We do not pre-emptively add
--   `IsForwardFirst`/etc. predicates -- those are step 2's job.
/-- The first `WalkStep` of a walk, if any: `none` on the trivial
walk, `some ⟨v, w, s⟩` on `cons s _` where `s : WalkStep G v w`.
Packaged as a dependent pair so the step's endpoints remain
inspectable. -/
def firstStep? : {v w : α} → Walk G v w → Option (Σ' (v' w' : α), WalkStep G v' w')
  | _, _, .nil _    => none
  | _, _, .cons s _ => some ⟨_, _, s⟩

/-- The trivial walk has no first step. -/
@[simp] theorem firstStep?_nil (v : α) :
    (nil v : Walk G v v).firstStep? = none := rfl

/-- The first step of `cons s p` is `s`. -/
@[simp] theorem firstStep?_cons {v w u : α} (s : WalkStep G v w) (p : Walk G w u) :
    (cons s p).firstStep? = some ⟨v, w, s⟩ := rfl

-- def_3_4 (item 1, last step accessor)
-- title: Walks -- tail step (optional)
--
-- Returns the last `WalkStep` of a walk if it has one. Trivial walk
-- → `none`; `cons s (nil _)` → `some ⟨_, _, s⟩` (the only step is the
-- last); `cons _ p@(cons _ _)` → `p.lastStep?` (the step before the
-- tail's last). Used by `WalkPredicates.lean` to phrase the
-- "into $v_n$" / "out of $v_n$" predicates of item 1.
--
-- ## Design choice
--
-- * **Three-pattern definition for clean `rfl` simp lemmas.** A
--   simpler definition would be `match p.lastStep? with ...` on the
--   tail walk, but then the simp lemma for `cons _ (cons _ _)` would
--   require non-trivial case analysis on `p.lastStep?` (which is
--   always `some _` for a non-trivial tail, but Lean cannot see that
--   without an auxiliary lemma). Pattern-matching the tail's
--   constructor directly makes both simp lemmas
--   (`lastStep?_cons_nil` and `lastStep?_cons_cons`) reduce by `rfl`.
--   Termination is structural: the recursive call's argument
--   `cons s' p'` is the second component of the outer `cons _ (cons
--   s' p')`, hence a strict subterm.
/-- The last `WalkStep` of a walk, if any. Trivial walk → `none`;
single-step walk → `some` of that step; longer walk → recurse into
the tail. -/
def lastStep? : {v w : α} → Walk G v w → Option (Σ' (v' w' : α), WalkStep G v' w')
  | _, _, .nil _              => none
  | _, _, .cons s (.nil _)    => some ⟨_, _, s⟩
  | _, _, .cons _ (.cons s p) => lastStep? (.cons s p)

/-- The trivial walk has no last step. -/
@[simp] theorem lastStep?_nil (v : α) :
    (nil v : Walk G v v).lastStep? = none := rfl

/-- A single-step walk `cons s (nil w)` has last step `s`. -/
@[simp] theorem lastStep?_cons_nil {v w : α} (s : WalkStep G v w) :
    (cons s (nil w) : Walk G v w).lastStep? = some ⟨v, w, s⟩ := rfl

/-- A walk with at least two steps recurses into its tail to find the
last step. -/
@[simp] theorem lastStep?_cons_cons {v w x u : α}
    (s : WalkStep G v w) (s' : WalkStep G w x) (p : Walk G x u) :
    (cons s (cons s' p)).lastStep? = (cons s' p).lastStep? := rfl

-- def_3_4 (item 1, append)
-- title: Walks -- concatenation of two walks
--
-- The concatenation `p.append q` of two compatible walks (the end of
-- `p` must coincide with the start of `q`). Defined by structural
-- recursion on `p`. Not strictly needed for def 3.4 itself, but
-- chapters 15 -- 16 use it heavily (Lemmas 270 -- 334 of fci.tex
-- compose sub-walks pervasively); including it now keeps `Walks.lean`
-- closed under the operations that downstream rows need, so we don't
-- have to reopen it later. Mirrors Mathlib's
-- `SimpleGraph.Walk.append`.
/-- The concatenation of two walks, sharing a common endpoint.
Mathlib's `SimpleGraph.Walk.append` is the structural precedent. -/
def append : {u v w : α} → Walk G u v → Walk G v w → Walk G u w
  | _, _, _, .nil _,    q => q
  | _, _, _, .cons s p, q => .cons s (p.append q)

/-- Appending onto the trivial walk leaves the second walk
unchanged. -/
@[simp] theorem nil_append {v w : α} (q : Walk G v w) :
    (nil v : Walk G v v).append q = q := rfl

/-- Append distributes over `cons` on the left: prepending a step and
then appending equals appending and then prepending the step. -/
@[simp] theorem cons_append {u v w x : α}
    (s : WalkStep G u v) (p : Walk G v w) (q : Walk G w x) :
    (cons s p).append q = cons s (p.append q) := rfl

/-- The length of a concatenated walk is the sum of the lengths.
Chapters 15 -- 16 use this when bounding sub-walks of bifurcations and
σ-blocked walks. -/
theorem length_append {u v w : α} (p : Walk G u v) (q : Walk G v w) :
    (p.append q).length = p.length + q.length := by
  induction p with
  | nil _ => simp
  | cons _ _ ih =>
    simp only [cons_append, length_cons, ih]
    omega

-- def_3_4 (item 1, reverse)
-- title: Walks -- the reversed walk
--
-- Reverse a walk by recursing on its structure: the trivial walk is
-- its own reverse, and `(cons s p).reverse = p.reverse.append (cons
-- s.reverse (nil _))` (Mathlib's `SimpleGraph.Walk.reverse_cons`
-- shape). Like `append`, this is included here because chapters
-- 15 -- 16 reverse walks routinely (Lemma 273 of fci.tex argues by
-- "reversing" a walk; bifurcation arguments compose a left arm with
-- the reverse of a right arm; etc.).
--
-- ## Design choice
--
-- * **Append-of-singletons, not `reverseAux` accumulator.** Mathlib
--   uses an accumulator-based `reverseAux` for an `O(n)` rather than
--   `O(n²)` walk reversal. For the leanification project we prefer
--   the simpler append-of-singletons style: the recursion is one
--   step shorter to reason about, every simp lemma falls out by
--   `rfl`, and we never actually evaluate `reverse` at runtime (it
--   appears only in proof-level reasoning). If performance ever
--   matters, the accumulator version can be added later as an
--   equivalent definition.
--
-- * **Cons-case body uses `WalkStep.reverse` and `Walk.append`.**
--   `(cons s p).reverse = p.reverse.append (cons s.reverse (nil v))`
--   reads as "reverse the tail, then append the reversed step to it".
--   The `nil v` at the end pins the result's endpoint to the original
--   walk's start vertex `v`.
/-- The walk in reverse. Defined by `(nil v).reverse = nil v` and
`(cons s p).reverse = p.reverse.append (cons s.reverse (nil v))`. -/
def reverse : {v w : α} → Walk G v w → Walk G w v
  | _, _, .nil v    => .nil v
  | v, _, .cons s p => p.reverse.append (.cons s.reverse (.nil v))

/-- Reversing the trivial walk leaves it unchanged. -/
@[simp] theorem reverse_nil (v : α) :
    (nil v : Walk G v v).reverse = nil v := rfl

/-- Reversing a `cons`-extended walk: reverse the tail, then append
the reversed step (followed by a trivial walk on the original start
vertex). -/
@[simp] theorem reverse_cons {v w u : α} (s : WalkStep G v w) (p : Walk G w u) :
    (cons s p).reverse = p.reverse.append (cons s.reverse (nil v)) := rfl

/-- Reversing preserves length: the reversed walk has the same number
of steps. Used downstream whenever a walk-length bound has to be
preserved through reversal. -/
theorem length_reverse {v w : α} (p : Walk G v w) :
    p.reverse.length = p.length := by
  induction p with
  | nil _      => rfl
  | cons _ _ ih => simp [length_append, ih]

end Walk

end Causality
