import Chapter3_GraphTheory.Section3_1.EdgeRelations
import Mathlib.Data.List.Nodup

-- The verbatim TeX source of the LN definition is reproduced inside the
-- comments below; some of its lines exceed 100 characters. Disable the
-- style linter for this file so the TeX is kept byte-for-byte identical
-- to `Section3_1/main.tex`.
set_option linter.style.longLine false

/-!
# def_3_4 — Walks, directed/bidirected/collider walks, paths, bifurcations

The fourth LN definition of subsection 3.1 bundles six concepts under one
`\begin{Def}[Walks]` block. We produce one Lean declaration per LN bullet,
sharing the `Causality.Chapter3` namespace with `def_3_1`–`def_3_3`.

Bullets are encoded as follows:

1. **Walk** — an inductive `Walk` with a single-step datatype `WalkStep`
   indexed on the pair of endpoints (in `J ⊕ V`). `WalkStep` has three
   constructors `out` / `inn` / `bid`, corresponding to the LN's three edge
   flavours (`\tuh`, `\hut`, `\huh`). `Walk` itself is a `cons`-list of
   steps with a `nil` constructor for the trivial walk.
2. **Directed walk** — `Prop`-predicate on `Walk` saying every step is
   `out`.
3. **Bidirected walk** — every step is `bid`.
4. **Collider walk** — first step is `out`/`bid`, last step is `inn`/`bid`,
   middle steps are `bid`; special-cased for length 0 and 1.
5. **Path** — vertex sequence is `Nodup`.
6. **Bifurcation** — a `structure` packaging an apex `v_{k-1} : V`, the
   middle vertex `v_k : J ⊕ V`, the middle `\hus`-edge, two directed arms,
   and side-conditions.

See the design-choice block before each declaration for the trade-offs.
-/

universe u_J u_V

namespace Causality
namespace Chapter3

variable {J : Type u_J} {V : Type u_V}

/-
Source (verbatim from `Section3_1/main.tex`, under `% def_3_4`):

\begin{defmark}
\begin{Def}[Walks]\label{def:walks}
     Let $G=(J,V,E,L)$ be a CDMG and $v,w \in G$.
\begin{enumerate}
    \item A \emph{walk} from $v$ to $w$ in $G$ is a finite alternating sequence of adjacent nodes and edges
      \[v=v_0, a_0,  v_1, \dots v_{n-1}, a_{n-1}, v_n=w\]
%      \[v=v_0 \sus v_1 \sus  \cdots \sus v_{n-1} \sus v_n=w\]
        in $G$ for some $n \ge 0$, i.e.\ such that for every $k=0,\dots,n-1$
        we have that $a_k = (v_k, v_{k+1}) \in E \cup L$ or $a_k = (v_{k+1}, v_k) \in E$, and with end nodes $v_0=v$ and $v_n=w$.
        An example walk from $v_0$ to $v_3$ could look like:
        \[v_0 \tuh v_1 \hut  v_2 \huh v_3, \qquad\text{ with } \qquad  v_0 \tuh v_1, v_2 \tuh v_1 \in E,\,v_2 \huh v_3 \in L. \]
        The same node may appear multiple times in a walk.
        Also the \emph{trivial walk} consisting of a single node $v_0 \in G$ is allowed (if $v=w$).
        The walk is called \emph{into $v_0$} if $a_0 = v_0 \hus v_1$, and \emph{out of $v_0$} if $a_0 = v_0 \tuh v_1$.
        Similarly, it is called \emph{into $v_n$} if $a_{n-1} = v_{n-1} \suh v_n$ and \emph{out of $v_n$} if $a_{n-1} = v_{n-1} \hut v_n$.
    \item A \emph{directed walk} from $v$ to $w$ in $G$ is of the form:
        \[v=v_0 \tuh v_1 \tuh  \cdots \tuh v_{n-1} \tuh v_n=w,\]
        for some $n \ge 0$,
        where all arrowheads point in the direction of $w$ and there are no arrowheads pointing back.
   % \item[] Directed walks exclude the trivial walk per definition.
    \item A \emph{bidirected walk} from $v$ to $w$ in $G$ is of the form:
        \[v=v_0 \huh v_1 \huh  \cdots \huh v_{n-1} \huh v_n=w,\]
        for some $n \ge 0$, where all edges are bidirected.
    \item A \emph{collider walk} from $v$ to $w$ in $G$ is of the form:
        \[v=v_0 \suh v_1 \huh  \cdots \huh v_{n-1} \hus v_n=w,\]
        for some $n \ge 0$, where all nodes in between $v$ and $w$ have two arrowheads pointing towards them (a.k.a.\ collider).
        Note that for $n=1$ this reads: $v\sus w \in G$.
    \item A walk is called \emph{path} if no node occurs more than once.
    \item A \emph{bifurcation} between $v$ and $w$ in $G$ is a walk of the form:
        \[v=v_0 \hut v_1 \hut  \cdots \hut v_{k-1} \hus v_k  \tuh \cdots \tuh v_{n-1} \tuh v_n=w,\]
   %             \[v=v_0 \hut v_1 \hut  \cdots \hut v_{k-1} \huh v_k  \tuh \cdots \tuh v_{n-1} \tuh v_n=w,\]
        such that $v \ne w$, the walk contains both endnodes exactly once,
	the subwalk $v_0 \hut \cdots v_{k-1}$ is a directed walk from $v_{k-1}$ to $v_0$,
	and the subwalk $v_k \tuh \cdots v_n$ is a directed walk from $v_k$ to $v_n$.
        %every node has at most one arrowhead pointing towards it, and
        %both endnodes have exactly one arrowhead pointing towards them.
        If the edge $v_{k-1} \hus v_k$ is directed ($v_{k-1} \hut v_k$) then we say that the bifurcation has \emph{source} $v_{k}$.
  \end{enumerate}
\end{Def}
\end{defmark}
-/

-- def_3_4 (part 1a/6) — single walk step.
--
-- A `WalkStep G u v` is data witnessing one of the three LN edge flavours
-- connecting `u` to `v` in walk-order (`u` first, `v` second):
--
-- * `out` — `\tuh`: forward directed edge, arrowhead on `v` (LN spec
--   `a_k = (v_k, v_{k+1}) ∈ E` with `v_k = u`, `v_{k+1} = v`).
-- * `inn` — `\hut`: reverse directed edge, arrowhead on `u` (LN spec
--   `a_k = (v_{k+1}, v_k) ∈ E` with `v_k = u`, `v_{k+1} = v`).
-- * `bid` — `\huh`: bidirected edge, arrowheads on both endpoints
--   (LN spec `(v_k, v_{k+1}) ∈ L`).
--
-- Typing matches `def_3_2`'s primitives: the *arrowhead-side* of each
-- edge is in `V`, the *tail-side* is allowed to be in `J ⊕ V`. This is
-- what the indices of `WalkStep` encode: `out` lets `u : J ⊕ V` (free) and
-- forces `v = Sum.inr _ : V`; `inn` forces `u = Sum.inr _ : V` and lets
-- `v : J ⊕ V`; `bid` forces both endpoints in `V`.
--
-- Design choice — `Type`, not `Prop`. A walk step carries the underlying
-- edge witness, and downstream definitions (`def_3_5` ancestors /
-- descendants / districts, `claim_3_2` walk surgery, …) need to inspect
-- and split that data. Keeping `WalkStep` in `Type` makes the structural
-- recursion immediate.
inductive WalkStep (G : CDMG J V) : (J ⊕ V) → (J ⊕ V) → Type (max u_J u_V) where
  | out  : ∀ {a : J ⊕ V} {b : V}, G.tuh a b → WalkStep G a (Sum.inr b)
  | inn  : ∀ {a : J ⊕ V} {b : V}, G.hut b a → WalkStep G (Sum.inr b) a
  | bid  : ∀ {a b : V},           G.huh a b → WalkStep G (Sum.inr a) (Sum.inr b)

-- def_3_4 (part 1b/6) — walks as a cons-list of steps.
--
-- LN fragment:
-- /- A *walk* from `v` to `w` in `G` is a finite alternating sequence of
--    adjacent nodes and edges `v=v_0, a_0, v_1, …, v_{n-1}, a_{n-1}, v_n=w`
--    in `G` for some `n ≥ 0` … . Also the *trivial walk* consisting of a
--    single node `v_0 ∈ G` is allowed (if `v=w`). -/
--
-- A `Walk G u w` is exactly the LN's alternating sequence: `nil v` is the
-- trivial walk at `v` (handling the LN's "trivial walk … if `v=w`"
-- clause), and `cons s rest` prepends one step `s : WalkStep G u v` to a
-- walk `rest : Walk G v w`.
--
-- Design choice — `Type`, not `Prop`. `def_3_5` (ancestors/descendants
-- as the set of `w` such that *there exists* a directed walk …) wants
-- the walk as data, not just its existence; phrasing the existence at
-- `def_3_5` time via `∃ p : Walk G v w, G.DirectedWalk p` keeps the data
-- handy when later proofs need walk-surgery.
--
-- Design choice — `cons`-list (not `snoc`-list, not function from
-- `Fin n`). The LN's recursive description ("for every `k=0,…,n-1` …")
-- is naturally captured by a `cons`-list, and structural recursion on
-- `cons`-lists is what every downstream induction wants. The "into/out
-- of `v_0`" / "into/out of `v_n`" classification (LN's last two
-- sentences of bullet 1) is *not* given a new name here — it is a direct
-- application of `def_3_3`'s `IntoFst` / `IntoSnd` / `OutOf` to the step
-- at the relevant endpoint of the walk.
inductive Walk (G : CDMG J V) : (J ⊕ V) → (J ⊕ V) → Type (max u_J u_V) where
  | nil  : ∀ (v : J ⊕ V), Walk G v v
  | cons : ∀ {u v w : J ⊕ V}, WalkStep G u v → Walk G v w → Walk G u w

-- Tag for the *kind* of a `WalkStep`. We use this to phrase the
-- `DirectedWalk` / `BidirectedWalk` / `ColliderWalk` predicates below as
-- list-level constraints on the sequence of step-kinds of a walk —
-- decoupled from the indexed typing of `WalkStep` so that the recursion
-- is purely list-level.
inductive StepKind | out | inn | bid
  deriving DecidableEq, Repr

-- The kind tag of a step.
def WalkStep.kind {G : CDMG J V} {u v : J ⊕ V} (s : WalkStep G u v) : StepKind :=
  match s with
  | .out _ => .out
  | .inn _ => .inn
  | .bid _ => .bid

-- The list of step-kinds of a walk, in walk-order. Length `n` for a walk
-- of `n` steps; `[]` for the trivial walk.
def Walk.stepKinds {G : CDMG J V} : ∀ {u w : J ⊕ V}, Walk G u w → List StepKind
  | _, _, .nil _      => []
  | _, _, .cons s rest => s.kind :: rest.stepKinds

-- The vertex sequence `[v_0, v_1, …, v_n]` of a walk, in walk-order.
-- Length `n + 1` for a walk of `n` steps; `[v]` for the trivial walk
-- at `v`.
def Walk.vertices {G : CDMG J V} : ∀ {u w : J ⊕ V}, Walk G u w → List (J ⊕ V)
  | _, _, .nil v       => [v]
  | u, _, .cons _ rest => u :: rest.vertices

-- def_3_4 (part 2/6) — directed walk.
--
-- LN fragment:
-- /- A *directed walk* from `v` to `w` in `G` is of the form
--    `v=v_0 \tuh v_1 \tuh ⋯ \tuh v_{n-1} \tuh v_n=w` for some `n ≥ 0`,
--    where all arrowheads point in the direction of `w` and there are no
--    arrowheads pointing back. -/
--
-- "Every edge is `\tuh`": every step constructor must be `out`. We phrase
-- this on `Walk.stepKinds` rather than recursively on the walk so that
-- the bidirected/collider variants share the same shape and projection.
-- The trivial walk (`n = 0`, no steps) satisfies the predicate vacuously,
-- consistent with the LN's "for some `n ≥ 0`".
def CDMG.DirectedWalk (G : CDMG J V) {v w : J ⊕ V} (p : Walk G v w) : Prop :=
  ∀ k ∈ p.stepKinds, k = StepKind.out

-- def_3_4 (part 3/6) — bidirected walk.
--
-- LN fragment:
-- /- A *bidirected walk* from `v` to `w` in `G` is of the form
--    `v=v_0 \huh v_1 \huh ⋯ \huh v_{n-1} \huh v_n=w` for some `n ≥ 0`,
--    where all edges are bidirected. -/
--
-- Every step is `\huh`. By the indexing of the `bid` constructor of
-- `WalkStep`, both endpoints of the walk are then forced to live in `V`
-- (`Sum.inr _`); we do not re-state that as a separate side-condition
-- because it falls out of the constructor's typing.
def CDMG.BidirectedWalk (G : CDMG J V) {v w : J ⊕ V} (p : Walk G v w) : Prop :=
  ∀ k ∈ p.stepKinds, k = StepKind.bid

-- Auxiliary: a "right-tail" of a collider walk — a non-empty list of
-- step-kinds that is `bid`-only except for its final entry which is
-- `\hus` (`inn` or `bid`). Used solely to define `colliderKinds` below.
def colliderTailKinds : List StepKind → Prop
  | []       => True   -- vacuous; never reached from `colliderKinds`
  | [k]      => k = StepKind.inn ∨ k = StepKind.bid
  | k :: ks  => k = StepKind.bid ∧ colliderTailKinds ks

-- A list of step-kinds matches the LN's collider walk shape iff:
--   * it is empty (`n = 0`, the trivial walk — vacuous), or
--   * it is a singleton (`n = 1`, which the LN explicitly notes "reads
--     `v \sus w ∈ G`" — i.e. any of `out` / `inn` / `bid` is allowed),
--     or
--   * it has length `≥ 2`, the first step is `\suh` (`out` or `bid`),
--     all middle steps are `bid`, and the last step is `\hus`
--     (`inn` or `bid`).
def colliderKinds : List StepKind → Prop
  | []      => True
  | [_]     => True
  | k :: ks => (k = StepKind.out ∨ k = StepKind.bid) ∧ colliderTailKinds ks

-- def_3_4 (part 4/6) — collider walk.
--
-- LN fragment:
-- /- A *collider walk* from `v` to `w` in `G` is of the form
--    `v=v_0 \suh v_1 \huh ⋯ \huh v_{n-1} \hus v_n=w` for some `n ≥ 0`,
--    where all nodes in between `v` and `w` have two arrowheads pointing
--    towards them (a.k.a. collider). Note that for `n=1` this reads
--    `v \sus w ∈ G`. -/
--
-- Encoded via `colliderKinds` on the walk's step-kind list. The `n = 0`
-- (trivial) case is accepted vacuously; the `n = 1` exception of the LN
-- is handled by the dedicated singleton branch in `colliderKinds`.
--
-- Design choice: the LN's "every interior node is a collider" clause is
-- automatically discharged by the `bid` constructor's typing (it forces
-- the in-between nodes to live in `V` and to receive two arrowheads), so
-- we do not re-state it as a separate per-node side-condition.
def CDMG.ColliderWalk (G : CDMG J V) {v w : J ⊕ V} (p : Walk G v w) : Prop :=
  colliderKinds p.stepKinds

-- def_3_4 (part 5/6) — path.
--
-- LN fragment:
-- /- A walk is called *path* if no node occurs more than once. -/
--
-- The LN's condition is exactly `Nodup` on the vertex sequence. We reuse
-- `List.Nodup` from `Mathlib.Data.List.Nodup` so that downstream code can
-- tap into its lemma ecosystem (`List.Nodup.sublist`, `List.Nodup.append`,
-- …). No DecidableEq on `J ⊕ V` is required — `List.Nodup` is a Prop.
def CDMG.IsPath (G : CDMG J V) {v w : J ⊕ V} (p : Walk G v w) : Prop :=
  p.vertices.Nodup

-- def_3_4 (part 6/6) — bifurcation.
--
-- LN fragment:
-- /- A *bifurcation* between `v` and `w` in `G` is a walk of the form
--    `v=v_0 \hut v_1 \hut ⋯ \hut v_{k-1} \hus v_k \tuh ⋯ \tuh v_{n-1} \tuh v_n=w`,
--    such that `v ≠ w`, the walk contains both endnodes exactly once,
--    the subwalk `v_0 \hut ⋯ v_{k-1}` is a directed walk from `v_{k-1}`
--    to `v_0`, and the subwalk `v_k \tuh ⋯ v_n` is a directed walk from
--    `v_k` to `v_n`. If the edge `v_{k-1} \hus v_k` is directed
--    (`v_{k-1} \hut v_k`) then we say that the bifurcation has *source*
--    `v_k`. -/
--
-- We package a bifurcation as a `structure`:
--
-- * `apex` is the V-node `v_{k-1}` where the two directed arms meet. It
--   lives in `V` because the middle edge `v_{k-1} \hus v_k` has its
--   arrowhead on `v_{k-1}`, and both `\hut`/`\huh` force that endpoint
--   into `V`.
-- * `mid` is the other endpoint of the middle edge, `v_k`, in `J ⊕ V`.
-- * `middle` is the LN's `\hus`-edge between `apex` and `mid`.
-- * `leftArm` is the LN's left subwalk read backwards: a *directed* walk
--   from `apex = v_{k-1}` to `v = v_0`. The LN itself spells this out
--   verbatim: "the subwalk `v_0 \hut ⋯ v_{k-1}` is a directed walk from
--   `v_{k-1}` to `v_0`". Similarly `rightArm` goes from `mid = v_k` to
--   `w = v_n`.
-- * `ne` is the LN's `v ≠ w`.
-- * `v_once` / `w_once` encode "the walk contains both endnodes exactly
--   once": `v` appears only as the first vertex of the combined sequence,
--   `w` only as the last. We do *not* strengthen this to "the combined
--   walk is a path" — the LN explicitly restricts the uniqueness
--   requirement to the two endnodes.
--
-- Design choice — `structure` (not a `Prop` over an explicit `Walk`).
-- Naming `apex` and `mid` as fields lets downstream consumers project
-- them out directly, which is how every later "decompose a bifurcation"
-- proof of the chapter wants to consume the data. The same data could
-- be encoded as `∃ k apex mid, …` over a single combined walk, but the
-- structure form spares every consumer one round of existential
-- elimination.
structure CDMG.Bifurcation (G : CDMG J V) (v w : J ⊕ V) : Type (max u_J u_V) where
  apex              : V
  mid               : J ⊕ V
  middle            : G.hus (Sum.inr apex) mid
  leftArm           : Walk G (Sum.inr apex) v
  leftArm_directed  : G.DirectedWalk leftArm
  rightArm          : Walk G mid w
  rightArm_directed : G.DirectedWalk rightArm
  ne                : v ≠ w
  v_once            : v ∉ (leftArm.vertices.reverse ++ rightArm.vertices).tail
  w_once            : w ∉ (leftArm.vertices.reverse ++ rightArm.vertices).dropLast

-- The combined vertex sequence of a bifurcation, in walk-order
-- `[v=v_0, v_1, …, v_{k-1}=apex, mid=v_k, …, v_n=w]`. Exposed as a
-- helper for downstream consumers so they need not re-derive the
-- concatenation pattern used in `v_once` / `w_once`.
def CDMG.Bifurcation.combinedVertices {G : CDMG J V} {v w : J ⊕ V}
    (b : CDMG.Bifurcation G v w) : List (J ⊕ V) :=
  b.leftArm.vertices.reverse ++ b.rightArm.vertices

-- The LN's "source of the bifurcation" feature.
--
-- LN fragment:
-- /- If the edge `v_{k-1} \hus v_k` is directed (`v_{k-1} \hut v_k`)
--    then we say that the bifurcation has *source* `v_k`. -/
--
-- "The middle edge is the `\hut` disjunct of `\hus`, not the `\huh`
-- disjunct" is precisely `G.hut b.apex b.mid`. The source itself (when
-- it exists) is then `b.mid` (= `v_k`).
def CDMG.Bifurcation.hasSource {G : CDMG J V} {v w : J ⊕ V}
    (b : CDMG.Bifurcation G v w) : Prop :=
  G.hut b.apex b.mid

end Chapter3
end Causality
