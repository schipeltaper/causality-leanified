import Chapter3_GraphTheory.Section3_1.Walks

namespace Causality

/-!
# Walks on a CDMG: item 6 of `def_3_4` (Bifurcation)

This file formalises the final concept of `def_3_4` — a *bifurcation*
between two vertices `v, w` of a CDMG `G`.  Items 1–5 (the `Walk`
inductive, `EdgeStep`, `support`, `length`, the into/out
classifications, `IsPath`, `IsDirectedWalk`, `IsBidirectedWalk`,
`IsColliderWalk`) live in the sibling file `Walks.lean`, which is
imported here.

A bifurcation packages *two* directed sub-walks emanating from a common
neighbourhood (the LN's nodes `v_{k-1}` and `v_k`, connected by a hinge
edge `v_{k-1} \hus v_k`) and pointing outward to the two endnodes
`v_0 = v` and `v_n = w`.  The shape is the LN's canonical
"common-cause / common-confounder" walk; downstream it is the central
data object of `claim_3_5` (`prp:bifurcations_alternative`) and of the
confounding theory in chapter 11 (`causal_relations.tex`,
`def:graph_unconfounded`).

## LN block (verbatim, item 6 of `\label{def:walks}`)

```
A \emph{bifurcation} between $v$ and $w$ in $G$ is a walk of the form:
    $v = v_0 \hut v_1 \hut \cdots \hut v_{k-1} \hus v_k
        \tuh \cdots \tuh v_{n-1} \tuh v_n = w$,
such that $v \ne w$, the walk contains both endnodes exactly once,
the subwalk $v_0 \hut \cdots v_{k-1}$ is a directed walk from $v_{k-1}$
to $v_0$, and the subwalk $v_k \tuh \cdots v_n$ is a directed walk
from $v_k$ to $v_n$.
If the edge $v_{k-1} \hus v_k$ is directed ($v_{k-1} \hut v_k$) then
we say that the bifurcation has \emph{source} $v_k$.
```

## LN addition that fires here (authoritative — treat as part of the LN)

`[bifurcation_right_chain_trivial_is_just_directed_walk]`: **both
endnodes $v_0$ and $v_n$ must have exactly one arrowhead pointing
towards them.**  This explicitly excludes the degenerate case `k = n`
with directed hinge `v_{n-1} \hut v_n`, in which the walk reduces to
a directed walk `v_0 ← v_1 ← … ← v_n` and `v_n` has no arrowhead
pointing towards it.  The corresponding `k = 1` + trivial-left-arm
case is automatically excluded by the LN form (see the design block
on `Bifurcation.hArrowW` for why the asymmetry vanishes once you
trace through the encoding).

## Wording-check subtleties relevant to item 6

* `bifurcation_admits_single_edge_at_n1_k1` (working-phase register) —
  a literal reading admits a single directed edge `v_1 → v_0` as a
  "bifurcation".  The addition restricts to "exactly one arrowhead at
  each endpoint", so the directed-hinge single-edge case is excluded,
  but the **bidirected-hinge single edge `v_0 \huh v_1` survives** as
  a valid (trivially fork-shaped) bifurcation.  The design block on
  `Bifurcation.hArrowW` walks through this boundary explicitly.

* `bifurcation_k_equals_n_is_just_directed_walk` (working-phase
  register) — a literal `k = n` + directed hinge reduces the
  "bifurcation" to a pure directed walk from `w` to `v` with no fork.
  Resolved by the addition; encoded by `hArrowW` rejecting the
  trivial-right-arm + `.hut`-hinge combination.

## Core encoding choices (load-bearing across the whole file)

* `Bifurcation` is a **`structure`**, not a `Prop`-side predicate
  (`∃ walk : Walk G v w, _ ∧ _ ∧ …`).  Two reasons.
  1. Downstream consumers manipulate bifurcations as **data**.
     `claim_3_5` (`prp:bifurcations_alternative`) extracts the
     `source : Option Node`; chapter 11+ confounding theory
     (`causal_relations.tex`) splits at the hinge, recomposes after
     graph marginalisation (`claim_3_16` /
     `rem:marg_preserves_ancestors_bifurcations_acyclicity`), and
     walks each arm independently.  A predicate would force every
     such consumer to existentially destructure inside the proof —
     `b.source`, `b.leftArm`, `b.hinge` as direct field access is
     orders of magnitude cleaner.
  2. The LN's prose enumerates *named pieces* — left subwalk, right
     subwalk, hinge edge, endpoint conditions, source — and a
     structure puts each on its own field, surface-matching the LN
     reading.

* The hinge edge is encoded by a **`Type`-valued ADT** `HingeKind`
  with constructors `.directed` (carrying a `G.hut` proof) and
  `.bidir` (carrying a `G.huh` proof), *not* the `Prop`-valued
  disjunction `G.hus apexL apexR := G.hut ∨ G.huh`.  This mirrors
  the `EdgeStep` pattern in `Walks.lean` and is forced by the same
  reason: `Bifurcation.source` needs to case-split on *which kind*
  of hinge was chosen, and a `Prop`-irrelevant `Or` cannot be
  pattern-matched at the `Type` level (no `Or.elim` into
  `Option Node` without classical choice).  The design block above
  `HingeKind` below walks through the verified bug a naive
  `Prop`-disjunction encoding produces in the coexistence regime
  admitted by `def_3_1`'s addition
  `[edge_set_disjointness_under_specified]`.
-/

variable {Node : Type*} [DecidableEq Node]

-- ref: def_3_4 (item 6 — supporting helper)
--
-- A `HingeKind G u v` records the *kind* of hinge edge between two
-- vertices `u` and `v`: either a directed edge `u \hut v` (i.e.
-- `(v, u) ∈ G.E`) carried by `.directed`, or a bidirected edge
-- `u \huh v` (i.e. `(u, v) ∈ G.L`) carried by `.bidir`.  This is
-- the LN macro `\hus` ("head-star") unfolded into its two cases,
-- but lifted from a `Prop`-valued `Or` to a `Type`-valued
-- inductive so that downstream pattern matching on the constructor
-- is sound.
/-
LN tex (item 6 of `\label{def:walks}`, hinge edge):

  $v_{k-1} \hus v_k$    (the LN's central "tip" edge of a
                         bifurcation; either directed `v_{k-1} \hut
                         v_k` — i.e. $v_k \to v_{k-1} \in E$ — or
                         bidirected $v_{k-1} \huh v_k \in L$).
-/
-- ## Design choice
--
-- *Why a `Type`-valued ADT instead of the `Prop`-valued disjunction
--   `G.hus apexL apexR := G.hut apexL apexR ∨ G.huh apexL apexR`.*
--   This is the load-bearing call for the entire file.  The earlier
--   draft of `Bifurcation` had `hinge : G.hus apexL apexR` (an
--   `Or`-typed `Prop`) and `Bifurcation.source` discriminated via
--   `if (apexR, apexL) ∈ G.E then some apexR else none`.  A
--   strict-equivalence solved-gate produced a verified
--   counter-example showing the `Prop`-disjunction shape is wrong:
--
--     `def_3_1`'s operator addition
--     `[edge_set_disjointness_under_specified]` explicitly admits
--     the *coexistence regime*: a directed edge `apexR \to apexL`
--     in `G.E` AND a bidirected edge `apexL \huh apexR` in `G.L`
--     can both inhabit `G` for the same vertex pair.  In that
--     regime, a `Bifurcation` constructed with the bidirected
--     hinge (`hinge := Or.inr h_huh`) still has the directed edge
--     hanging around in `G.E`.  The naive `source` definition
--     `if (apexR, apexL) ∈ G.E then some apexR else none` returns
--     `some apexR` (because `(apexR, apexL) ∈ G.E` is true,
--     regardless of which disjunct of `hinge` was supplied).  But
--     the LN explicitly conditions `source` on the hinge *being*
--     directed — not on some unrelated directed edge happening to
--     exist between the same vertex pair.  So the LN says `source
--     = none`; the naive code says `source = some apexR`.
--     Disagreement, gate fails.
--
--   Promoting `hinge` to `HingeKind G apexL apexR` records *which
--   constructor was used*, so `Bifurcation.source` can pattern-match
--   on `b.hinge` and produce `some apexR` / `none` exactly in
--   accordance with the chosen hinge.  Proof-irrelevance of `Or`
--   would otherwise erase the constructor choice — `Or.inl h1` and
--   `Or.inr h2` of the same propositional type collapse to a single
--   inhabitant up to proof irrelevance, so case-matching to a
--   `Type`-valued result is unsound for `Prop` disjunctions.
--
-- *Why this mirrors `EdgeStep` from `Walks.lean`.*  `EdgeStep`
--   carries three cases (`.forward / .backward / .bidir`) for
--   exactly the same reason: a walk's individual edge `a_k` needs
--   to be inspected by downstream code (specialised-walk
--   predicates, into/out classifications), and that inspection has
--   to be `Type`-level, not `Prop`-level.  `HingeKind` is the
--   2-case analogue: the hinge edge's kind needs to be inspected
--   by `Bifurcation.source` and by the `hArrowW` arrowhead
--   constraint.  Both files use the same idiom; both rely on the
--   ADT carrying the underlying `G.tuh / G.hut / G.huh` proof as
--   constructor data.
--
-- *Naming.*  `directed` (rather than `hut`) because the LN reads
--   the directed case explicitly as "the edge is directed", and
--   `.directed h` consumers grep cleanly for the conceptual case
--   rather than the LN macro mnemonic; `bidir` matches the
--   `EdgeStep.bidir` constructor name from `Walks.lean` and the
--   LN's "bidirected" terminology.  An alternative naming
--   `HingeKind.hut / .huh` was rejected: those macro names are
--   visually identical at the call site and easy to misread, while
--   `directed / bidir` carry the LN's meaning on their face.
--
-- *Constraint on consumers.*  A downstream proof that has only
--   the `Prop` `h : G.hus apexL apexR` (= `G.hut ∨ G.huh`) and
--   wants to *construct* a `Bifurcation` must case-split on `h`
--   to choose which `HingeKind` constructor to feed.  This is a
--   minor friction at the use site, but it is the explicit price
--   of soundness in the coexistence regime — and the same friction
--   applies to anything else that wants to discriminate between
--   the two edge types as data.
-- def_3_4 --- start helper
inductive HingeKind (G : CDMG Node) (u v : Node) : Type where
  | directed (h : G.hut u v) : HingeKind G u v
  | bidir    (h : G.huh u v) : HingeKind G u v
-- def_3_4 --- end helper

-- ref: def_3_4 (item 6 — supporting helper)
--
-- `HingeKind.isBidir hk` is `True` exactly when the hinge was
-- constructed with `.bidir`, i.e. the underlying edge is
-- `G.huh u v`.  This is the only piece of information about the
-- hinge that the bifurcation's `hArrowW` field needs.
/-
LN tex (no direct LN counterpart — this is a Lean-internal projection
of the `HingeKind` ADT; the LN's symbolic form `\hus` /
`\hut` / `\huh` carries the same case distinction).
-/
-- ## Design choice
--
-- *Why a `Prop`-valued projection rather than a `Bool`-valued
--   discriminator.*  `hArrowW` (below in `Bifurcation`) is a `Prop`
--   conjunctively / disjunctively combined with `rightArm.length >
--   0`, so the natural form is `Prop`-valued and lets `hArrowW` be
--   stated as a clean disjunction without `Bool`-to-`Prop`
--   coercions.  A `Bool` version would be `match hk with | .bidir
--   _ => true | _ => false` and force `hArrowW` to be
--   `rightArm.length > 0 ∨ hinge.isBidir = true` (extra `= true`
--   noise) or to introduce a `Bool → Prop` coercion.
--
-- *Why a separate `def` rather than inlining the pattern match into
--   `hArrowW`.*  Inlining would force the structure declaration to
--   contain a `match` expression in the field's type, which is
--   syntactically heavier and obscures the conceptual reading
--   ("right arm non-trivial OR hinge is bidirected").  A named
--   helper makes the reading self-documenting.
--
-- *Naming.*  `isBidir` (camelCase) matches the LN's "is bidirected"
--   reading and parallels the `is*` predicate naming on `Walk`
--   (`IsDirectedWalk` etc.) from `Walks.lean`.
-- def_3_4 --- start helper
def HingeKind.isBidir {G : CDMG Node} {u v : Node} : HingeKind G u v → Prop
  | .directed _ => False
  | .bidir _    => True
-- def_3_4 --- end helper

-- ref: def_3_4 (item 6 — main concept)
--
-- A `Bifurcation G v w` is the LN's "bifurcation between `v` and `w`
-- in `G`": two directed sub-walks (`leftArm`, `rightArm`) pointing
-- *outward* from a hinge edge `apexL \hus apexR`, with `leftArm`
-- ending at the left endpoint `v` and `rightArm` ending at the right
-- endpoint `w`.  The structure carries the LN's distinctness
-- (`hVneW`), single-occurrence (`hVOnce`, `hWOnce`), and
-- arrowhead-at-endpoint (`hArrowW`) constraints as separate fields.
/-
LN tex (item 6 of `\label{def:walks}`):

  A \emph{bifurcation} between $v$ and $w$ in $G$ is a walk of the
  form:
    $v = v_0 \hut v_1 \hut \cdots \hut v_{k-1} \hus v_k
        \tuh \cdots \tuh v_{n-1} \tuh v_n = w$,
  such that $v \ne w$, the walk contains both endnodes exactly once,
  the subwalk $v_0 \hut \cdots v_{k-1}$ is a directed walk from
  $v_{k-1}$ to $v_0$, and the subwalk $v_k \tuh \cdots v_n$ is a
  directed walk from $v_k$ to $v_n$.

LN addition `[bifurcation_right_chain_trivial_is_just_directed_walk]`
(treated as part of the LN):

  Both endnodes $v_0$ and $v_n$ must have exactly one arrowhead
  pointing towards them.  In particular, this excludes the
  degenerate case $k = n$ with directed hinge $v_{n-1} \hut v_n$, in
  which the walk reduces to a directed walk
  $v_0 \leftarrow v_1 \leftarrow \cdots \leftarrow v_n$ and $v_n$ has
  no arrowhead pointing towards it.
-/
-- ## Design choice
--
-- *Why a `structure` and not a `Prop` predicate on `Walk`.*  The
--   load-bearing reason is **data flow**.  `claim_3_5`
--   (`prp:bifurcations_alternative`) reads "there exists a
--   bifurcation between $v$ and $w$ in $G$ with source $c$ iff …",
--   where the source is a *specific node* extracted from the
--   bifurcation; chapter 11+ confounding (`causal_relations.tex`,
--   `def:graph_unconfounded`) phrases unconfoundedness as "there
--   exists no bifurcation … without source or with source $c \in V$"
--   — both phrasings destructure the bifurcation to pick out the
--   source and the two arms.  A `Prop`-side `∃ walk, P walk` would
--   force every such consumer to peer into the existential to recover
--   the apex / arms / hinge.  A structure makes them first-class
--   fields, `b.apexR`, `b.leftArm`, `b.hinge` — exactly the LN's
--   reading direction.  A second consideration: `claim_3_16`
--   (`rem:marg_preserves_ancestors_bifurcations_acyclicity`) and the
--   bidirected-edge construction in `def_3_14` marginalisation
--   *manipulate* bifurcations (insert directed-path expansions into
--   the arms, replace bidirected hinges with bifurcation expansions);
--   that pattern of "modify the data" reads naturally over a
--   structure but awkwardly through an existential proof.
--
-- *Why two apex names `apexL` / `apexR` rather than a single shared
--   apex.*  The LN names them `v_{k-1}` and `v_k`, two distinct
--   vertices joined by the hinge edge.  In the bidirected-hinge case
--   they are graph-theoretically "co-apex" (the fork lives across
--   the bidirected edge, neither is the source), and in the
--   directed-hinge case `apexR = v_k` is *the* source (the LN's
--   word).  Collapsing to a single apex would erase the apexR /
--   source identification and break the symmetric naming in
--   `b.leftArm : Walk G apexL v` vs `b.rightArm : Walk G apexR w`.
--   Each apex sits at the *base* of its corresponding arm.
--
-- *Why `leftArm : Walk G apexL v` runs from `apexL` to `v`, not from
--   `v` to `apexL`.*  This is the "reversed reading" of the LN's
--   $v_0 \hut v_1 \hut \cdots \hut v_{k-1}$.  The LN writes the left
--   subwalk *left-to-right* (`v_0` first, `v_{k-1}` last) and then
--   says "this subwalk is a *directed walk from $v_{k-1}$ to $v_0$*"
--   — i.e. the LN already orients the directed reading as
--   `v_{k-1} → v_{k-2} → … → v_0`.  Our encoding matches that
--   directed reading verbatim: `leftArm : Walk G apexL v` with
--   `IsDirectedWalk` (all steps `.forward`).  The first
--   `EdgeStep` of `leftArm` goes from `apexL = v_{k-1}` to some
--   `v_{k-2}`; the last `EdgeStep` lands at `v = v_0`.
--   Alternative — `leftArm : Walk G v apexL` with all steps
--   `.backward` — was rejected: `Walk.IsDirectedWalk` is `True` only
--   for `.forward`-chain walks (see `Walks.lean`'s `IsDirectedWalk`
--   block), so we would have had to introduce a new predicate
--   `IsReverseDirectedWalk` or coerce via `.symm`.  Reading the LN's
--   "directed walk from $v_{k-1}$ to $v_0$" literally, the encoding
--   we use is the natural one.
--
-- *Why the directed-walk constraints are `IsDirectedWalk` predicates
--   on `Walk`, not a bespoke `DirectedWalk` type.*  Same rationale
--   as the design block above `Walk.IsDirectedWalk` in `Walks.lean`:
--   the predicate form preserves `Walk.support`, `Walk.length`, and
--   all walk-level lemmas (concat, sub-walk extraction) for free.
--   Downstream `def_3_14` marginalisation expansions take
--   `b.leftArm` and *grow* it by concatenating per-edge directed
--   walks through marginalised nodes; that operation lives on
--   `Walk` and preserves `IsDirectedWalk`.  A bespoke
--   `DirectedWalk` would need a fresh concat operation and a fresh
--   `support` recursor.
--
-- *Why `hinge : HingeKind G apexL apexR` (not `G.hus apexL apexR`).*
--   Spells the LN's `$v_{k-1} \hus v_k$` as a `Type`-level ADT
--   recording which of the two possible edge kinds (directed
--   `.directed h_hut` or bidirected `.bidir h_huh`) was chosen.
--   The naive `Prop`-disjunction spelling `hinge : G.hus apexL
--   apexR` (= `G.hut ∨ G.huh`) was the original draft and FAILED
--   the strict-equivalence solved-gate with a verified
--   counter-example: in the coexistence regime admitted by
--   `def_3_1`'s `[edge_set_disjointness_under_specified]`
--   addition, both edge kinds can simultaneously exist between
--   the same vertex pair, and a `Prop`-irrelevant `Or` loses the
--   constructor information needed by `Bifurcation.source` to
--   pick the right branch.  The full bug trace lives in the
--   design block above `HingeKind` itself.
--
-- *Why `hVneW : v ≠ w` is its own field.*  The LN explicitly imposes
--   `v ≠ w`.  In a few corner cases (single-bidirected-edge
--   bifurcation, `n = k = 1`) this is automatically implied by
--   `G.hL_irrefl` applied to the bidirected hinge, but in the
--   directed-hinge cases it must be supplied separately (a directed
--   edge `v → v` could in principle inhabit `G.E` since `def_3_1`
--   does not exclude directed self-loops — see the `directed_self_
--   loops_unrestricted_in_E` subtlety in `CDMG.lean`).  Making
--   `hVneW` a structure field keeps the LN's "such that $v \ne w$"
--   clause visible at the type level.
--
-- *How `hVOnce` and `hWOnce` encode "the walk contains both endnodes
--   exactly once".*  The LN's full bifurcation walk has support
--   `[v_0, v_1, …, v_{k-1}, v_k, …, v_n]`.  In our encoding this
--   support equals `leftArm.support.reverse ++ rightArm.support`
--   (where `leftArm.support = [v_{k-1}, …, v_0]` and
--   `rightArm.support = [v_k, …, v_n]`).  The LN's "both endnodes
--   exactly once" therefore reads:
--     * `v = v_0` appears exactly once in the full support →
--       `v ∉ rightArm.support` (not in the right arm) AND
--       `leftArm.support.count v = 1` (appears exactly once in the
--       left arm, at the right end).
--     * `w = v_n` symmetric.
--   We split each into two conjunctive fields so a downstream proof
--   can extract just the half it needs (e.g. "v is in the left arm
--   exactly once" vs "v is not in the right arm").
--   `List.count` is well-defined under `DecidableEq Node` (which is
--   part of the file's `variable`-bound prelude) via the auto-
--   derived `BEq` / `LawfulBEq` instance.
--
-- *How `hArrowW` encodes the addition* — load-bearing.  The LN
--   addition `[bifurcation_right_chain_trivial_is_just_directed_
--   walk]` (treated as part of the LN, hence binding on this
--   formalisation) requires "$v_n$ has exactly one arrowhead
--   pointing towards it".  This field is where the addition is
--   *enforced* on the type.  In the LN's bifurcation walk, $v_n$
--   is adjacent to exactly one edge — the last edge of the walk.
--   That last edge is:
--     * the last step of the rightArm, if `rightArm.length > 0`
--       (`k < n` in the LN's notation);
--     * the hinge `v_{k-1} \hus v_k`, if `rightArm.length = 0`
--       (`k = n`, the right arm collapses).
--   In the first case `rightArm.IsDirectedWalk` already forces the
--   last step to be `.forward`, whose underlying directed edge has
--   its head at the right index (= $v_n$) — so $v_n$ automatically
--   has an arrowhead.  In the second case the *hinge itself* has
--   its head at the right (= apexR = $v_n$) iff the hinge is
--   *bidirected* (`.bidir`); a directed hinge (`.directed`) has
--   its head only at `apexL`, leaving $v_n$ without arrowhead.
--   Hence the encoding: `rightArm.length > 0 ∨ hinge.isBidir`.
--   This directly excludes the LN-critic's `bifurcation_k_equals_
--   n_is_just_directed_walk` corner case (`rightArm = .nil _` AND
--   `hinge = .directed _` → both disjuncts fail → constructor
--   rejected), and likewise excludes the directed-hinge half of
--   `bifurcation_admits_single_edge_at_n1_k1` (a lone directed
--   edge $v_1 \to v_0$ is NOT a bifurcation between $v_0$ and
--   $v_1$); the bidirected-edge half of the latter (`hinge =
--   .bidir _`, both arms trivial, $v_0 \huh v_1$) survives by
--   design — see the boundary-examples block below.
--
-- *Why `hinge.isBidir` and NOT `G.huh apexL apexR`* — same bug
--   class as the hinge-typing one (see the `HingeKind` design
--   block).  `G.huh apexL apexR` only says "a bidirected edge
--   exists between the apex pair somewhere in `G.L`"; in the
--   coexistence regime, a stand-alone bidirected edge can be in
--   `G.L` *without* being the hinge.  If we keyed `hArrowW` off
--   `G.huh apexL apexR` we would permit a directed-hinge
--   bifurcation (`hinge := .directed _`) with a trivial right arm
--   to silently satisfy `hArrowW` via the *unrelated* bidirected
--   edge — even though the actual last-edge-of-the-walk (= the
--   hinge) has no head at $v_n$.  `hinge.isBidir` keys the
--   constraint off the chosen hinge constructor specifically,
--   which is what the LN means by "the *walk* has an arrowhead at
--   $v_n$".
--
-- *Why there is no symmetric `hArrowV` field — the v-side is
--   automatic from the other fields.*  The dual condition "$v_0$
--   has an arrowhead" decomposes the same way:
--     * `leftArm.length > 0`: the last step of `leftArm` (in walk
--       direction) ends at `v` and, being `.forward` per
--       `hLeftArmDir`, has its head at `v` — arrowhead present.
--     * `leftArm.length = 0`: then `apexL = v`, and the hinge —
--       whichever `HingeKind` constructor was chosen — has its
--       head at `apexL = v` (both `.directed` and `.bidir` carry
--       an arrowhead at the *left* index: `.directed` wraps
--       `G.hut apexL apexR = (apexR, apexL) ∈ G.E`, the directed
--       edge whose head is at `apexL`; `.bidir` wraps
--       `G.huh apexL apexR = (apexL, apexR) ∈ G.L`, bidirected
--       so heads at both indices, in particular at `apexL`).
--       Arrowhead present.
--   The left-asymmetry of `\hus` is intrinsic to its `CDMGNotation`
--   definition (and inherited by `HingeKind` since each constructor
--   wraps the corresponding `G.hut` / `G.huh` proof): both kinds
--   guarantee a head at the left index — see the design block
--   above `CDMG.hus` in `CDMGNotation.lean` for the underlying
--   primitive design and the design block above `CDMG.edgeInto`
--   in `EdgeRelations.lean` for the same asymmetry used to encode
--   "edge into the focal vertex".  So `$v_0$ has arrowhead` is
--   true unconditionally given the existing fields `hLeftArmDir`
--   and `hinge`.  Encoding it as an additional structure field
--   would force every `Bifurcation` constructor to discharge a
--   redundant proof obligation; we document the absence here
--   instead.  This is the asymmetric resolution of the LN
--   addition: the LN's "both endnodes" is symmetric in prose, but
--   the bifurcation's *form* (head at `v_{k-1}` always, via the
--   `\hus` macro's left-asymmetry; head at `v_k` only when hinge
--   is `.bidir`) makes the W-side constraint the only non-trivial
--   one.
--
-- *Worked boundary examples — n = 1, k = 1; n = 2, k = 1; n = 2,
--   k = 2; n = 3, k = 2.*  Each one is the test case for one branch
--   of `hArrowW` and `Bifurcation.source`:
--   1.  `n = 1, k = 1, hinge = .bidir _`.  Both arms trivial
--       (`leftArm = .nil _`, `rightArm = .nil _`); `apexL = v`,
--       `apexR = w`; hinge = bidirected.  `hArrowW`:
--       `rightArm.length = 0`, but `hinge.isBidir` holds, so the
--       second disjunct fires.  ✓ valid bifurcation.
--       `source = none` (bidirected hinge).
--   2.  `n = 1, k = 1, hinge = .directed _`.  Same shape but hinge
--       directed.  `hArrowW`: `rightArm.length = 0` AND `¬
--       hinge.isBidir`; both disjuncts fail.  ✗ excluded — this is
--       the LN-critic's `bifurcation_admits_single_edge_at_n1_k1`
--       corner case resolved by the addition.  Note: even in the
--       coexistence regime where a bidirected edge between the
--       same `(apexL, apexR)` pair happens to exist in `G.L`,
--       this case stays excluded — `hinge.isBidir` checks the
--       chosen constructor, not the wider graph.
--   3.  `n = 2, k = 1, any hinge`.  `leftArm = .nil _`,
--       `rightArm = .cons (.forward _) (.nil _)`; left arm trivial,
--       right arm one `.forward` step from `apexR = v_1` to
--       `v_2 = w`.  `hArrowW`: `rightArm.length = 1 > 0`, so the
--       first disjunct fires.  ✓ valid for *both* `.directed` and
--       `.bidir` hinges.  When hinge is `.directed`, source =
--       `some v_1 = apexR` (the LN's "source" when the hinge is
--       directed).
--   4.  `n = 2, k = 2, hinge = .directed _`.  `leftArm = .cons
--       (.forward _) (.nil _)`, `rightArm = .nil _`; `apexL = v_1`,
--       `apexR = v_2 = w`; hinge directed.  `hArrowW`:
--       `rightArm.length = 0` AND `¬ hinge.isBidir`.  ✗ excluded
--       — this is the LN addition's prototypical "$k = n$ +
--       directed hinge" case (the walk would reduce to
--       $w \to v_1 \to v$, a pure directed walk, which the LN
--       explicitly excludes from being a bifurcation).
--   5.  `n = 2, k = 2, hinge = .bidir _`.  Same shape but hinge
--       bidirected.  `hArrowW`: `rightArm.length = 0` AND
--       `hinge.isBidir`; second disjunct fires.  ✓ valid
--       (`source = none`).
--   6.  `n = 3, k = 2, hinge = .directed _`.  `leftArm = .cons
--       (.forward _) (.nil _)` (length 1, ends at `v = v_0`);
--       `rightArm = .cons (.forward _) (.cons (.forward _) (.nil
--       _))` (length 2, ends at `w = v_3`); hinge directed.
--       `hArrowW`: `rightArm.length = 2 > 0`, first disjunct
--       fires.  ✓ valid, `source = some apexR = some v_2`.  This
--       is the textbook "fork bifurcation" with the source as
--       the LN names it.
--
-- *Single-edge surviving case is intentional — bidirected siblings
--   are bifurcations.*  Example (1) above (n = k = 1, hinge
--   `.bidir _`) means a single bidirected edge `v \huh w \in L`
--   automatically yields a bifurcation between `v` and `w` (with no
--   source).  This
--   matches the chapter-11 confounding intuition: bidirected
--   siblings ARE confounded (`def:graph_unconfounded`), and
--   `\Sib^G(v)` in `def_3_5` is exactly the length-1 bidirected
--   neighbours.  The LN-critic's
--   `bifurcation_admits_single_edge_at_n1_k1` subtlety flagged this
--   as potentially counter-intuitive (a "bifurcation" with zero arms
--   doesn't fork in any geometric sense), but the chapter-11 theory
--   consumes it directly and the addition's arrowhead constraint
--   admits it without further work.
--
-- *Why `apexL`, `apexR` are explicit fields rather than derived from
--   the arms' starting vertices.*  `leftArm : Walk G apexL v`'s
--   starting vertex IS `apexL`; technically one could project
--   `apexL := leftArm.startVertex` and similar for `apexR`.  We make
--   them explicit fields because (a) they appear in the hinge's
--   type `HingeKind G apexL apexR` and need to be available before
--   the arms are constructed (or pattern-matched in tandem with
--   the arms), (b) the source returns `apexR` directly and a field
--   is cleaner than a projection through `rightArm`, (c) downstream
--   chapter-11 destructuring `match b with | { apexL := c, … } => …`
--   reads the same way as the LN's "with source $c$".
--
-- *Downstream consumers.*  `claim_3_5`
--   (`prp:bifurcations_alternative`) characterises the existence of
--   a bifurcation with a given source as a pair of ancestor
--   conditions in intervened graphs; `claim_3_16`
--   (`rem:marg_preserves_ancestors_bifurcations_acyclicity` /
--   `def_3_14` marginalisation) shows bifurcations are preserved by
--   marginalisation, with the proof literally splitting the
--   bifurcation at the hinge and recomposing per-edge expansions;
--   `def:graph_unconfounded` (`causal_relations.tex`) defines
--   confounding as "there exists a bifurcation between $a$ and $b$
--   with no source or with source $c \in V$", a direct existential
--   over `Bifurcation G a b` paired with
--   `b.source = none ∨ ∃ c ∈ G.V, b.source = some c`.
--
-- *Mathlib re-use.*  No Mathlib structure captures a "two-arm
--   directed walk meeting at a hinge edge" of the right shape —
--   `SimpleGraph` has no directed edges, `Quiver` has no bidirected
--   channel, and no graph theory in Mathlib currently encodes the
--   CDMG's mixed `E + L` structure.  We therefore roll our own
--   `Bifurcation`, building on top of our own `Walk` /
--   `IsDirectedWalk` (which themselves are in the style of
--   `SimpleGraph.Walk` — see the design block above `Walk` in
--   `Walks.lean`).  The endpoint single-occurrence constraints use
--   `List.count` and `List ∉` from Mathlib's `List` library; the
--   irreflexivity / `Ne` clauses use plain `Ne`.
--
-- *Constraints / known limitations* (things this structure does
--   NOT enforce, but that downstream consumers may need to add at
--   the use site):
--   1. **No internal-node distinctness across arms.**  The LN's
--      "the walk contains both endnodes exactly once" only constrains
--      $v_0$ and $v_n$; internal nodes $v_1, \dots, v_{k-1},
--      v_{k+1}, \dots, v_{n-1}$ may repeat.  In particular, the
--      left arm's interior and the right arm's interior may share
--      vertices — our `hVOnce` / `hWOnce` fields do not preclude
--      a node `v_i = v_j` for `1 ≤ i ≤ k-1, k+1 ≤ j ≤ n-1`.  This
--      matches the LN, but downstream `claim_3_5` and chapter-11
--      proofs that need a *path-shaped* (no internal repeats)
--      bifurcation will combine `Bifurcation` with
--      `(leftArm.support ++ rightArm.support).Nodup` at the use
--      site.
--   2. **No arm-direction homogeneity check across the hinge.**
--      The structure separately constrains `hLeftArmDir` and
--      `hRightArmDir`, but the LN's geometric reading "the fork
--      *emanates* from a common neighbourhood" is a *consequence* of
--      the arrow directions, not directly checked.  Concretely, a
--      `Bifurcation` with `leftArm = .nil _` and `rightArm = .nil _`
--      and hinge `.bidir _` (Example 1 in the boundary-examples
--      block above) is structurally valid but has *no arms
--      emanating from anywhere* — it is a single bidirected edge.
--      This is the LN's
--      intent under the addition; downstream consumers that need a
--      non-trivial fork add `leftArm.length > 0 ∨ rightArm.length > 0`
--      at the use site.
--   3. **No symmetric `hArrowV` field.**  As documented above, the
--      v-side arrowhead is automatic from `hLeftArmDir` + the
--      left-asymmetry of `G.hus`, so we drop the field.  This is
--      asymmetric in *shape* but symmetric in *content* — a future
--      reader who expected a `hArrowV` field should consult the
--      design block above for the proof sketch.
--   4. **`def_3_4` item 6 is `Type _`-valued** (a `structure`); the
--      `Bifurcation G v w` itself is data, not a `Prop`.  A
--      `Prop`-side "there exists a bifurcation between $v$ and $w$"
--      is then written `Nonempty (Bifurcation G v w)` — see
--      `claim_3_5` / `def:graph_unconfounded` for the canonical
--      shape.  This is the load-bearing reason for the
--      structure-vs-predicate choice; flagged here so it doesn't
--      surprise a future reader who expects a `Prop`.
-- def_3_4 -- start statement
structure Bifurcation (G : CDMG Node) (v w : Node) where
  /-- LN's `v_{k-1}` — the right end of the left arm, sitting on the
      `apexL`-side of the hinge edge. -/
  apexL : Node
  /-- LN's `v_k` — the left end of the right arm, sitting on the
      `apexR`-side of the hinge edge.  When the hinge is directed
      (`.directed`), this is the LN's "source". -/
  apexR : Node
  /-- The left arm of the bifurcation, oriented to match the LN's
      "directed walk from $v_{k-1}$ to $v_0$" reading. -/
  leftArm : Walk G apexL v
  /-- The left arm is a directed walk (LN: "the subwalk
      $v_0 \hut \cdots v_{k-1}$ is a directed walk from $v_{k-1}$ to
      $v_0$"). -/
  hLeftArmDir : leftArm.IsDirectedWalk
  /-- The right arm of the bifurcation, oriented as the LN's "directed
      walk from $v_k$ to $v_n$". -/
  rightArm : Walk G apexR w
  /-- The right arm is a directed walk (LN: "the subwalk
      $v_k \tuh \cdots v_n$ is a directed walk from $v_k$ to $v_n$"). -/
  hRightArmDir : rightArm.IsDirectedWalk
  /-- The hinge edge `v_{k-1} \hus v_k`, encoded as a `HingeKind`
      to record *which* edge kind was chosen (rather than the
      `Prop`-irrelevant `Or` of `G.hus`).  `.directed` makes the
      bifurcation *directed-hinged* (the LN's "source" case);
      `.bidir` makes it *bidirected-hinged* (no source). -/
  hinge : HingeKind G apexL apexR
  /-- LN: "such that $v \ne w$". -/
  hVneW : v ≠ w
  /-- LN: "the walk contains $v$ exactly once".  Encoded as: `v` is
      not in the right arm's support, and appears exactly once in the
      left arm's support (necessarily at the right end of `leftArm`,
      since `leftArm` ends at `v`). -/
  hVOnce : v ∉ rightArm.support ∧ leftArm.support.count v = 1
  /-- LN: "the walk contains $w$ exactly once" (dual to `hVOnce`). -/
  hWOnce : w ∉ leftArm.support ∧ rightArm.support.count w = 1
  /-- LN addition `[bifurcation_right_chain_trivial_is_just_directed_
      walk]`: `w` has an arrowhead pointing towards it.  Either the
      right arm is non-trivial (then its last `.forward` step
      supplies the arrowhead automatically) or the right arm is
      trivial AND the *hinge itself* is bidirected (`.bidir`, head
      at both ends).  `hinge.isBidir` — not `G.huh apexL apexR` —
      is the load-bearing predicate here: see the design block
      above `HingeKind` for the verified bug a `G.huh apexL apexR`
      spelling produces in the coexistence regime, where a
      stand-alone bidirected edge between the apex pair would
      satisfy `G.huh apexL apexR` without actually being the
      hinge.  The dual condition for `v` is automatic from
      `hLeftArmDir` + the LN form of `hinge` — see the design
      comment above for why no `hArrowV` field is needed. -/
  hArrowW : rightArm.length > 0 ∨ hinge.isBidir
-- def_3_4 -- end statement

-- ref: def_3_4 (item 6 — source predicate)
--
-- `Bifurcation.source b` extracts the LN's "source $v_k$" when the
-- bifurcation's hinge was constructed with `.directed _`, and
-- returns `none` otherwise (`.bidir _` hinge has no source).
/-
LN tex (closing sentence of item 6 of `\label{def:walks}`):

  If the edge $v_{k-1} \hus v_k$ is directed ($v_{k-1} \hut v_k$)
  then we say that the bifurcation has \emph{source} $v_k$.
-/
-- ## Design choice
--
-- *Why `Option Node` and not a `Prop` predicate /
--   `Σ' c : Node, …`.*  The LN's "source" is defined *conditionally*:
--   the bifurcation has a source iff the hinge is directed.  An
--   `Option Node` directly captures the partiality:
--     * `some apexR` when the hinge is `.directed _` — the LN's
--       "source $v_k$";
--     * `none` when the hinge is `.bidir _` — no source.
--   A `Prop`-side `∃ c, c = source` would force every downstream
--   use to existentially destructure; an `Option`-valued function
--   lets `claim_3_5` and `def:graph_unconfounded` (chapter 11)
--   phrase their existence claims as `b.source = some c` or
--   `b.source = none` directly.
--
-- *Why pattern-match on `b.hinge` rather than `if … ∈ G.E then …`.*
--   The earlier draft used `if (b.apexR, b.apexL) ∈ G.E then some
--   b.apexR else none` as a decidable proxy for "hinge is
--   directed".  The strict-equivalence solved-gate produced a
--   verified counter-example exposing the proxy as wrong: in the
--   coexistence regime admitted by `def_3_1`'s addition
--   `[edge_set_disjointness_under_specified]`, a stand-alone
--   directed edge `(apexR, apexL) ∈ G.E` can coexist with the
--   *bidirected* hinge `.bidir _` actually chosen for the
--   `Bifurcation`.  The membership test fires regardless of which
--   `HingeKind` constructor was used, so a `.bidir`-hinged
--   bifurcation gets `source = some apexR` — disagreeing with the
--   LN ("`.bidir` hinge has no source").  Pattern-matching on
--   `b.hinge : HingeKind G b.apexL b.apexR` directly (`Type`-valued
--   ADT, no proof-irrelevance) yields exactly the LN's case split.
--   The verified counter-example used `Node := Fin 6`, edge sets
--   `E = {(1, 0), (5, 4)}` and `L = {(0, 1), (1, 0), (2, 3), (3,
--   2)}`, and `Bifurcation G 0 1` with trivial arms and bidirected
--   hinge; under the old `if`-based code, `source = some 1`
--   instead of the LN's expected `none`.  The new `match`-based
--   code returns `none`, correctly.
--
-- *Why `some b.apexR` (not `some b.apexL`).*  The LN: "If the edge
--   $v_{k-1} \hus v_k$ is directed ($v_{k-1} \hut v_k$) then we say
--   that the bifurcation has *source* $v_k$".  In our encoding
--   `apexR = v_k`, so the source is `apexR`.  This is the right
--   side of the hinge — the *target* of the LN's `\hus` and the
--   *tail* of the directed hinge edge (the `.directed h_hut` edge,
--   where `h_hut : G.hut apexL apexR = (apexR, apexL) ∈ G.E`,
--   reads as "$apexR \to apexL$" — tail at `apexR`, head at
--   `apexL`).
--
-- *Why a `def` rather than a structure field*.  `source` is *derived
--   data*: it is fully determined by `hinge` and `apexR`, so making
--   it a separate field would risk inconsistency (a structure
--   constructor could supply `source := none` while the hinge was
--   `.directed _`, or vice versa).  A `def` couples the value to
--   the hinge automatically.
--
-- *Downstream consumers.*  `claim_3_5`
--   (`prp:bifurcations_alternative`) reads "there exists a
--   bifurcation between $v$ and $w$ with source $c$", which in Lean
--   becomes `∃ b : Bifurcation G v w, b.source = some c`;
--   `def:graph_unconfounded` (chapter 11) defines confounding via
--   "there exists a bifurcation without source or with source $c
--   \in V$", literally `∃ b, b.source = none ∨ ∃ c ∈ G.V,
--   b.source = some c`; `claim_3_16`
--   (`rem:marg_preserves_ancestors_bifurcations_acyclicity`) and
--   marginalisation arguments use `b.source` to track which side
--   of the bifurcation expands which way under graph
--   marginalisation.
--
-- *Mathlib re-use.*  `Option` is Mathlib's standard partiality
--   monad (`Option.some` / `Option.none` from `Init.Data.Option`),
--   chosen here over `WithBot Node` (no useful bot-element semantics
--   for "no source"), `Sum Unit Node` (more cumbersome destructuring
--   at call sites), or `Σ' c : Node, b.hinge = .directed …`
--   (which would bake the proof of directedness into the source's
--   *type*, forcing downstream consumers to carry the proof
--   everywhere they refer to the source).  `Option` lets
--   `b.source = some c` and `b.source = none` read as plain
--   equalities decidable by `Option`-level lemmas, which is what
--   `claim_3_5` and chapter-11 confounding statements actually
--   want.
--
-- *Constraints / known limitations.*
--   1. `b.source = some c` does NOT by itself prove `c = b.apexR` —
--      one needs to case-split on `b.hinge`.  A small downstream
--      lemma `source_some_iff` stating `b.source = some c ↔
--      (∃ h, b.hinge = .directed h) ∧ c = b.apexR` would smooth
--      out `claim_3_5`'s destructuring; we leave it for the
--      consumer to add on demand.
--   2. The match returns based purely on the `HingeKind`
--      constructor — *not* on whether some other directed edge
--      between the apex pair happens to exist in `G.E`.  This is
--      the load-bearing correctness property and the reason for
--      the `HingeKind` typing decision (see its design block).
-- def_3_4 -- start statement
def Bifurcation.source {G : CDMG Node} {v w : Node}
    (b : Bifurcation G v w) : Option Node :=
  match b.hinge with
  | .directed _ => some b.apexR
  | .bidir _    => none
-- def_3_4 -- end statement

end Causality
