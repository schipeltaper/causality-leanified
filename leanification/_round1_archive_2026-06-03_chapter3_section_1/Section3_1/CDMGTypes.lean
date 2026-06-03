import Chapter3_GraphTheory.Section3_1.Acyclicity

namespace Causality

/-!
# CDMG taxonomy: the seven named subtypes of `def_3_7`

This file formalises `def_3_7` (`CDMGTypes`) — the LN's taxonomy of seven
named CDMG subtypes (CADMG, DMG, ADMG, CDG, DG, CDAG, DAG), each obtained
by imposing some combination of the three atomic constraints
"(a) `G` is acyclic", "(b) `J = ∅`", "(c) `L = ∅`" on a CDMG.

## LN block (verbatim)

```
A Conditional Directed Mixed Graph (CDMG) G=(J,V,E,L) is called:
  1. Conditional Acyclic Directed Mixed Graph (CADMG) if G is acyclic.
  2. Directed Mixed Graph (DMG) if J = ∅.
  3. Acyclic Directed Mixed Graph (ADMG) if G is acyclic and J = ∅.
  4. Conditional Directed Graph (CDG) if L = ∅.
  5. Directed Graph (DG) if J = ∅ and L = ∅.
  6. Conditional Directed Acyclic Graph (CDAG) if G is acyclic and L = ∅.
  7. Directed Acyclic Graph (DAG) if G is acyclic, J = ∅ and L = ∅.
```

## File-level design

Each of the seven names is encoded as a `Prop`-valued `def` on `CDMG`,
not as a refined subtype, sum, inductive, or `structure CADMG extends
CDMG`-style record carrying its own data.  The LN's "A CDMG is called
X if Y" pattern attaches a name X to `G` whenever the predicate Y
holds — and the seven Y's overlap: items 3, 5, 6, 7 are conjunctions
of items 1, 2, 4, so the same `G` can satisfy several names at once.
A predicate-style encoding mirrors this literally; a sum/subtype/
`extends`-style encoding would impose a (non-existent) partition, force
coercions back to `CDMG` at every downstream pattern-match (chapter 4
CBNs, chapter 5+ separations, chapter 8+ iSCMs all destructure the
underlying `J / V / E / L` directly), and force a choice of "primary
type" — e.g. is an acyclic CDMG with `J = ∅` natively a CADMG, an ADMG,
or a DMG?  The predicate encoding sidesteps the question: it is all
three (and a CDG, DG, CDAG, DAG too if `L = ∅` as well — see below).

Two LN-critic subtleties governed the design and are honoured by it:

* `subtypes_are_overlapping_predicates_not_partition` (registered
  globally in `leanification/working_subtlety_register.json`) — the
  seven names are *overlapping* predicates, not a partition.  A DAG is
  also a CADMG, ADMG, DMG, CDG, DG, CDAG.  Since `def_3_1` admits the
  empty CDMG, the empty CDMG satisfies all 7 names simultaneously.
  Predicate-style encoding makes this literally true on the nose; no
  Lean machinery has to be invoked to express the lattice
  `DAG ⊆ ADMG ⊆ DMG ⊆ CDMG`, `DAG ⊆ CDAG ⊆ CDG ⊆ CDMG`, etc. — it is
  the meet of the relevant `Prop`-valued fields.

* `conditional_and_mixed_prefixes_dont_constrain_components` — the
  suggestive prefixes are *upper bounds*, not requirements.
  "Conditional" in CADMG / CDG / CDAG does **not** require `J ≠ ∅`;
  "Mixed" in CDMG / CADMG / DMG / ADMG does **not** require `L ≠ ∅`.
  The literal LN definitions impose only the constraints explicitly
  listed (acyclic / `J = ∅` / `L = ∅`), and we encode only those.
  A CADMG with `J = ∅` is admissible; a DMG with `L = ∅` is
  admissible.  Downstream rows that genuinely need the "with-J" or
  "with-L" variant must add that hypothesis at the use site.

Two structural choices follow:

1. **Conjunctions are spelled out literally** — `IsADMG` is
   `G.IsAcyclic ∧ G.J = ∅`, not `G.IsCADMG ∧ G.IsDMG`.  The LN writes
   "`G` is acyclic and `J = ∅`" in surface form; downstream proofs
   that quote the LN will pattern-match on the literal conjuncts.
   Friendly small iff-lemmas (e.g. `IsADMG ↔ IsCADMG ∧ IsDMG`) are
   one-line corollaries and can be added on demand if a chapter-5+
   consumer wants them.

2. **Conjunction order follows the LN** — items 6 and 7 list the
   atoms in the order "acyclic, J = ∅, L = ∅", and the Lean
   encoding preserves that left-to-right order so `rcases` patterns
   in downstream proofs match the LN reading.

The per-item design notes immediately above each `start statement`
marker drill into the LN-faithfulness, naming, and downstream-consumer
considerations for each predicate individually.
-/

namespace CDMG

variable {Node : Type*} [DecidableEq Node]

-- ref: def_3_7 (item 1)
--
-- `IsCADMG G` ("Conditional Acyclic Directed Mixed Graph") holds iff
-- `G` is acyclic.  One of the three independent atomic constraint
-- axes in `def_3_7` (the other two being `IsDMG`'s `J = ∅` and
-- `IsCDG`'s `L = ∅`); items 3, 5, 6, 7 are conjunctions of these
-- three atoms.  Per subtlety
-- `conditional_and_mixed_prefixes_dont_constrain_components`, the
-- "Conditional" / "Mixed" prefixes are *not* additional constraints:
-- `IsCADMG` does NOT require `G.J ≠ ∅` or `G.L ≠ ∅`.
/-
LN tex (item 1 of def_3_7):

  Conditional Acyclic Directed Mixed Graph (CADMG) if $G$ is acyclic.
-/
-- ## Design choice
--
-- *Body is exactly `G.IsAcyclic`.*  Re-uses the def_3_6 predicate
--   (Acyclicity.lean) verbatim, so any rewrite / unfolding pipeline
--   set up for `G.IsAcyclic` lifts to `G.IsCADMG` for free.  No
--   alternative re-statement (e.g. inline-expanding the
--   walk-existential) is admitted: that would break the
--   `unfold IsCADMG` → `G.IsAcyclic` chain that downstream rows will
--   rely on when CADMG-restricted theorems (chapter 11+ FCI on
--   "acyclic ADMGs", swig/acyclification preservation) reduce to
--   pre-existing acyclicity lemmas.
-- def_3_7 -- start statement
def IsCADMG (G : CDMG Node) : Prop := G.IsAcyclic
-- def_3_7 -- end statement

-- ref: def_3_7 (item 2)
--
-- `IsDMG G` ("Directed Mixed Graph") holds iff `G` has no input
-- nodes.  One of the three independent atomic constraint axes in
-- `def_3_7` (the other two being `IsCADMG`'s `G.IsAcyclic` and
-- `IsCDG`'s `L = ∅`).  Per subtlety
-- `conditional_and_mixed_prefixes_dont_constrain_components`, the
-- "Mixed" prefix is suggestive only: `IsDMG` does NOT require
-- `G.L ≠ ∅` — a CDMG with `J = ∅` and `L = ∅` is still a DMG.
/-
LN tex (item 2 of def_3_7):

  Directed Mixed Graph (DMG) if $J = \emptyset$.
-/
-- ## Design choice
--
-- *Body is literal `G.J = ∅`.*  `G.J : Finset Node` (def_3_1), so
--   `G.J = ∅` is `Finset` equality with the empty Finset — the
--   literal LN reading.  Equivalent encodings (`G.J.card = 0`,
--   `∀ v, v ∉ G.J`) were considered and rejected: the literal
--   `= ∅` is what the LN writes, rewrites trivially via
--   `Finset.eq_empty_iff_forall_not_mem` /
--   `Finset.card_eq_zero` when a consumer needs the alternative
--   form, and keeps the surface shape uniform with `IsCDG`'s
--   `G.L = ∅` clause.
-- def_3_7 -- start statement
def IsDMG (G : CDMG Node) : Prop := G.J = ∅
-- def_3_7 -- end statement

-- ref: def_3_7 (item 3)
--
-- `IsADMG G` ("Acyclic Directed Mixed Graph") holds iff `G` is
-- acyclic AND has no input nodes.  Conjunction of items 1 and 2.
/-
LN tex (item 3 of def_3_7):

  Acyclic Directed Mixed Graph (ADMG) if $G$ is acyclic and
  $J = \emptyset$.
-/
-- ## Design choice
--
-- *Spelled out as `G.IsAcyclic ∧ G.J = ∅`, not as
--   `G.IsCADMG ∧ G.IsDMG`.*  The LN writes "$G$ is acyclic and
--   $J = \emptyset$" in surface form; mirroring the conjuncts
--   literally keeps consumer proofs in step with the LN reading.
--   A `iff`-lemma `IsADMG_iff_IsCADMG_and_IsDMG` is a one-line
--   corollary (`Iff.rfl` modulo unfolding) and can be added later
--   if needed — not pre-emptive.
--
-- *Conjunction order matches the LN.*  Acyclicity first, `J = ∅`
--   second.  Reordering was considered (`G.J = ∅ ∧ G.IsAcyclic`)
--   but rejected for the same LN-fidelity reason.
-- def_3_7 -- start statement
def IsADMG (G : CDMG Node) : Prop := G.IsAcyclic ∧ G.J = ∅
-- def_3_7 -- end statement

-- ref: def_3_7 (item 4)
--
-- `IsCDG G` ("Conditional Directed Graph") holds iff `G` has no
-- bidirected edges.  One of the three independent atomic constraint
-- axes in `def_3_7` (the other two being `IsCADMG`'s `G.IsAcyclic`
-- and `IsDMG`'s `J = ∅`).  Per subtlety
-- `conditional_and_mixed_prefixes_dont_constrain_components`,
-- "Conditional" is suggestive only: `IsCDG` does NOT require
-- `G.J ≠ ∅` — a CDMG with `L = ∅` and `J = ∅` is still a CDG.
/-
LN tex (item 4 of def_3_7):

  Conditional Directed Graph (CDG) if $L = \emptyset$.
-/
-- ## Design choice
--
-- *Body is literal `G.L = ∅`.*  `G.L : Finset (Node × Node)`
--   (def_3_1), so `G.L = ∅` is `Finset` equality.  Note: this is
--   the *ordered-pair* L, not the LN's quotient; the choice was
--   made at the def_3_1 stage (see `CDMG.lean`'s design block on
--   `[l_quotient_vs_ordered_pair_typing_inconsistent]`) and `L = ∅`
--   under either encoding picks out the same CDMGs.
-- def_3_7 -- start statement
def IsCDG (G : CDMG Node) : Prop := G.L = ∅
-- def_3_7 -- end statement

-- ref: def_3_7 (item 5)
--
-- `IsDG G` ("Directed Graph") holds iff `G` has no input nodes
-- AND no bidirected edges.  Conjunction of items 2 and 4.
/-
LN tex (item 5 of def_3_7):

  Directed Graph (DG) if $J = \emptyset$ and $L = \emptyset$.
-/
-- ## Design choice
--
-- *Spelled out as `G.J = ∅ ∧ G.L = ∅`, conjunction order matches
--   the LN.*  Acyclicity is *not* assumed here — a directed graph
--   with cycles is still a DG by the literal LN.  Downstream rows
--   that want "acyclic DG" should reach for `IsDAG` (item 7), not
--   refine `IsDG`.
-- def_3_7 -- start statement
def IsDG (G : CDMG Node) : Prop := G.J = ∅ ∧ G.L = ∅
-- def_3_7 -- end statement

-- ref: def_3_7 (item 6)
--
-- `IsCDAG G` ("Conditional Directed Acyclic Graph") holds iff `G`
-- is acyclic AND has no bidirected edges.  Conjunction of items 1
-- and 4.  Per subtlety
-- `conditional_and_mixed_prefixes_dont_constrain_components`, the
-- "Conditional" prefix does NOT require `G.J ≠ ∅`.
/-
LN tex (item 6 of def_3_7):

  Conditional Directed Acyclic Graph (CDAG) if $G$ is acyclic and
  $L = \emptyset$.
-/
-- ## Design choice
--
-- *Conjunction order matches the LN.*  Acyclicity first, `L = ∅`
--   second, as item 6 of the tex block writes them.
-- def_3_7 -- start statement
def IsCDAG (G : CDMG Node) : Prop := G.IsAcyclic ∧ G.L = ∅
-- def_3_7 -- end statement

-- ref: def_3_7 (item 7)
--
-- `IsDAG G` ("Directed Acyclic Graph") holds iff `G` is acyclic
-- AND has no input nodes AND no bidirected edges.  Conjunction of
-- all three atomic axes — `IsDAG` is the strongest of the seven
-- predicates and implies each of the other six (`IsCADMG`, `IsDMG`,
-- `IsADMG`, `IsCDG`, `IsDG`, `IsCDAG`) by projection out of its
-- triple conjunction.  In the lattice picture of subtlety
-- `subtypes_are_overlapping_predicates_not_partition`, `IsDAG` sits
-- at the bottom: `{G : G.IsDAG} ⊆ {G : G.IsCDAG} ⊆ {G : G.IsCADMG}`,
-- `{G : G.IsDAG} ⊆ {G : G.IsADMG} ⊆ {G : G.IsDMG}`, and similarly
-- through `IsCDG`, `IsDG`.
/-
LN tex (item 7 of def_3_7):

  Directed Acyclic Graph (DAG) if $G$ is acyclic, $J=\emptyset$ and
  $L = \emptyset$.
-/
-- ## Design choice
--
-- *Spelled out as a three-conjunct `∧`, in the LN's order
--   `IsAcyclic ∧ J = ∅ ∧ L = ∅`.*  Right-associated by Lean
--   convention: parses as `G.IsAcyclic ∧ (G.J = ∅ ∧ G.L = ∅)`.
--   Downstream consumers that want the "G.IsADMG ∧ G.L = ∅" or
--   "G.IsCDAG ∧ G.J = ∅" form (i.e. DAG as the intersection of two
--   chapter-3 lattice paths) can derive it as a one-line iff
--   corollary; the literal `∧`-flat form is what the LN writes
--   and is the most convenient surface for `obtain ⟨_, _, _⟩ := h`
--   destructuring.
--
-- *Load-bearing for chapter 8+ iSCMs.*  `def:scm_acyclic` and
--   downstream iSCM theory quote "DAG" repeatedly; our `IsDAG`
--   predicate is the literal Lean translation those hypotheses
--   will use.
-- def_3_7 -- start statement
def IsDAG (G : CDMG Node) : Prop := G.IsAcyclic ∧ G.J = ∅ ∧ G.L = ∅
-- def_3_7 -- end statement

end CDMG

end Causality
