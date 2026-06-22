import Chapter3_GraphTheory.Section3_3.ISigmaSeparation
import Chapter3_GraphTheory.Section3_3.SigmaOpenPathsWalks

namespace Causality

/-!
# σ-separation equivalences (`claim_3_24`)

This file formalises `claim_3_24` (`SigmaSeparationEquivalences`), the
Remark in Section 3.3 of the lecture notes that records four
structurally distinct corollaries of `claim_3_23`
(`SigmaOpenPathsWalks`, `\label{prp:sigma_opens}`):

> By Proposition `prp:sigma_opens`:
>
>   1.  `A ⊥^iσ_G B | C` is equivalent to each of:
>       (a) every *walk* from a node in `A` to a node in `J ∪ B` is
>           `C`-σ-blocked;
>       (b) every *path* from a node in `A` to a node in `J ∪ B` is
>           `C`-σ-blocked.
>
>   2.  if `A ⊥̸^iσ_G B | C` (i.e.\ negation of σ-separation) then:
>       (a) there exists a (shortest) `C`-σ-open *path* from a node in
>           `A` to a node in `J ∪ B`;
>       (b) there exists a (shortest) `C`-σ-open *walk* from a node in
>           `A` to a node in `J ∪ B` such that **all** its colliders
>           lie in `C`.
>
>   In practice, characterisation (1b) is the one that gets checked
>   (there are only finitely many paths in a finite graph), while in
>   proofs (1a) and (2b) are the easier ones to manipulate because
>   walks concatenate.

The authoritative spec is the rewritten canonical tex statement at
`leanification/Chapter3_GraphTheory/Section3_3/tex/`
`claim_3_24_statement_SigmaSeparationEquivalences.tex`, verified
equivalent (both structurally and semantically) to the LN block
(`graphs.tex`) augmented with the operator-authored addition
`[shortest_qualifier_reference_class_ambiguous]`.  The rewrite
spells out the four sub-statements in full and pins down the
"(shortest)" qualifier of items~2(a)/(b) as part of the existence
claim: the witness's length is minimum among the *joint* class of
walks/paths satisfying *all* of the stated conditions (not within
the wider class of `C`-σ-open walks alone).

## Design pillars

1. **Four separate `theorem` declarations, one per LN sub-item.**
   Each of `(1a)`, `(1b)`, `(2a)`, `(2b)` carries its own
   `-- claim_3_24 -- start statement` / `-- claim_3_24 -- end
   statement` marker pair so the website builder pulls each sub-
   statement out individually.  Bundling all four into a single
   `And`-shaped statement was considered and rejected: downstream
   consumers cite *different* sub-items in isolation (1a/1b for
   the σ-separation characterisations; 2a/2b for the σ-non-
   separation existence witnesses), and a single bundled lemma
   would force every consumer through a `.left.left` / `.right.right`
   tuple projection.

2. **`(1a)` is recorded as a separate biconditional, even though
   its RHS is exactly the def-unfold of
   `IsISigmaSeparated`.**  The LN explicitly lists `(1a)` as one
   of two equivalent characterisations of `A ⊥^iσ_G B | C`; for LN
   fidelity we record it as a biconditional whose proof is
   `Iff.rfl` (the RHS *is* the body of `IsISigmaSeparated`).  This
   is the worker-prompt rule "include 'trivially' or 'obviously'
   clauses as part of the statement".

3. **`(1b)` is the non-trivial walk → path lift via `claim_3_23`.**
   The body restricts the universal quantifier of `(1a)` to paths.
   The (⇒) direction is trivial (every path is a walk).  The (⇐)
   direction needs `claim_3_23`'s TFAE (1)↔(2) — given a σ-open
   walk witness, extract a σ-open *path* witness with the same
   endpoints via `sigma_open_paths_walks.out 1 0`.

4. **`(2a)` and `(2b)` are conditional existence claims, with the
   "(shortest)" qualifier encoded as a per-witness universal
   bound.**  For `(2a)`: the witness is a σ-open path `π : Walk G
   u v` with `u ∈ A`, `v ∈ J ∪ B`, and `π.length ≤ π'.length` for
   every other such witness `π'` (i.e.\ length-minimum among σ-open
   paths from `A` to `J ∪ B`).  For `(2b)`: same shape, but the
   witness predicate is "σ-open AND all colliders lie in `C`"
   (the LN's strict strengthening of σ-openness, per the
   wording-check subtlety
   `walk_colliders_strictly_in_C_is_strengthening_not_translation`).
   The minimisation runs over the *joint* class (σ-open ∧
   colliders-in-C), per the addition
   `[shortest_qualifier_reference_class_ambiguous]`.

5. **Walk endpoints `u, v : Node` existentially bound at the
   statement surface.**  The LN says "exists a walk from a node in
   `A` to a node in `J ∪ B`", so the start and end nodes are
   existential at the statement level — not implicit binders
   inferred from a fixed `Walk G u v` type.  The existential is
   over the dependent pair `(u, v) : Node × Node` plus the
   `Walk G u v` itself.

6. **"All colliders lie in C" encoded inline as the same
   one-line universal used by `claim_3_23` variant (3).**  The
   LN's "every collider of `π` lies in `C`" is the predicate
   `∀ (k : ℕ) (vk : Node), π.vertices[k]? = some vk →
   π.IsCollider k → vk ∈ C` — identical to the third clause of
   `sigma_open_paths_walks`'s TFAE.  A bundled
   `Walk.AllCollidersIn` helper was considered and rejected by the
   worker-prompt rule: single-line universal predicates do not
   earn helper extraction.  Lifting it later if a downstream row
   needs the predicate as an independent hypothesis is a trivial
   refactor.

7. **No `(shortest)` helper / `MinLengthWitness` structure.**
   The minimality clause is a one-line universal `∀ π', cond π' →
   π.length ≤ π'.length` (over the same conditioned class as the
   witness).  Bundling it into a structure would obscure the LN's
   plain-English "shortest" reading; inline `∀` keeps the LN-faithful
   surface visible at the type level.

## Awareness of LN subtleties

* `[overlap_between_A_and_J_union_B_via_length_zero_walk]` —
  flagged by the LN-critic (in this row's wording-check) and
  recorded in the canonical tex spec's "Length-zero/overlap corner
  case" remark.  Length-zero walks `Walk.nil v hv` are vacuously
  `C`-σ-open (no collider / blockable-non-collider positions to
  constrain) under `def_3_17`'s reading.  Consequently, whenever
  `A ∩ (J ∪ B) ≠ ∅`, statements `(1a)` and `(1b)` both *force*
  `A ⊥^iσ_G B | C` to fail (the trivial walk on any
  `v ∈ A ∩ (J ∪ B)` is a non-blocked walk), and statement `(2a)`'s
  shortest path is automatically of length 0.  The corner case is
  consistent with `def_3_18`'s body — no Lean obligation here.

* `[walk_colliders_strictly_in_C_is_strengthening_not_translation]` —
  encoded as a *conjunction* on the witness predicate of `(2b)`
  (the `π.IsSigmaOpenGiven` clause AND the "all colliders in C"
  clause), not as a consequence of σ-openness.  Matches
  `claim_3_23` variant (3)'s shape.

* `[doubled_C_in_C_sigma_blocked_by_C]` — the LN-critic's parse
  ambiguity ("`C`-σ-blocked by `C`" — same `C` twice).  Both
  occurrences denote the same conditioning set; encoded as the
  single `C : Set Node` argument with a single `hC : C ⊆ ↑G.J ∪
  ↑G.V` subset hypothesis, matching `def_3_17`'s
  `IsSigmaBlockedGiven` signature.

## Imports

* `Chapter3_GraphTheory.Section3_3.ISigmaSeparation` —
  `def_3_18`, the σ-separation predicate
  `CDMG.IsISigmaSeparated` and its negation
  `CDMG.IsNotISigmaSeparated`.
* `Chapter3_GraphTheory.Section3_3.SigmaOpenPathsWalks` —
  `claim_3_23` (`prp:sigma_opens`), the three-way TFAE between
  σ-open path / σ-open walk / σ-open walk with all colliders in
  `C`.  Transitively imports `SigmaBlockedWalks`
  (`IsSigmaOpenGiven` / `IsSigmaBlockedGiven`), `CollidersAndNon`
  (`Walk.IsCollider`), and the walk / path machinery from
  `Section3_1.Walks`.
-/

end Causality

namespace Causality

namespace CDMG

-- ## Design choice — section-wide statement context
--
-- *Polymorphic `Node : Type*` with `[DecidableEq Node]`.*  Same
--   chapter-wide convention used by every `CDMG`-opening file in
--   Sections 3.1, 3.2 and 3.3 (`Section3_1/CDMG.lean`,
--   `Section3_1/Walks.lean`, `Section3_3/SigmaBlockedWalks.lean`,
--   `Section3_3/SigmaSeparationSymmetric.lean`,
--   `Section3_3/SigmaOpenPathsWalks.lean`, etc.).  The
--   `IsISigmaSeparated`, `IsNotISigmaSeparated`,
--   `IsSigmaOpenGiven`, `IsSigmaBlockedGiven`, `IsPath`,
--   `IsCollider` predicates referenced in the four theorem
--   signatures below are all parameterised over this same implicit
--   binder block, so the theorems auto-bind these binders into
--   their types.
--
-- *Three-dash `--- start helper` / `--- end helper` markers.*  This
--   `variable` block is statement-typing infrastructure that the
--   wrapped theorem signatures cannot compile without — chapter
--   convention for that kind of declaration is the three-dash helper
--   flavour, distinct from the two-dash main-statement marker used
--   to wrap the theorems themselves.  Matches the marker convention
--   at `claim_3_22`'s `SigmaSeparationSymmetric.lean:78-80` and
--   `claim_3_23`'s `SigmaOpenPathsWalks.lean:116-118`.
-- claim_3_24 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- claim_3_24 --- end helper

-- ref: claim_3_24 (part 1/4) — Rem item 1(a), walks characterisation.
--
-- `A ⊥^iσ_G B | C` is equivalent to "every walk from a node in `A`
-- to a node in `J ∪ B` is `C`-σ-blocked".  This biconditional is
-- the def-unfold of `IsISigmaSeparated`; recorded as a separate
-- theorem for LN fidelity (the LN explicitly lists it as one of
-- two equivalent characterisations).
--
-- ## Design choice — sigma_separation_iff_all_walks_blocked
--
-- *Recorded as a biconditional even though the RHS is the def
--   body.*  The LN's literal "is equivalent to either of the
--   following: (a) every walk … is C-σ-blocked; (b) every path …"
--   commits `(1a)` to the role of one of two equivalent
--   characterisations.  Encoding it as an `Iff` (proof by
--   `Iff.rfl`) preserves that surface reading and lets downstream
--   consumers cite `(1a)` symmetrically with `(1b)` without
--   pattern-matching on a def-unfold.
--
-- *Universal-walk quantifier identical to `IsISigmaSeparated`'s
--   body.*  Same `∀ {u v : Node} (π : Walk G u v), u ∈ A → v ∈
--   (G.J : Set Node) ∪ B → π.IsSigmaBlockedGiven C hC` shape.  The
--   right-endpoint constraint `v ∈ (G.J : Set Node) ∪ B` (rather
--   than `v ∈ B`) is the LN's deliberate asymmetric `J`-inclusion
--   from `def_3_18` item 1, NOT a typo.
--
-- *Alternative considered & rejected: omit the lemma and let
--   downstream consumers `unfold IsISigmaSeparated` directly.*  The
--   LN explicitly *names* (1a) as one of two characterisations on
--   equal footing with (1b); having a named `Iff`-lemma keeps the
--   downstream LN-style citation pattern symmetric between the two
--   sub-items (consumers do not need to know that one is a def-
--   unfold and the other a substantive translation).
--
-- *Trivial proof note.*  Because the RHS is literally the body of
--   `IsISigmaSeparated`, the eventual proof is `Iff.rfl`.  No
--   mathlib reuse here — there is no general-purpose equivalent;
--   this lemma exists purely to expose the def-body as a
--   citable `Iff`.
set_option linter.unusedVariables false in
-- claim_3_24 -- start statement
theorem sigma_separation_iff_all_walks_blocked
    (G : CDMG Node) (A B C : Set Node)
    (hA : A ⊆ ↑G.J ∪ ↑G.V) (hB : B ⊆ ↑G.J ∪ ↑G.V) (hC : C ⊆ ↑G.J ∪ ↑G.V) :
    G.IsISigmaSeparated A B C hA hB hC ↔
      ∀ {u v : Node} (π : Walk G u v),
          u ∈ A → v ∈ (G.J : Set Node) ∪ B → π.IsSigmaBlockedGiven C hC
-- claim_3_24 -- end statement
:= Iff.rfl

-- ref: claim_3_24 (part 2/4) — Rem item 1(b), paths characterisation.
--
-- `A ⊥^iσ_G B | C` is equivalent to "every *path* from a node in
-- `A` to a node in `J ∪ B` is `C`-σ-blocked".  Unlike `(1a)`, this
-- biconditional is *not* the def-unfold: it restricts the
-- universal quantifier to paths, and its non-trivial (⇐) direction
-- routes through `claim_3_23` (`sigma_open_paths_walks`).
--
-- ## Design choice — sigma_separation_iff_all_paths_blocked
--
-- *Universal-path quantifier hoisted into the conclusion.*  The
--   path predicate `π.IsPath` is added as an extra antecedent on
--   the universal (rather than `π` being constrained to a
--   `{ π : Walk … // π.IsPath }` subtype) so the biconditional
--   reads as the LN's "every walk that is a path".  Matches the
--   shape of `claim_3_23`'s variant (1).
--
-- *The (⇐) direction is the non-trivial half.*  Given that every
--   *path* from `A` to `J ∪ B` is blocked, suppose for contradiction
--   `A ⊥^iσ_G B | C` fails — then by `def_3_18` item 2 there exists
--   a *walk* from `A` to `J ∪ B` that is not blocked (i.e., is
--   σ-open).  By `claim_3_23` (1)↔(2) the σ-open walk yields a
--   σ-open *path* with the same endpoints; this path contradicts
--   the universal-path hypothesis.
--
-- *The (⇒) direction is trivial.*  Every path is a walk, so the
--   universal over walks specialises to a universal over paths.
--
-- *Why this characterisation matters in practice (LN's "practice
--   remark"), and why it gets its own theorem rather than being
--   bundled into a TFAE alongside (1a).*  The LN's closing
--   paragraph explicitly motivates (1b): in a finite graph there
--   are only finitely many paths (`def_3_3`/`def:walks` item~v.
--   forbids repeated nodes, bounding path length by
--   `|J ∪ V|`), so "every path is blocked" is the
--   *decidable* / *finite-search* check.  Downstream proofs that
--   need an algorithmic σ-separation oracle pattern-match on this
--   biconditional; bundling it into a TFAE with (1a) would force
--   them to extract via `.out 0 1` and obscure the finiteness story.
--   In Lean we keep the two characterisations as separate named
--   `Iff`s for the same reason.
set_option linter.unusedVariables false in
-- claim_3_24 -- start statement
theorem sigma_separation_iff_all_paths_blocked
    (G : CDMG Node) (A B C : Set Node)
    (hA : A ⊆ ↑G.J ∪ ↑G.V) (hB : B ⊆ ↑G.J ∪ ↑G.V) (hC : C ⊆ ↑G.J ∪ ↑G.V) :
    G.IsISigmaSeparated A B C hA hB hC ↔
      ∀ {u v : Node} (π : Walk G u v),
          π.IsPath → u ∈ A → v ∈ (G.J : Set Node) ∪ B →
          π.IsSigmaBlockedGiven C hC
-- claim_3_24 -- end statement
:= by
  constructor
  · -- (⇒): every walk blocked ⇒ every path blocked.
    intro h u v π _ hu hv
    exact h π hu hv
  · -- (⇐): every path blocked ⇒ every walk blocked.  Contradiction via
    -- the open-walk-to-open-path lift of claim_3_23.
    intro h_paths
    rw [sigma_separation_iff_all_walks_blocked]
    intro u v π hu hv
    by_contra h_nb
    have h_open : π.IsSigmaOpenGiven C hC := by
      refine ⟨?_, ?_⟩
      · intro k vk hvk hcol
        by_contra h_nin
        exact h_nb (Or.inl ⟨k, vk, hvk, hcol, h_nin⟩)
      · intro k vk hvk hbnc
        by_contra h_in
        exact h_nb (Or.inr ⟨k, vk, hvk, hbnc, h_in⟩)
    have hu_mem : u ∈ (↑G.J ∪ ↑G.V : Set Node) := hA hu
    have hv_mem : v ∈ (↑G.J ∪ ↑G.V : Set Node) := by
      rcases hv with h | h
      · exact Or.inl h
      · exact hB h
    have h_tfae := sigma_open_paths_walks G C hC hu_mem hv_mem
    have h_ex_walk : ∃ π' : Walk G u v, π'.IsSigmaOpenGiven C hC := ⟨π, h_open⟩
    obtain ⟨π_p, h_path, h_open_p⟩ := (h_tfae.out 1 0).mp h_ex_walk
    have h_blocked_p : π_p.IsSigmaBlockedGiven C hC := h_paths π_p h_path hu hv
    rcases h_blocked_p with ⟨k, vk, hvk, hcol, hnin⟩ | ⟨k, vk, hvk, hbnc, hin⟩
    · exact hnin (h_open_p.1 k vk hvk hcol)
    · exact (h_open_p.2 k vk hvk hbnc) hin

-- ref: claim_3_24 (part 3/4) — Rem item 2(a), shortest open path
-- exists under σ-non-separation.
--
-- If `A ⊥̸^iσ_G B | C` (the negation of σ-separation, per
-- `def_3_18` item 2), then there exists a `C`-σ-open *path*
-- `π : Walk G u v` with `u ∈ A`, `v ∈ J ∪ B`, AND `π.length` is
-- minimum among the length of all such σ-open paths from `A` to
-- `J ∪ B`.
--
-- ## Design choice — exists_shortest_sigma_open_path
--
-- *Endpoints `u, v` existentialised at the statement surface.*
--   The LN's "there exists a path from a node in `A` to a node in
--   `J ∪ B`" leaves both endpoints as existential witnesses (not
--   fixed by an outer universal); the Lean encoding existentialises
--   `u v : Node` alongside the walk `π : Walk G u v`.  Matches
--   the LN's plain reading.
--
-- *The "(shortest)" qualifier as an inline universal bound on
--   `π.length`.*  Per the addition
--   `[shortest_qualifier_reference_class_ambiguous]`, the witness's
--   length is minimum among the *joint* class of σ-open paths from
--   `A` to `J ∪ B`.  Encoded as
--     `∀ u' v' (π' : Walk G u' v'), <conds on π'> → π.length ≤
--     π'.length`
--   — the universal explicitly runs over *the same conditioned
--   class* (start ∈ A, end ∈ J ∪ B, `π'.IsPath`,
--   `π'.IsSigmaOpenGiven C hC`), so "shortest" is taken within the
--   joint class and not within the wider class of all paths from
--   `A` to `J ∪ B`.
--
-- *Reading (iii) of the LN's "(shortest)" parenthetical is
--   explicitly rejected.*  The LN-critic's wording-check identified
--   three textually-admissible readings of the parenthetical "a
--   (shortest) X"; reading (iii) — "the literal shortest path
--   between `A` and `J ∪ B` (irrespective of openness) is
--   σ-open" — is too strong and false in general (the shortest
--   path between `A` and `J ∪ B` need not be σ-open).  The Lean
--   encoding chooses reading (i)/(ii): the witness exists *and*
--   has minimum length among the σ-open class.  The addition tag
--   pins this down as the authoritative reading.
--
-- *Encoding choice: flat existential, no sigma-types / no
--   `Classical.choose`.*  The five-conjunct existential
--   `∃ u v (π : Walk G u v), <P₁> ∧ <P₂> ∧ <P₃> ∧ <P₄> ∧ <min>`
--   keeps the LN's plain-English "there exists a path satisfying
--   ..." reading visible at the type level.  Alternatives
--   considered and rejected: (i) wrapping the witness in a
--   `MinLengthWitness` structure (would obscure the LN-faithful
--   surface and force every consumer through projection lemmas);
--   (ii) returning a `Classical.choose`-style picked witness
--   (would commit us to a non-constructive proof shape and hide
--   the minimisation contract behind a separate spec lemma).  The
--   flat ∃ is decidable-pattern-friendly and matches `claim_3_23`'s
--   existential shape.
--
-- *Mathlib re-use note.*  No mathlib equivalent exists; this is a
--   bespoke shortest-σ-open-path existential.  Length-minimisation
--   in the proof routes through `Nat.find` on a decidable predicate
--   (see proof strategy below), which is mathlib's idiomatic tool
--   for "pick a minimum-length witness from a non-empty class".
--
-- *Proof strategy (sketch).*  By `def_3_18` item 2 applied to the
--   hypothesis `h`, there exists a walk `π_w : Walk G u v` with
--   `u ∈ A`, `v ∈ J ∪ B`, and `¬ π_w.IsSigmaBlockedGiven C hC` —
--   equivalently, by classical De Morgan, `π_w` is σ-open.  By
--   `claim_3_23` (2)↔(1) we obtain a σ-open *path*
--   `π_p : Walk G u v` with the same endpoints.  Picking a
--   length-minimum element of the *non-empty* set of length-valid
--   σ-open paths from `A` to `J ∪ B` (which `π_p` witnesses is
--   non-empty) yields the asserted shortest witness — well-founded
--   by `Nat.find` on the predicate "there exists a σ-open path of
--   length `m` from `A` to `J ∪ B`".
set_option linter.unusedVariables false in
-- claim_3_24 -- start statement
theorem exists_shortest_sigma_open_path
    (G : CDMG Node) (A B C : Set Node)
    (hA : A ⊆ ↑G.J ∪ ↑G.V) (hB : B ⊆ ↑G.J ∪ ↑G.V) (hC : C ⊆ ↑G.J ∪ ↑G.V)
    (h : G.IsNotISigmaSeparated A B C hA hB hC) :
    ∃ (u v : Node) (π : Walk G u v),
        u ∈ A ∧
        v ∈ (G.J : Set Node) ∪ B ∧
        π.IsPath ∧
        π.IsSigmaOpenGiven C hC ∧
        (∀ (u' v' : Node) (π' : Walk G u' v'),
            u' ∈ A → v' ∈ (G.J : Set Node) ∪ B →
            π'.IsPath → π'.IsSigmaOpenGiven C hC →
            π.length ≤ π'.length)
-- claim_3_24 -- end statement
:= by
  -- Step 1: Extract a σ-open walk witness from h : IsNotISigmaSeparated.
  have h_exists_walk : ∃ (u v : Node) (π : Walk G u v),
      u ∈ A ∧ v ∈ (G.J : Set Node) ∪ B ∧ π.IsSigmaOpenGiven C hC := by
    by_contra h_ne
    apply h
    rw [sigma_separation_iff_all_walks_blocked]
    intro u v π hu hv
    by_contra h_nb
    apply h_ne
    refine ⟨u, v, π, hu, hv, ?_, ?_⟩
    · intro k vk hvk hcol
      by_contra h_nin
      exact h_nb (Or.inl ⟨k, vk, hvk, hcol, h_nin⟩)
    · intro k vk hvk hbnc
      by_contra h_in
      exact h_nb (Or.inr ⟨k, vk, hvk, hbnc, h_in⟩)
  obtain ⟨u₀, v₀, π₀, hu₀, hv₀, h_open_w⟩ := h_exists_walk
  -- Step 2: endpoint memberships for claim_3_23.
  have hu₀_mem : u₀ ∈ (↑G.J ∪ ↑G.V : Set Node) := hA hu₀
  have hv₀_mem : v₀ ∈ (↑G.J ∪ ↑G.V : Set Node) := by
    rcases hv₀ with h | h
    · exact Or.inl h
    · exact hB h
  -- Step 3: apply claim_3_23 (2)↔(1) to extract a σ-open path.
  have h_tfae := sigma_open_paths_walks G C hC hu₀_mem hv₀_mem
  have h_ex_w : ∃ π' : Walk G u₀ v₀, π'.IsSigmaOpenGiven C hC := ⟨π₀, h_open_w⟩
  obtain ⟨π_p, h_path, h_open_p⟩ := (h_tfae.out 1 0).mp h_ex_w
  -- Step 4: pick the minimum length via Nat.find.
  classical
  let P : ℕ → Prop := fun m =>
    ∃ (u v : Node) (π : Walk G u v),
      u ∈ A ∧ v ∈ (G.J : Set Node) ∪ B ∧
      π.IsPath ∧ π.IsSigmaOpenGiven C hC ∧ π.length = m
  have h_ne : ∃ m, P m :=
    ⟨π_p.length, u₀, v₀, π_p, hu₀, hv₀, h_path, h_open_p, rfl⟩
  obtain ⟨u_s, v_s, π_s, hu_s, hv_s, hpath_s, hopen_s, h_len_s⟩ :
      P (Nat.find h_ne) := Nat.find_spec h_ne
  refine ⟨u_s, v_s, π_s, hu_s, hv_s, hpath_s, hopen_s, ?_⟩
  intro u' v' π' hu' hv' hpath' hopen'
  have h_pl : P π'.length :=
    ⟨u', v', π', hu', hv', hpath', hopen', rfl⟩
  have h_le : Nat.find h_ne ≤ π'.length := Nat.find_le h_pl
  rw [h_len_s]
  exact h_le

-- ref: claim_3_24 (part 4/4) — Rem item 2(b), shortest open walk
-- with all colliders in `C` exists under σ-non-separation.
--
-- If `A ⊥̸^iσ_G B | C`, then there exists a `C`-σ-open *walk*
-- `π : Walk G u v` with `u ∈ A`, `v ∈ J ∪ B`, every collider of
-- `π` lying in `C` (not merely in `Anc^G(C)`), AND `π.length` is
-- minimum among the length of all such walks (σ-open ∧ all
-- colliders in `C`) from `A` to `J ∪ B`.
--
-- ## Design choice — exists_shortest_sigma_open_walk_colliders_in_C
--
-- *Witness shape mirrors `claim_3_23`'s variant (3).*  The
--   "σ-open AND all colliders in `C`" predicate is encoded
--   verbatim as
--     `π.IsSigmaOpenGiven C hC ∧
--      (∀ (k : ℕ) (vk : Node), π.vertices[k]? = some vk →
--          π.IsCollider k → vk ∈ C)`
--   — identical to the third clause of `sigma_open_paths_walks`'s
--   TFAE.  The conjunction is a *strict strengthening* of σ-
--   openness (the σ-open clause only demands `vk ∈ Anc^G(C)`, per
--   `def_3_17`); the additional clause demands `vk ∈ C` itself.
--   See the LN-critic subtlety
--   `walk_colliders_strictly_in_C_is_strengthening_not_translation`.
--
-- *The "(shortest)" qualifier as an inline universal bound over
--   the joint class.*  Per the addition
--   `[shortest_qualifier_reference_class_ambiguous]`, the witness's
--   length is minimum among the *joint* class of σ-open walks
--   with all colliders in `C` from `A` to `J ∪ B` (NOT within the
--   wider class of σ-open walks alone — under which the witness
--   would not necessarily have all colliders in `C`).  Encoded as
--     `∀ u' v' (π' : Walk G u' v'), <conds on π'> → π.length ≤
--     π'.length`
--   with the same four-conjunct condition on `π'`.
--
-- *No `IsPath` clause on the witness or in the minimisation
--   class.*  The LN's item 2(b) does NOT require the witness walk
--   to be a path (in contrast to 2(a) for paths); accordingly, the
--   minimisation runs over *walks* with all colliders in `C`,
--   which is a strictly wider class than the paths in 2(a).  The
--   shortest witness here may therefore have length strictly less
--   than the shortest path of 2(a), or vice versa (a walk with
--   colliders pinned to `C` may have to detour through more
--   nodes than the unconstrained shortest open path).
--
-- *Alternative considered & rejected: relax the "all colliders
--   in `C`" clause and have (2b) assert only the existence of a
--   shortest σ-open walk.*  Reading the LN's "such that all its
--   colliders lie in `C`" as a derivable property of σ-openness
--   (rather than as an independent conjunct) would be a
--   *weakening* of the asserted existential: σ-openness only
--   forces colliders into `Anc^G(C)`, not into `C` itself.  The
--   LN-critic subtlety
--   `walk_colliders_strictly_in_C_is_strengthening_not_translation`
--   identified this as a substantive strengthening; encoding the
--   collider-in-`C` clause as an inline conjunct keeps that
--   strengthening visible at the type level and matches the body
--   of `claim_3_23`'s variant (3) (which is the proof's pivot).
--
-- *Encoding choice: same flat existential as (2a), no
--   `Walk.AllCollidersIn` helper.*  The "all colliders in `C`"
--   predicate is a single-line universal
--   `∀ k vk, π.vertices[k]? = some vk → π.IsCollider k → vk ∈ C`;
--   extracting it as a named `Walk.AllCollidersIn` helper was
--   considered and rejected — worker-prompt rule "single-line
--   universal predicates do not earn helper extraction".  A later
--   refactor lifting the helper is trivial if a downstream row
--   needs it as an independent hypothesis.
--
-- *Proof strategy (sketch).*  Same shape as `(2a)`'s sketch but
--   routed through `claim_3_23` (2)↔(3) instead of (2)↔(1).
--   Negation of `IsISigmaSeparated` gives a σ-open walk; (2)→(3)
--   produces a σ-open walk with all colliders in `C`; `Nat.find`
--   on the predicate "there exists a σ-open walk of length `m`
--   from `A` to `J ∪ B` with all colliders in `C`" picks out the
--   minimum-length element.
set_option linter.unusedVariables false in
-- claim_3_24 -- start statement
theorem exists_shortest_sigma_open_walk_colliders_in_C
    (G : CDMG Node) (A B C : Set Node)
    (hA : A ⊆ ↑G.J ∪ ↑G.V) (hB : B ⊆ ↑G.J ∪ ↑G.V) (hC : C ⊆ ↑G.J ∪ ↑G.V)
    (h : G.IsNotISigmaSeparated A B C hA hB hC) :
    ∃ (u v : Node) (π : Walk G u v),
        u ∈ A ∧
        v ∈ (G.J : Set Node) ∪ B ∧
        π.IsSigmaOpenGiven C hC ∧
        (∀ (k : ℕ) (vk : Node),
            π.vertices[k]? = some vk → π.IsCollider k → vk ∈ C) ∧
        (∀ (u' v' : Node) (π' : Walk G u' v'),
            u' ∈ A → v' ∈ (G.J : Set Node) ∪ B →
            π'.IsSigmaOpenGiven C hC →
            (∀ (k : ℕ) (vk : Node),
                π'.vertices[k]? = some vk → π'.IsCollider k → vk ∈ C) →
            π.length ≤ π'.length)
-- claim_3_24 -- end statement
:= by
  -- Step 1: Extract a σ-open walk witness from h : IsNotISigmaSeparated.
  have h_exists_walk : ∃ (u v : Node) (π : Walk G u v),
      u ∈ A ∧ v ∈ (G.J : Set Node) ∪ B ∧ π.IsSigmaOpenGiven C hC := by
    by_contra h_ne
    apply h
    rw [sigma_separation_iff_all_walks_blocked]
    intro u v π hu hv
    by_contra h_nb
    apply h_ne
    refine ⟨u, v, π, hu, hv, ?_, ?_⟩
    · intro k vk hvk hcol
      by_contra h_nin
      exact h_nb (Or.inl ⟨k, vk, hvk, hcol, h_nin⟩)
    · intro k vk hvk hbnc
      by_contra h_in
      exact h_nb (Or.inr ⟨k, vk, hvk, hbnc, h_in⟩)
  obtain ⟨u₀, v₀, π₀, hu₀, hv₀, h_open_w⟩ := h_exists_walk
  -- Step 2: endpoint memberships for claim_3_23.
  have hu₀_mem : u₀ ∈ (↑G.J ∪ ↑G.V : Set Node) := hA hu₀
  have hv₀_mem : v₀ ∈ (↑G.J ∪ ↑G.V : Set Node) := by
    rcases hv₀ with h | h
    · exact Or.inl h
    · exact hB h
  -- Step 3: apply claim_3_23 (2)↔(3) to extract a σ-open walk with all
  -- colliders in C.
  have h_tfae := sigma_open_paths_walks G C hC hu₀_mem hv₀_mem
  have h_ex_w : ∃ π' : Walk G u₀ v₀, π'.IsSigmaOpenGiven C hC := ⟨π₀, h_open_w⟩
  obtain ⟨π_w, h_open_πw, h_colliders_C⟩ := (h_tfae.out 1 2).mp h_ex_w
  -- Step 4: pick the minimum length via Nat.find.
  classical
  let P : ℕ → Prop := fun m =>
    ∃ (u v : Node) (π : Walk G u v),
      u ∈ A ∧ v ∈ (G.J : Set Node) ∪ B ∧
      π.IsSigmaOpenGiven C hC ∧
      (∀ (k : ℕ) (vk : Node),
          π.vertices[k]? = some vk → π.IsCollider k → vk ∈ C) ∧
      π.length = m
  have h_ne : ∃ m, P m :=
    ⟨π_w.length, u₀, v₀, π_w, hu₀, hv₀, h_open_πw, h_colliders_C, rfl⟩
  obtain ⟨u_s, v_s, π_s, hu_s, hv_s, hopen_s, hcolc_s, h_len_s⟩ :
      P (Nat.find h_ne) := Nat.find_spec h_ne
  refine ⟨u_s, v_s, π_s, hu_s, hv_s, hopen_s, hcolc_s, ?_⟩
  intro u' v' π' hu' hv' hopen' hcolc'
  have h_pl : P π'.length :=
    ⟨u', v', π', hu', hv', hopen', hcolc', rfl⟩
  have h_le : Nat.find h_ne ≤ π'.length := Nat.find_le h_pl
  rw [h_len_s]
  exact h_le

end CDMG

end Causality
