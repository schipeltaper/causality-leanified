# Workspace for def_3_5 — FamilyRelationships

## Scope of the LN block

`def_3_5` is a single `\begin{Def}` block listing **eight family-relationship
operators** in a CDMG `G = (J, V, E, L)`, each with a vertex-input variant
and (almost always) a set-input variant. Specifically:

1. **Parents** `Pa^G(v) := {w ∈ G | w ⟶[G] v}` and `Pa^G(A) := ⋃_{v∈A} Pa^G(v)`
2. **Children** `Ch^G(v) := {w ∈ G | v ⟶[G] w}` and `Ch^G(A)`
3. **Siblings** `Sib^G(v) := {w ∈ G | v ⟷[G] w}` (vertex only; no set variant
   in the LN)
4. **Ancestors** `Anc^G(v) := {w ∈ G | ∃ directed walk w ⟶ … ⟶ v}` and
   `Anc^G(A)`; note `v ∈ Anc^G(v)` (trivial walk), and `A ⊆ Anc^G(A)`
5. **Descendants** `Desc^G(v)`, `Desc^G(A)`; same reflexivity notes
6. **Non-descendants** `NonDesc^G(A) := (J ∪ V) \ Desc^G(A)` (set-only)
7. **Strongly connected component** `Sc^G(v) := Anc^G(v) ∩ Desc^G(v)` and
   `Sc^G(A)`; note `v ∈ Sc^G(v)`
8. **District** `Dist^G(v) := {w ∈ G | ∃ bidirected walk v ⟷ v_1 ⟷ … ⟷ w}`
   and `Dist^G(A)`; note `v ∈ Dist^G(v)`

The `\PF{...}` commented-out variants for parents-of-a-set and the
Markov-blanket items in the LN block are commented out in the source —
the instructions say "Skip the comments! only what is rendered", so we
exclude them. Only what is rendered between `\begin{Def}` and `\end{Def}`,
ignoring `%` lines, is formalised.

## Underpinnings already in place

- `CDMG` structure with `J, V, E, L` fields (`CDMG.lean`)
- Membership `v ∈ G` ↔ `v ∈ G.J ∪ G.V` (`CDMGNotation.lean`)
- Arrow notations `v ⟶[G] w` (directed), `v ⟷[G] w` (bidirected)
- `Walk G v w` data type with `nil` / `cons` (`Walks.lean`)
- `Walk.IsDirected` and `Walk.IsBidirected` predicates
  (`WalkPredicates.lean`) — these are *exactly* what we need for ancestors,
  descendants, district. The directed-walk reflexivity note
  (`v ∈ Anc^G(v)`) follows from `Walk.nil v` being trivially `IsDirected`.

## Plan

Single new Lean file: `FamilyRelationships.lean` (might need to split if it
exceeds ~700 lines; natural split points would be Direct/Reachability/District).
For each operator: a `def` with a comment block in our usual format (`-- ref:`,
"title:", verbatim LN snippet between `/- -/`, design-choice note, docstring).
For the membership notes the LN flags (e.g. `v ∈ Anc^G(v)`, `A ⊆ Anc^G(A)`),
add a `theorem` next to each so the LN's "Note: …" lines have a Lean
counterpart that downstream rows can cite.

## Progress

- [x] Formalize all eight operators — `FamilyDirect.lean` (Pa/PaSet, Ch/ChSet, Sib), `FamilyReachability.lean` (Anc/AncSet, Desc/DescSet, NonDesc, Sc/ScSet, plus 6 reflexivity thms), `FamilyDistrict.lean` (Dist/DistSet, plus 2 reflexivity thms). All in `Causality.CDMG` namespace.
- [ ] `review_design` — full-LN-context check (dispatched)
- [ ] `verify_equivalence` — Lean-vs-LN statement check
- [ ] `solved` → `verify_row_solved`

## Worker session ids

- formalizer (turn 1): `cd89c47d-aa17-4b14-b8c6-2902a3f8a73d`
