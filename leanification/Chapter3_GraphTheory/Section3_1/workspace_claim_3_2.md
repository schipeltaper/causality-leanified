# Workspace -- claim_3_2 (refactor: claim_3_2_no_finite)

## Row at a glance

- **Refactor name:** `claim_3_2_no_finite`, **root ref:** `claim_3_2`.
- **Goal:** remove `[Finite α]` from `theorem isAcyclic_iff_hasTopologicalOrder`.
- **LN statement (`graphs.tex` 222--226):** "A CDMG G=(J,V,E,L) is acyclic iff it has a topological order." -- no finiteness.
- **Why the refactor:** the LN statement itself has no finiteness hypothesis. The existing Lean carried `[Finite α]` only because the LN proof's iterative parent-free-node route needs it, but our Lean proof has always used Szpilrajn (`extend_partialOrder`) which doesn't. So dropping `[Finite α]` aligns with both the LN statement and what our proof actually shows -- and lifts the same baggage off every downstream consumer (claim_3_6, _12, _16, _17, _18, _19, _23, _27 in this refactor table).

## Files involved

- **Lean:** `leanification/Chapter3_GraphTheory/Section3_1/AcyclicIffTopologicalOrder.lean`
  - ORIGINAL block lines 168--402 (`theorem isAcyclic_iff_hasTopologicalOrder [Finite α] ...`)
  - REPLACEMENT block lines 404--590 (`theorem refactor_isAcyclic_iff_hasTopologicalOrder ...`)
  - Proof body of replacement is character-identical to original (Szpilrajn route)
- **Tex (original, do NOT edit):** `tex/claim_3_2_proof_AcyclicIffTopologicalOrder.tex` -- LN iterative-construction proof verbatim.
- **Tex twin (TO CREATE):** `tex/refactor_claim_3_2_proof_AcyclicIffTopologicalOrder.tex`. Must match the Szpilrajn route the Lean uses (the LN's iterative proof presupposes finiteness, contradicting the new finiteness-free statement).

## Plan

1. **review_design** -- full-LN-context check that the no-finiteness shape is natural. Verifier should look at downstream consumers (esp. the iSCM rows that wanted `[Finite α]` lifted) and judge the trade-off.
2. **verify_equivalence** -- focused check that the Lean statement `G.IsAcyclic ↔ G.HasTopologicalOrder` (no finiteness) matches the LN's `\begin{Lem}...A CDMG G=(J,V,E,L) is acyclic if and only if it has a topological order.\end{Lem}`. Should be straightforward -- the LN itself has no finiteness in the statement.
3. **add_design_choice_comments** -- the formalize worker already wrote a substantial design block (lines 405--520), but enrich with anything review_design / verify_equivalence surface.
4. **new_manager** handoff -- proof phase. Tex twin work is light because the Lean proof is already done.
5. **Proof phase (next manager):**
   - `spawn_agent_sub_task` -> `write_tex_proof.md` targeting the twin file; write the Szpilrajn route (matches the Lean), with a note that the LN's iterative proof (preserved in the original tex file) is a valid alternative for the finite case.
   - `verify_tex_proof` against the twin
   - (Lean proof is already in place; skip `prove_claim_in_lean`.)
   - `simplify_proof` against the replacement block
   - `solved` (strict-equivalence gate will check the replacement vs LN)

## Tried / done

- Turn 1 (`spawn_agent_sub_task` -> `formalize_claim_in_lean.md`): SUCCEEDED. Replacement block in place (lines 404--590), lake build clean per worker report. Proof character-identical to original (Szpilrajn route, finiteness-free).
- Turn 2 (`review_design`): **PASS**. Verifier confirmed the no-finiteness shape is faithful to the LN statement and explicitly noted `Section3_2/SplitTopologicalOrder.lean:42-53` already foreshadowed this refactor (claim_3_6 part B kept `[Finite α]` off, citing the Szpilrajn route on this iff).
- Turn 3 (`verify_equivalence`): **PASS**. Friendly check confirmed `G.IsAcyclic ↔ G.HasTopologicalOrder` matches LN exactly; no hidden hypotheses on either side; no finiteness mention in LN.
- Turn 4 (`add_design_choice_comments`): DONE. Tightened the WHY block in the REPLACEMENT (lines ~432-446): shortened the duplicate technical description of Szpilrajn, forward-referenced bullet 3, and kept the downstream-beneficiaries list (claim_3_6 part B + iSCM consumers). Build clean.
- Turn 5 (`new_manager`): handoff to proof manager.
- Turn 6 (`spawn_agent_sub_task` -> `write_tex_proof.md`): DONE. Tex twin written at `tex/refactor_claim_3_2_proof_AcyclicIffTopologicalOrder.tex` (101 lines). Mirrors the Lean replacement: (i) explanatory intro re route change, (ii) ⇐ direction copied/lightly-edited from LN (parent-lt chain on cycle, transitivity collapse), (iii) ⇒ direction via reachable-by-directed-walk preorder $r_0$ + Szpilrajn (`extend_partialOrder`), with antisymmetry derived from acyclicity + $E \subseteq (J \cup V) \times V$ from def_3_1.
- Turn 7 (`verify_tex_proof`): **PASS**. Verifier confirmed all checklist items: filename per twin convention, claim restated verbatim, strategy stated, no `sorry`/"omitted"/"obvious", all citations (def_3_1, def_3_6, def_3_8) valid.
- **Next: `simplify_proof` on the REPLACEMENT block (lines 404-590).**

## Open questions / risks

- **Tex twin: Szpilrajn or LN-iterative?** Going with Szpilrajn in the twin (matches Lean). LN's iterative proof would contradict the no-finiteness statement (it explicitly cites "since `G_i` is acyclic and finite"). The LN's proof stays preserved verbatim in the *original* tex (which is on disk until Phase 7 cleanup), so nothing is lost.
- **Strict-equivalence gate (at `solved`):** the gate checks Lean-vs-LN. The LN statement and the Lean replacement statement are both finiteness-free, so this should pass cleanly.
