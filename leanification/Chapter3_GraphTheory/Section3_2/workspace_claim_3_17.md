# Workspace for claim_3_17 — MarginalizationsCommute

## Spec summary

LN tex block (verbatim):
```
\begin{Lem}[Marginalizations commute]\label{marginalizations-commute}
      Let $G=(J,V,E,L)$ be a CDMG and $W_1, W_2 \ins V$ two disjoint subsets of output nodes.
      Then we have:
      \[ \lp G^{\sm W_1} \rp^{\sm W_2} = \lp G^{\sm W_2} \rp^{\sm W_1} =  G^{\sm (W_1 \cup W_2)}. \]
\end{Lem}
```

- `addition_to_the_LN` = `""` (empty) — the literal LN is authoritative.
- Working-phase wording-check returned `NO_SUBTLETIES`.

## Key context

- The marginalization operator `G.marginalize W hW : CDMG Node` is the `def_3_14`
  formalisation living at `Section3_2/MarginalizationAK.lean`. It takes
  `(G : CDMG Node) (W : Finset Node) (hW : W ⊆ G.V)` and returns a CDMG with
  - `J := G.J`, `V := G.V \ W`,
  - `E := ((G.J ∪ (G.V \ W)) ×ˢ (G.V \ W)).filter (G.MarginalizationΦE W)`,
  - `L := ((G.V \ W) ×ˢ (G.V \ W)).filter (fun e => e.1 ≠ e.2 ∧ G.MarginalizationΦL W)`.
- `MarginalizationΦE` = ∃ directed walk through `W`, length ≥ 1, self-cycle ⇒ length ≥ 2.
- `MarginalizationΦL` = symmetrised `∃ bifurcation through W` (Or over both walk orientations).

## Typing subtleties for the formalisation

To state `(G.marginalize W₁ hW₁).marginalize W₂ hW₂` we need:
- `hW₁ : W₁ ⊆ G.V`
- `hW₂ : W₂ ⊆ (G.marginalize W₁ hW₁).V = G.V \ W₁`
  — derivable from `W₁ ∩ W₂ = ∅` (Disjoint W₁ W₂) and `W₂ ⊆ G.V`.

Mirror: `(G.marginalize W₂ hW₂').marginalize W₁ hW₁'`.

Joint: `G.marginalize (W₁ ∪ W₂) hW₁₂`.

The claim is a triple equality of `CDMG Node` values. Equality at the level of
the `structure` should reduce (via `CDMG.ext` or a per-field decomposition) to:
- `J` agree (all = `G.J`, immediate);
- `V` agree (need `G.V \ W₁ \ W₂ = G.V \ W₂ \ W₁ = G.V \ (W₁ ∪ W₂)` — `Finset` set algebra);
- `E` agree (the substantive walk-concatenation argument);
- `L` agree (the substantive bifurcation-substitution argument).

## Plan (claim row, two managers)

**Manager A — statement only:**
1. `spawn_agent_sub_task` → `formalize_claim_in_tex` to rewrite
   `claim_3_17_statement_MarginalizationsCommute.tex` integrating the typing
   subtleties (disjointness + subset preconditions for nested marginalizations)
   and translating `\lp G^{\sm W_1} \rp^{\sm W_2}` into set-theoretic phrasing.
2. `verify_tex_statement_only` — structural.
3. `verify_tex_statement_equivalence` — semantic vs LN.
4. `spawn_agent_sub_task` → `formalize_claim_in_lean` for the theorem signature
   (with `sorry` body). Likely two equalities chained via `And`, or a single
   `theorem` whose statement is `(G.marginalize W₁ hW₁).marginalize W₂ hW₂ = … = …`.
5. `review_design` — natural Lean shape.
6. `verify_equivalence` — friendly.
7. (recommended) `verify_equivalence_strict` early — catches CONTENT deviations.
8. `add_design_choice_comments` — write the *why*.
9. `new_manager` — handoff to Manager B.

**Manager B — proof:**
10. `spawn_agent_sub_task` → `write_tex_proof`. The LN actually CONTAINS a
    `\Claude{}` proof immediately after the claim (graphs.tex lines 1006-1118).
    The worker should sync the statement and copy/adapt this LN proof. Key
    structure: prove `(G^{\sm W_1})^{\sm W_2} = G^{\sm (W_1 \cup W_2)}` first
    (symmetry gives the other equality). Split into J, V, E, L. The E case
    uses walk concatenation/extraction; the L case uses bifurcation
    substitution with a left-arm/right-arm/hinge decomposition.
11. `verify_tex_statement_plus_proof` — structural.
12. `verify_tex_proof` — math check.
13. `spawn_agent_sub_task` → `prove_claim_in_lean`. This will need walk
    concatenation infrastructure — much of which `MargPreservesAncestors.lean`
    already developed as `private def Walk.comp`, `Walk.length_comp`,
    `Walk.isDirectedWalk_comp`, `Walk.vertices_comp` (lines 128-171). Reuse
    those (probably needs to lift them out of `private`, or re-derive them
    locally).
14. `solved` → `verify_row_solved` + sorry-check + strict-equivalence gate.

## Tries log

- T1: `formalize_claim_in_tex` → rewrote `claim_3_17_statement_MarginalizationsCommute.tex` integrating typing/disjointness preconditions; compiles standalone.
- T2: `verify_tex_statement_only` → PASS (structural).
- T3: `verify_tex_statement_equivalence` → PASS (semantic vs LN).
- Next: `formalize_claim_in_lean` for the theorem signature (with `sorry`).

---
## Run summary -- 2026-06-13T05:17:24+00:00
**Reason for stop:** REFACTOR REQUESTED -- the manager called the
(advisory) refactor planner. No rows were reset; no Lean files deleted; the original chapter's
data.json is unchanged. To execute the refactor:
  plan markdown: leanification/refactors/refactor_marginalize_loose_self_cycle.md
  1. switch to the server branch:
       git checkout server_setting_up_scaffold
  2. launch the refactor pipeline:
       python extras/do_refactor.py init --chapter 3 --root-ref def_3_14 --name marginalize_loose_self_cycle
  3. drive the refactor table:
       python scaffold/scripts/phase3_solving/solve_chapter.py --data-path <refactor_data.json>
  4. once every refactor row is solved=yes, finalize:
       python extras/do_refactor.py finalize --refactor-data <path>
  5. merge back into the server branch:
       python extras/do_refactor.py merge --refactor-data <archived path> --push --delete-remote-branch

**Turns this run:** 5
**Elapsed:** 82.9 min
**Row state at exit:** formalized=no proven=not proven solved=no

### Action sequence
    8. new_manager               fresh manager taking over.
    9. spawn_agent_sub_task      Both jobs done in one write to `tex/claim_3_17_proof_MarginalizationsCommute.tex`.

**Job 1 — statement sync:** Replaced the raw LN `\begin{Lem}...\end{Lem}` block with the canonical statement body...
   10. verify_tex_statement_plus_proof  Reading the file to verify structure.

Structural check results:

1. **Statement block at top**: `\begin{Lem}[Marginalizations commute]\label{marginalizations-commute}` at line 33, `\end{Lem}` at l...
   11. verify_tex_proof          I now have enough to issue a verdict. Let me finalize the analysis.

## Walk-through summary

**Items 1–6, 8 (pass):**
- File name `claim_3_17_proof_MarginalizationsCommute.tex` starts with the rig...
   12. refactor                  Plan written. Report:

```
REFACTOR_PLAN_FILE: leanification/refactors/refactor_marginalize_loose_self_cycle.md
ROOT_REF: def_3_14
ROOT_CHAPTER: 3
NAME: marginalize_loose_self_cycle
RECOMMENDED_INV...

### Latest verifier verdicts
  (none captured)

### Resumable past agents (most recent 10)
  - add_design_choice_comments  id=befe613c-4e5e-4138-8b84-fbb3fef73440  last=2026-06-13T04:23:42+00:00
  - manager                   id=0fe419f9-4abf-4617-b2eb-a5bda9ef1504  last=2026-06-13T04:24:44+00:00
  - manager                   id=65751c42-cd32-4000-a2a3-aeb37ca155cf  last=2026-06-13T04:25:56+00:00
  - spawn_agent_sub_task      id=13de7aea-86cf-4e80-a0fd-8adb2171f66d  last=2026-06-13T04:27:44+00:00
  - manager                   id=e2f734ab-b741-442c-941a-1b54b778a375  last=2026-06-13T04:28:02+00:00
  - verify_tex_statement_plus_proof  id=0f397414-864f-423a-b68a-3235817b9539  last=2026-06-13T04:28:25+00:00
  - manager                   id=ba7e31b9-e39c-41c0-b4d8-d17afd81b75a  last=2026-06-13T04:29:17+00:00
  - verify_tex_proof          id=5d7a989b-ca38-4693-b1ec-4bbced362911  last=2026-06-13T05:08:27+00:00
  - manager                   id=325753a5-aff3-4759-80ee-f5f23b3cc287  last=2026-06-13T05:12:03+00:00
  - refactor                  id=e98d758e-676a-4db8-8ef9-08c011ed7356  last=2026-06-13T05:17:24+00:00

### What the next manager should NOT repeat
_(Auto-recorded section. The next manager may overwrite this with a
sharper diagnosis once it has read above. The bullets below are a
heuristic from the action sequence -- treat them as hypotheses, not facts.)_
- Actions emitted this run, in order, are listed above. Re-running the
  same sequence is unlikely to help -- pick a different angle.
- If a verifier last reported FAIL, the feedback was inside its
  `BEGIN[feedback]…END[feedback]` block; read your history before
  dispatching the same verifier again.
- If you want to talk to a specific past agent, use `continue_agent`
  with one of the session ids above instead of spawning fresh.
