# Appendix — first-attempt manager workspace for `def_3_14_no_L_exclusion`

**Provenance:** verbatim copy of `leanification/Chapter3_GraphTheory/Section3_2/workspace_def_3_14.md`
from the discarded branch `refactor_def_3_14_no_L_exclusion` (HEAD `d54899f`,
2026-05-31). The follow-up Path α / Path δ analysis (which extended this
workspace by another 374 lines after the commit) is preserved in
`appendix_path_alpha_genwalk_analysis.md`.

**Why preserved:** §C-E include detailed engineering cost breakdowns
of three alternatives not covered in the polished article (§D's Sym2,
bundled-output, predicate-lift alternatives; §E's additional
priority-L counter-evidence; §G's row-ordering proposal for Path α).
For the polished diagnosis and conclusions, read
`02_CDMG_disjoint_EL_refactor_needed.tex` first; this appendix is
the raw analysis it was distilled from.

---

# Workspace for def_3_14 -- MarginalizationAK (REFACTOR `def_3_14_no_L_exclusion`)

## Refactor goal (from `.refactor_state.json` + deviations.json)

Resolve these four deviations:
- `def_3_14_marginalize_L_excludes_E`        -- root: L^{sm W} drops literal LN
  pairs because of two `¬ ∃ directed walk` exclusion clauses
- `def_3_14_l_w_membership_in_marginalization` -- companion observation by
  the auditor (same deviation, more detail; cites
  `def_3_1.CDMG.disjoint_EL` as the *forcing culprit*)
- `claim_3_16_with_source_bifurcation_deferred` -- with-source iff is
  deferred because the exclusion can flip a no-source bifurcation in G
  into a with-source bifurcation in G^{sm W}
- `claim_3_25_the_lean_file_does_not_formalise_the_ln` -- the Lean file
  proves the *negation* of the LN's iff (a counter-example fabricated
  precisely from the L-exclusion deviation)

## Refactor scope (rows in `Refactor_def_3_14_no_L_exclusion/refactor_data.json`)

- def_3_14 (this row, root)             -- Section3_2/Marginalization.lean
- claim_3_16 MarginalizationPreserves   -- Section3_2/MarginalizationPreserves.lean
- claim_3_17 MarginalizationsCommute    -- Section3_2/MarginalizationsCommute.lean
- claim_3_18 MarginalizationAndIntervention -- Section3_2/MarginalizationAndIntervention.lean
- claim_3_19 MarginalizingOutSplitOutput -- Section3_2/MarginalizingOutSplitOutput.lean
- def_3_18  ISigmaSeparation            -- Section3_3/ISigmaSeparation.lean
- claim_3_25 ISigmaSeparation           -- Section3_3/ISigmaSeparationMarginalization.lean
                                           (+ SigmaOpenWalkMarginalization.lean)

Note: **def_3_1.CDMG is NOT in the refactor scope.** The cascade analysis in
`Documenting Progression/01_disjoint_EL_cascade.tex` explicitly identifies
def_3_1's `disjoint_EL` field as the upstream cause.

## My analysis of the design space (turn 1)

The LN's `L^{sm W}` is defined as: all unordered bidirected pairs {u,v} with
u, v ∈ V\W, u ≠ v, such that a bifurcation through W exists in G. The LN
treats L as a quotient `V × V / ~` (different ambient type from E), so
L^{sm W} can freely contain pairs that are also in E^{sm W} -- no conflict.

Our Lean encoding has `E, L : Set (α × α)` with `disjoint_EL : Disjoint E L`.
A pair (u, v) cannot be in both literally. Where the LN has a collision
(both LN-directed-edge and LN-bidirected-edge between (u, v)), we must
project to one or the other.

**Possible encodings within the refactor scope (no def_3_1 change):**

1. **Priority-E (current code).** L^{sm W}_lean excludes pairs already in
   E^{sm W} (in either direction). Matches LN E^{sm W} literally; deviates
   from LN L^{sm W}. Breaks claim_3_25 (LN proof reroutes a fork into a
   bidirected edge that's not in our L^{sm W}). The current 6-row cascade.

2. **Priority-L (the obvious "no_L_exclusion" interpretation).** L^{sm W}_lean
   matches LN literally; tighten E^{sm W} to exclude pairs where a
   bifurcation through W exists. Matches LN L^{sm W} literally; deviates
   from LN E^{sm W}. **Breaks claim_3_16 item 1 (marginalize preserves
   ancestors): a pair (u, v) with both a directed walk and a bifurcation
   through W loses its directed edge in E^{sm W}_lean, so u stops being an
   ancestor of v in G^{sm W}_lean -- contradicting LN.**

3. **Helper lemma only (deviation entry's option (a)).** Keep the encoding,
   add a `marg_bif_exists_iff` lemma that bundles (L^{sm W}_lean ∨
   E^{sm W}_lean ∨ swap E^{sm W}_lean) ↔ "bifurcation between u and v
   through W in G". Doesn't actually remove the L exclusion; the refactor
   name suggests this isn't the intended path.

4. **Refactor def_3_1.CDMG** (out of scope). The cascade doc says this is
   the only structural fix. Options: drop `disjoint_EL`; or move L to a
   different ambient type (`Sym2 α` or wrapped). Touches every CDMG
   constructor in the whole project.

**Why none of (1)/(2)/(3) is a clean "no_L_exclusion":**
- (1) is the current state -- the refactor exists to *change* this.
- (2) literally drops the L exclusion clauses but introduces *equivalent*
  E exclusion clauses; no net "no_L_exclusion" if "exclusion" means
  "structural-disjointness-forced exclusion clause". And it breaks Anc.
- (3) keeps the L exclusion in place.

Only (4) achieves a literal "no exclusion" in either field, and (4) is out
of scope.

**Open question for the planner / human:** does the user intend
"no_L_exclusion" to mean (a) literal removal of the two `¬ ∃ directed walk`
clauses (which requires (4)), or (b) the L^{sm W} side of the
field-balance trade-off (i.e., (2))?

If (a), the refactor scope is wrong and we need to escalate.
If (b), we proceed with (2) and accept the new deviation on E^{sm W}
+ figure out how to repair claim_3_16's `marginalize_ancestor` (probably
by reformulating it to go through bifurcation-existence rather than
literal E membership).

## What I have NOT yet done

- Read the LN proofs of claim_3_16..3_19, def_3_18, claim_3_25 in
  `lecture-notes/lecture_notes/graphs.tex` end-to-end, to see exactly
  which membership facts (E^{sm W} vs L^{sm W}) each proof actually uses.
  This is the key input for choosing between (1)/(2)/(3)/(4).
- Inspect the current Lean of MarginalizationPreserves.lean,
  MarginalizationsCommute.lean, MarginalizationAndIntervention.lean,
  MarginalizingOutSplitOutput.lean, ISigmaSeparation.lean,
  ISigmaSeparationMarginalization.lean, SigmaOpenWalkMarginalization.lean
  to see *exactly* what API surface they consume.

I am about to dispatch `make_plan` with the full context above; the plan
worker will do the deep reads and propose a concrete path.

## Plan from `plan_subtasks` worker, 2026-05-31T15:30:00+00:00

### 1. Assessment of options (A) / (B) / (C) / (D)

I read all five consumer LN proofs end-to-end (`graphs.tex` lines
934-1211, 1416-1579), the current Lean consumer files (especially
`MarginalizationPreserves.lean` lines 3620-3700,
`ISigmaSeparationMarginalization.lean` lines 1450-1510, and
`SigmaOpenWalkMarginalization.lean` `mem_marginalize_L` usage), and
the cascade write-up. The manager's turn-1 framing of the four options
is **correct in shape**, but I refine it below.

The decisive test is **what each LN proof literally does at the
membership level on `E^{\sm W}` vs `L^{\sm W}` for collision pairs**
(pairs `(u, v)` for which both a directed-walk-through-W and a
bifurcation-through-W exist in `G`).

#### The breaking step (LN claim_3_25, `graphs.tex:1559`):

> "Since $b_j \tuh u \tuh w$ is a directed walk through $u$ in $G$,
>  we have $b_j \tuh w \in E^{\sm u}$. **The fork bifurcation
>  $w \ot u \tuh b_{j+1}$ yields $w \huh b_{j+1} \in L^{\sm u}$.**
>  We replace the edge $b_j \tuh b_{j+1}$ in $\pi'$ by
>  $b_j \tuh w \huh b_{j+1}$ ..."

The proof **simultaneously** uses, on the same vertex pair `w`:
- `(b_j, w) ∈ E^{\sm u}`  (directed walk `b_j → u → w`)
- `(w, b_{j+1}) ∈ L^{\sm u}`  (fork bifurcation `w ← u → b_{j+1}`)

In the cascade's counter-example graph, the pair `(w, b_{j+1})` *also*
has a directed walk through `{u}` (`w → u → b_{j+1}`). The LN's
ambient-type separation puts this pair in **both** `E^{\sm u}_LN` and
`L^{\sm u}_LN`. Lean's `disjoint_EL` makes that impossible.

**This is not a presentation issue.** The LN proof literally needs the
*same vertex pair* to be both an E-edge and an L-edge of the
marginalised graph. No Lean encoding that enforces `Disjoint E L` on
the output graph can accept that proof. Helper lemmas cannot help, because
the membership conditions on Lean's `mem_marginalize_L` are
syntactically false on this pair.

#### Companion test (LN claim_3_16 item 1, `graphs.tex:967`):

For the same counter-example, item 1 says `w ∈ Anc^G(b_{j+1}) ⟺
w ∈ Anc^{G^{\sm u}}(b_{j+1})`. In the LN, this is true via
`w → u → b_{j+1}` being a directed walk. Reading
`Anc^{G^{\sm u}}(b_{j+1})` in Lean requires
`(w, b_{j+1}) ∈ (G.marginalize {u}).E`. So the LN forces the same pair
into `E^{\sm u}` *and* `L^{\sm u}`.

#### Per-option verdict:

**(A) priority-E (current code).** Pair goes only to `E^{\sm u}`.
- claim_3_16 item 1 (`marginalize_anc_iff`): ✓ (current code proves it).
- claim_3_16 item 2 (no-source): ✓ via the symmetric-`∨` reading
  (current code proves `marginalize_bifurcation_iff`).
- claim_3_16 item 2 (with-source): ✗ deferred
  (`claim_3_16_with_source_bifurcation_deferred` deviation).
- claim_3_17 (marginalizations commute) / claim_3_18 / claim_3_19: I
  believe these all survive priority-E because they reason at the
  *bifurcation existence* level, not at literal `L^{\sm W}` membership.
  (Their current Lean files exist and consume `mem_marginalize_E` /
  `mem_marginalize_L`; the `_for_website.json` exists for claim_3_17
  but I did not check whether the LN proofs go through. **Not free of
  risk, but no current artefact disproves them.**)
- def_3_18 (`IsISigmaSeparated`): purely structural; ✓.
- claim_3_25: ✗ — actively proves the **negation** of the LN, via the
  `isISigmaSeparated_marginalize_iff_disproved` theorem
  (`ISigmaSeparationMarginalization.lean:1493`). This is the cascade
  the refactor exists to undo.
- **Net: cannot resolve `claim_3_25_the_lean_file_does_not_formalise_the_ln`.**

**(B) priority-L (the literal "no_L_exclusion" code change).** Pair goes
only to `L^{\sm u}`; `E^{\sm u}` gets a symmetric `¬ ∃ bifurcation`
exclusion. Verdict on the same five-claim sweep:
- claim_3_16 item 1 (`marginalize_anc_iff`): ✗ **breaks**. In the
  counter-example, `w` is not an ancestor of `b_{j+1}` in
  `G^{\sm u}_Lean` (no E-edge), but is in `G^{\sm u}_LN`.
- claim_3_16 item 2 (no-source bifurcation iff): probably ✓ via the
  same symmetric-`∨` workaround currently used (the existence on the
  G-side is unchanged; the marg-side now has the bif edge in `L`, no
  longer absorbed via the directed-walk reversal trick).
- claim_3_16 item 2 (with-source): unclear — might *unbreak* if the
  exclusion that forces a source-introduction goes away.
- claim_3_17 (commute): the proof routes through both
  `mem_marginalize_E` and `mem_marginalize_L`. Swapping the
  exclusion side could break it in *new* ways: the `(⇐)` direction at
  `graphs.tex:1105` ("$\beta \huh \gamma \in L^{\sm W_1}$") is now
  available without restriction, but the `(⇒)` direction's
  expansion of an `E^{\sm W_1}` edge into a directed walk requires
  *no bifurcation through W_1* — which is now a new precondition that
  has to hold or block the expansion.
- claim_3_18, claim_3_19: similar — every consumer of the
  `mem_marginalize_E` / `mem_marginalize_L` API would need re-proof
  with the new membership conditions, and some proofs may fail
  symmetrically to how (A) makes claim_3_25 fail.
- claim_3_25: probably ✓ — the LN's `(⇐)` rerouting now succeeds
  because the bidirected edge it constructs *is* in `L^{\sm u}`.
- **Net: undoes claim_3_25's disproof but rebreaks claim_3_16 item 1
  (and possibly claim_3_17). Just shifts the deviation.**

**(C) helper-only.** Keeps priority-E; adds a helper lemma
`marg_bif_exists_iff` bundling
`(p ∈ L^{\sm W}) ∨ (p ∈ E^{\sm W}) ∨ (p.swap ∈ E^{\sm W}) ↔
∃ bifurcation between p.1, p.2 through W`.
- This is what the existing code morally already does via the
  symmetric-`∨` reading; it does *not* unbreak claim_3_25, because the
  Lean `IsISigmaSeparated` predicate (`def_3_18`) routes through
  membership-of-edge predicates on `G^{\sm u}.E` and `G^{\sm u}.L`,
  not through a "bifurcation-exists" abstraction.
- To make claim_3_25 work via (C), one would have to *reformulate*
  `IsISigmaSeparated` itself to be invariant under E↔L collision, or
  reformulate `IsBlockable` / `IsCollider` to consume the abstraction.
  That is a chapter-3 design change of similar magnitude to (D), with
  the added downside of being a *deviation from the LN* (the LN's
  `σ-blocking` definition reads off the edge type at each walk
  position; abstracting the edge-type-at-position requires changing
  `def_3_15` or `def_3_17`).
- **Net: makes no progress on claim_3_25 without further
  structural changes.**

**(D) refactor def_3_1 (drop `disjoint_EL` or restratify L).** Restores
the LN's literal ambient-type separation. Every LN proof goes through
*as written*.
- The cascade doc identifies this as the only fix.
- The impact is much smaller than feared (see §3 below) — about 10
  Lean files in chapter 3, all mechanical.
- **Net: only option that achieves literal LN-faithful encoding.**

#### Summary of the design space

| Option | claim_3_25 | claim_3_16 i.1 | claim_3_16 i.2 ws | LN-faithful? | In scope? |
|---|---|---|---|---|---|
| (A) priority-E | ✗ disproved | ✓ | deferred | partial | ✓ |
| (B) priority-L | ✓ likely | ✗ breaks | maybe ✓ | partial | ✓ |
| (C) helper only | ✗ unchanged | ✓ | deferred | partial | ✓ |
| (D) def_3_1 fix | ✓ | ✓ | ✓ | **literal** | ✗ (out of scope) |

Options (A), (B), (C) just *shift* the deviation. Only (D) removes it.

### 2. Recommendation: **escalate to the human via `request_from_human`**

The refactor as currently scoped (`def_3_14_no_L_exclusion`, 7 rows,
def_3_1 NOT included) **cannot produce a literal LN-faithful encoding**.
The only options actually available inside this scope (B and C) trade
one undesirable deviation for another. None of them are an improvement
over the current state (A).

I therefore recommend the manager emit `request_from_human` after the
gate, with this body:

> The `def_3_14_no_L_exclusion` refactor cannot achieve its stated
> goal (resolving the four deviations
> `def_3_14_marginalize_L_excludes_E`,
> `def_3_14_l_w_membership_in_marginalization`,
> `claim_3_16_with_source_bifurcation_deferred`,
> `claim_3_25_the_lean_file_does_not_formalise_the_ln`) inside its
> current scope. The plan worker confirmed the cascade document
> (`Documenting Progression/01_disjoint_EL_cascade.tex`)'s finding:
> the only LN-faithful fix is upstream in `def_3_1.CDMG`'s
> `disjoint_EL` field, which is not in `refactor_data.json`.
>
> The local option "priority-L" (move the exclusion clauses from
> `L^{\sm W}` to `E^{\sm W}`) is a literal "no_L_exclusion" code
> change but breaks `marginalize_anc_iff` (claim_3_16 item 1) on a
> structurally non-trivial set of inputs (any pair with both a
> directed-walk-through-W and a bifurcation-through-W in G now loses
> its directed edge in the marginalised graph). Helper-lemma-only is
> a no-op that leaves claim_3_25 disproved.
>
> The impact estimate for option (D) is small: `G.disjoint_EL` is used
> as a hypothesis in 5 spots across 4 Lean files (HardInterventionOn,
> ExtendingCDMGsWithInterventionNodes, MarginalizingOutSplitOutput,
> NodeSplittingOn) and as a discharge-of-the-field in ~6 more chapter-3
> Lean files. No file outside chapter 3 uses `disjoint_EL`. The
> refactor would touch ~10 files, all mechanically.
>
> Three options for the human:
>
> 1. **Abandon this refactor and spin up `def_3_1_no_disjoint_EL`**
>    (recommended). Roll back the branch; on `server_setting_up_scaffold`,
>    re-emit `refactor` against def_3_1 with the new scope; let
>    `do_refactor.py init` build the correct transitive table (likely
>    includes def_3_1, def_3_10, def_3_11, def_3_12, def_3_13, def_3_14,
>    def_3_18, claims 3_10..3_25 — basically all of chapter 3 that
>    constructs a CDMG or proves equality of CDMG values).
> 2. **Extend this refactor's scope to include def_3_1** by editing
>    `refactor_data.json` and `.refactor_state.json` directly (requires
>    a fresh dependents scan; bypasses the orchestrator's normal init
>    path). The orchestrator's `refactor` action is blocked inside
>    refactor rows, so the human has to do this manually.
> 3. **Abandon the refactor**, accept the four deviations as long-term
>    documented limitations, and move on.

If the human picks (1) or (2), this row exits via `request_from_human`
and the manager halts.

If the human picks (3), the orchestrator can finalize this refactor as
a no-op for all 7 rows (the originals stay; no replacements are
needed). The four deviations remain registered.

#### Why not just try (B) inside this refactor?

Even setting aside the LN-fidelity argument: priority-L breaks
`marginalize_anc_iff`. That theorem is *the* foundational lemma
claim_3_25's own LN proof cites in its first preparatory fact
(`eq:anc_preserved`, `graphs.tex:1432`). Breaking it doesn't just
break one claim — it leaks into claim_3_25's correctness proof, into
chapter 5's do-calculus Rule 3 proof, and into every downstream lift
that needs ancestor preservation under marginalisation. A new cascade.

### 3. Impact estimate for option (D)

I greppped `\.disjoint_EL` (excluding the `Refactor_def_3_14...`
folder, the audit/deviation/website JSON, and the workspace file)
across `leanification/`:

**Usage as a hypothesis** (5 spots across 4 Lean files):
- `Section3_2/ExtendingCDMGsWithInterventionNodes.lean:291`
- `Section3_2/MarginalizingOutSplitOutput.lean:710`
- `Section3_2/HardInterventionOn.lean:264`
- `Section3_2/NodeSplittingOn.lean:464` (and a comment at line 371)

Each of these is a CDMG constructor proving the output graph satisfies
`disjoint_EL` using the input graph's `disjoint_EL`. If the field
disappears, all 5 sites are simply deleted (no obligation to discharge,
no obligation to prove); they don't carry semantic weight.

**Field discharge `disjoint_EL := by ...`** (one per CDMG constructor):
- `Section3_1/CDMG.lean` (the field itself, 1 line)
- `Section3_2/Marginalization.lean` (~6 lines)
- `Section3_2/HardInterventionOn.lean` (~3 lines)
- `Section3_2/NodeSplittingOn.lean` (~5 lines)
- `Section3_2/ExtendingCDMGsWithInterventionNodes.lean` (~3 lines)
- `Section3_2/MarginalizingOutSplitOutput.lean` (~3 lines)
- `Section3_2/NodeSplittingHard.lean` (~2 lines)
- `Section3_2/HardInterventionsCommute.lean` (~2 lines)
- `Section3_2/HardInterventionNodeSplittingCommute.lean` (~2 lines)
- `Section3_2/TwoDisjointNodeSplittingsCommute.lean` (~2 lines)
- `Section3_3/ISigmaSeparationMarginalization.lean` (~2 lines, the
  `G_witness` counter-example — entire file goes away anyway when
  claim_3_25 flips to a positive proof)
- `Section3_3/SigmaOpenWalkMarginalization.lean` (~2 lines, the same)

Total: ~13 files affected, ~35-40 lines of code modified or deleted.

**Tot impact:**
- 1 structure field deleted.
- 5 hypothesis uses deleted.
- ~12 field-discharge blocks deleted.
- ~6 of the 7 rows currently in `refactor_data.json` still need their
  Lean re-proven from scratch (because the membership conditions on
  `mem_marginalize_L` change to drop the exclusion clauses, which is
  the whole point of the refactor — most existing proofs at consumers
  reference the symmetric-`∨` shape).
- def_3_10 (hardInterventionOn), def_3_11 (the "L excludes" Lean
  constructors), def_3_12 (nodeSplittingOn), def_3_13 (the SWIG /
  extending-with-intervention-nodes), all of Section3_2 commutation
  claims (claim_3_10..claim_3_15) — these need their *transitive*
  inclusion in the refactor table, even though their statement
  doesn't change, because the *type* of `CDMG` changed.

The transitive-consumer scan that `do_refactor.py init` runs
automatically would catch all of these — that's why option (D) needs
a fresh refactor branch, not a manual table edit.

**Out-of-chapter-3 impact: zero.** Chapter 4+ consumes CDMG values,
not their structural fields. They don't construct CDMGs except via
the chapter-3 constructors and don't pattern-match the field list.

### 4. Suggested row ordering — IF (B) is chosen against my recommendation

(Only relevant if the human overrides my recommendation. For (D) the
new refactor's `do_refactor.py init` builds its own table; for (1)/(3)
no row ordering is needed.)

Order the 7 rows to maximise reuse of solved API:

1. **def_3_14 (this row)** — first. The new `marginalize` definition
   is the foundation; nothing else can be re-validated until it exists.
2. **def_3_18 (ISigmaSeparation)** — second. It does not consume
   marginalisation. Re-validating it first lets the manager *prove
   the structural lift lemma* downstream rows depend on, without the
   complication of a not-yet-stable marginalize.
3. **claim_3_16 (MarginalizationPreserves)** — third. Item 1
   (`marginalize_anc_iff`) is the breaking point under (B); seeing
   the breakage *here* (rather than at claim_3_25) gives the manager
   the earliest chance to surface the cascade-via-(B) failure mode.
   If item 1 cannot be repaired, escalate again. If it can be (e.g.
   by reformulating to "ancestor via E ∨ swap-bifurcation"), document
   the new deviation.
4. **claim_3_17 (MarginalizationsCommute)** — fourth. Its proof's
   `(⇒)` direction may also break under (B) (the `E^{\sm W_1}` →
   directed-walk-in-G expansion now has the new "no bifurcation"
   precondition). Repair or escalate.
5. **claim_3_18 (MarginalizationAndIntervention)** — fifth. Composes
   marginalize with hardInterventionOn; should survive (B) cleanly
   because hardInterventionOn doesn't introduce collisions.
6. **claim_3_19 (MarginalizingOutSplitOutput)** — sixth. Composes
   marginalize with nodeSplittingOn / SWIG; same reasoning as
   claim_3_18.
7. **claim_3_25 (ISigmaSeparation)** — last. The acid test. If the
   first six all worked under (B), this is the one that should now
   *flip from disproof to proof*. If it still fails, the refactor
   has not improved anything and should be rolled back.

Risk note: I expect step 3 to fail and trigger an escalation. The
plan above assumes the human's response is to either give up on (B)
or accept the new deviation.

### 5. What I am NOT confident about

- **Whether claim_3_17 actually survives priority-E or (B)** — I
  inferred from the LN proof shape that bifurcation-existence is
  preserved, but I did not verify the proof rewrite end-to-end. The
  current chapter doesn't have a solved Lean for claim_3_17 (its
  Lean file is the *original* pre-refactor draft).
- **Whether the with-source bifurcation iff (claim_3_16 item 2 with
  source) survives (D)** — I assume it does because (D) reproduces
  the LN literally, but I did not verify the LN's own proof of the
  with-source half handles all corner cases. The currently-registered
  `claim_3_16_with_source_bifurcation_deferred` deviation says
  "either (a) introduce `IsBifurcationWithSource`, then re-attempt;
  or (b) route via the no-source iff and reconstruct v_3
  downstream". Option (a) is independent of the refactor; option (b)
  is preserved by (D). Both are tractable post-(D).
- **The "may take many sessions" cost of (D)** — `do_refactor.py
  init` builds the transitive table via `find_dependents.py`'s
  rename + lake build, but I don't know how many chapter-3 rows that
  scan would surface. It could be 7 (the current 7) or 20 (every
  CDMG constructor + every commutation/equality claim). The human's
  decision should weigh this against the cost of leaving the
  cascade in place.

### 6. End of plan

Manager: please surface §2 (recommendation) to the human via
`request_from_human` on this row. Do *not* attempt option (B) on
faith — the breakage of `marginalize_anc_iff` is concrete and
predictable, and proceeding would burn a refactor cycle for no gain.

## Plan from `plan_subtasks` worker, 2026-05-31T15:55:00+00:00

The prior plan (§§1-6 above) recommended escalation. The manager
escalated; the orchestrator nudged back asking for a second-pass
investigation of two specific paths. This is that second pass.

### A. Recap of the constraint

`def_3_1.CDMG` has `disjoint_EL : Disjoint E L` on a shared
`Set (α × α)` carrier. **OUT OF SCOPE** for this refactor.

Therefore: any `CDMG α` value -- including `G.marginalize W` --
**cannot** carry a pair `(u, v)` in both `E` and `L`. The LN's
`L^{\sm W}` has no such restriction; collision pairs (pairs with
both a directed-walk-through-W AND a bifurcation-through-W in `G`)
belong to **both** in the LN.

The LN proof of claim_3_25 at `graphs.tex:1559` uses exactly such
a pair: it places `(w, b_{j+1})` simultaneously in `E^{\sm u}`
(for the step `b_j \tuh w`) and `L^{\sm u}` (for the step
`w \huh b_{j+1}` in the same walk).

### B. The `Walk G` constraint cascade

In the Lean encoding, a `Walk G v w` is a list of `WalkStep G v w`
constructors: `forward h` (with `h : (v, w) ∈ G.E`), `backward h`
(`(w, v) ∈ G.E`), `bidir h` (`(v, w) ∈ G.L`). **The constructor
of a step requires literal membership in `G.E` or `G.L`.**

For `G_marg = G.marginalize {u}`, a `bidir h` step at
`(w, b_{j+1})` requires `(w, b_{j+1}) ∈ G_marg.L`. Priority-E
excludes this pair from `G_marg.L` (`disjoint_EL` forces the
exclusion because `(w, b_{j+1}) ∈ G_marg.E`).

So the walk `b_j \tuh w \huh b_{j+1}` that the LN proof
constructs **cannot be expressed as a `Walk G_marg v w` value**.
No predicate-level reformulation of `IsISigmaSeparated` can change
this, because the issue is at the *walk-type-existence* level, not
at the predicate level.

### C. Path 1 (Option E) -- result

#### C.1. Dependency map of `IsISigmaSeparated`

Section 3.3 stack consumed by `IsISigmaSeparated` (def_3_18):

```
IsISigmaSeparated G A B C := ∀ v ∈ A, w ∈ G.J ∪ B,
                              ∀ π : Walk G v w, π.IsSigmaBlocked C
  ├── Walk G v w                                      -- def_3_4 (Section 3.1, OUT OF SCOPE)
  │     └── WalkStep G v w
  │           ├── forward (h : v ⟶[G] w)              -- requires (v, w) ∈ G.E
  │           ├── backward (h : v ⟵[G] w)             -- requires (w, v) ∈ G.E
  │           └── bidir (h : v ⟷[G] w)                -- requires (v, w) ∈ G.L
  └── π.IsSigmaBlocked C                              -- def_3_17 (Section 3.3, OUT OF SCOPE)
        ├── π.IsColliderAt k                          -- def_3_15 (Section 3.3, OUT OF SCOPE)
        │     └── matches arrowhead-at-target/source
        │         predicates on adjacent steps        -- WalkPredicates (Section 3.1, OUT OF SCOPE)
        └── π.IsBlockableNonColliderAt k              -- def_3_16 (Section 3.3, OUT OF SCOPE)
              └── IsUnblockableJoint at adjacent steps -- references G.E (strict outgoing arrows)
```

**Every predicate downstream of `Walk G v w` is structurally
fixed by `G`'s edge sets.** Only def_3_18 itself is in scope.

#### C.2. Membership-check failure on the counter-example

Cascade counter-example (the disproof's `G_witness`):
`V = {v_0, b_j, u, w, b_{j+1}, v_n}`, `J = ∅`,
`E = {(v_0, b_j), (b_j, u), (u, b_{j+1}), (b_{j+1}, v_n),
     (u, w), (w, u), (w, b_j)}`, `L = ∅`.
`A = {v_0}`, `B = {v_n}`, `C = {b_j, w}`, `D = {u}`.

Under priority-E, `(G.marginalize {u}).L = {(w, b_{j+1}),
(b_{j+1}, w)}` MINUS the exclusion (a directed walk
`w \tuh u \tuh b_{j+1}` exists through `{u}`), so
`(w, b_{j+1}) ∉ (G.marginalize {u}).L`.

The membership check that fails: the `bidir h` constructor
requires `h : (w, b_{j+1}) ∈ (G.marginalize {u}).L`. No such `h`
exists. So no `bidir` step at this pair exists in
`Walk (G.marginalize {u}) _ _`.

#### C.3. The `bif_exists_at` helper proposal

The manager suggested: a `bif_exists_at p G W` predicate at the
marginalize level (capturing "bifurcation through W between p.1
and p.2 in G"), wired into def_3_18 to absorb the E↔L
distinction.

**Concrete realisation**: define a parallel walk type that admits
"ghost" bidir steps via `bif_exists_at`.

```
def shadow_L (G : CDMG α) (W : Set α) : Set (α × α) :=
  { p | p.1 ∈ G.V \ W ∧ p.2 ∈ G.V \ W ∧ p.1 ≠ p.2 ∧
        (∃ π : Walk G p.1 p.2, π.IsBifurcation ∧ π.InteriorIn W) }
  \ (G.marginalize W).L  -- (the pairs the priority-E marginalize dropped)

inductive WalkStepAug (G : CDMG α) (shadow : Set (α × α))
    : α → α → Type _ where
  | base (s : WalkStep G v w) : WalkStepAug G shadow v w
  | ghost (h : (v, w) ∈ shadow) : WalkStepAug G shadow v w

inductive WalkAug (G : CDMG α) (shadow : Set (α × α))
    : α → α → Type _ where
  | nil (v : α) : WalkAug G shadow v v
  | cons (s : WalkStepAug G shadow v w) (p : WalkAug G shadow w u)
      : WalkAug G shadow v u

-- Per-step arrowhead predicates: ghost steps are treated as
-- bidirected (arrowhead at both endpoints).
def WalkStepAug.HasArrowheadAtTarget : WalkStepAug G shadow v w → Prop
  | .base s   => s.HasArrowheadAtTarget
  | .ghost _  => True
def WalkStepAug.HasArrowheadAtSource : WalkStepAug G shadow v w → Prop
  | .base s   => s.HasArrowheadAtSource
  | .ghost _  => True
def WalkStepAug.IsForward / IsBackward / IsBidir : ...
  | .base s   => s.IsForward / ...
  | .ghost _  => False / False / True

-- Redefine the position-indexed predicates on WalkAug (NEW
-- IsColliderAtAug, IsBlockableNonColliderAtAug, ...) -- ~500 lines
-- of duplication of CollidersAndNon + BlockableAndUnblockable +
-- SigmaBlockedWalks, but the bodies are mechanical translations.

def IsSigmaBlockedAug (π : WalkAug G shadow v w) (C : Set α) : Prop := ...

def IsISigmaSeparatedAug (G : CDMG α) (shadow : Set (α × α))
    (A B C : Set α) : Prop :=
  ∀ v ∈ A, w ∈ G.J ∪ B, ∀ π : WalkAug G shadow v w, π.IsSigmaBlockedAug C
```

Then `IsISigmaSeparated G A B C := IsISigmaSeparatedAug G ∅ A B C`
(equiv to current, since with `shadow = ∅` the ghost constructor
is uninhabited and `WalkAug G ∅` ≃ `Walk G`).

Claim_3_25's Lean statement becomes:
```
G.IsISigmaSeparated A B C ↔
  IsISigmaSeparatedAug (G.marginalize D) (shadow_L G D) A B C
```

#### C.4. Trace of LN proof at `graphs.tex:1559` under E5

Step 1559: "The fork bifurcation `w ← u → b_{j+1}` yields
`w ↔ b_{j+1} ∈ L^{\sm u}`."

Under E5: `(w, b_{j+1}) ∈ shadow_L G D` (because a fork
bifurcation exists in `G` with interior `{u}`).

The walk `π' = (v_0 \tuh b_j \tuh w \huh b_{j+1} \tuh v_n)` becomes
a `WalkAug (G.marginalize {u}) (shadow_L G {u}) v_0 v_n`:
- `forward (v_0 \tuh b_j)` via `.base` (E-membership preserved).
- `forward (b_j \tuh w)` via `.base` (E-membership preserved
  via `b_j \tuh u \tuh w` lift, no bifurcation between b_j and w
  through {u} because (u, b_j) ∉ E).
- `ghost (w \huh b_{j+1})` via `.ghost` (shadow_L
  membership: fork `w ← u → b_{j+1}` exists in G).
- `forward (b_{j+1} \tuh v_n)` via `.base`.

At position 3 (`w`): joint between
`base (forward (b_j, w))` and `ghost (w \huh b_{j+1})`.
- `HasArrowheadAtTargetAug(base (forward _)) = True`.
- `HasArrowheadAtSourceAug(ghost _) = True`.
- → `w` is a collider on this WalkAug.

Need: `w ∈ Anc^{(G.marginalize {u})}(C)`. (Anc-set on the BASE
marginalized graph, since ghost steps are bidirected and Anc only
follows directed edges -- so the augmented Anc = base Anc.)

In the counter-example: Sc^G(b_j) = {b_j, u, w}. Sc^{G.marg{u}}(b_j)
= {b_j, w} (priority-E preserves Anc, hence Sc, via claim_3_16
item 1). So `w ∈ Sc^{(G.marginalize {u})}(b_j) ⊆ Anc^{(...)}(b_j)
⊆ Anc^{(...)}(C)` (since b_j ∈ C).

→ `w` σ-open as collider in Anc(C). ✓.

The rest of the LN proof of claim_3_25 (positions b_j, u-runs,
b_{j+1}, etc., and the (⇒) direction's contrapositive walk
lifting) goes through analogously, because:
- All E-step membership facts on the augmented walk are
  identical to priority-E (which already proves anc/Sc
  preservation, claim_3_16 item 1).
- All L-step / ghost-step expansions back to G use exactly the
  LN's bifurcation-through-W constructions.

**Result**: under E5, claim_3_25's LN proof is reconstructible
in both directions. ✓.

#### C.5. Trace of claim_3_16 item 1 under E5

`marginalize_anc_iff`: `v_1 ∈ Anc^G(v_2) ↔ v_1 ∈ Anc^{(G.marginalize W)}(v_2)`.

`Anc` follows *directed* edges, i.e. `G.E`. E5 leaves
`(G.marginalize W).E` unchanged (priority-E). So the iff
holds **unchanged from the current state** (it's currently
proven; no work needed).

Crucially, E5 keeps the `Anc` API at the standard `CDMG`-level
predicate. The augmentation is exposed only via the new
`IsISigmaSeparatedAug` / `WalkAug` -- it does *not* propagate to
`Anc`/`Desc`/`Sc`/`IsAcyclic`/etc. So **claim_3_16 items 1, 3
survive intact** under E5.

Item 2 (bifurcation preservation): the LN's "bifurcation between
v_1 and v_2 in G^{\sm W}" is captured by the augmented walk type
(a bifurcation in WalkAug uses bidir steps from both base.L and
shadow_L = LN's full L^{\sm W}). So claim_3_16 item 2 with the
WalkAug-reading matches the LN exactly. The current Lean
symmetric-or workaround is no longer needed; item 2's statement
restates in terms of WalkAug.

But this means claim_3_16 item 2's Lean statement changes from
`IsBifurcation` on `Walk` to `IsBifurcationAug` on `WalkAug` --
itself a deviation (the statement deviates from the LN-literal
"bifurcation between..." which the LN reads at the walk level).
Soft deviation, structural.

#### C.6. New deviations introduced by E5

| # | Description | Severity |
|---|---|---|
| New 1 | `def_3_18`: parallel `IsISigmaSeparatedAug` predicate. | Structural |
| New 2 | `Walk` vs `WalkAug` split throughout Section 3.3. | Structural |
| New 3 | `claim_3_25`'s RHS uses `IsISigmaSeparatedAug` (not standard). | Soft |
| New 4 | `claim_3_16` item 2 restated over `WalkAug` (not standard). | Soft |
| Retained | `def_3_14_marginalize_L_excludes_E` (priority-E kept). | Structural |
| Retained | `def_3_14_l_w_membership_in_marginalization`. | Structural |
| Maybe-Retained | `claim_3_16_with_source_bifurcation_deferred`. | Soft |
| Resolved | `claim_3_25_the_lean_file_does_not_formalise_the_ln`. | (was Severe) |

Total deviation count: 4 retained/maybe + 4 new = up to 8.
Compared to current 4. **Net increase.**

But quality shifts: severe "claim_3_25 disproved" becomes
soft "claim_3_25 uses augmented predicate". Net usability arguably
improves.

#### C.7. Engineering cost of E5

- **`shadow_L` helper** (~50 lines, in `Marginalization.lean`).
- **`WalkStepAug` + `WalkAug` inductives** (~150 lines, in a new
  file `Section3_3/SigmaSeparationAug.lean`).
- **Augmented per-step arrowhead predicates** (~100 lines).
- **Augmented collider / non-collider / unblockable / blockable
  predicates** (DUPLICATES `CollidersAndNon.lean` +
  `BlockableAndUnblockable.lean`, ~600 lines).
- **`WalkAug.IsSigmaBlockedAug` / `IsSigmaOpenAug` + iff lemmas**
  (DUPLICATES `SigmaBlockedWalks.lean`, ~300 lines).
- **`IsISigmaSeparatedAug` + iff lemmas** (~150 lines).
- **Coercion `Walk G ≃ WalkAug G ∅` + lift lemmas** (~200 lines).
- **claim_3_25 proof in the augmented form** (~600 lines based
  on the cascade-document length and the LN proof's intricacy).
- **claim_3_16 item 2 re-statement and re-proof in WalkAug terms**
  (~100 lines).

**Total: ~2200 lines of new Lean code.**

The duplication of σ-blocking infrastructure (collider /
non-collider / unblockable / σ-open / σ-blocked) is mandatory
because:
- The existing predicates take `Walk G v w` (not `WalkAug ...`).
- They're in Section 3.3 files (def_3_15, def_3_16, def_3_17),
  which are **out of scope**.
- Adding an extra parameter to the existing predicates (to make
  them parametric over `WalkAug` shadow) would change their
  signature -- breaks the in-scope/out-of-scope wall.

### D. Path 2 (encoding tricks) -- result

#### D.1. (a) Sym2 for L

**Rejected**: changes `def_3_1.CDMG`'s L field type from
`Set (α × α)` to something via `Sym2 α`. The `disjoint_EL`
field's *type* becomes vacuous, but the L field itself is
restructured. This is a structural change to def_3_1 --
**OUT OF SCOPE**.

#### D.2. (b) Bundled output for marginalize

**Investigated and rejected**.

The proposal: `marginalize G W : CDMG α × Set (α × α)`, where the
first component is the priority-E CDMG and the second is the
LN's literal `L^{\sm W}`.

Tracing the LN proof at `graphs.tex:1559`:
- `(w, b_{j+1}) ∈ second_component` (the LN's L^{\sm u}). ✓.
- But the LN's proof builds a *walk* in the marginalized graph.
  In Lean, that walk is `Walk first_component v w`, which only
  admits `bidir` steps for pairs in `first_component.L` (priority-E,
  no collision pair).
- So even with the bundle, the walk type doesn't admit the
  needed step. **The bundle doesn't help unless we ALSO
  reformulate the walk type** -- which is E5 in disguise (just
  with the augmentation data delivered via a tuple-projection
  rather than a shadow_L definition).

Conclusion: (b) reduces to E5 once we trace it concretely. Same
costs, same deviations.

#### D.3. (c) Predicate lift in the claim's statement

**Investigated and rejected as standalone**.

The proposal: keep marginalize and `IsISigmaSeparated` exactly
as-is, but reformulate claim_3_25's statement to use a predicate
`marg_bif_pair p G W := (p ∈ G_marg.L) ∨ (collision pattern)`,
making the claim's iff trivially navigable.

Tracing: claim_3_25's LN statement is
`A ⊥^{iσ}_G B | C ↔ A ⊥^{iσ}_{G^{\sm D}} B | C`. The LHS uses
`IsISigmaSeparated` on G; the RHS uses `IsISigmaSeparated` on
`G^{\sm D}`. Both sides quantify over walks in their respective
graphs.

If we modify only the *statement* of claim_3_25 (without
modifying `IsISigmaSeparated`), the iff's RHS is still
`G.marginalize D` quantified over `Walk (G.marginalize D)`, which
suffers the same cascade. No matter how we phrase it, the
membership conditions on the walks don't change.

If we modify the RHS's predicate to a *different* predicate
(`marg_bif_pair`-based) that absorbs the E↔L collision, we've
reinvented E5. Same costs, same deviations, just with the
augmentation delivered via the claim statement's predicate name.

Conclusion: (c) collapses to E5 once realised concretely.

### E. Why priority-L also fails (additional evidence beyond §1)

I went deeper than the prior plan to see whether priority-L
actually rebreaks claim_3_25 in any concrete way. **It does.**

Construct G:
- `V = {b_j, u, w, x, b_{j+1}, v_n, A, B}`,
- `E = {(A, b_j), (b_j, u), (u, b_{j+1}), (b_{j+1}, v_n),
      (u, w), (w, u), (w, x), (u, x), (x, b_j), (b_{j+1}, B)}`,
- `L = ∅`.
- `A = {A}, B = {B}, C = {b_j}, D = {u}`.

Sc^G(b_j) = {b_j, u, w, x}, so Sc^G(b_j) \ {u} = {b_j, w, x}.

Under priority-L:
- `(w, x) ∉ E^{\sm u}_priority-L` because the fork
  `w ← u → x` exists in G (via (u, w), (u, x) ∈ E).
- `(w, b_{j+1}) ∉ E^{\sm u}_priority-L` because fork
  `w ← u → b_{j+1}` exists.
- `w` has no outgoing edges in `E^{\sm u}_priority-L`.
- So `w ∉ Anc^{(G.marg{u})_priority-L}(b_j)`, breaking
  `claim_3_16 item 1` (LN says w ∈ Anc^{G^{\sm u}}(b_j) via
  w → u → x → b_j, which our encoding loses).

Now follow the LN's claim_3_25 proof at `graphs.tex:1555`:
> "Since u ∈ Sc^G(b_j), there is a directed path from u to b_j
> in G; let w be the successor of u on this path, so u → w ∈ E
> and w ∈ Sc^G(b_j) \ {u} = Sc^{G^{\sm u}}(b_j)"

In this graph, the directed path from u to b_j in G goes via
`u → w → x → b_j` (or `u → x → b_j`). The successor of u is `w`
or `x`. The LN claims w ∈ Sc^{G^{\sm u}}(b_j).

Under priority-L: w ∉ Anc^{(G.marg{u})}(b_j), so w ∉ Sc^{(G.marg{u})}(b_j).
**The LN's equality fails under priority-L.** The proof step is
unsalvageable here.

Conclusion: priority-L doesn't merely shift the deviation -- it
actively breaks `claim_3_25`'s own LN proof at the sc-preservation
step, in addition to breaking `claim_3_16 item 1`. **Strictly
worse than priority-E in scope.**

### F. Final recommendation

**Two viable in-scope paths**, plus the prior plan's escalation:

**Path α (E5, in-scope augmentation, NEW)**:
Pursue the WalkAug-based augmentation of `IsISigmaSeparated`.
- Pro: positive proof of claim_3_25 (in augmented form).
- Pro: contained within this refactor's 7 rows.
- Con: ~2200 lines of new Lean code (mostly duplicated σ-blocking
  infrastructure).
- Con: increases net deviation count (4 → ~8), but improves
  *quality* (severe disproof → soft predicate-augmentation).
- Con: downstream consumers (chapter 4+) must select between
  standard `IsISigmaSeparated` and `IsISigmaSeparatedAug` when
  reasoning about marginalized graphs.

**Path β (option D from prior plan, OUT OF SCOPE)**:
Refactor `def_3_1.CDMG` to drop `disjoint_EL` (or restratify L
via Sym2).
- Pro: literal LN encoding, no deviations.
- Pro: minimal lines of code change (~40 lines deleted + ~5
  hypothesis sites + ~12 field discharges).
- Con: requires spinning up a NEW refactor branch.
- Con: transitive consumers within chapter 3 (def_3_10..3_19,
  claims 3_10..3_25) likely all need their Lean re-validated --
  the `do_refactor.py init` scan will surface 15-25 rows.

**Path γ (prior plan's option 3, status quo)**:
Document the four deviations as long-term limitations, finalize
this refactor as a no-op. Move on.

#### Per-path recommendation strength

- **Path β is the technically cleanest** and is what I'd
  recommend if the human has scaffold-time available for a new
  refactor.
- **Path α is the in-scope-fastest** and unlocks claim_3_25
  positively, but at the cost of significant code duplication
  and a structural API deviation in def_3_18 (the augmented
  predicate). It is **a real alternative** to escalation.
- **Path γ leaves the cascade in place** and the 4 deviations
  documented; only acceptable if claim_3_25 disproof is OK
  to live with permanently.

**My final pick**: still recommend escalation to the human with
all three options on the table. **The new evidence is that Path α
(E5) is a viable in-scope option**, contrary to the prior plan's
one-sentence dismissal. The human's call between α / β / γ
depends on:
- Project time budget (α: 1-2 sessions of careful work;
  β: a fresh refactor surfaced via `do_refactor.py init`).
- Tolerance for code duplication in σ-blocking infrastructure (α
  is heavy here).
- Long-term plans for chapter 4+ Markov-property results on
  marginalized graphs (β makes them clean; α makes them carry an
  augmented-vs-standard choice).

### G. Row execution order, IF Path α (E5) is chosen

(For Path β: a new refactor scan rebuilds its own order. For
Path γ: no ordering needed.)

E5's execution order across the 7 current rows:

1. **def_3_14 (this row) -- AUGMENT, KEEP**. Keep priority-E
   marginalize as-is (its existing replacement block is
   essentially the original, possibly with prose-only edits).
   ADD: `shadow_L : CDMG α → Set α → Set (α × α)` helper at the
   end of `Marginalization.lean`. Define it as
   "bifurcation-through-W-exists minus literal-L-membership".

2. **def_3_18 (ISigmaSeparation) -- MAJOR EXTEND**. Add
   `WalkStepAug`, `WalkAug`, augmented arrowhead predicates,
   augmented collider/non-collider/blockable/σ-blocked
   predicates, `IsISigmaSeparatedAug`. Prove the coercion
   `WalkAug G ∅ ≃ Walk G` and `IsISigmaSeparatedAug G ∅ ↔
   IsISigmaSeparated G`. Bulk of the code lives here -- about
   ~1500 lines of duplicated infrastructure plus the new
   predicate.

3. **claim_3_16 (MarginalizationPreserves) -- KEEP item 1
   (priority-E preserves anc), RESTATE item 2 over WalkAug,
   address item 3**. Item 1 needs no change. Item 2's Lean
   restatement uses `IsBifurcationAug` on `WalkAug (G.marginalize
   W) (shadow_L G W)`. Item 3 (acyclicity preservation) is
   directed-only and survives priority-E unchanged.

4. **claim_3_17 (MarginalizationsCommute) -- VERIFY UNCHANGED**.
   Equates two `CDMG` values; the augmentation doesn't enter the
   statement. Should be re-checkable from priority-E unchanged.
   Risk: priority-E exclusion clauses are *idempotent under
   composition* and the LN's claim_3_17 is at the CDMG-equality
   level. **NEED A TARGETED VERIFICATION**: does
   `(G^{\sm W_1})^{\sm W_2} = G^{\sm (W_1 ∪ W_2)}` hold for
   priority-E? Cited as "not free of risk" by the prior plan;
   I did not verify in this pass.

5. **claim_3_18 (MarginalizationAndIntervention) -- VERIFY
   UNCHANGED**. Same risk as claim_3_17 -- CDMG-equality at the
   priority-E level. Probably survives; the LN proof routes
   through bifurcation-existence (item 2), which our symmetric-or
   reading preserves.

6. **claim_3_19 (MarginalizingOutSplitOutput) -- VERIFY
   UNCHANGED**. Same comment as claim_3_18.

7. **claim_3_25 (ISigmaSeparation) -- REWRITE positively in
   augmented form**. Lean statement:
   `G.IsISigmaSeparated A B C ↔
      IsISigmaSeparatedAug (G.marginalize D) (shadow_L G D) A B C`.
   Reproduce the LN's proof using `WalkAug`. Bulk of the proof
   work; ~600 lines.

Risk note on Path α: step 2 dominates the engineering. The
duplicated infrastructure is large, but mechanically derivable
from the existing Section 3.3 files. The proof of claim_3_25
itself (step 7) is the original LN proof transcribed faithfully;
the cascade analysis above gives confidence that no individual
step blocks.

### H. End of second-pass plan

Manager: I recommend you escalate to the human via
`request_from_human` again, but with this expanded list:

1. (NEW) **Pursue Path α (E5)** inside this refactor: ~2200
   lines of code, ~1-2 sessions, positive proof of claim_3_25 in
   augmented form. Increases deviation count but improves
   quality.

2. (was #1) **Spin up `def_3_1_no_disjoint_EL` refactor**:
   structurally cleanest; rolls back this branch, re-emits
   `refactor` against def_3_1; the new refactor's transitive
   scan will likely surface 15-25 chapter-3 rows.

3. (was #2) **Manual table edit** to extend this refactor's
   scope to include def_3_1.

4. (was #3) **Abandon, accept the 4 deviations**.

My ranking: 2 > 1 > 4 > 3.

- 2 is the right long-term fix (no deviations, LN-faithful).
- 1 is the right "make progress now" fix (in-scope, claim_3_25
  positively proven, but accepts a structural deviation in
  def_3_18).
- 4 is a stable retreat.
- 3 is fragile (manual JSON edits bypass the orchestrator's
  refactor machinery).

**Do not attempt priority-L** on faith -- it breaks claim_3_25's
own LN proof at sc-preservation, not just claim_3_16 item 1.

