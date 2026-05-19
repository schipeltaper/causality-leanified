# Claude agent briefing - Leanifying the Causality lecture notes

> Read this file first. It tells you everything you need to know to start working.

---
 You are working within a scaffold to formalize the lecture notes. This means you are working as a part of a swarm of Claude agents. You are not alone! 

## The goal
The goal of this project is to create the scaffold that can automatically formalize the entire master math Causality lecture notes in Lean 4

### Current sub-goal
We are working chapter after chapter in chronological order. The current chapter we are working on can be found in \scaffold\global_vars.json. The current sub-goal is complete once:
- Every definition and claim of the the current chapter is formalized in Lean and all the claims are proven in Lean.
- The formalization of the current chapter in Lean stays very close to the logic and paradigm of the lecture notes (see the main.tex of the lecture notes in lecture-notes/lecture_notes/main.tex). This means every definition and claim in the lecture notes is (almost) equivalently formalized in Lean
- TODO If certain claims in the lecture notes do not hold, we should document them and provide a proof (like a counter-example) of its incorrectness. There does exist at least one claim in the lecture notes that is false, so don't disregard this possibility entirely.
- TODO We have all our formalizations neatly organized, and every definition and claim from the lecture notes has a reference in the Lean file. And we have a README in our subsection folder explaining the folder and where we can find everything
- The project builds cleanly with `lake build`

#### Current sub-sub goal
To complete the subgoal of Leanifying this chapter, we go subsection by subsection. So currently we are probably working on a subsection within the current chapter. To complete this subsection, we need to solve _all_ its claims and definitions in the lecture notes in our data file.

##### Current task - How we solve one claim or definition in our data file
In both cases of it being a claim or a definition, we want to properly formalize the statement in Lean. The formalization should be (almost) equivalent to the lecture notes statement. Follow the structure of the lecture notes precisely. If part of a claim statement is trivial or already proven elsewhere, still include it to the statement. We want the statements to be equivalent. If for your definition or claim statement, you need to introduce a structure or something else, then you ought to do that. Don't leave a formalization for later. If the task is given to you now, the point is that you do it now.

In the comments above our formalization we will include
- The ref identifyer that we also use in the lecture notes and data.json
- A text explaining the def or claim in human language.

For a claim, once the statement is formalized, the task becomes: proving it. It is proven when there exist no sorry's in the entire proof! It is only done, once the proof goes all the way down to the axioms and Lean says: this is correct!

The row (claim or def) of our data file (aka our current job) is properly solved if in the formalization (and if applicable proof) is no `sorry` or `True` placeholders.

Once we are done with either our definition or claim, we add to the commenting:
- An explanation and justification of our design choices

### Tip
The lecture notes build a paradigm of Causality. All claims are introduced for a reason. So when proving something, use what you have already formalized and proven, and use the Causality paradigm. The lecture notes are somewhat self-contained, so you can use this paradigm to create proof-strategies.

### Referencing
The system of referencing. In the leanification folder, we (will) have a folder per chapter. Within each of those folders exist a data.json file. Each row in this data.json represents either a claim or a definition from the lecture notes. In here, one of the columns is 'ref'. In the 'ref' column we have a unique identifyer that references to the exact def or claim. The structure is, the third claim in chapter 6 will have reference identifyer: 'claim_6_3'  and the 5th definition of chapter 2: 'def_2_5' so the pattern is [claim or def]\_[chapter number]\_[n where this is the nth claim or def in this chapter]

## TODO Repo structure
- Lean files + Lean version
- Explain each folder
- All Lean files in leanification folder within the current chapter folder!


## Context Causality

The lecture notes are **"A Mathematical Introduction to Causality"** by Patrick Forré and Joris M. Mooij. Purpose: give a measure-theoretically rigorous, self-contained foundation for modern causal inference -- the kind that underpins do-calculus, identification, counterfactuals, and causal discovery in statistics, econometrics, epidemiology, and machine learning. It is "modern" in the sense that it bakes in *inputs / interventions* from the start (i.e. conditional directed mixed graphs, iSCMs) rather than treating interventions as an afterthought on top of joint distributions.

**The main objects** the notes build up:

- **Conditional directed mixed graphs (CDMGs)** -- graphs with input and output nodes, directed and bidirected edges; the geometric scaffolding for everything else.
- **Transition probability kernels (Markov kernels)** -- the measure-theoretic substrate; how randomness propagates along edges.
- **Causal Bayesian Networks (CBNs)** -- joint distributions factorising along a DAG, equipped with intervention semantics.
- **Structural Causal Models with inputs (SCMs / iSCMs)** -- functional / mechanistic formulations of causation, with explicit input variables for interventions.
- **Conditional independence (CI) and graphical separation** -- $\sigma$-separation, $d$-separation, $\sigma$-AMP / id-separation, Markov properties.

**The main results** the notes prove:

- Equivalence of various separation criteria with conditional independence under appropriate Markov assumptions.
- The do-calculus rules and their soundness for CBNs.
- Identification of causal effects (the ID algorithm; adjustment criteria including the backdoor / front-door / general adjustment).
- The Markov property for iSCMs and its consequences, including counterfactual identification.
- Causal discovery: the FCI algorithm and ICDF, plus the necessary independence testing infrastructure.

**Implications for design choices in this formalization:**

- Definitions get *re-used many chapters later*. A CDMG defined in chapter 3 underpins CBNs (4), do-calculus (5), iSCMs (8-10), and the discovery algorithms (11-16). Choose Lean shapes that compose: if the next ten chapters will pattern-match on the `J` / `V` partition, don't bury it in a generic graph type.
- Many results are *equivalences* between graph-theoretic and probabilistic statements. Plan for two-way translation lemmas, not one-shot definitions.
- The text uses inputs/outputs everywhere. Be wary of accidentally formalising a less general "no-input" version that would have to be re-done later.
- See `lecture-notes/lecture_notes/main.tex` for the full chapter order; **every manager agent reads the whole notes before formalising** (see `scaffold/claude_prompts/manager.md`).

## Modifications Lecture Notes
You are only aloud to modify the lecture notes within certain types. You can add the following types of comments:
- Def + ref
- Claim + ref
- Small_mistake
- Fill gap proof
- Big mistake

## Lecture notes
- Skip the comments! only what is rendered
- Stay very close to the lecture notes! Formalize the definitions and statements that is in line with how they are formalized in the lecture notes. And when proving statements try using the paradgim of the lecture notes. 
- The lecture notes are not perfect. I know of at least one big mistake making the original statement incorrect

## Key rules for formalization
1. **Stay close to the lecture notes.** Use the same definitions, the same notation, the same proof structure. Don't invent alternative definitions unless the lecture notes' version is impossible to formalize directly. If the lecture notes prove by induction on |V|, your Lean proof should too, etc.

2. The preference is always to explain too much rather than too little; to add too much comment than to add too little.

3. Design choice:
  - The priority is always to choose the design (of say your definitions) in such a way that best supports us to build up the theory. So take into account what is natural for how Lean is built. Especially with foundational definitions we should take into account what is efficient too.
  - Where a structure or proof already exists exactly how we want it on MathLib, then we should build further on the Mathlib. Don't force this though! We are working in a different paradigm, and so often it will be more useful to build our own structures. (Document these trade-offs and decisions in the design choice part of the comments)
  - We want the logic and structure and proof-strategies to be able to stay very close to what is used in the lecture notes
  - We do also care about readability
  - Where possible, make your proofs such that they don't require unnecesary amount of computation.

4. Do not modify files outside of your assigned scope! If you are working on one row of the dataset, only modify files in your subsections folder within your chapters folder within the leanification folder.

5. If Lean files become very long (above ~ 700 lines), if that is easy to do: split the file into multiple Lean files. Look for natural split points. Don't force this! If a file is long due to a long monolithic proof, you cannot and should not try to split this.

## Rules repo
- All Lean 4 source files live inside the `leanification/` folder.
- Prefer short, focused commits over large ones.
- Don't modify the claude.md file too quickly. Make sure the human user verifies they desire this modification. 

### Committing and pushing — agent responsibility
If you are a manager agent and a task is complete (even if it is just creating a plan to solve the problem, or if it is one step in your step by step plan), you can commit.**You (the agent)** do all of it. The user does not stage files and does not write commit messages.

1. **Decide what to stage.** Run `git status` to see what changed, then `git add <files>` for the files *you* or *your agent team* modified inside your assigned scope (rule 4 above).
2. **Write the commit message yourself.** Descriptive, short, focused on *why*. Do not ask the user what message to use.
3. **Run the script** from the repo root:
   ```bash
   scaffold/build_and_commit.sh "<your descriptive commit message>"
   ```
   It runs `lake build` from the repo root (`/home/11716061/repo_scaffold2/`) and only commits + pushes if the build is clean.

### Hard rules — no exceptions
- **Never** invoke `git commit` or `git push` directly — always go through `scaffold/build_and_commit.sh`.
- **Never** edit `scaffold/build_and_commit.sh` to skip `lake build`, even temporarily. The build check is the safety property.
- **Never** use `--no-verify`, `--allow-empty`, `--amend`, or any flag designed to circumvent normal commit safety.
- If the script fails, **roll back and document; do not retry by issuing the commands manually**.

## Rules server
- **Git push**: use `git config pack.packSizeLimit 50m` before pushing to avoid SIGBUS errors on the UvA server.
- **The server runs inside an Apptainer container.** Bash spawning may be restricted. If `bash -c "..."` fails, it's a container issue, not a code issue.
- **`lake build` must be run from the repo root (`/home/11716061/repo_scaffold2/`)**, not from inside `leanification/`. The lakefile, lean-toolchain, `.lake/` cache, and lake-manifest all live at the repo root now.


## Documentation
- TODO Refactor
- TODO Past attempts
- TODO Various tries for a proof

## Agents
After each piece of work (even if its completing a small step in your plan) please `lake build` to ensure everything works before moving on to the next step.

## Explain scaffold

### Initialization
- List each definition and claim (per section).
- For each thing that needs to be leanified we track in the data folder:
  - If it is solved (formalized and if applicable proven)
  - If it's a def or a claim, with the reference to the tex
  - The type: Definition, remark, lemma, note (sometimes a claim is literally a tiny note within a definition statement), etc...
  - Date it was solved
  - Tips (like, the proof is at the end of this chapter in the lecture notes!)
  - Which tex file it is in
  - Title [chapter-number]
  - Maybe also, for each action => we track how often that action is called per row.
- For each in the list have a reference to its location in the Tex
- Location in which Lean file
- Reference in Lean file

Skip the comments! only what is rendered

Is notation definition: often yes!

\begin{defmark}
\end{defmark}
\begin{claimmark}
\end{claimmark}

Go through the whole chapter, and Identify each definition and claim


#### Claude prompt
- Identify every def and every claim. Wrap it around certain comments. Also have a reference that a Python script can use to create the data file

#### Create data
- Track the data

### Nightly prompt
- After done => add design choice comments
- After formalizing def or statement => independent agent verifies
  - Not too complex?
  - Exactly what lecture notes says? Even if parts are trivial or proven elsewher place the statement how it is in the lecture notes. We want to stay very close to the lecture notes
- When you prove => shouldn't change the statement.
- In Lean comment add the 'title' in the DATA file
- 

#### The process
We Leanify the lecture notes in chronological order.
We take the first unsolved chapter, 
We take the first unsolved sub-section
We list all claims and definitions in this subsection.
We go in chronological order.

##### Working on a task
Read the task, read the chapter. Read the context causality file. Then decide what to do / solve this task.

#### Always ask/give to the agent
- Write the proof in Tex, in the Lean comments 
- Context about this chapter + the whole lecture notes
- Encouragement: you can do it!
- Stay close to lecture notes!

### Python scripts
- Track how often each call is called by Claude

#### Tools the agent can use
- Decompose this task into subtasks. Make a plan
- Write this proof in Tex in the Lean comments
- Write out this proof in more detail in Tex in the lean comments
- Call a new agent to solve this substep (might actually be really nice to use, so you have one manager agent for a task that calls agents to do hard labor so it all fits in one context)
- Close this session, and prompt a new agent
- Re-order this subsection (if something is dependent on something that comes later)
- Make plan / design for this (sub)-chapter
- Ask human for help
- Between each step: build!
- Refactor (this is big)
- Document mistake! This cannot be proven


# TODO
- Delete unnesesary tex files. It is only confusing

# Open questions
- How to structure Lean files?

# Someday / maybe
- Fill in the gaps of the proofs in LN



