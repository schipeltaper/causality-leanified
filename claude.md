# Leanifying the Causality lecture notes

## The goal
The goal of this project is to
- To create the scaffold that can automatically formalize the entire master math Causality lecture notes in Lean 4

The process is section by section in chronological order.

When you are working on Leanifying something (formalizing a definition or statement, or proving a claim), please take this file into consideration. 

Take the zoomed out context of the lecture notes into consideration when designing  your definitions. (you might want to consider what the application will be when designing something fundamental right now)

## Repo structure




## Context Causality
main theorems, etc and purpose

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




## Initialization
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


### Claude prompt
- Identify every def and every claim. Wrap it around certain comments. Also have a reference that a Python script can use to create the data file

### Create data
- Track the data

## Nightly prompt
- After done => add design choice comments
- After formalizing def or statement => independent agent verifies
  - Not too complex?
  - Exactly what lecture notes says? Even if parts are trivial or proven elsewher place the statement how it is in the lecture notes. We want to stay very close to the lecture notes
- When you prove => shouldn't change the statement.
- In Lean comment add the 'title' in the DATA file
- 

### The process
We Leanify the lecture notes in chronological order.
We take the first unsolved chapter, 
We take the first unsolved sub-section
We list all claims and definitions in this subsection.
We go in chronological order.

#### Working on a task
Read the task, read the chapter. Read the context causality file. Then decide what to do / solve this task.

### Always ask/give to the agent
- Write the proof in Tex, in the Lean comments 
- Context about this chapter + the whole lecture notes
- Encouragement: you can do it!
- Stay close to lecture notes!

## Python scripts
- Track how often each call is called by Claude

### Tools the agent can use
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