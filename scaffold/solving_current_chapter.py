
def solve_current_row():
    # build to check everything works
    if not builds():
        solve_build()

    # Check commits are empty
    if not commits_empty():
        solve_commits()

    # Take first row that is not yet solved from data
    current_task_data = take_first_row_not_yet_solved()

    solve_row(current_task_data)

def solve_row(current_task_data):
    # A definition and a claim require different approaches
    claim_or_def = current_task_data["def_or_claim"]


    # Get claude_prompts/solve_{claim_or_def}.md info
    prompt = get_prompt("solve_{claim_or_def}.md")
    context = "Context. We are solving a {claim_or_def}.\n\n" # Or maybe just "Remember, the original prompt was: {og}"

    while True:
        output = prompt_agent(prompt, context)
        prompt = process_output(output, claim_or_def, current_task_data)
        if not prompt:
            break

def process_output(output, claim_or_def, current_task_data):
    # Count whichever action was taken in this row's actions_tracking table.
    actions_tracking = current_task_data["actions_tracking"]

    if claim_or_def == "claim":
        if action == "Write proof":
            # Write proof
            actions_tracking["Write proof"] += 1
        if action == "Write proof in more detail":
            # Write proof in more detail
            actions_tracking["Write proof in more detail"] += 1

    if action == "solved":
        # Spawn independent agent to check correctness
        actions_tracking["solved"] += 1
    if action == "add or delete rows":
        # We will add or delete claimmarks and defmarks and then run data processing again?
        actions_tracking["add or delete rows"] += 1
    if action == "refactor":
        # prepare refactor
        actions_tracking["refactor"] += 1
    if action == "make plan":
        # prepare a multi-step plan to solve this task
        actions_tracking["make plan"] += 1
    if action == "decompose":
        # decompose task
        actions_tracking["decompose"] += 1
    if action == "spawn_agent_sub_task":
        # spawn agent to solve subtask
        actions_tracking["spawn_agent_sub_task"] += 1
    if action == "reaching context limit":
        # prompt new manager agent
        actions_tracking["reaching context limit"] += 1
    if action == "re-order":
        # Re-order data
        actions_tracking["re-order"] += 1
    if action == "help":
        # Human needs to intervene
        actions_tracking["help"] += 1
    if action == "mistake":
        # independent agent verifies (provide counter-example)
        # Track mistakes
        actions_tracking["mistake"] += 1
    else:
        # action = no_action
        # Spwan agent to check what action should be taken
        actions_tracking["no_action"] += 1

    return


    # end this subsection: double check, structure (maybe put all relevant items in one main doc?? for_the_reviewer.lean)

    # repeat for next chapter

    return

def take_first_row_not_yet_solved():
    return

def is_def(current_task_data):
    return

def is_claim(current_task_data):
    return
