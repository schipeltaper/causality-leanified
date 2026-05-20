"""Prep step for a new chapter — runs the find-defs-and-claims agent.

Spawns a Claude Code agent that edits the chapter's `.tex` file in the
lecture notes IN PLACE, wrapping every definition with
``\\begin{defmark}...\\end{defmark}`` and every claim with
``\\begin{claimmark}...\\end{claimmark}``. After this step, `fill_data`
(in `create_data.py`) can parse the marks into rows.

Run this once per chapter, BEFORE `initialize_chapter.py`. It is slow and
costly (one long agent run per chapter), so we keep it isolated.

Entry point: `python3 scaffold/prep_chapter.py` (reads `current_chapter`
from `scaffold/global_vars.json`).
"""
from __future__ import annotations

import json
import subprocess
from pathlib import Path


SCAFFOLD_DIR = Path(__file__).resolve().parent
LECTURE_NOTES_DIR = SCAFFOLD_DIR.parent / "lecture-notes" / "lecture_notes"
GLOBAL_VARS_PATH = SCAFFOLD_DIR / "global_vars.json"


def mark_defs_and_claims(chapter: int, tex_file: str) -> None:
    """Spawn the Claude agent that wraps every def/claim in the chapter's
    `.tex` file with ``\\begin{defmark}``/``\\begin{claimmark}`` blocks.

    The agent follows the prompt at
    ``scaffold/claude_prompts/chapter_setup/mark_definitions_and_claims_in_tex.md``.
    Raises ``RuntimeError`` on non-zero exit.
    """
    prompt_template = (
        SCAFFOLD_DIR
        / "claude_prompts"
        / "chapter_setup"
        / "mark_definitions_and_claims_in_tex.md"
    ).read_text(encoding="utf-8")
    tex_path = LECTURE_NOTES_DIR / tex_file

    context = (
        "You are an agent in the causality-leanification swarm. Your one job is\n"
        f"to mark up chapter {chapter} of the lecture notes.\n\n"
        f"Edit ONLY this file, in place:\n  {tex_path}\n\n"
        "Be exhaustive -- find every definition and claim, however small.\n"
        "Do not modify any other file. When done, briefly summarise how many\n"
        "defs and claims you marked.\n\n"
        "---\n\n"
    )
    full_prompt = context + prompt_template

    result = subprocess.run(
        ["claude", "-p", full_prompt, "--dangerously-skip-permissions",
         "--model", "claude-opus-4-7[1m]", "--effort", "max"],
        check=False,
    )
    if result.returncode != 0:
        raise RuntimeError(
            f"find_def_claim agent exited with code {result.returncode}"
        )


def prep() -> None:
    """Resolve the current chapter from ``global_vars.json`` and run the
    find-defs-and-claims agent on its `.tex` file in the lecture notes.
    """
    # Local import so prep is usable even if initialize_chapter isn't yet wired.
    from initialize_chapter import get_title_and_tex_file_chapter

    cur = json.loads(GLOBAL_VARS_PATH.read_text(encoding="utf-8"))["current_chapter"]
    title, tex_file = get_title_and_tex_file_chapter(cur)
    print(f"[prep] chapter {cur}: {title!r} in {tex_file}", flush=True)
    mark_defs_and_claims(cur, tex_file)
    print("[prep] done.", flush=True)


if __name__ == "__main__":
    prep()
