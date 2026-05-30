#!/usr/bin/env python3
"""End-to-end refactor lifecycle driver.

Branches involved (hardcoded):

- ``server_setting_up_scaffold``: the normal "server" branch where row
  solving happens. `do_refactor.py init` is ONLY allowed from this
  branch.
- ``refactor_<name>``: created by `do_refactor.py init` off
  ``server_setting_up_scaffold``. The refactor table lives here,
  refactor rows are solved here via
  ``python scaffold/solve_chapter.py --data-path …``, and
  ``apply_refactor_cleanup.py`` runs here via
  ``do_refactor.py finalize``.

Three subcommands:

- ``init``    — create the refactor branch, run the dependency scan,
                build the refactor table, commit, push.
- ``finalize`` — run the 8-phase cleanup, commit + push via
                ``build_and_commit.sh`` (clean lake build gate).
- ``merge``   — switch back to ``server_setting_up_scaffold``, merge
                ``--no-ff`` the refactor branch. ``--push`` and
                ``--delete-remote-branch`` are opt-in (operations that
                affect shared state require explicit consent).

State file: ``leanification/Chapter{N}_*/Refactor_<name>/.refactor_state.json``
records ``source_branch``, ``refactor_branch``, ``root_ref``, ``name``,
``chapter``, and ``init_date``. After cleanup the file is carried
along into the archived folder ``Refactor_<name>_DONE_<YYYY-MM-DD>/``
so ``merge`` can still find it.

Nested-refactor guards: `init` refuses if the current branch is anything
other than ``server_setting_up_scaffold`` (so it can't be invoked from
``refactor_*``, ``main``, ``building_refactor``, etc.). The orchestrator's
own ``refactor`` action handler additionally refuses inside a refactor
row (see ``solve_chapter.py``).

Usage::

    # On server_setting_up_scaffold:
    python extras/do_refactor.py init --chapter 3 --root-ref def_3_14 \
        --name Marginalize

    # Drive the refactor table (long-running; over many sessions):
    python scaffold/solve_chapter.py --data-path \
        leanification/Chapter3_GraphTheory/Refactor_Marginalize/refactor_data.json

    # Once every refactor row is solved=yes:
    python extras/do_refactor.py finalize --refactor-data \
        leanification/Chapter3_GraphTheory/Refactor_Marginalize/refactor_data.json \
        --mark-deviations-resolved=auto

    # Merge back (default: local only; pass --push to publish):
    python extras/do_refactor.py merge --refactor-data \
        leanification/Chapter3_GraphTheory/Refactor_Marginalize_DONE_2026-05-30/refactor_data.json \
        --push --delete-remote-branch
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
EXTRAS = REPO_ROOT / "extras"
SCAFFOLD = REPO_ROOT / "scaffold"
LEANIFICATION = REPO_ROOT / "leanification"

# Hardcoded branches -- the user explicitly asked for this. See module
# docstring for the lifecycle.
SERVER_BRANCH = "server_setting_up_scaffold"
REFACTOR_BRANCH_PREFIX = "refactor_"
STATE_FILE_NAME = ".refactor_state.json"


# ---------------------------------------------------------------------------
# Git helpers
# ---------------------------------------------------------------------------

def _git(cmd: list[str], check: bool = True, capture: bool = False
         ) -> subprocess.CompletedProcess:
    """Run ``git <cmd>`` from the repo root. Prints the command.
    Aborts the script on failure when ``check`` is True."""
    full = ["git", *cmd]
    print(f"$ {' '.join(full)}", flush=True)
    r = subprocess.run(
        full, cwd=str(REPO_ROOT), text=True,
        capture_output=capture,
    )
    if check and r.returncode != 0:
        sys.exit(f"ERROR: git {cmd[0]} exited {r.returncode}")
    return r


def _current_branch() -> str:
    r = subprocess.run(
        ["git", "branch", "--show-current"],
        cwd=str(REPO_ROOT), capture_output=True, text=True,
    )
    return r.stdout.strip()


def _working_tree_clean() -> bool:
    r = subprocess.run(
        ["git", "status", "--short"],
        cwd=str(REPO_ROOT), capture_output=True, text=True,
    )
    return not r.stdout.strip()


def _branch_exists(branch: str, remote: bool = False) -> bool:
    ref = f"refs/{'remotes/origin/' if remote else 'heads/'}{branch}"
    r = subprocess.run(
        ["git", "show-ref", "--verify", "--quiet", ref],
        cwd=str(REPO_ROOT),
    )
    return r.returncode == 0


def _run(cmd: list[str], check: bool = True) -> subprocess.CompletedProcess:
    """Run a non-git command from the repo root, streaming output."""
    print(f"$ {' '.join(cmd)}", flush=True)
    r = subprocess.run(cmd, cwd=str(REPO_ROOT), text=True)
    if check and r.returncode != 0:
        sys.exit(f"ERROR: command failed (exit {r.returncode})")
    return r


# ---------------------------------------------------------------------------
# State file
# ---------------------------------------------------------------------------

def _write_state(folder: Path, state: dict) -> Path:
    folder.mkdir(parents=True, exist_ok=True)
    path = folder / STATE_FILE_NAME
    path.write_text(json.dumps(state, indent=2) + "\n", encoding="utf-8")
    print(f"  wrote {path.relative_to(REPO_ROOT)}", flush=True)
    return path


def _read_state(refactor_data: Path) -> dict:
    """Read the state file from the same folder as the refactor_data.json.
    Works both pre-cleanup (Refactor_X/) and post-cleanup (Refactor_X_DONE_*/)."""
    state_path = refactor_data.parent / STATE_FILE_NAME
    if not state_path.exists():
        sys.exit(f"ERROR: state file not found at {state_path} -- was "
                 f"the refactor initialized via `do_refactor.py init`?")
    return json.loads(state_path.read_text(encoding="utf-8"))


# ---------------------------------------------------------------------------
# init
# ---------------------------------------------------------------------------

def cmd_init(args: argparse.Namespace) -> int:
    # Branch guards
    cur = _current_branch()
    if cur != SERVER_BRANCH:
        sys.exit(
            f"ERROR: `do_refactor.py init` must be run from "
            f"`{SERVER_BRANCH}` (the server branch). You are currently "
            f"on `{cur}`.\n"
            f"  - If `{cur}` is a refactor branch (`{REFACTOR_BRANCH_PREFIX}*`), "
            f"this is a NESTED refactor attempt; abort and re-plan from "
            f"`{SERVER_BRANCH}`.\n"
            f"  - Otherwise: `git checkout {SERVER_BRANCH}` first."
        )
    if not _working_tree_clean():
        sys.exit("ERROR: working tree not clean. Commit or stash first.")

    refactor_branch = f"{REFACTOR_BRANCH_PREFIX}{args.name}"
    if _branch_exists(refactor_branch):
        sys.exit(f"ERROR: branch `{refactor_branch}` already exists. "
                 f"Pick a different --name, or `git branch -D "
                 f"{refactor_branch}` if you really want to start over.")

    # Find the chapter folder up front -- if it doesn't exist there's
    # no point creating the branch.
    chapter_folder = _find_chapter_folder(args.chapter)
    refactor_folder = chapter_folder / f"Refactor_{args.name}"
    if refactor_folder.exists():
        sys.exit(f"ERROR: {refactor_folder.relative_to(REPO_ROOT)} "
                 f"already exists. Pick a different --name.")

    # Create the refactor branch
    print(f"\n[do_refactor] === Creating branch `{refactor_branch}` "
          f"off `{SERVER_BRANCH}` ===", flush=True)
    _git(["checkout", "-b", refactor_branch, SERVER_BRANCH])

    # Run find_dependents (rename + lake build + grep). Output to a
    # temp path under the refactor folder (so it gets committed for
    # auditability). Folder doesn't exist yet; create it first.
    refactor_folder.mkdir(parents=True, exist_ok=True)
    deps_json = refactor_folder / "dependents_scan.json"
    print(f"\n[do_refactor] === Running find_dependents.py "
          f"(this runs `lake build`; can take a few minutes) ===",
          flush=True)
    fd_cmd = [
        "python3", str(EXTRAS / "find_dependents.py"),
        "--chapter", str(args.chapter),
        "--ref", args.root_ref,
        "--out", str(deps_json),
    ]
    if args.no_build:
        fd_cmd.append("--no-build")
    _run(fd_cmd)

    # Read deps + initialize the refactor table
    print(f"\n[do_refactor] === Running initialize_refactor.py ===",
          flush=True)
    ir_cmd = [
        "python3", str(EXTRAS / "initialize_refactor.py"),
        "--root-chapter", str(args.chapter),
        "--root-ref", args.root_ref,
        "--name", args.name,
        "--dependents-json", str(deps_json),
    ]
    if args.extra_refs:
        ir_cmd.extend(["--extra-refs", args.extra_refs])
    if args.exclude_refs:
        ir_cmd.extend(["--exclude-refs", args.exclude_refs])
    _run(ir_cmd)

    refactor_data = refactor_folder / "refactor_data.json"
    if not refactor_data.exists():
        sys.exit(f"ERROR: initialize_refactor.py did not produce "
                 f"{refactor_data}; something went wrong.")

    # Write state file
    print(f"\n[do_refactor] === Writing state file ===", flush=True)
    _write_state(refactor_folder, {
        "source_branch":   SERVER_BRANCH,
        "refactor_branch": refactor_branch,
        "root_ref":        args.root_ref,
        "name":            args.name,
        "chapter":         args.chapter,
        "init_date":       datetime.now(timezone.utc).isoformat(timespec="seconds"),
    })

    # Commit + push
    print(f"\n[do_refactor] === Committing + pushing refactor branch ===",
          flush=True)
    _git(["add", str(refactor_folder.relative_to(REPO_ROOT))])
    msg = (f"refactor:init: {args.name} (root: {args.root_ref}); "
           f"{len(json.loads(refactor_data.read_text())['rows'])} row(s)")
    _git(["commit", "-m", msg])
    if not args.no_push:
        _git(["push", "-u", "origin", refactor_branch])

    # Done -- print the next step
    rel = refactor_data.relative_to(REPO_ROOT)
    n_rows = len(json.loads(refactor_data.read_text())['rows'])
    print(f"\n[do_refactor] === DONE: refactor `{args.name}` initialized ===")
    print(f"  source branch:   {SERVER_BRANCH}")
    print(f"  refactor branch: {refactor_branch} (currently checked out)")
    print(f"  refactor table:  {rel} ({n_rows} rows)")
    print(f"\nNext step -- drive the refactor table to completion "
          f"(may take many sessions):")
    print(f"  python scaffold/solve_chapter.py --data-path {rel}")
    print(f"\nOnce every row is solved=yes, finalize with:")
    print(f"  python extras/do_refactor.py finalize --refactor-data {rel}")
    return 0


# ---------------------------------------------------------------------------
# finalize
# ---------------------------------------------------------------------------

def cmd_finalize(args: argparse.Namespace) -> int:
    refactor_data = args.refactor_data.resolve()
    if not refactor_data.exists():
        sys.exit(f"ERROR: refactor-data not found: {refactor_data}")
    state = _read_state(refactor_data)
    refactor_branch = state["refactor_branch"]

    cur = _current_branch()
    if cur != refactor_branch:
        sys.exit(f"ERROR: not on the refactor branch. Expected "
                 f"`{refactor_branch}` (per state file); currently on "
                 f"`{cur}`. Run `git checkout {refactor_branch}` first.")
    if not _working_tree_clean():
        sys.exit("ERROR: working tree not clean. Commit or stash first.")

    print(f"\n[do_refactor] === Running apply_refactor_cleanup.py "
          f"(all 8 phases) ===", flush=True)
    rc_cmd = [
        "python3", str(EXTRAS / "apply_refactor_cleanup.py"),
        "--refactor-data", str(refactor_data),
    ]
    if args.mark_deviations_resolved:
        rc_cmd.extend(["--mark-deviations-resolved",
                       args.mark_deviations_resolved])
    if args.dry_run:
        rc_cmd.append("--dry-run")
    _run(rc_cmd)

    if args.dry_run:
        print(f"\n[do_refactor] DRY-RUN: nothing committed. Re-run "
              f"without --dry-run to apply.", flush=True)
        return 0

    # The cleanup phase 7h archived the refactor folder. The state file
    # moved with it. Find the new location for downstream commands.
    archived_folder = _find_archived_refactor_folder(
        state, datetime.now(timezone.utc).date().isoformat())
    archived_data = archived_folder / "refactor_data.json"

    print(f"\n[do_refactor] === Committing + pushing via "
          f"build_and_commit.sh ===", flush=True)
    msg = (f"refactor:finalize: {state['name']} (root: {state['root_ref']}, "
           f"cleanup applied; archived at "
           f"{archived_folder.relative_to(REPO_ROOT)})")
    bcs = SCAFFOLD / "build_and_commit.sh"
    _run(["bash", str(bcs), msg])

    print(f"\n[do_refactor] === DONE: refactor `{state['name']}` finalized ===")
    print(f"  archived to:    {archived_folder.relative_to(REPO_ROOT)}")
    print(f"\nNext step -- merge back into {state['source_branch']}:")
    print(f"  python extras/do_refactor.py merge --refactor-data "
          f"{archived_data.relative_to(REPO_ROOT)}")
    print(f"\n  (add --push to publish the merge, "
          f"--delete-remote-branch to drop the {refactor_branch} branch "
          f"on origin too.)")
    return 0


def _find_archived_refactor_folder(state: dict, today: str) -> Path:
    """The cleanup script renamed Refactor_<name>/ -> Refactor_<name>_DONE_<YYYY-MM-DD>/.
    Find it. Tries today's date first; falls back to globbing if needed."""
    chapter_folder = _find_chapter_folder(state["chapter"])
    name = state["name"]
    candidates = sorted(chapter_folder.glob(f"Refactor_{name}_DONE_*"))
    if not candidates:
        sys.exit(f"ERROR: cannot find archived refactor folder under "
                 f"{chapter_folder} -- expected `Refactor_{name}_DONE_*`; "
                 f"did the cleanup's archive phase run?")
    # Prefer one matching today's date, else the most recent.
    for c in reversed(candidates):
        if c.name.endswith(today):
            return c
    return candidates[-1]


# ---------------------------------------------------------------------------
# merge
# ---------------------------------------------------------------------------

def cmd_merge(args: argparse.Namespace) -> int:
    refactor_data = args.refactor_data.resolve()
    if not refactor_data.exists():
        sys.exit(f"ERROR: refactor-data not found: {refactor_data}")
    state = _read_state(refactor_data)
    refactor_branch = state["refactor_branch"]
    source_branch = state["source_branch"]

    if source_branch != SERVER_BRANCH:
        sys.exit(f"ERROR: refusing to merge into `{source_branch}` -- "
                 f"only the hardcoded server branch `{SERVER_BRANCH}` "
                 f"is supported as a merge target.")

    if not _working_tree_clean():
        sys.exit("ERROR: working tree not clean. Commit or stash first.")

    cur = _current_branch()
    if cur not in (refactor_branch, source_branch):
        sys.exit(f"ERROR: not on the refactor branch (`{refactor_branch}`) "
                 f"or source branch (`{source_branch}`). Currently on "
                 f"`{cur}`. Switch to one of those first.")

    # Switch to source branch and pull latest
    print(f"\n[do_refactor] === Switching to {source_branch} + pulling ===",
          flush=True)
    if cur != source_branch:
        _git(["checkout", source_branch])
    _git(["pull", "origin", source_branch])

    # Merge
    print(f"\n[do_refactor] === Merging --no-ff {refactor_branch} ===",
          flush=True)
    merge_msg = (f"refactor: merge `{state['name']}` (root: "
                 f"{state['root_ref']}) from {refactor_branch}")
    _git(["merge", "--no-ff", refactor_branch, "-m", merge_msg])

    # Optional push of the merged source branch
    if args.push:
        print(f"\n[do_refactor] === Pushing {source_branch} ===", flush=True)
        _git(["push", "origin", source_branch])
    else:
        print(f"\n[do_refactor] (skipping push; pass --push to publish "
              f"{source_branch} to origin)", flush=True)

    # Optional remote branch deletion
    if args.delete_remote_branch:
        if _branch_exists(refactor_branch, remote=True):
            print(f"\n[do_refactor] === Deleting remote branch "
                  f"origin/{refactor_branch} ===", flush=True)
            _git(["push", "origin", "--delete", refactor_branch])
        else:
            print(f"\n[do_refactor] (no remote branch origin/{refactor_branch} "
                  f"to delete)", flush=True)
    else:
        print(f"\n[do_refactor] (keeping refactor branch; pass "
              f"--delete-remote-branch to drop origin/{refactor_branch})",
              flush=True)

    # Optional local branch deletion (only if remote already gone)
    if args.delete_remote_branch:
        # Safe to delete local too (we just merged it).
        print(f"\n[do_refactor] === Deleting local branch "
              f"{refactor_branch} ===", flush=True)
        _git(["branch", "-d", refactor_branch], check=False)

    print(f"\n[do_refactor] === DONE: refactor `{state['name']}` merged "
          f"into {source_branch} ===")
    if not args.push:
        print(f"  Inspect the merge, then `git push origin {source_branch}` "
              f"when ready.")
    return 0


# ---------------------------------------------------------------------------
# Misc
# ---------------------------------------------------------------------------

def _find_chapter_folder(chapter: int) -> Path:
    for child in sorted(LEANIFICATION.iterdir()):
        if child.is_dir() and child.name.startswith(f"Chapter{chapter}_"):
            return child
    sys.exit(f"ERROR: no leanification folder for chapter {chapter}")


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(
        description="End-to-end refactor lifecycle (init / finalize / merge).",
    )
    sub = parser.add_subparsers(dest="cmd", required=True)

    # init
    p_init = sub.add_parser(
        "init",
        help="Create refactor branch + run dependency scan + build "
             "refactor table + commit + push.")
    p_init.add_argument("--chapter", type=int, required=True,
                        help="chapter of the root ref")
    p_init.add_argument("--root-ref", type=str, required=True,
                        help="root row being refactored (e.g. def_3_14)")
    p_init.add_argument("--name", type=str, required=True,
                        help="refactor name (becomes the "
                             "refactor_<name> branch + Refactor_<name>/ "
                             "folder)")
    p_init.add_argument("--no-build", action="store_true",
                        help="pass to find_dependents (skip lake build, "
                             "do only git grep -- much faster but misses "
                             "transitive consumers)")
    p_init.add_argument("--extra-refs", type=str, default="",
                        help="comma-separated additional refs to "
                             "include in the table beyond what "
                             "find_dependents detected")
    p_init.add_argument("--exclude-refs", type=str, default="",
                        help="comma-separated refs to exclude from the "
                             "dependents list (false positives)")
    p_init.add_argument("--no-push", action="store_true",
                        help="skip the `git push -u origin "
                             "refactor_<name>` step (default: push so "
                             "the branch has a remote backup)")

    # finalize
    p_fin = sub.add_parser(
        "finalize",
        help="Run apply_refactor_cleanup.py (all 8 phases) + commit "
             "+ push via build_and_commit.sh.")
    p_fin.add_argument("--refactor-data", type=Path, required=True,
                       help="path to refactor_data.json (pre-archive)")
    p_fin.add_argument("--mark-deviations-resolved", type=str, default="",
                       help="forwarded to apply_refactor_cleanup; 'auto' "
                            "or comma-separated deviation ids")
    p_fin.add_argument("--dry-run", action="store_true",
                       help="forward --dry-run to apply_refactor_cleanup; "
                            "no commit/push")

    # merge
    p_merge = sub.add_parser(
        "merge",
        help=f"Switch to {SERVER_BRANCH}, merge --no-ff the refactor "
             f"branch. Push and delete-remote-branch are opt-in.")
    p_merge.add_argument("--refactor-data", type=Path, required=True,
                         help="path to refactor_data.json (use the "
                              "archived path returned by `finalize`)")
    p_merge.add_argument("--push", action="store_true",
                         help=f"push the merged {SERVER_BRANCH} to origin")
    p_merge.add_argument("--delete-remote-branch", action="store_true",
                         help="delete origin/refactor_<name> AND the "
                              "local branch (after the merge)")

    args = parser.parse_args(argv)

    if args.cmd == "init":
        return cmd_init(args)
    elif args.cmd == "finalize":
        return cmd_finalize(args)
    elif args.cmd == "merge":
        return cmd_merge(args)
    return 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
