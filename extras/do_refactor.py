#!/usr/bin/env python3
"""End-to-end refactor lifecycle driver.

Branches involved (hardcoded):

- ``server_setting_up_scaffold``: the normal "server" branch where row
  solving happens. `do_refactor.py init` is ONLY allowed from this
  branch.
- ``refactor_<name>``: created by `do_refactor.py init` off
  ``server_setting_up_scaffold``. The refactor table lives here,
  refactor rows are solved here via
  ``python scaffold/scripts/phase3_solving/solve_chapter.py --data-path …``, and
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
    python scaffold/scripts/phase3_solving/solve_chapter.py --data-path \
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

# Branches that MUST NEVER be deleted by this script. Includes the
# source branch (whose deletion would orphan every refactor branch and
# all chapter data) and the standard upstream names. Every branch-
# deletion call site (remote or local) calls ``_assert_safe_to_delete``
# first; if the computed target is in this set, the script aborts.
PROTECTED_BRANCHES: frozenset[str] = frozenset({
    SERVER_BRANCH, "main", "master",
})


def _assert_safe_to_delete(branch: str) -> None:
    """Abort the script if ``branch`` is in ``PROTECTED_BRANCHES``.

    Defense-in-depth guard against a corrupted state file or a
    programmer error that could otherwise delete the source branch.
    """
    if branch in PROTECTED_BRANCHES:
        sys.exit(
            f"ERROR: refusing to delete protected branch `{branch}` "
            f"(PROTECTED_BRANCHES = {sorted(PROTECTED_BRANCHES)}). "
            f"This branch is the source of truth and must not be "
            f"deleted by automation. Aborting.")


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

def _resolve_init_roots(args: argparse.Namespace) -> list[str]:
    """Resolve the --root-refs / --root-ref CLI into a deduped list."""
    raw: list[str] = []
    if args.root_refs:
        raw.extend(r.strip() for r in args.root_refs.split(",")
                   if r.strip())
    if args.root_ref:
        print("[do_refactor] WARNING: --root-ref is deprecated; use "
              "--root-refs (comma-separated) instead. Accepted as a "
              "single-element list for back-compat.", file=sys.stderr)
        raw.append(args.root_ref.strip())
    seen: set[str] = set()
    out: list[str] = []
    for r in raw:
        if r and r not in seen:
            seen.add(r)
            out.append(r)
    return out


def _resolve_init_decl_names(args: argparse.Namespace,
                             roots: list[str]) -> dict[str, str]:
    """Resolve --decl-names / --decl-name into ``{root: lean_decl_name}``.
    Roots not in the map fall back to the row's ``title``."""
    out: dict[str, str] = {}
    if args.decl_name:
        # Legacy single-root form.
        if len(roots) != 1:
            sys.exit("ERROR: --decl-name (singular) only works with one "
                     "root; use --decl-names root1=Name1,root2=Name2 "
                     "for multi-root.")
        out[roots[0]] = args.decl_name
    if args.decl_names:
        for pair in args.decl_names.split(","):
            pair = pair.strip()
            if not pair:
                continue
            if "=" not in pair:
                sys.exit(f"ERROR: --decl-names entry {pair!r} must be "
                         f"of the form root=DeclName")
            k, v = pair.split("=", 1)
            k, v = k.strip(), v.strip()
            if k not in roots:
                sys.exit(f"ERROR: --decl-names key {k!r} is not in "
                         f"--root-refs {roots}")
            out[k] = v
    return out


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

    roots = _resolve_init_roots(args)
    if not roots:
        sys.exit("ERROR: no roots supplied (use --root-refs)")
    decl_overrides = _resolve_init_decl_names(args, roots)

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
          f"off `{SERVER_BRANCH}` ({len(roots)} root(s): {roots}) ===",
          flush=True)
    _git(["checkout", "-b", refactor_branch, SERVER_BRANCH])

    # Folder doesn't exist yet; create it before any tool writes there.
    refactor_folder.mkdir(parents=True, exist_ok=True)

    # Run find_dependents.py once per root. Each invocation does its
    # own rename + lake build + restore (try/finally inside
    # find_dependents), so scans are baseline-pristine and independent.
    # Per-root scan JSONs are kept for audit; we also assemble a
    # combined "per_root" JSON to hand to initialize_refactor.
    per_root_scans: dict[str, dict] = {}
    for root in roots:
        scan_path = refactor_folder / f"dependents_scan_{root}.json"
        print(f"\n[do_refactor] === find_dependents.py (root: {root}) ===",
              flush=True)
        fd_cmd = [
            "python3", str(EXTRAS / "find_dependents.py"),
            "--chapter", str(args.chapter),
            "--ref", root,
            "--out", str(scan_path),
        ]
        if args.no_build:
            fd_cmd.append("--no-build")
        if root in decl_overrides:
            fd_cmd.extend(["--decl-name", decl_overrides[root]])
        _run(fd_cmd)
        if not scan_path.exists():
            sys.exit(f"ERROR: find_dependents.py did not produce "
                     f"{scan_path}")
        per_root_scans[root] = json.loads(
            scan_path.read_text(encoding="utf-8"))

    # Combined dependents JSON (handed to initialize_refactor.py). The
    # `per_root` shape preserves provenance so initialize_refactor can
    # attach `caused_by_roots` to every dependent row.
    combined_path = refactor_folder / "dependents_scan.json"
    combined_path.write_text(
        json.dumps({
            "roots": roots,
            "per_root": {
                root: {"consumer_refs":
                       per_root_scans[root].get("consumer_refs", [])}
                for root in roots
            },
        }, indent=2) + "\n",
        encoding="utf-8",
    )
    print(f"\n[do_refactor] === Combined dependents -> "
          f"{combined_path.relative_to(REPO_ROOT)} ===", flush=True)

    # Initialize the refactor table.
    print(f"\n[do_refactor] === Running initialize_refactor.py ===",
          flush=True)
    ir_cmd = [
        "python3", str(EXTRAS / "initialize_refactor.py"),
        "--root-chapter", str(args.chapter),
        "--root-refs", ",".join(roots),
        "--name", args.name,
        "--dependents-json", str(combined_path),
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
    # Snapshot which deviation entries this refactor is meant to
    # resolve: any entry in the register whose `introduced_by_ref`
    # is in the refactor table's row set. These ids are then blocked
    # at solve-time -- accept_deviation refuses to acknowledge them,
    # forcing the refactor to actually FIX the issue (so the strict
    # gate passes cleanly) rather than rubber-stamp it.
    sys.path.insert(0, str(SCAFFOLD / "scripts"))
    import _path_setup                                                # noqa: F401
    from deviations import load_register                              # type: ignore
    refactor_refs = {r["ref"] for r in
                     json.loads(refactor_data.read_text())["rows"]}
    deviations_to_resolve = sorted(
        e["id"] for e in load_register(include_resolved=False)
        if e.get("introduced_by_ref") in refactor_refs
    )
    print(f"\n[do_refactor] === Snapshotting deviations_to_resolve "
          f"({len(deviations_to_resolve)} entry(s)) ===",
          file=sys.stderr, flush=True)
    for did in deviations_to_resolve:
        print(f"  - {did}", file=sys.stderr)

    _write_state(refactor_folder, {
        "source_branch":          SERVER_BRANCH,
        "refactor_branch":        refactor_branch,
        "roots":                  roots,
        "root_ref":               roots[0],     # legacy alias
        "name":                   args.name,
        "chapter":                args.chapter,
        "init_date":              datetime.now(timezone.utc).isoformat(timespec="seconds"),
        "deviations_to_resolve":  deviations_to_resolve,
    })

    # Commit + push
    print(f"\n[do_refactor] === Committing + pushing refactor branch ===",
          flush=True)
    _git(["add", str(refactor_folder.relative_to(REPO_ROOT))])
    msg = (f"refactor:init: {args.name} "
           f"(roots: {', '.join(roots)}); "
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
    print(f"  roots:           {', '.join(roots)}")
    print(f"  refactor table:  {rel} ({n_rows} rows)")
    print(f"\nNext step -- drive the refactor table to completion "
          f"(may take many sessions):")
    print(f"  python scaffold/scripts/phase3_solving/solve_chapter.py --data-path {rel}")
    print(f"\nOnce every row is solved=yes, finalize with:")
    print(f"  python extras/do_refactor.py finalize --refactor-data {rel}")
    return 0


# ---------------------------------------------------------------------------
# finalize
# ---------------------------------------------------------------------------

_POLISH_WORKER_PROMPT = (
    SCAFFOLD / "claude_prompts" / "phase3_solving"
    / "row_workers" / "polish_refactor_comments.md"
)
_POLISH_PER_FILE_TIMEOUT_S = 900   # 15 min per file; the worker is small


def _run_polish_worker(file_path: Path, refactor_name: str,
                       roots: list[str]) -> bool:
    """Spawn the polish_refactor_comments worker against a single Lean
    file. Returns True iff the worker exited 0; on timeout / non-zero
    exit, prints a warning and returns False (the file is left as-is).

    The worker reads the prompt at ``polish_refactor_comments.md``
    plus the brief constructed here, then makes its own Edit calls to
    rewrite comments. The dispatcher doesn't validate the worker's
    edits beyond the post-step lake build (see ``_post_polish_lake_check``).
    """
    if not _POLISH_WORKER_PROMPT.exists():
        print(f"  WARNING: polish worker prompt missing at "
              f"{_POLISH_WORKER_PROMPT.relative_to(REPO_ROOT)}; "
              f"skipping polish for this file.")
        return False

    rel = file_path.relative_to(REPO_ROOT)
    prompt = _POLISH_WORKER_PROMPT.read_text(encoding="utf-8")
    brief = (
        f"\n\n# Brief\n\n"
        f"- Lean file to polish (absolute path): `{file_path}`\n"
        f"- Lean file (repo-relative): `{rel}`\n"
        f"- Refactor name: `{refactor_name}`\n"
        f"- Refactor root refs: {', '.join(roots)}\n"
        f"\nFollow the worker prompt above: read the whole file, write "
        f"the plan, apply Edits in plan order, sanity-check, report.\n"
    )
    full_prompt = prompt + brief

    cmd = [
        "claude", "-p", "--dangerously-skip-permissions",
        "--model", "claude-opus-4-7",
        "--effort", "max",
        "--output-format", "json",
    ]
    try:
        result = subprocess.run(
            cmd, input=full_prompt.encode("utf-8"),
            capture_output=True,
            timeout=_POLISH_PER_FILE_TIMEOUT_S,
        )
    except subprocess.TimeoutExpired:
        print(f"  WARNING: polish worker on {rel} timed out after "
              f"{_POLISH_PER_FILE_TIMEOUT_S//60} min; leaving as-is.")
        return False
    except FileNotFoundError:
        print(f"  WARNING: `claude` CLI not on PATH; skipping polish.")
        return False

    if result.returncode != 0:
        stderr_tail = (result.stderr or b"").decode(
            "utf-8", errors="replace")[:500]
        print(f"  WARNING: polish worker on {rel} exited "
              f"{result.returncode}; leaving as-is.\n"
              f"    stderr: {stderr_tail}")
        return False
    return True


def _polish_refactor_comments(archived_data: Path, state: dict) -> None:
    """Iterate the archived refactor table's affected Lean files and
    dispatch the polish worker on each. All errors are best-effort: a
    file that fails polish is left as-is; the commit step still runs.
    """
    try:
        data = json.loads(archived_data.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as e:
        print(f"  WARNING: could not read archived refactor_data.json: "
              f"{e}; skipping polish step.")
        return

    roots = state.get("roots") or [state.get("root_ref", "")]
    affected: set[Path] = set()
    for row in data.get("rows", []):
        if row.get("main_lean_file"):
            affected.add(REPO_ROOT / row["main_lean_file"])
        for lf in row.get("lean_files") or []:
            affected.add(REPO_ROOT / lf)

    n_ok = 0
    n_total = 0
    for f in sorted(affected):
        if not f.exists():
            print(f"  - {f.relative_to(REPO_ROOT)}: not on disk, skipping")
            continue
        n_total += 1
        print(f"  - {f.relative_to(REPO_ROOT)}: dispatching polish worker ...")
        if _run_polish_worker(f, state["name"], roots):
            n_ok += 1
    if n_total == 0:
        print(f"  no Lean files to polish.")
    else:
        print(f"  polish: {n_ok}/{n_total} file(s) cleaned by the worker.")


def _post_polish_lake_check() -> None:
    """Run `lake build` after the polish step to confirm the worker
    didn't accidentally damage non-comment code. Non-fatal: a failure
    here logs a loud warning but lets build_and_commit.sh run (which
    will itself fail loudly if the build is broken, halting the commit).
    """
    try:
        r = subprocess.run(
            ["lake", "build"], cwd=str(REPO_ROOT),
            capture_output=True, timeout=900,
        )
    except subprocess.TimeoutExpired:
        print(f"  WARNING: post-polish lake build timed out; "
              f"build_and_commit.sh will re-run it.")
        return
    except FileNotFoundError:
        print(f"  WARNING: `lake` not on PATH; skipping post-polish "
              f"build check.")
        return
    if r.returncode == 0:
        print(f"  build clean.")
    else:
        tail = ((r.stdout or b"") + (r.stderr or b"")).decode(
            "utf-8", errors="replace").splitlines()[-15:]
        print(f"  WARNING: lake build returned {r.returncode} after "
              f"polish. Tail:\n  " + "\n  ".join(tail))
        print(f"  The polish worker may have edited non-comment "
              f"code; build_and_commit.sh will refuse to commit if "
              f"so.")


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
    if getattr(args, "auto_rename_strays", False):
        rc_cmd.append("--auto-rename-strays")
    if getattr(args, "allow_strays", False):
        rc_cmd.append("--allow-strays")
    if getattr(args, "skip_dup_check", False):
        rc_cmd.append("--skip-dup-check")
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

    # LLM polish step: dispatch the polish_refactor_comments worker
    # per affected Lean file to remove leftover "refactor"/"pre-refactor"
    # /"post-refactor" prose, stale tex-twin cross-references, and
    # coexistence-narrative paragraphs that Pass 3's regex didn't quite
    # catch. Comment-edit only — the worker prompt forbids touching any
    # non-comment code. Best-effort: timeouts / non-zero exits log a
    # warning and skip the affected file; the commit step still runs.
    print(f"\n[do_refactor] === Polish step: refactor-naming comment "
          f"cleanup ===", flush=True)
    _polish_refactor_comments(archived_data, state)

    # Verify the polish didn't break anything before commit.
    print(f"\n[do_refactor] === Post-polish lake build ===", flush=True)
    _post_polish_lake_check()

    print(f"\n[do_refactor] === Committing + pushing via "
          f"build_and_commit.sh ===", flush=True)
    roots = state.get("roots") or [state["root_ref"]]
    roots_str = ", ".join(roots)
    msg = (f"refactor:finalize: {state['name']} "
           f"(root{'s' if len(roots) > 1 else ''}: {roots_str}, "
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
    """The cleanup script renamed Refactor_<name>/ -> Refactor_<name>_<marker>_<YYYY-MM-DD>[_vN]/
    where ``<marker>`` is ``DONE`` on a clean run and ``BUILDFAIL`` if
    phase 7b's lake build failed. Find the most recent archive."""
    chapter_folder = _find_chapter_folder(state["chapter"])
    name = state["name"]
    candidates = sorted(
        list(chapter_folder.glob(f"Refactor_{name}_DONE_*"))
        + list(chapter_folder.glob(f"Refactor_{name}_BUILDFAIL_*"))
    )
    if not candidates:
        sys.exit(f"ERROR: cannot find archived refactor folder under "
                 f"{chapter_folder} -- expected "
                 f"`Refactor_{name}_(DONE|BUILDFAIL)_*`; "
                 f"did the cleanup's archive phase run?")
    # Prefer one matching today's date, else the most recent. The same-day
    # collision suffix (`_vN`) is included so the most recent v-suffixed
    # archive wins.
    for c in reversed(candidates):
        if today in c.name:
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
    roots = state.get("roots") or [state["root_ref"]]
    merge_msg = (f"refactor: merge `{state['name']}` "
                 f"(root{'s' if len(roots) > 1 else ''}: "
                 f"{', '.join(roots)}) from {refactor_branch}")
    _git(["merge", "--no-ff", refactor_branch, "-m", merge_msg])

    # Optional push of the merged source branch
    if args.push:
        print(f"\n[do_refactor] === Pushing {source_branch} ===", flush=True)
        _git(["push", "origin", source_branch])
    else:
        print(f"\n[do_refactor] (skipping push; pass --push to publish "
              f"{source_branch} to origin)", flush=True)

    # Optional remote branch deletion. Guarded against deleting any
    # PROTECTED_BRANCHES member (server / main / master) -- if the
    # state file's ``refactor_branch`` has been corrupted to one of
    # those, the script aborts before issuing the push.
    if args.delete_remote_branch:
        _assert_safe_to_delete(refactor_branch)
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

    # Optional local branch deletion (only if remote already gone).
    # Same protected-branches guard applies.
    if args.delete_remote_branch:
        _assert_safe_to_delete(refactor_branch)
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
                        help="chapter under which to place the "
                             "Refactor_<name>/ folder")
    p_init.add_argument("--root-refs", type=str, default="",
                        help="comma-separated root refs being refactored "
                             "(e.g. `def_3_1,def_3_4`). Multi-root "
                             "refactors run all roots' dependency scans "
                             "and union the results into one table.")
    p_init.add_argument("--root-ref", type=str, default="",
                        help="[DEPRECATED] single root ref; use "
                             "--root-refs instead. Kept as a single-"
                             "element alias for back-compat.")
    p_init.add_argument("--name", type=str, required=True,
                        help="refactor name (becomes the "
                             "refactor_<name> branch + Refactor_<name>/ "
                             "folder); make it semantically describe "
                             "the bundle, e.g. "
                             "ch3_disjoint_EL_and_collider_loose.")
    p_init.add_argument("--decl-name", type=str, default=None,
                        help="[single-root only] Lean declaration name "
                             "to rename in the find_dependents scan "
                             "(default: row's `title`). For multi-root, "
                             "use --decl-names.")
    p_init.add_argument("--decl-names", type=str, default="",
                        help="per-root decl-name overrides as "
                             "`root1=Name1,root2=Name2`; roots not "
                             "listed fall back to their row `title`.")
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
    p_fin_strays = p_fin.add_mutually_exclusive_group()
    p_fin_strays.add_argument("--auto-rename-strays", action="store_true",
                              help="forward --auto-rename-strays to "
                                   "apply_refactor_cleanup; drops the "
                                   "`refactor_` prefix on any top-level "
                                   "`refactor_*` decl not covered by a "
                                   "REPLACEMENT marker (collision-checked)")
    p_fin_strays.add_argument("--allow-strays", action="store_true",
                              help="forward --allow-strays to "
                                   "apply_refactor_cleanup; last resort")
    p_fin.add_argument("--skip-dup-check", action="store_true",
                       help="forward --skip-dup-check to "
                            "apply_refactor_cleanup; skips Pass 1.7's "
                            "predicted-duplicate-decl gate (use only "
                            "after confirming false positives by hand)")

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
