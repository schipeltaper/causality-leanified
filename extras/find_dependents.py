#!/usr/bin/env python3
"""Bullet-proof dependency scanner: which rows depend on a given def/claim?

The Phase 4 step of a refactor: before touching a row's encoding, list
every other row (in this chapter and every other chapter) whose Lean
files use the row's declaration -- directly or transitively. The result
is the seed list for the refactor table built by
``initialize_refactor.py``.

Bullet-proof method (two complementary passes, results are unioned):

1. **Rename + lake build.** Read the target row's ``main_lean_file``;
   rename the top-level declaration matching the row's ``title`` to
   ``<title>_REFACTOR_DISABLED``. Run ``lake build`` from the repo
   root. Every error site (file + line) is a consumer -- direct
   consumers fail with ``unknown identifier 'CDMG'``, transitive
   consumers fail with ``module X failed to compile``. Restore the
   file from the in-memory snapshot in a ``finally`` clause so an
   interrupted run leaves the repo clean.

2. **`git grep`.** Catches references in comments, strings, and any
   syntactic context the rename misses (e.g., a metaprogram that
   constructs the name from a string).

The script also walks every ``leanification/Chapter*/data.json`` (it
skips refactor tables) to map Lean file paths back to the rows that
own them, so the output includes ``consumer_refs`` -- the refs you'd
feed to ``initialize_refactor.py``.

Prerequisites:
- The repo must build cleanly before invocation (the script does NOT
  diff against a baseline; it assumes the build was clean and any
  post-rename error is a consequence of the rename).

Usage::

    python extras/find_dependents.py --chapter 3 --ref def_3_1
    python extras/find_dependents.py --chapter 3 --ref def_3_1 \
        --out /tmp/cdmg_dependents.json
    python extras/find_dependents.py --chapter 3 --ref def_3_1 \
        --no-build     # skip lake build, do only git grep (fast)
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
LEANIFICATION = REPO_ROOT / "leanification"

# Lean declaration keywords (the ones we rename). `noncomputable` and
# `private` etc. modifiers are handled by anchoring on the keyword.
_DECL_KEYWORDS = (
    "def", "theorem", "lemma", "structure", "class", "abbrev",
    "instance", "inductive", "opaque",
)

# Template: ``(prefix = keyword + space)(name)\b`` -- matches the first
# top-level occurrence on a line. Modifiers like ``noncomputable`` are
# captured by allowing optional leading words before the keyword.
def _decl_re(name: str) -> re.Pattern[str]:
    return re.compile(
        r"^(?P<prefix>(?:[\w]+\s+)?(?:"
        + "|".join(re.escape(k) for k in _DECL_KEYWORDS)
        + r")\s+)(?P<name>" + re.escape(name) + r")\b",
        re.MULTILINE,
    )


def _find_declarations(content: str, name: str) -> list[tuple[int, str]]:
    """Return ``[(line_number, full_match_text), ...]`` for every
    top-level declaration of ``name`` in ``content``. Lines are 1-based."""
    pattern = _decl_re(name)
    hits: list[tuple[int, str]] = []
    for m in pattern.finditer(content):
        line_no = content[: m.start()].count("\n") + 1
        hits.append((line_no, m.group(0)))
    return hits


def _rename_declaration(file_path: Path, name: str, new_name: str) -> str:
    """Rename top-level declarations of ``name`` to ``new_name`` in
    ``file_path``. Returns the original content for restoration. Raises
    ``RuntimeError`` if no declaration was matched."""
    original = file_path.read_text(encoding="utf-8")
    pattern = _decl_re(name)
    modified, n_subs = pattern.subn(
        lambda m: m.group("prefix") + new_name, original
    )
    if n_subs == 0:
        raise RuntimeError(
            f"could not find top-level declaration `{name}` in {file_path}"
        )
    file_path.write_text(modified, encoding="utf-8")
    return original


def _restore_file(file_path: Path, original: str) -> None:
    file_path.write_text(original, encoding="utf-8")


def _run_lake_build(timeout_sec: int) -> tuple[int, str]:
    """Run ``lake build`` from the repo root. Returns
    ``(returncode, stdout+stderr_combined)``. Raises
    ``subprocess.TimeoutExpired`` on timeout."""
    r = subprocess.run(
        ["lake", "build"],
        cwd=str(REPO_ROOT),
        capture_output=True, text=True, timeout=timeout_sec,
    )
    return r.returncode, (r.stdout or "") + (r.stderr or "")


# Lake error lines look like:
#   error: ./leanification/Chapter3_GraphTheory/Section3_2/Walk.lean:42:5: ...
#   warning: ./<path>:LINE:COL: ...
# We capture all of them in .lean files (errors AND build-failure warnings
# both indicate the file's compile depends on something now broken).
_LAKE_ERR_RE = re.compile(
    r"^(?P<level>error|warning):\s+\.?\/?(?P<file>\S+\.lean):"
    r"(?P<line>\d+):(?P<col>\d+):\s*(?P<msg>.*)$",
    re.MULTILINE,
)


def _parse_lake_errors(blob: str) -> list[dict]:
    """Pull every error/warning site in a .lean file out of the lake
    build output. Caller is responsible for distinguishing "real" errors
    (introduced by the rename) from preexisting noise."""
    hits = []
    seen: set[tuple[str, int]] = set()
    for m in _LAKE_ERR_RE.finditer(blob):
        key = (m.group("file"), int(m.group("line")))
        if key in seen:
            continue
        seen.add(key)
        hits.append({
            "level":   m.group("level"),
            "file":    m.group("file").lstrip("./"),
            "line":    int(m.group("line")),
            "col":     int(m.group("col")),
            "snippet": m.group("msg").strip()[:200],
        })
    return hits


def _hit_key(h: dict) -> tuple:
    """Stable key for an error/warning entry. Includes file + line +
    level + first 80 chars of the snippet. snippet-prefix matters
    because a single line can host multiple distinct warnings (we
    want to detect "new" warnings even at the same line)."""
    return (h.get("file"), h.get("line"), h.get("level"),
            (h.get("snippet") or "")[:80])


def _hash_lake_hits(hits: list[dict]) -> set[tuple]:
    """Project a list of lake error/warning entries into a set of
    stable keys, for set-diff against another build."""
    return {_hit_key(h) for h in hits}


def _git_grep(name: str) -> list[dict]:
    """``git grep -nw <name>`` under leanification/Chapter*/. Returns
    one entry per match. Note: a hit in the target row's own file is
    expected (the declaration itself); the caller filters it out."""
    r = subprocess.run(
        ["git", "grep", "-n", "-w", name, "--",
         "leanification/"],
        cwd=str(REPO_ROOT),
        capture_output=True, text=True,
    )
    # `git grep` returns 1 when there are no matches; not an error.
    hits = []
    for line in (r.stdout or "").splitlines():
        # Format: ``path:line:content``
        parts = line.split(":", 2)
        if len(parts) != 3:
            continue
        try:
            ln = int(parts[1])
        except ValueError:
            continue
        hits.append({
            "file":    parts[0].lstrip("./"),
            "line":    ln,
            "snippet": parts[2][:200],
        })
    return hits


def _build_file_to_refs_index() -> dict[str, list[str]]:
    """Walk every ``leanification/Chapter*/data.json`` (NOT refactor
    tables) and map ``"path/to/File.lean" -> [refs that own it]``.
    Used to translate consumer-file hits back into consumer-row refs."""
    index: dict[str, set[str]] = {}
    for data_json in sorted(LEANIFICATION.glob("Chapter*/data.json")):
        try:
            data = json.loads(data_json.read_text(encoding="utf-8"))
        except json.JSONDecodeError:
            continue
        for row in data.get("rows", []):
            ref = row.get("ref")
            if not ref:
                continue
            for lf in (row.get("lean_files") or []):
                index.setdefault(lf.lstrip("./"), set()).add(ref)
            mlf = row.get("main_lean_file")
            if mlf:
                index.setdefault(mlf.lstrip("./"), set()).add(ref)
    return {k: sorted(v) for k, v in index.items()}


def _find_chapter_data_path(chapter: int) -> Path:
    for child in sorted(LEANIFICATION.iterdir()):
        if child.is_dir() and child.name.startswith(f"Chapter{chapter}_"):
            return child / "data.json"
    raise FileNotFoundError(
        f"no leanification folder for chapter {chapter}"
    )


def _section_for_file(lean_path: str, index: dict[str, list[str]],
                      all_data: list[dict]) -> str | None:
    """Best-effort: walk the chapter data.json for the row that owns
    this Lean file and return its ``section``. ``None`` if unknown."""
    refs = index.get(lean_path, [])
    if not refs:
        return None
    for data in all_data:
        for row in data.get("rows", []):
            if row.get("ref") in refs:
                return row.get("section")
    return None


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(
        description=("Find every row that depends on the given def/claim "
                     "(transitive + grep cross-check). Repo must build "
                     "cleanly before invocation."),
    )
    parser.add_argument("--chapter", type=int, required=True,
                        help="chapter number of the target row")
    parser.add_argument("--ref", type=str, required=True,
                        help="row ref, e.g. def_3_1")
    parser.add_argument("--decl-name", type=str, default=None,
                        help="declaration name to rename (default: row's "
                             "`title`). Override when the row's Lean "
                             "declaration name differs from its title.")
    parser.add_argument("--out", type=Path, default=None,
                        help="write JSON to PATH (default: stdout)")
    parser.add_argument("--no-build", action="store_true",
                        help="skip rename + lake build; do only git grep")
    parser.add_argument("--build-timeout", type=int, default=900,
                        help="lake build timeout in seconds (default 900)")
    args = parser.parse_args(argv)

    # ----- Resolve the row + target file -----------------------------
    try:
        data_path = _find_chapter_data_path(args.chapter)
    except FileNotFoundError as e:
        print(f"ERROR: {e}", file=sys.stderr)
        return 1
    data = json.loads(data_path.read_text(encoding="utf-8"))
    row = next((r for r in data["rows"] if r.get("ref") == args.ref), None)
    if row is None:
        print(f"ERROR: ref {args.ref!r} not found in {data_path}",
              file=sys.stderr)
        return 1

    decl_name = args.decl_name or row.get("title")
    if not decl_name:
        print(f"ERROR: row {args.ref!r} has no `title`; pass "
              f"--decl-name explicitly", file=sys.stderr)
        return 1
    target_file = row.get("main_lean_file")
    if not target_file:
        print(f"ERROR: row {args.ref!r} has no `main_lean_file`; can't "
              f"locate the declaration", file=sys.stderr)
        return 1
    target_path = REPO_ROOT / target_file
    if not target_path.exists():
        print(f"ERROR: target Lean file does not exist: {target_path}",
              file=sys.stderr)
        return 1

    # If the decl_name isn't a top-level declaration of main_lean_file,
    # fall back to scanning the row's `lean_files` siblings. Use case:
    # def_3_4 (title `Walks`, main `Walks.lean`) is the row whose
    # IsCollider definition lives in WalkPredicates.lean (a sibling in
    # the same row's lean_files). Without this fallback the caller
    # would have to add a --target-file CLI override.
    if not _find_declarations(target_path.read_text(encoding="utf-8"),
                              decl_name):
        matches: list[str] = []
        for lf in row.get("lean_files") or []:
            p = REPO_ROOT / lf
            if p == target_path or not p.exists():
                continue
            if _find_declarations(p.read_text(encoding="utf-8"), decl_name):
                matches.append(lf)
        if len(matches) == 1:
            print(f"[find_dependents] `{decl_name}` not in "
                  f"{target_file}; found in sibling `{matches[0]}` -- "
                  f"using that as target.", file=sys.stderr)
            target_file = matches[0]
            target_path = REPO_ROOT / target_file
        elif len(matches) > 1:
            print(f"ERROR: `{decl_name}` found in multiple sibling "
                  f"lean_files: {matches}. Disambiguate by passing "
                  f"--decl-name to a unique declaration.", file=sys.stderr)
            return 1
        # zero matches -> let the existing error path at line ~337 fire

    result: dict = {
        "target_ref":   args.ref,
        "target_title": decl_name,
        "target_file":  target_file,
        "method":       ("grep only" if args.no_build
                         else "rename + lake build + grep"),
        "grep_hits":    [],
        "lake_errors":  [],
        "consumer_files": [],
        "consumer_refs":  [],
    }

    # ----- Pass 1: git grep (cheap, always run) ----------------------
    print(f"[find_dependents] git grep -nw {decl_name} under leanification/ ...",
          file=sys.stderr, flush=True)
    result["grep_hits"] = _git_grep(decl_name)
    print(f"[find_dependents]   -> {len(result['grep_hits'])} grep hit(s)",
          file=sys.stderr, flush=True)

    # ----- Pass 2: baseline + rename + lake build, then diff ---------
    # Why the diff: lake emits pre-existing LINTER WARNINGS on every
    # file it walks (unused vars, deprecated tactics, line-length
    # nits) -- those have nothing to do with the rename but, if we
    # scrape them as "errors", they wrongly flag every file with
    # any pre-existing noise as a "consumer". Caught when
    # def_3_14_no_L_exclusion's initial scan reported claim_3_12,
    # claim_3_23, claim_3_27 as consumers (3 false positives out of
    # 9 "consumers" reported) because their files happened to have
    # pre-existing linter warnings.
    #
    # Fix: run lake build BEFORE the rename to capture every
    # baseline error+warning site as a set of (file, line, level,
    # msg_prefix) tuples. Then after the rename, scrape again, and
    # subtract: only entries that newly appear post-rename are real
    # signals of the rename's breakage.
    #
    # The diff also won't catch transitive cascades that lake
    # short-circuits (when the rename's home file fails, dependent
    # files are never attempted by lake -- so they never produce
    # post-rename errors either). For those we rely on the git grep
    # pass (which catches every direct text-reference to the symbol)
    # and on _build_file_to_refs_index mapping greps to refs.
    if not args.no_build:
        decls = _find_declarations(target_path.read_text(encoding="utf-8"),
                                   decl_name)
        if not decls:
            print(f"ERROR: no top-level declaration `{decl_name}` found in "
                  f"{target_path}; pass --decl-name if the Lean name "
                  f"differs from the row title.", file=sys.stderr)
            return 1
        print(f"[find_dependents] found {len(decls)} declaration(s) of "
              f"`{decl_name}` at line(s) "
              f"{', '.join(str(ln) for ln, _ in decls)}",
              file=sys.stderr, flush=True)

        # --- Baseline build (pre-rename) ---
        print(f"[find_dependents] capturing baseline (pre-rename lake "
              f"build, expected clean)...", file=sys.stderr, flush=True)
        try:
            base_rc, base_blob = _run_lake_build(args.build_timeout)
        except subprocess.TimeoutExpired:
            print(f"[find_dependents] BASELINE lake build timed out; "
                  f"falling back to no-baseline mode (post-rename "
                  f"errors will include pre-existing warnings).",
                  file=sys.stderr, flush=True)
            base_blob = ""
            base_rc = -1
        print(f"[find_dependents]   baseline returncode={base_rc}",
              file=sys.stderr, flush=True)
        baseline_set = _hash_lake_hits(_parse_lake_errors(base_blob))
        print(f"[find_dependents]   baseline has "
              f"{len(baseline_set)} unique error/warning site(s)",
              file=sys.stderr, flush=True)

        # --- Rename + post-rename build ---
        new_name = f"{decl_name}_REFACTOR_DISABLED"
        original = None
        try:
            original = _rename_declaration(target_path, decl_name, new_name)
            print(f"[find_dependents] renamed `{decl_name}` -> `{new_name}`; "
                  f"running post-rename `lake build` (timeout "
                  f"{args.build_timeout}s) ...",
                  file=sys.stderr, flush=True)
            try:
                rc, blob = _run_lake_build(args.build_timeout)
                print(f"[find_dependents] post-rename returncode={rc}",
                      file=sys.stderr, flush=True)
                post_hits = _parse_lake_errors(blob)
                # Diff: keep only hits whose (file, line, level, prefix)
                # tuple wasn't in baseline AND whose level is 'error'.
                # Pure warnings still get filtered (they're noise even
                # when "new" -- e.g., a one-line shift caused by some
                # other concurrent edit could shift a warning's line).
                new_hits = [h for h in post_hits
                            if _hit_key(h) not in baseline_set
                            and h.get("level") == "error"]
                result["lake_errors"] = new_hits
                print(f"[find_dependents]   raw post-rename hits: "
                      f"{len(post_hits)}; new ERRORS after diff: "
                      f"{len(new_hits)}", file=sys.stderr, flush=True)
            except subprocess.TimeoutExpired:
                print(f"[find_dependents] post-rename lake build timed "
                      f"out after {args.build_timeout}s",
                      file=sys.stderr, flush=True)
                result["error"] = (
                    f"lake build timed out after {args.build_timeout}s; "
                    "use --build-timeout to extend or --no-build to skip"
                )
        finally:
            if original is not None:
                _restore_file(target_path, original)
                print(f"[find_dependents] restored {target_path}",
                      file=sys.stderr, flush=True)

    # ----- Union the file lists + map to refs ------------------------
    consumer_files: set[str] = set()
    for hit in result["lake_errors"] + result["grep_hits"]:
        f = hit["file"].lstrip("./")
        if f != target_file.lstrip("./"):    # exclude the row's own file
            consumer_files.add(f)
    result["consumer_files"] = sorted(consumer_files)

    index = _build_file_to_refs_index()
    all_data = []
    for dj in sorted(LEANIFICATION.glob("Chapter*/data.json")):
        try:
            all_data.append(json.loads(dj.read_text(encoding="utf-8")))
        except json.JSONDecodeError:
            pass
    consumer_refs: set[str] = set()
    for cf in consumer_files:
        for ref in index.get(cf, []):
            if ref != args.ref:
                consumer_refs.add(ref)
    result["consumer_refs"] = sorted(consumer_refs)

    print(f"[find_dependents] DONE: {len(result['consumer_files'])} "
          f"consumer file(s), {len(result['consumer_refs'])} consumer ref(s)",
          file=sys.stderr, flush=True)

    # ----- Output ----------------------------------------------------
    out_text = json.dumps(result, indent=2, ensure_ascii=False) + "\n"
    if args.out:
        args.out.write_text(out_text, encoding="utf-8")
        print(f"[find_dependents] wrote {args.out}",
              file=sys.stderr, flush=True)
    else:
        sys.stdout.write(out_text)

    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
