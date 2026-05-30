#!/usr/bin/env python3
"""Phase 7 cleanup: apply a completed refactor table by swapping every
``refactor_<X>`` declaration in for the original ``<X>``.

Given a refactor table whose rows all read ``solved=yes``, this script
walks every Lean file the table touched and:

1. **Deletes** every ``REFACTOR-BLOCK-ORIGINAL-BEGIN: <Name>`` ...
   ``REFACTOR-BLOCK-ORIGINAL-END: <Name>`` block (the old definition
   that the refactor superseded).
2. **Strips** the ``REFACTOR-BLOCK-REPLACEMENT-BEGIN/END`` markers
   around the new definition while keeping its body in place.
3. **Renames** every whole-word occurrence of ``refactor_<Name>`` ->
   ``<Name>`` across the file (declaration heads + every use site).

Validation gate before any write: each block's BEGIN must have a
matching END with the same name, every ORIGINAL block must have a
matching REPLACEMENT (and vice versa), and the file must be UTF-8
text. If any check fails the file is left untouched and the script
exits non-zero so the caller can investigate.

By default ends with ``lake build`` to confirm the swap is consistent;
pass ``--no-lake-build`` to skip (e.g., when iterating on a dry-run).

Usage::

    # Preview the diff for every affected file:
    python extras/apply_refactor_cleanup.py \
        --refactor-data leanification/Chapter3_GraphTheory/Refactor_X/refactor_data.json \
        --dry-run

    # Apply for real (default: runs lake build afterwards):
    python extras/apply_refactor_cleanup.py \
        --refactor-data leanification/Chapter3_GraphTheory/Refactor_X/refactor_data.json

    # Apply without the final lake build (faster, but you should run
    # build manually after):
    python extras/apply_refactor_cleanup.py \
        --refactor-data leanification/Chapter3_GraphTheory/Refactor_X/refactor_data.json \
        --no-lake-build
"""

from __future__ import annotations

import argparse
import difflib
import json
import re
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent

# Marker regexes. The BEGIN/END must agree on the name (enforced via
# back-reference in the block-level regex below).
_BEGIN_RE = re.compile(
    r"--\s*REFACTOR-BLOCK-(?P<kind>ORIGINAL|REPLACEMENT)-BEGIN:\s*"
    r"(?P<name>[A-Za-z_][\w]*)",
    re.IGNORECASE,
)
_END_RE = re.compile(
    r"--\s*REFACTOR-BLOCK-(?P<kind>ORIGINAL|REPLACEMENT)-END:\s*"
    r"(?P<name>[A-Za-z_][\w]*)",
    re.IGNORECASE,
)

# A complete marker block: BEGIN line, body, matching END line. The `\1`
# and `\2` back-references force kind + name to match. The optional
# ``(was: refactor_X)`` part on REPLACEMENT-BEGIN is just commentary
# absorbed by the trailing ``[^\n]*``.
_BLOCK_RE = re.compile(
    r"^[ \t]*--\s*REFACTOR-BLOCK-(ORIGINAL|REPLACEMENT)-BEGIN:\s*"
    r"([A-Za-z_][\w]*)[^\n]*\n"
    r"(.*?)"
    r"^[ \t]*--\s*REFACTOR-BLOCK-\1-END:\s*\2[^\n]*\n?",
    re.MULTILINE | re.DOTALL | re.IGNORECASE,
)


def _parse_marker_blocks(content: str) -> list[dict]:
    """Return every marker block in source order, each as::

        {kind: "original" | "replacement",
         name: <FinalName>,
         start: <char offset of BEGIN line>,
         end:   <char offset just past the END line>,
         full:  <substring covering the whole block>,
         body:  <substring between BEGIN and END, exclusive>}
    """
    return [
        {
            "kind":  m.group(1).lower(),
            "name":  m.group(2),
            "start": m.start(),
            "end":   m.end(),
            "full":  m.group(0),
            "body":  m.group(3),
        }
        for m in _BLOCK_RE.finditer(content)
    ]


def _check_unmatched_markers(content: str, file_path: Path) -> list[str]:
    """Return a list of complaints if any BEGIN has no matching END (or
    vice versa). Walks BEGIN / END independently of ``_BLOCK_RE`` so
    that a missing END can be diagnosed precisely."""
    complaints: list[str] = []
    begins: list[tuple[int, str, str]] = []     # (line, kind, name)
    ends: list[tuple[int, str, str]] = []
    for i, line in enumerate(content.splitlines(), start=1):
        bm = _BEGIN_RE.search(line)
        em = _END_RE.search(line)
        if bm:
            begins.append((i, bm.group("kind").lower(), bm.group("name")))
        if em:
            ends.append((i, em.group("kind").lower(), em.group("name")))
    # Walk in pairs: every BEGIN should be followed by a matching END
    # before the next BEGIN of the same (kind, name).
    open_stack: dict[tuple[str, str], int] = {}
    for ln, kind, name in sorted(begins + ends, key=lambda x: x[0]):
        key = (kind, name)
        is_begin = any(b == (ln, kind, name) for b in begins)
        if is_begin:
            if key in open_stack:
                complaints.append(
                    f"{file_path}:{ln}: nested BEGIN for "
                    f"{kind} {name!r} (already open at line {open_stack[key]})")
            open_stack[key] = ln
        else:
            if key not in open_stack:
                complaints.append(
                    f"{file_path}:{ln}: END for {kind} {name!r} with no "
                    f"matching BEGIN")
            else:
                open_stack.pop(key)
    for (kind, name), ln in open_stack.items():
        complaints.append(
            f"{file_path}: unclosed BEGIN for {kind} {name!r} at line {ln}")
    return complaints


def _validate_blocks(blocks: list[dict], file_path: Path) -> list[str]:
    """Cross-check: every ORIGINAL has a matching REPLACEMENT with the
    same final name, and vice versa. Returns a list of complaints
    (empty = clean)."""
    orig_names = {b["name"] for b in blocks if b["kind"] == "original"}
    repl_names = {b["name"] for b in blocks if b["kind"] == "replacement"}
    complaints: list[str] = []
    only_orig = orig_names - repl_names
    if only_orig:
        complaints.append(
            f"{file_path}: ORIGINAL block(s) without matching "
            f"REPLACEMENT: {sorted(only_orig)} -- refusing to delete "
            f"originals when the refactor isn't complete")
    # only_repl is allowed (a refactor that adds a brand-new declaration
    # with no prior original). Don't complain about it; just rename
    # refactor_X -> X at the end.
    return complaints


def _apply_to_content(content: str, file_path: Path,
                      ) -> tuple[str, list[str], dict]:
    """Apply the cleanup transform to ``content``. Returns
    ``(new_content, complaints, summary_dict)``. If ``complaints`` is
    non-empty, ``new_content`` equals the original (no transform
    attempted)."""
    # Validation first
    unmatched = _check_unmatched_markers(content, file_path)
    if unmatched:
        return content, unmatched, {}
    blocks = _parse_marker_blocks(content)
    semantic = _validate_blocks(blocks, file_path)
    if semantic:
        return content, semantic, {}

    if not blocks:
        return content, [], {
            "originals_deleted":   0,
            "replacements_kept":   0,
            "names_renamed":       [],
        }

    # Process in reverse source order so char offsets stay valid as we
    # splice the string.
    new_content = content
    originals_deleted = 0
    replacements_kept = 0
    final_names: list[str] = []
    for b in sorted(blocks, key=lambda x: x["start"], reverse=True):
        if b["kind"] == "original":
            new_content = new_content[:b["start"]] + new_content[b["end"]:]
            originals_deleted += 1
        else:                                             # replacement
            new_content = new_content[:b["start"]] + b["body"] + new_content[b["end"]:]
            replacements_kept += 1
            final_names.append(b["name"])

    # Rename refactor_<Name> -> <Name>, whole-word. Process names from
    # longest to shortest to avoid prefix collisions (e.g., if both
    # `Foo` and `Foo_Bar` are refactored).
    unique_names = sorted(set(final_names), key=len, reverse=True)
    for name in unique_names:
        pat = re.compile(
            r"(?<![A-Za-z0-9_])refactor_" + re.escape(name)
            + r"(?![A-Za-z0-9_])"
        )
        new_content = pat.sub(name, new_content)

    return new_content, [], {
        "originals_deleted":   originals_deleted,
        "replacements_kept":   replacements_kept,
        "names_renamed":       unique_names,
    }


def _collect_affected_files(refactor_data: dict) -> list[Path]:
    """Union of main_lean_file + lean_files across every row in the
    refactor table. Returned as absolute paths under ``REPO_ROOT``,
    deduplicated, sorted."""
    seen: set[str] = set()
    out: list[Path] = []
    for row in refactor_data.get("rows", []):
        for lf in (row.get("lean_files") or []):
            if lf and lf not in seen:
                seen.add(lf)
                out.append(REPO_ROOT / lf)
        mlf = row.get("main_lean_file")
        if mlf and mlf not in seen:
            seen.add(mlf)
            out.append(REPO_ROOT / mlf)
    return sorted(out)


def _diff(old: str, new: str, label: str) -> str:
    return "".join(difflib.unified_diff(
        old.splitlines(keepends=True),
        new.splitlines(keepends=True),
        fromfile=f"{label} (before)",
        tofile=f"{label} (after)",
    ))


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(
        description="Apply a completed refactor table: swap originals "
                    "for replacements via the marker convention.",
    )
    parser.add_argument("--refactor-data", type=Path, required=True,
                        help="path to the refactor_data.json whose rows "
                             "describe the affected Lean files")
    parser.add_argument("--dry-run", action="store_true",
                        help="print unified diffs without writing")
    parser.add_argument("--no-lake-build", action="store_true",
                        help="skip the final lake build (default: build "
                             "after applying)")
    parser.add_argument("--ignore-unsolved", action="store_true",
                        help="apply even if some refactor rows aren't "
                             "marked solved=yes (NOT recommended)")
    parser.add_argument("--build-timeout", type=int, default=1200)
    args = parser.parse_args(argv)

    # Load the refactor data
    try:
        rd = json.loads(args.refactor_data.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as e:
        print(f"ERROR: cannot read {args.refactor_data}: {e}", file=sys.stderr)
        return 1
    if not rd.get("refactor"):
        print(f"ERROR: {args.refactor_data} doesn't look like a refactor "
              f"table (missing top-level `refactor: true`)", file=sys.stderr)
        return 1

    rows = rd.get("rows", [])
    unsolved = [r["ref"] for r in rows if r.get("solved") != "yes"]
    if unsolved and not args.ignore_unsolved:
        print(f"ERROR: {len(unsolved)} row(s) in the refactor table are "
              f"NOT marked solved=yes: {unsolved}\n  Pass --ignore-"
              f"unsolved to override (NOT recommended -- a partial "
              f"refactor likely won't compile after swap).", file=sys.stderr)
        return 1

    affected = _collect_affected_files(rd)
    print(f"[apply_refactor_cleanup] {len(affected)} Lean file(s) to "
          f"process (mode: {'DRY-RUN' if args.dry_run else 'WRITE'})",
          file=sys.stderr, flush=True)

    total_complaints: list[str] = []
    total_originals_deleted = 0
    total_replacements_kept = 0
    all_renamed: list[str] = []
    transformed_writes: list[tuple[Path, str]] = []     # (path, new_content)
    for p in affected:
        if not p.exists():
            print(f"  - SKIP {p.relative_to(REPO_ROOT)}: file does not exist",
                  file=sys.stderr)
            continue
        try:
            old = p.read_text(encoding="utf-8")
        except UnicodeDecodeError as e:
            total_complaints.append(f"{p}: not valid UTF-8: {e}")
            continue
        new, complaints, summary = _apply_to_content(old, p)
        if complaints:
            total_complaints.extend(complaints)
            continue
        if new == old:
            print(f"  - {p.relative_to(REPO_ROOT)}: no marker blocks (no-op)",
                  file=sys.stderr)
            continue
        total_originals_deleted += summary["originals_deleted"]
        total_replacements_kept += summary["replacements_kept"]
        all_renamed.extend(summary["names_renamed"])
        rel = p.relative_to(REPO_ROOT)
        print(f"  - {rel}: -{summary['originals_deleted']} original, "
              f"+{summary['replacements_kept']} replacement, renamed "
              f"{summary['names_renamed']}", file=sys.stderr)
        if args.dry_run:
            sys.stdout.write(_diff(old, new, str(rel)))
        else:
            transformed_writes.append((p, new))

    if total_complaints:
        print("\nERROR: marker-block validation failed; NO files written:",
              file=sys.stderr)
        for c in total_complaints:
            print(f"  - {c}", file=sys.stderr)
        return 1

    print(f"\n[apply_refactor_cleanup] summary: "
          f"-{total_originals_deleted} originals, "
          f"+{total_replacements_kept} replacements, "
          f"renamed {len(set(all_renamed))} unique name(s)",
          file=sys.stderr, flush=True)

    if args.dry_run:
        print("[apply_refactor_cleanup] DRY-RUN: no files written.",
              file=sys.stderr)
        return 0

    # Commit the writes
    for p, new in transformed_writes:
        p.write_text(new, encoding="utf-8")
    print(f"[apply_refactor_cleanup] wrote {len(transformed_writes)} file(s)",
          file=sys.stderr)

    if args.no_lake_build:
        print("[apply_refactor_cleanup] --no-lake-build: skipping final "
              "build (run `lake build` from the repo root yourself).",
              file=sys.stderr)
        return 0

    print(f"[apply_refactor_cleanup] running final lake build (timeout "
          f"{args.build_timeout}s) ...", file=sys.stderr, flush=True)
    try:
        r = subprocess.run(
            ["lake", "build"],
            cwd=str(REPO_ROOT),
            capture_output=True, text=True,
            timeout=args.build_timeout,
        )
    except subprocess.TimeoutExpired:
        print(f"ERROR: lake build timed out after {args.build_timeout}s; "
              f"the swap is on disk but unverified. Check the build "
              f"yourself before committing.", file=sys.stderr)
        return 2
    print(f"[apply_refactor_cleanup] lake build returncode={r.returncode}",
          file=sys.stderr)
    if r.returncode != 0:
        tail = "\n".join((r.stdout + r.stderr).splitlines()[-25:])
        print(f"ERROR: lake build failed -- swap may need fixup. Tail:\n"
              f"{tail}", file=sys.stderr)
        return 2
    print("[apply_refactor_cleanup] DONE -- cleanup applied and build "
          "clean. You can now `git diff` to review and commit.",
          file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
