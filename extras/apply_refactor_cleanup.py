#!/usr/bin/env python3
"""Phase 7 cleanup: apply a completed refactor table.

Runs in eight phases (each opt-out via ``--skip-<phase>``):

  7a. **Lean marker swap.** In every Lean file the table touched, delete
      ``REFACTOR-BLOCK-ORIGINAL-BEGIN: <Name>`` ...
      ``REFACTOR-BLOCK-ORIGINAL-END: <Name>`` blocks; strip the
      surrounding markers around ``REFACTOR-BLOCK-REPLACEMENT-BEGIN``
      blocks (keeping the body); also delete
      ``REFACTOR-BLOCK-DELETE-BEGIN: <Name>`` ...
      ``REFACTOR-BLOCK-DELETE-END: <Name>`` blocks (a self-contained
      "this declaration is going away with no successor" -- use this
      when the refactor genuinely removes a decl, instead of
      ORIGINAL+empty-REPLACEMENT). Finally rename every whole-word
      ``refactor_<Name>`` -> ``<Name>`` -- across ALL files at once so
      cross-file references (file A's replacement using ``refactor_X``
      from file B) all flip together.

  7b. **Lake build.** Confirm the swap actually compiles.

  7c. **Tex proof twin swap.** For each claim refactor row, rename
      ``tex/refactor_<ref>_proof_<title>.tex`` (the twin the refactor
      manager wrote) over the original ``tex/<ref>_proof_<title>.tex``.
      Def refactors don't have a tex twin (their LN block doesn't
      change in a refactor).

  7d. **Original data.json sync.** For each refactor row, find the
      matching row in the chapter's original ``data.json``. Before
      mutating, snapshot the pre-sync row state into
      ``pre_refactor_rows.json`` inside the refactor folder (rides
      along to ``Refactor_<name>_DONE_<date>/`` after Phase 7h).
      Then overwrite the LN-independent fields the refactor may have
      updated -- ``proven`` (mistake-sweep), ``formalized``,
      ``time_needed_to_solve``, ``addition_to_the_LN``,
      ``main_lean_file`` / ``lean_files``, ``actions_tracking``,
      ``agent_registry`` -- stamp ``last_refactored_at``, and append a
      one-line tip pointing at the refactor name + date. LN-anchored
      fields (``tex_block``, ``tex_file``, ``def_or_claim``, ``ref``,
      ``section``, ``title``, ``type``) and historical state
      (``date_solved``, ``wording_check``) are left untouched.

  7e. **Deviation register surface + (optional) mark-resolved.** List
      every entry in ``leanification/deviations.json`` whose
      ``introduced_by_ref`` is one of the refactored rows; the
      refactor may have superseded them. With
      ``--mark-deviations-resolved=auto``, all matching entries get
      ``resolved_at`` + ``resolved_by_refactor`` fields; with
      ``--mark-deviations-resolved=id1,id2,...`` only those listed are
      marked. Default: list-only (human reviews + edits the JSON).

  7f. **Stale for-website JSON cleanup.** For each refactored row,
      delete ``tex/<ref>_for_website.json`` (it describes the OLD
      encoding's design choices; the next batch run regenerates).

  7g. **Workspace cleanup.** Delete every ``workspace_<ref>.md`` the
      refactor solve created in the section folders.

  7h. **Refactor folder archive.** Rename ``Refactor_<name>/`` to
      ``Refactor_<name>_DONE_<YYYY-MM-DD>/`` so the folder is clearly
      historical but the table is preserved.

Validation before any write: marker-block well-formedness (every BEGIN
has a matching END; every ORIGINAL has a matching REPLACEMENT). If
any check fails, NO files are written and the script exits non-zero.

Usage::

    # Preview every change without writing:
    python extras/apply_refactor_cleanup.py \
        --refactor-data leanification/Chapter3_GraphTheory/Refactor_X/refactor_data.json \
        --dry-run

    # Apply for real (auto-resolves matching deviations):
    python extras/apply_refactor_cleanup.py \
        --refactor-data leanification/Chapter3_GraphTheory/Refactor_X/refactor_data.json \
        --mark-deviations-resolved=auto
"""

from __future__ import annotations

import argparse
import copy
import difflib
import json
import re
import shutil
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
LEANIFICATION = REPO_ROOT / "leanification"
SCAFFOLD = REPO_ROOT / "scaffold"
SCRIPTS = SCAFFOLD / "scripts"

# Add scaffold/scripts/ to sys.path so `import _path_setup` resolves;
# _path_setup then adds every phase folder + utils/ to sys.path.
sys.path.insert(0, str(SCRIPTS))
import _path_setup                                              # noqa: F401, E402
# Imported lazily inside functions (avoid cold-importing the heavy
# orchestrator when only the cleanup phases are used):
#   from solve_chapter import _chapter_folder_for, _file_basename,
#                              _refactor_proof_basename
#   from deviations import load_register, mark_resolved


# ----- marker regexes ------------------------------------------------

_BEGIN_RE = re.compile(
    r"--\s*REFACTOR-BLOCK-(?P<kind>ORIGINAL|REPLACEMENT|DELETE)-BEGIN:\s*"
    r"(?P<name>[^\W\d][\w']*)",
    re.IGNORECASE,
)
_END_RE = re.compile(
    r"--\s*REFACTOR-BLOCK-(?P<kind>ORIGINAL|REPLACEMENT|DELETE)-END:\s*"
    r"(?P<name>[^\W\d][\w']*)",
    re.IGNORECASE,
)
_BLOCK_RE = re.compile(
    r"^[ \t]*--\s*REFACTOR-BLOCK-(ORIGINAL|REPLACEMENT|DELETE)-BEGIN:\s*"
    r"([^\W\d][\w']*)[^\n]*\n"
    r"(.*?)"
    r"^[ \t]*--\s*REFACTOR-BLOCK-\1-END:\s*\2[^\n]*\n?",
    re.MULTILINE | re.DOTALL | re.IGNORECASE,
)

# Top-level Lean declarations beginning with ``refactor_``. The keyword
# set matches Phase 7a's rename rule (only top-level declarations get
# the refactor_ prefix); inner / let-bound / local names are ignored.
# Allows optional modifiers like ``noncomputable`` / ``private`` /
# ``protected`` before the keyword.
_STRAY_REFACTOR_DECL_RE = re.compile(
    r"^(?P<prefix>(?:[\w]+\s+)?"
    r"(?:def|theorem|lemma|structure|class|abbrev|instance|inductive|opaque)\s+)"
    r"refactor_(?P<rest>[^\W\d][\w']*)",
    re.MULTILINE,
)


def _find_stray_refactor_decls(content: str, marker_names: set[str]
                               ) -> list[tuple[int, str, str]]:
    """Find every top-level ``refactor_<X>`` declaration in ``content``
    whose ``<X>`` is NOT in ``marker_names``. These would silently
    survive Phase 7a's rename (which only renames names collected from
    REPLACEMENT markers) and pollute the post-cleanup naming.

    Returns ``[(line_number, match_text, stripped_name), ...]``.
    Line numbers are 1-based."""
    hits: list[tuple[int, str, str]] = []
    for m in _STRAY_REFACTOR_DECL_RE.finditer(content):
        rest = m.group("rest")
        if rest in marker_names:
            continue                      # already covered by a marker
        line_no = content[: m.start()].count("\n") + 1
        hits.append((line_no, m.group(0).strip(), rest))
    return hits


# Same shape as _STRAY_REFACTOR_DECL_RE but for the unprefixed form,
# used for collision detection on `--auto-rename-strays`.
def _has_top_level_decl(content: str, name: str) -> bool:
    pat = re.compile(
        r"^(?:[\w]+\s+)?"
        r"(?:def|theorem|lemma|structure|class|abbrev|instance|inductive|opaque)\s+"
        + re.escape(name) + r"\b",
        re.MULTILINE,
    )
    return pat.search(content) is not None


def _parse_marker_blocks(content: str) -> list[dict]:
    """Return every marker block in source order."""
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
    complaints: list[str] = []
    begins: list[tuple[int, str, str]] = []
    ends: list[tuple[int, str, str]] = []
    for i, line in enumerate(content.splitlines(), start=1):
        bm = _BEGIN_RE.search(line)
        em = _END_RE.search(line)
        if bm:
            begins.append((i, bm.group("kind").lower(), bm.group("name")))
        if em:
            ends.append((i, em.group("kind").lower(), em.group("name")))
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
    orig_names = {b["name"] for b in blocks if b["kind"] == "original"}
    repl_names = {b["name"] for b in blocks if b["kind"] == "replacement"}
    del_names  = {b["name"] for b in blocks if b["kind"] == "delete"}
    complaints: list[str] = []
    # ORIGINAL must pair with a REPLACEMENT of the same name. A DELETE
    # block is a self-contained "this declaration is going away with no
    # successor"; it does NOT pair with anything and does NOT satisfy a
    # bare ORIGINAL. If the refactor genuinely removes a decl, use a
    # DELETE block (alone) -- not an ORIGINAL block.
    only_orig = orig_names - repl_names
    if only_orig:
        complaints.append(
            f"{file_path}: ORIGINAL block(s) without matching "
            f"REPLACEMENT: {sorted(only_orig)} -- refusing to delete "
            f"originals when the refactor isn't complete. If the "
            f"declaration is genuinely removed by the refactor, wrap "
            f"it in `REFACTOR-BLOCK-DELETE-BEGIN/END: <name>` instead.")
    # DELETE / REPLACEMENT name collisions are a worker mistake: a name
    # can't both be deleted and replaced.
    both = del_names & repl_names
    if both:
        complaints.append(
            f"{file_path}: name(s) {sorted(both)} appear as BOTH "
            f"DELETE and REPLACEMENT blocks. A declaration is either "
            f"removed or replaced -- pick one.")
    # ORIGINAL with same name as DELETE is also a worker mistake: the
    # convention is DELETE *replaces* ORIGINAL for the removal case.
    orig_del = orig_names & del_names
    if orig_del:
        complaints.append(
            f"{file_path}: name(s) {sorted(orig_del)} appear as BOTH "
            f"ORIGINAL and DELETE blocks. For genuine removals use "
            f"DELETE alone (no ORIGINAL).")
    return complaints


def _apply_to_content(content: str, file_path: Path,
                      all_final_names: set[str],
                      ) -> tuple[str, list[str], dict]:
    """Apply the cleanup transform to ``content``. ``all_final_names``
    is the union of replacement names across ALL files in the refactor
    -- this ensures cross-file ``refactor_<Name>`` references are
    renamed even in files that don't themselves define ``Name``."""
    unmatched = _check_unmatched_markers(content, file_path)
    if unmatched:
        return content, unmatched, {}
    blocks = _parse_marker_blocks(content)
    semantic = _validate_blocks(blocks, file_path)
    if semantic:
        return content, semantic, {}

    new_content = content
    originals_deleted = 0
    replacements_kept = 0
    deletions_applied = 0
    local_names: list[str] = []
    for b in sorted(blocks, key=lambda x: x["start"], reverse=True):
        if b["kind"] == "original":
            new_content = new_content[:b["start"]] + new_content[b["end"]:]
            originals_deleted += 1
        elif b["kind"] == "delete":
            # DELETE behaves like ORIGINAL: span is removed, no body kept.
            # Distinct kind exists so the validator can let it stand
            # alone (no paired REPLACEMENT) without weakening the
            # ORIGINAL-must-pair rule.
            new_content = new_content[:b["start"]] + new_content[b["end"]:]
            deletions_applied += 1
        else:                                       # replacement
            new_content = new_content[:b["start"]] + b["body"] + new_content[b["end"]:]
            replacements_kept += 1
            local_names.append(b["name"])

    # Rename using the GLOBAL name set (cross-file consistency). Process
    # longest-to-shortest to avoid prefix collisions (`Foo_Bar` before `Foo`).
    # Identifier-boundary character class includes Unicode word chars and
    # the apostrophe (Lean identifier conventions): so `refactor_π`
    # matches only when not part of a longer Lean identifier like
    # `refactor_π_isCollider` or `refactor_π'_vertices`.
    rename_set = set(all_final_names) | set(local_names)
    rename_log: list[str] = []
    for name in sorted(rename_set, key=len, reverse=True):
        pat = re.compile(
            r"(?<![\w'])refactor_" + re.escape(name)
            + r"(?![\w'])"
        )
        new_content, n = pat.subn(name, new_content)
        if n > 0:
            rename_log.append(f"{name}(x{n})")

    return new_content, [], {
        "originals_deleted":   originals_deleted,
        "replacements_kept":   replacements_kept,
        "deletions_applied":   deletions_applied,
        "renamed":             rename_log,
    }


# ----- phase 7a pass 3 helpers: strip stale refactor narratives ------

def _strip_refactor_narratives(
    content: str, refactor_name: str,
) -> tuple[str, list[str]]:
    """Strip stale solver-written refactor narratives from a Lean file.

    During a refactor row's solve, the solver agents typically write
    "in-progress" documentation in the affected file's docstrings and
    inline comments — section headings like
    ``## Refactor `<name>` (in progress)``, paragraphs explaining how
    ORIGINAL and REPLACEMENT blocks coexist, and cross-references like
    ``(see the `REFACTOR-BLOCK-ORIGINAL` block above)``. After Pass 2
    strips the markers and ORIGINAL blocks, those narratives become
    historically inaccurate (the markers they reference are gone, the
    "in progress" tense is wrong, and the "Coexistence" paragraphs
    describe a state that no longer exists).

    Three patterns are stripped (each idempotent — re-running on
    already-cleaned content is a no-op):

    1. The file-top docstring's ``## Refactor `<refactor_name>` (in
       progress)`` section heading plus the narrative body that
       follows it, up to the next ``## `` heading or the docstring
       closer ``-/``.
    2. Standalone ``**Coexistence during the refactor.**`` paragraphs.
    3. Inline parenthetical asides of the form
       ``(see the `REFACTOR-BLOCK-...` ... above)``.

    Patterns 1 and 2 are pinned to phrases solver agents emit verbatim;
    pattern 3 is a narrow regex for the specific cross-reference
    shape. All three are deliberately conservative — false positives
    would have to use these exact phrases AND reference the refactor's
    name by string.

    Returns ``(new_content, descriptions)``. ``descriptions`` is the
    list of human-readable strings naming what was stripped (empty
    list if nothing changed).
    """
    strips: list[str] = []
    name_re = re.escape(refactor_name)

    # Pattern 1: `## Refactor `<name>` (in progress)` section heading + body
    # up to next `## ` heading or `-/` docstring closer.
    section_pat = re.compile(
        rf"^## Refactor\s*`?{name_re}`?\s*\(in progress\).*?"
        rf"(?=^## |^-/|\Z)",
        re.MULTILINE | re.DOTALL,
    )
    n1 = len(section_pat.findall(content))
    if n1 > 0:
        content = section_pat.sub("", content)
        strips.append(f"stripped {n1} 'Refactor (in progress)' section(s)")

    # Pattern 2: `**Coexistence during the refactor.**` paragraph,
    # running until the next blank line, `## ` heading, or `-/` closer.
    coex_pat = re.compile(
        r"\*\*Coexistence during the refactor\.\*\*.*?"
        r"(?=\n[ \t]*\n|^## |^-/|\Z)",
        re.MULTILINE | re.DOTALL,
    )
    n2 = len(coex_pat.findall(content))
    if n2 > 0:
        content = coex_pat.sub("", content)
        strips.append(f"stripped {n2} 'Coexistence during the refactor' paragraph(s)")

    # Pattern 3: any inline parenthetical aside that mentions a
    # `REFACTOR-BLOCK-*` marker. Catches the common forms:
    #   "(see the `REFACTOR-BLOCK-ORIGINAL` block above)"
    #   "(`REFACTOR-BLOCK-ORIGINAL` above)"
    #   "(the `REFACTOR-BLOCK-ORIGINAL: Foo` block earlier in this file)"
    #   "(in the `REFACTOR-BLOCK-ORIGINAL` …)"
    # The `[^)]*` segments confine each match to a single parenthetical
    # (no `)` inside the match), so false positives would need to
    # genuinely place "REFACTOR-BLOCK-*" inside a parenthetical aside —
    # vanishingly unlikely outside the refactor-narrative pattern this
    # function targets. Non-parenthetical mentions are intentionally
    # NOT stripped (they sit in design-choice prose where blanket
    # removal would damage surrounding sentences); the operator can
    # rewrite those by hand if needed.
    xref_pat = re.compile(
        r"[ \t]*\([^)]*REFACTOR-BLOCK-[A-Z]+(?:-[A-Z]+)*\b[^)]*\)",
        re.IGNORECASE,
    )
    n3 = len(xref_pat.findall(content))
    if n3 > 0:
        content = xref_pat.sub("", content)
        strips.append(
            f"stripped {n3} REFACTOR-BLOCK cross-reference(s) "
            f"from inline comments"
        )

    # Normalize: collapse 3+ consecutive blank lines that may have
    # resulted from strips into a single blank line.
    content = re.sub(r"\n{3,}", "\n\n", content)

    return content, strips


# ----- phase 7a pass 4 helpers: prune empty namespace shells ----------

_NAMESPACE_OPEN_RE = re.compile(
    r"^[ \t]*namespace\s+(?P<name>[A-Za-z_][\w.]*)\s*$",
    re.MULTILINE,
)
_NAMESPACE_CLOSE_RE = re.compile(
    r"^[ \t]*end\s+(?P<name>[A-Za-z_][\w.]*)\s*$",
    re.MULTILINE,
)
_BLOCK_COMMENT_RE = re.compile(r"/-[^-]?.*?-/", re.DOTALL)
# Non-documentation block comments only (`/- ... -/`, *not* `/-! ... -/`).
# Lean module docstrings use the `/-!` form; treating them as content lets
# the pruner skip namespaces that hold load-bearing file-top docs while
# still allowing it to clean up namespaces whose only block content is
# code-annotation `/- ... -/` snippets (LN tex pastes, design-choice
# narratives) that the refactor twin's namespace has already duplicated.
_NONDOC_BLOCK_COMMENT_RE = re.compile(r"/-(?!!)[\s\S]*?-/", re.DOTALL)


def _is_empty_namespace_body(body: str) -> bool:
    """A namespace body counts as "empty" if every line is one of:
    blank, a ``--`` line-comment, content of a non-doc ``/- ... -/``
    block comment, or a single bare ``variable`` declaration.

    ``/-! ... -/`` *module-doc* block comments do NOT count as empty
    -- they are file-top docstrings whose silent removal would
    confuse readers with no Lean error to surface the loss. Non-doc
    ``/- ... -/`` blocks (LN tex pastes, code-annotation narratives
    that the refactor twin's namespace already duplicates) are
    pre-stripped before the check, so the typical dual-namespace
    pre-refactor shell -- variable + line-comment design notes +
    non-doc LN tex snippets, no real decls -- gets pruned. The
    distinction is the `!` after `/-` -- it marks a Lean module
    docstring."""
    # Strip non-doc block comments before the line scan; whatever
    # remains is either content or pure annotations we don't preserve.
    stripped = _NONDOC_BLOCK_COMMENT_RE.sub("", body)
    var_seen = False
    for raw in stripped.splitlines():
        line = raw.strip()
        if not line:
            continue
        if line.startswith("--"):
            continue                                # full-line line-comment
        # Any non-line-comment line still touching block-comment syntax
        # belongs to a `/-! ... -/` module-doc block (post-strip
        # invariant: only doc blocks remain). Treat as content.
        if "/-" in line or "-/" in line:
            return False
        if line.startswith("variable"):
            if var_seen:
                return False                       # >1 variable line
            var_seen = True
            continue
        return False
    return True


def _strip_empty_namespace_shells(content: str) -> tuple[str, list[str]]:
    """Find ``namespace X`` ... ``end X`` blocks whose body is empty
    (per `_is_empty_namespace_body`) and delete the whole shell.

    Pairs are matched via a simple stack-based pass over open/close
    lines; only correctly nested pairs are considered (a mismatch
    leaves the file alone). Idempotent: re-running on already-pruned
    content is a no-op.

    Returns ``(new_content, descriptions)``. The descriptions list
    names each pruned shell (empty list if no change)."""
    strips: list[str] = []
    while True:
        # Collect all open/close marker positions in source order.
        opens = [(m.start(), m.end(), m.group("name"))
                 for m in _NAMESPACE_OPEN_RE.finditer(content)]
        closes = [(m.start(), m.end(), m.group("name"))
                  for m in _NAMESPACE_CLOSE_RE.finditer(content)]
        events = sorted(
            [(s, e, n, "open")  for (s, e, n) in opens] +
            [(s, e, n, "close") for (s, e, n) in closes],
            key=lambda x: x[0],
        )
        # Pair using a stack; find the FIRST innermost empty pair.
        stack: list[tuple[int, int, str]] = []      # (line_start, line_end, name)
        pruned = False
        for (start, end, name, kind) in events:
            if kind == "open":
                stack.append((start, end, name))
            else:
                if not stack or stack[-1][2] != name:
                    # mismatch -- bail without touching the file
                    return content, strips
                (open_start, open_end, open_name) = stack.pop()
                body = content[open_end:start]
                if _is_empty_namespace_body(body):
                    # Delete from the start of the `namespace X` line
                    # through the end of the `end X` line (and its
                    # trailing newline if present).
                    cut_start = open_start
                    cut_end = end
                    if cut_end < len(content) and content[cut_end] == "\n":
                        cut_end += 1
                    content = content[:cut_start] + content[cut_end:]
                    strips.append(f"pruned empty `namespace {name}` shell")
                    pruned = True
                    break                          # restart the scan
        if not pruned:
            break
    # Normalize trailing blank-line runs.
    content = re.sub(r"\n{3,}", "\n\n", content)
    return content, strips


# ----- file collection -----------------------------------------------

def _collect_affected_lean_files(refactor_data: dict) -> list[Path]:
    """Union of main_lean_file + lean_files across every row."""
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


# ----- phase 7c helpers: tex twin swap -------------------------------

def _build_tex_twin_pairs(refactor_data: dict, data_path: Path
                          ) -> list[tuple[Path, Path, dict]]:
    """For each claim row in the refactor table, compute
    ``(twin_path, original_path, row_dict)``. Both paths absolute."""
    from solve_chapter import (                                # type: ignore
        _chapter_folder_for, ensure_subsection_folder,
        _file_basename, _refactor_proof_basename,
    )
    pairs: list[tuple[Path, Path, dict]] = []
    chapter_folder = _chapter_folder_for(data_path)
    for row in refactor_data.get("rows", []):
        if row.get("def_or_claim") != "claim":
            continue
        section = row.get("section", "")
        sub = ensure_subsection_folder(chapter_folder, section)
        twin_name = _refactor_proof_basename(row)
        orig_name = _file_basename(row, "proof")
        if not twin_name or not orig_name:
            continue
        pairs.append((sub / "tex" / twin_name,
                      sub / "tex" / orig_name,
                      row))
    return pairs


# ----- phase 7d helpers: sync original data.json ---------------------

def _find_original_row_locations(refactor_refs: list[str]
                                 ) -> dict[str, tuple[Path, int]]:
    """Map ``ref -> (chapter_data_json_path, row_index)`` by scanning
    every ``leanification/Chapter*/data.json`` (NOT refactor tables)."""
    out: dict[str, tuple[Path, int]] = {}
    wanted = set(refactor_refs)
    for dj in sorted(LEANIFICATION.glob("Chapter*/data.json")):
        try:
            data = json.loads(dj.read_text(encoding="utf-8"))
        except json.JSONDecodeError:
            continue
        for idx, row in enumerate(data.get("rows", [])):
            ref = row.get("ref")
            if ref in wanted and ref not in out:
                out[ref] = (dj, idx)
    return out


# Fields the refactor row may have updated, which should overwrite the
# original row's values when they differ. Anchored / structural fields
# (def_or_claim, ref, section, title, type, tex_file, tex_block,
# wording_check, solved, date_solved) are deliberately NOT in this list
# -- those either come from the LN and never change, or carry historical
# state that the pre-refactor snapshot already preserves.
_SYNC_OVERWRITE_FIELDS = (
    "formalized",
    "time_needed_to_solve",
    "addition_to_the_LN",
    "main_lean_file",
    "lean_files",
    "actions_tracking",
    "agent_registry",
)


def _sync_original_row(refactor_row: dict, original_row: dict,
                       refactor_name: str, today: str) -> dict:
    """Mutate ``original_row`` (in-place) to reflect the refactor
    outcome, then return the per-row sync summary for logging.

    The caller is responsible for snapshotting ``original_row`` BEFORE
    invoking this function if it wants to archive the pre-sync state
    (see the Phase 7d block in ``main``)."""
    changed: list[str] = []
    # proven: mistake-sweep may have flipped it
    rp = refactor_row.get("proven")
    op = original_row.get("proven")
    if rp and rp != op:
        original_row["proven"] = rp
        changed.append(f"proven {op!r} -> {rp!r}")
    # Overwrite refactor-driven fields when they differ. These reflect
    # the row's CURRENT state after the refactor; the pre-sync snapshot
    # the caller archives preserves the original values for audit.
    for fld in _SYNC_OVERWRITE_FIELDS:
        if fld not in refactor_row:
            continue
        rv = refactor_row[fld]
        ov = original_row.get(fld)
        if rv != ov:
            original_row[fld] = rv
            changed.append(f"{fld} overwritten")
    # Stamp the refactor date (new field; visible in row JSON)
    original_row["last_refactored_at"] = today
    changed.append("last_refactored_at set")
    # Append a one-line tip (keep any prior tips)
    tip_addition = (
        f"Refactored on {today} via `{refactor_name}` "
        f"(see leanification/Chapter*/Refactor_{refactor_name}_DONE_*/refactor_data.json)."
    )
    existing = (original_row.get("tips") or "").strip()
    original_row["tips"] = (
        existing + "\n\n" + tip_addition if existing else tip_addition
    )
    changed.append("tips appended")
    return {"changed": changed}


# ----- phase 7e helpers: deviation register --------------------------

def _affected_deviations(refactor_refs: list[str]) -> list[dict]:
    """All register entries whose ``introduced_by_ref`` is a refactored
    ref (includes already-resolved entries -- so a second refactor on
    the same root can re-resolve cleanly)."""
    from deviations import load_register                        # type: ignore
    wanted = set(refactor_refs)
    return [
        e for e in load_register(include_resolved=True)
        if e.get("introduced_by_ref") in wanted
    ]


# ----- main ----------------------------------------------------------

def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(
        description="Apply a completed refactor table: Lean swap, tex "
                    "twin swap, original data.json sync, deviation "
                    "register update, stale-file cleanup, folder archive.",
    )
    parser.add_argument("--refactor-data", type=Path, required=True,
                        help="path to refactor_data.json")
    parser.add_argument("--dry-run", action="store_true",
                        help="print every action without writing")
    parser.add_argument("--ignore-unsolved", action="store_true",
                        help="apply even if some refactor rows aren't "
                             "solved=yes (NOT recommended)")
    parser.add_argument("--build-timeout", type=int, default=1200)
    # Per-phase skip flags
    parser.add_argument("--skip-build", action="store_true",
                        help="skip phase 7b (lake build verification)")
    parser.add_argument("--skip-tex", action="store_true",
                        help="skip phase 7c (tex proof twin swap)")
    parser.add_argument("--skip-sync", action="store_true",
                        help="skip phase 7d (original data.json sync)")
    parser.add_argument("--skip-deviations", action="store_true",
                        help="skip phase 7e (deviation register surface)")
    parser.add_argument("--mark-deviations-resolved", type=str, default="",
                        help="phase 7e: 'auto' (mark every affected entry "
                             "resolved) or a comma-separated list of "
                             "specific deviation ids. Default: surface "
                             "only, don't modify the register.")
    parser.add_argument("--skip-website-cleanup", action="store_true",
                        help="skip phase 7f (stale for-website JSON deletion)")
    parser.add_argument("--skip-workspace-cleanup", action="store_true",
                        help="skip phase 7g (workspace_<ref>.md deletion)")
    parser.add_argument("--skip-archive", action="store_true",
                        help="skip phase 7h (rename Refactor_X/ -> "
                             "Refactor_X_DONE_<date>/)")
    # Stray refactor_* decl handling (Phase 7a Pass 1.5). Default:
    # refuse if any are found. Mutually exclusive overrides:
    g_stray = parser.add_mutually_exclusive_group()
    g_stray.add_argument("--auto-rename-strays", action="store_true",
                         help="if Phase 7a finds top-level `refactor_*` "
                              "declarations OUTSIDE any REPLACEMENT marker, "
                              "add their stripped names to the rename "
                              "set (collision-checked first). The "
                              "default behavior is to refuse and ask "
                              "the user to either fix the source or "
                              "explicitly pass this flag.")
    g_stray.add_argument("--allow-strays", action="store_true",
                         help="proceed past Phase 7a's stray-refactor_* "
                              "check WITHOUT renaming the strays "
                              "(leaves the `refactor_` prefix in the "
                              "final code; last-resort, you'll need to "
                              "clean up naming by hand).")
    parser.add_argument("--skip-dup-check", action="store_true",
                        help="skip Phase 7a Pass 1.7's predicted-"
                             "duplicate-decl gate. Use only after "
                             "confirming by inspection that flagged "
                             "duplicates live in genuinely-different "
                             "namespaces (which Lean allows).")
    args = parser.parse_args(argv)

    # ----- Load and sanity-check refactor table ----------------------
    try:
        rd = json.loads(args.refactor_data.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as e:
        print(f"ERROR: cannot read {args.refactor_data}: {e}", file=sys.stderr)
        return 1
    if not rd.get("refactor"):
        print(f"ERROR: {args.refactor_data} doesn't look like a refactor "
              f"table (missing top-level `refactor: true`)", file=sys.stderr)
        return 1
    refactor_name = rd.get("refactor_name") or args.refactor_data.parent.name
    refactor_roots = (rd.get("refactor_roots")
                      or ([rd["refactor_root"]] if rd.get("refactor_root") else []))
    rows = rd.get("rows", [])
    refactor_refs = [r["ref"] for r in rows if r.get("ref")]
    unsolved = [r["ref"] for r in rows if r.get("solved") != "yes"]
    if unsolved and not args.ignore_unsolved:
        print(f"ERROR: {len(unsolved)} row(s) in the refactor table are "
              f"NOT marked solved=yes: {unsolved}\n  Pass --ignore-"
              f"unsolved to override.", file=sys.stderr)
        return 1
    today = datetime.now(timezone.utc).date().isoformat()
    mode_label = "DRY-RUN" if args.dry_run else "WRITE"
    roots_summary = (f", root{'s' if len(refactor_roots) > 1 else ''}="
                     f"{refactor_roots}" if refactor_roots else "")
    print(f"[apply_refactor_cleanup] refactor={refactor_name!r}"
          f"{roots_summary}, {len(refactor_refs)} row(s), mode={mode_label}",
          file=sys.stderr, flush=True)

    # =================================================================
    # Phase 7a: Lean marker swap (validate first, two-pass for cross-file)
    # =================================================================
    print(f"\n[apply_refactor_cleanup] === Phase 7a: Lean marker swap ===",
          file=sys.stderr, flush=True)
    affected = _collect_affected_lean_files(rd)
    print(f"  {len(affected)} Lean file(s) to process", file=sys.stderr)

    # Pass 1: collect ALL replacement names across ALL files (so
    # cross-file `refactor_X` references get renamed even in files
    # that don't define X themselves).
    all_final_names: set[str] = set()
    file_blobs: dict[Path, str] = {}
    parse_complaints: list[str] = []
    for p in affected:
        if not p.exists():
            print(f"  - SKIP {p.relative_to(REPO_ROOT)}: file missing",
                  file=sys.stderr)
            continue
        try:
            content = p.read_text(encoding="utf-8")
        except UnicodeDecodeError as e:
            parse_complaints.append(f"{p}: not valid UTF-8: {e}")
            continue
        file_blobs[p] = content
        # Validate structure
        parse_complaints.extend(_check_unmatched_markers(content, p))
        blocks = _parse_marker_blocks(content)
        parse_complaints.extend(_validate_blocks(blocks, p))
        for b in blocks:
            if b["kind"] == "replacement":
                all_final_names.add(b["name"])
    if parse_complaints:
        print("\n  ERROR: marker validation failed; NO files written:",
              file=sys.stderr)
        for c in parse_complaints:
            print(f"    - {c}", file=sys.stderr)
        return 1
    print(f"  union of replacement names across all files: "
          f"{sorted(all_final_names)}", file=sys.stderr)

    # ---- Pass 1.5: stray `refactor_*` declaration check -----------------
    # Phase 7a's rename pass only knows about names collected from
    # REPLACEMENT markers. A top-level `def refactor_X` *without* an
    # enclosing marker (i.e., the manager wrote a net-new helper with
    # the `refactor_` prefix but forgot the marker block) would
    # silently survive cleanup with the prefix intact, polluting the
    # post-refactor naming. Caught in the claim_3_2_no_finite refactor:
    # 3 stray `refactor_swig_*` helpers in HardInterventionNodeSplitOrder.lean
    # made it through cleanup; they were the actual content of the
    # claim's Remark proof but had wrong names.
    #
    # Default: REFUSE and tell the user. Two override flags:
    #   --auto-rename-strays  add their stripped names to the rename
    #                         set (refactor_X -> X), checking for
    #                         collisions first.
    #   --allow-strays        proceed without renaming (last resort).
    stray_findings: dict[Path, list[tuple[int, str, str]]] = {}
    for p, content in file_blobs.items():
        strays = _find_stray_refactor_decls(content, all_final_names)
        if strays:
            stray_findings[p] = strays

    if stray_findings:
        print(f"\n  Found stray `refactor_*` top-level declaration(s) "
              f"NOT covered by any REPLACEMENT marker:", file=sys.stderr)
        for p, hits in stray_findings.items():
            for ln, match_text, rest in hits:
                print(f"    - {p.relative_to(REPO_ROOT)}:{ln}: "
                      f"`{match_text}`  (-> would rename to `{rest}` "
                      f"if marker-wrapped)", file=sys.stderr)
        n_strays = sum(len(v) for v in stray_findings.values())
        if args.auto_rename_strays:
            added: set[str] = set()
            for hits in stray_findings.values():
                for _, _, rest in hits:
                    added.add(rest)
            # Collision check: would `<rest>` collide with an existing
            # top-level `<rest>` declaration (one that's NOT inside an
            # ORIGINAL marker block, since those are about to be
            # deleted)?
            collisions: list[str] = []
            for rest in sorted(added):
                for content in file_blobs.values():
                    if _has_top_level_decl(content, rest):
                        # Check if this existing decl is inside an
                        # ORIGINAL marker block (will be deleted).
                        # Build a quick "deleted ranges" map per file.
                        blocks = _parse_marker_blocks(content)
                        deleted_ranges = [
                            (b["start"], b["end"]) for b in blocks
                            if b["kind"] == "original"
                        ]
                        # If every match of `rest` falls inside a
                        # deleted range, no collision.
                        pat = re.compile(
                            r"^(?:[\w]+\s+)?"
                            r"(?:def|theorem|lemma|structure|class"
                            r"|abbrev|instance|inductive|opaque)\s+"
                            + re.escape(rest) + r"\b",
                            re.MULTILINE,
                        )
                        for m in pat.finditer(content):
                            in_deleted = any(s <= m.start() < e
                                             for s, e in deleted_ranges)
                            if not in_deleted:
                                collisions.append(rest)
                                break
                        if rest in collisions:
                            break
            if collisions:
                print(f"\n  ERROR: --auto-rename-strays would collide "
                      f"with existing declaration(s): "
                      f"{sorted(set(collisions))}. Refusing -- the "
                      f"rename would produce duplicate declarations "
                      f"that lake build will reject. Fix the source "
                      f"by renaming the strays by hand and re-run.",
                      file=sys.stderr)
                return 1
            all_final_names |= added
            print(f"\n  --auto-rename-strays: adding {sorted(added)} "
                  f"to the rename set. `refactor_<X>` -> `<X>` will "
                  f"fire on these too.", file=sys.stderr)
        elif args.allow_strays:
            print(f"\n  --allow-strays: leaving {n_strays} stray "
                  f"`refactor_*` declaration(s) prefixed; manager "
                  f"wrote them, manager owns the naming.",
                  file=sys.stderr)
        else:
            print(f"\n  REFUSING to proceed ({n_strays} stray "
                  f"declaration(s)). Either:\n"
                  f"    --auto-rename-strays   drop the `refactor_` "
                  f"prefix on each (collision-checked first)\n"
                  f"    --allow-strays         proceed without "
                  f"renaming (last resort; cleanup leaves them "
                  f"prefixed)\n"
                  f"  Or fix the source: wrap each stray in a "
                  f"REPLACEMENT marker block and re-run finalize.",
                  file=sys.stderr)
            return 1

    # ---- Pass 1.7: post-cleanup duplicate-decl prediction --------------
    # Synthesize Pass 2's output in memory and scan for top-level
    # declarations of the same name appearing twice. Catches the
    # `cdmg_typed_edges` failure mode: unwrapped pre-refactor helpers
    # sitting next to their marker-wrapped post-refactor twin, which
    # post-rename collide as duplicate decls and break Phase 7b's lake
    # build. Doing the check here (before Pass 2 mutates anything) lets
    # the script abort cleanly with a clear error instead of leaving
    # the working tree in a half-cleaned state.
    _DECL_RE = re.compile(
        r"^(?:[\w]+\s+)?"
        r"(?:def|theorem|lemma|structure|class|abbrev|instance|inductive|opaque)"
        r"\s+(?P<name>[^\W\d][\w']*)(?![\w'])",
        re.MULTILINE,
    )
    dup_findings: dict[Path, list[str]] = {}
    if not args.skip_dup_check:
        for p, content in file_blobs.items():
            try:
                synthesized, _, _ = _apply_to_content(
                    content, p, all_final_names)
            except Exception:                       # pragma: no cover
                continue
            clean = _BLOCK_COMMENT_RE.sub("", synthesized)
            counts: dict[str, int] = {}
            for m in _DECL_RE.finditer(clean):
                n = m.group("name")
                counts[n] = counts.get(n, 0) + 1
            dups = sorted(n for n, c in counts.items() if c > 1)
            if dups:
                dup_findings[p] = dups
    if dup_findings:
        print(f"\n  Predicted duplicate top-level declaration(s) "
              f"AFTER cleanup (would break Phase 7b lake build):",
              file=sys.stderr)
        for p, dups in dup_findings.items():
            try:
                rel = p.relative_to(REPO_ROOT)
            except ValueError:
                rel = p
            print(f"    - {rel}: {dups}", file=sys.stderr)
        print(f"\n  Likely cause: an unwrapped pre-refactor helper "
              f"sitting next to its marker-wrapped post-refactor twin. "
              f"Fix: wrap each pre-refactor helper in an ORIGINAL or "
              f"DELETE marker block (per `manager.md`'s "
              f"helper-discipline rule), or delete it if it's dead "
              f"code. Then re-run finalize.\n"
              f"  (Note: this check does not track namespace scoping; "
              f"if the duplicates are in genuinely-different "
              f"namespaces (Lean allows that) and you've confirmed by "
              f"inspection, re-run with `--skip-dup-check`.)\n",
              file=sys.stderr)
        return 1

    # Pass 2: apply transforms using the global name set
    transformed_writes: list[tuple[Path, str]] = []
    total_orig_deleted = 0
    total_repl_kept = 0
    for p, old in file_blobs.items():
        new, complaints, summary = _apply_to_content(
            old, p, all_final_names)
        if complaints:        # shouldn't happen after pass 1 but safety
            parse_complaints.extend(complaints)
            continue
        if new == old:
            print(f"  - {p.relative_to(REPO_ROOT)}: no-op",
                  file=sys.stderr)
            continue
        total_orig_deleted += summary["originals_deleted"]
        total_repl_kept += summary["replacements_kept"]
        rel = p.relative_to(REPO_ROOT)
        del_applied = summary.get("deletions_applied", 0)
        del_part = f", -{del_applied} delete" if del_applied else ""
        print(f"  - {rel}: -{summary['originals_deleted']} original, "
              f"+{summary['replacements_kept']} replacement{del_part}, "
              f"rename hits: {summary['renamed']}", file=sys.stderr)
        if args.dry_run:
            sys.stdout.write(_diff(old, new, str(rel)))
        else:
            transformed_writes.append((p, new))
    if parse_complaints:
        print(f"\n  ERROR (pass 2): {parse_complaints}", file=sys.stderr)
        return 1
    if not args.dry_run:
        for p, new in transformed_writes:
            p.write_text(new, encoding="utf-8")
        print(f"  wrote {len(transformed_writes)} file(s) "
              f"(-{total_orig_deleted} orig, +{total_repl_kept} repl)",
              file=sys.stderr)

    # Pass 3: strip stale solver-written refactor narratives from
    # docstrings and inline comments. Pass 2 removed the actual marker
    # blocks; Pass 3 removes the commentary about those blocks ("##
    # Refactor (in progress)" sections, "**Coexistence during the
    # refactor**" paragraphs, "(see the `REFACTOR-BLOCK-ORIGINAL` block
    # above)" cross-references). Each pattern is pinned narrowly enough
    # that false positives are vanishingly unlikely; see
    # `_strip_refactor_narratives`'s docstring.
    print(f"\n  [pass 3] stripping stale refactor narratives ...",
          file=sys.stderr)
    n_pass3_changed = 0
    pass3_writes: list[tuple[Path, str]] = []
    for p in file_blobs:
        # Re-read from disk in apply mode (Pass 2 just wrote);
        # in dry-run, take Pass 2's in-memory result if it exists,
        # otherwise the original.
        if args.dry_run:
            old_for_pass3 = next(
                (n for fp, n in transformed_writes if fp == p),
                file_blobs[p],
            )
        else:
            old_for_pass3 = p.read_text(encoding="utf-8")
        new_p3, descs = _strip_refactor_narratives(
            old_for_pass3, refactor_name)
        if not descs:
            continue
        n_pass3_changed += 1
        rel = p.relative_to(REPO_ROOT)
        print(f"    - {rel}: " + "; ".join(descs), file=sys.stderr)
        if args.dry_run:
            sys.stdout.write(_diff(old_for_pass3, new_p3,
                                   f"{rel} (pass 3)"))
        else:
            pass3_writes.append((p, new_p3))
    if not args.dry_run:
        for p, new in pass3_writes:
            p.write_text(new, encoding="utf-8")
        if n_pass3_changed:
            print(f"  pass 3 cleaned {n_pass3_changed} file(s)",
                  file=sys.stderr)
        else:
            print(f"  pass 3: no narratives to strip", file=sys.stderr)
    elif n_pass3_changed == 0:
        print(f"  pass 3: no narratives to strip", file=sys.stderr)

    # Pass 4: prune empty namespace shells. Pass 2 deletes ORIGINAL
    # marker blocks; for refactors that used the dual-namespace pattern
    # (one `namespace CDMG` block for the pre-refactor body, a separate
    # `namespace CDMG` block for the refactor twin), that leaves an
    # orphan shell of the form `namespace X / [comments + variable
    # only] / end X`. Build-correct but noisy. Pass 4 sweeps them.
    print(f"\n  [pass 4] pruning empty namespace shells ...",
          file=sys.stderr)
    n_pass4_changed = 0
    pass4_writes: list[tuple[Path, str]] = []
    for p in file_blobs:
        if args.dry_run:
            old_for_pass4 = next(
                (n for fp, n in (pass3_writes or [])
                 if fp == p),
                next(
                    (n for fp, n in transformed_writes if fp == p),
                    file_blobs[p],
                ),
            )
        else:
            old_for_pass4 = p.read_text(encoding="utf-8")
        new_p4, descs = _strip_empty_namespace_shells(old_for_pass4)
        if not descs:
            continue
        n_pass4_changed += 1
        rel = p.relative_to(REPO_ROOT)
        print(f"    - {rel}: " + "; ".join(descs), file=sys.stderr)
        if args.dry_run:
            sys.stdout.write(_diff(old_for_pass4, new_p4,
                                   f"{rel} (pass 4)"))
        else:
            pass4_writes.append((p, new_p4))
    if not args.dry_run:
        for p, new in pass4_writes:
            p.write_text(new, encoding="utf-8")
        if n_pass4_changed:
            print(f"  pass 4 pruned {n_pass4_changed} file(s)",
                  file=sys.stderr)
        else:
            print(f"  pass 4: no empty shells", file=sys.stderr)
    elif n_pass4_changed == 0:
        print(f"  pass 4: no empty shells", file=sys.stderr)

    # =================================================================
    # Phase 7b: Lake build verification
    # =================================================================
    # `build_failed` flag: on lake build failure or timeout we continue
    # through the remaining phases (7c-7g operate on metadata, not Lean
    # code, so they succeed) and let phase 7h archive the folder under a
    # `_BUILDFAIL_<today>` suffix so the operator can grep for it. The
    # final returncode is still 2 so `do_refactor.py finalize` halts and
    # the operator notices.
    build_failed = False
    if args.skip_build or args.dry_run:
        if args.dry_run:
            print(f"\n[apply_refactor_cleanup] === Phase 7b: SKIPPED (dry-run) ===",
                  file=sys.stderr)
        else:
            print(f"\n[apply_refactor_cleanup] === Phase 7b: SKIPPED (--skip-build) ===",
                  file=sys.stderr)
    else:
        print(f"\n[apply_refactor_cleanup] === Phase 7b: lake build "
              f"(timeout {args.build_timeout}s) ===",
              file=sys.stderr, flush=True)
        try:
            r = subprocess.run(
                ["lake", "build"], cwd=str(REPO_ROOT),
                capture_output=True, text=True, timeout=args.build_timeout,
            )
        except subprocess.TimeoutExpired:
            print(f"  ERROR: lake build timed out; swap on disk but "
                  f"unverified. Continuing to later phases anyway so the "
                  f"folder gets archived under _BUILDFAIL_; fix the Lean "
                  f"error and re-run with --skip-build.", file=sys.stderr)
            build_failed = True
        else:
            print(f"  returncode={r.returncode}", file=sys.stderr)
            if r.returncode != 0:
                tail = "\n".join((r.stdout + r.stderr).splitlines()[-25:])
                print(f"  ERROR: lake build failed. Continuing to later "
                      f"phases so the folder gets archived under "
                      f"_BUILDFAIL_; fix the Lean error and re-run with "
                      f"--skip-build.\n  Tail:\n{tail}", file=sys.stderr)
                build_failed = True

    # =================================================================
    # Phase 7c: tex proof twin swap
    # =================================================================
    if args.skip_tex:
        print(f"\n[apply_refactor_cleanup] === Phase 7c: SKIPPED (--skip-tex) ===",
              file=sys.stderr)
    else:
        print(f"\n[apply_refactor_cleanup] === Phase 7c: tex proof twin swap ===",
              file=sys.stderr, flush=True)
        try:
            pairs = _build_tex_twin_pairs(rd, args.refactor_data)
        except Exception as e:                                  # noqa: BLE001
            print(f"  WARNING: could not compute tex twin paths: {e}",
                  file=sys.stderr)
            pairs = []
        n_swapped = 0
        n_missing = 0
        for twin, original, row in pairs:
            twin_rel = twin.relative_to(REPO_ROOT)
            orig_rel = original.relative_to(REPO_ROOT)
            if not twin.exists():
                print(f"  - WARNING: {twin_rel} does not exist (refactor "
                      f"row {row.get('ref')} didn't write a tex twin); "
                      f"skipping", file=sys.stderr)
                n_missing += 1
                continue
            print(f"  - rename {twin_rel} -> {orig_rel}", file=sys.stderr)
            if not args.dry_run:
                twin.replace(original)       # atomic; overwrites original
                n_swapped += 1
        print(f"  {n_swapped} swap(s), {n_missing} twin(s) missing",
              file=sys.stderr)

    # =================================================================
    # Phase 7d: original data.json sync
    # =================================================================
    if args.skip_sync:
        print(f"\n[apply_refactor_cleanup] === Phase 7d: SKIPPED (--skip-sync) ===",
              file=sys.stderr)
    else:
        print(f"\n[apply_refactor_cleanup] === Phase 7d: original "
              f"data.json sync ===", file=sys.stderr, flush=True)
        locations = _find_original_row_locations(refactor_refs)
        # Group by data.json path so we read/write each file once.
        by_data: dict[Path, list[tuple[int, dict]]] = {}
        for ref in refactor_refs:
            if ref not in locations:
                print(f"  - WARNING: {ref!r} not found in any chapter "
                      f"data.json; nothing to sync", file=sys.stderr)
                continue
            dj, idx = locations[ref]
            by_data.setdefault(dj, []).append((idx, next(
                r for r in rows if r["ref"] == ref)))
        # Accumulate pre-sync snapshots across all chapters' rows so
        # one archive file in the refactor folder captures the full
        # pre-refactor state of every touched row.
        pre_sync_snapshots: list[dict] = []
        for dj, items in by_data.items():
            data = json.loads(dj.read_text(encoding="utf-8"))
            for idx, refactor_row in items:
                # Snapshot BEFORE _sync_original_row mutates the row.
                pre_sync_snapshots.append({
                    "ref": data["rows"][idx]["ref"],
                    "chapter_data_path": str(dj.relative_to(REPO_ROOT)),
                    "row_index": idx,
                    "pre_sync_row": copy.deepcopy(data["rows"][idx]),
                })
                summary = _sync_original_row(
                    refactor_row, data["rows"][idx],
                    refactor_name, today)
                print(f"  - {dj.relative_to(REPO_ROOT)}[{idx}] "
                      f"({data['rows'][idx]['ref']}): "
                      f"{', '.join(summary['changed'])}", file=sys.stderr)
            if not args.dry_run:
                dj.write_text(
                    json.dumps(data, indent=2, ensure_ascii=False) + "\n",
                    encoding="utf-8")
        # Archive the pre-sync snapshots into the refactor folder so
        # they ride along when Phase 7h renames the folder to DONE_*.
        # The file accumulates one entry per touched row across all
        # chapters.
        if pre_sync_snapshots:
            archive_path = (
                args.refactor_data.parent / "pre_refactor_rows.json"
            )
            print(f"  - pre-sync snapshot: "
                  f"{archive_path.relative_to(REPO_ROOT)} "
                  f"({len(pre_sync_snapshots)} row(s))",
                  file=sys.stderr)
            if not args.dry_run:
                archive_path.write_text(
                    json.dumps(pre_sync_snapshots, indent=2,
                               ensure_ascii=False) + "\n",
                    encoding="utf-8")

    # =================================================================
    # Phase 7e: deviation register surface (+ optional resolve)
    # =================================================================
    if args.skip_deviations:
        print(f"\n[apply_refactor_cleanup] === Phase 7e: SKIPPED "
              f"(--skip-deviations) ===", file=sys.stderr)
    else:
        print(f"\n[apply_refactor_cleanup] === Phase 7e: deviation "
              f"register ===", file=sys.stderr, flush=True)
        affected_devs = _affected_deviations(refactor_refs)
        if not affected_devs:
            print(f"  (no deviation entries reference any refactored ref)",
                  file=sys.stderr)
        else:
            for e in affected_devs:
                already = (" [RESOLVED " + str(e.get("resolved_at")) + "]"
                           if e.get("resolved_at") else "")
                print(f"  - {e.get('id')!r} "
                      f"(introduced_by_ref={e.get('introduced_by_ref')!r}"
                      f"){already}", file=sys.stderr)
                print(f"      breaks:     {e.get('breaks')}",
                      file=sys.stderr)
                print(f"      preserves:  {e.get('preserves')}",
                      file=sys.stderr)
            mark_arg = args.mark_deviations_resolved.strip()
            if not mark_arg:
                print(f"  (default: surface only; review and either edit "
                      f"`leanification/deviations.json` by hand or re-run "
                      f"with --mark-deviations-resolved=auto / =id1,id2)",
                      file=sys.stderr)
            else:
                from deviations import mark_resolved as _mr      # type: ignore
                if mark_arg.lower() == "auto":
                    # `auto` resolves entries that PRE-DATE this refactor
                    # (auditor drafts, hand-seeded). Skip entries tagged
                    # `manager-accepted`: those were created by the
                    # refactor's own accept_deviation calls -- they're
                    # NEW deviations in the post-refactor state, not
                    # resolved ones. Resolving them would be wrong.
                    # Use --mark-deviations-resolved=id1,id2 to override
                    # case-by-case if you really do want to mark a
                    # manager-accepted entry resolved.
                    to_mark = [
                        e["id"] for e in affected_devs
                        if (not e.get("resolved_at")
                            and e.get("id")
                            and "manager-accepted" not in (e.get("tags") or []))
                    ]
                else:
                    explicit = {s.strip() for s in mark_arg.split(",")
                                if s.strip()}
                    to_mark = [eid for eid in (e.get("id") for e in affected_devs)
                               if eid in explicit]
                print(f"  marking {len(to_mark)} entry(s) resolved: {to_mark}",
                      file=sys.stderr)
                if not args.dry_run:
                    for eid in to_mark:
                        try:
                            _mr(eid, refactor_name, resolved_at=today)
                        except KeyError as e:
                            print(f"  WARNING: {e}", file=sys.stderr)

    # =================================================================
    # Phase 7f: stale for-website JSON cleanup
    # =================================================================
    if args.skip_website_cleanup:
        print(f"\n[apply_refactor_cleanup] === Phase 7f: SKIPPED "
              f"(--skip-website-cleanup) ===", file=sys.stderr)
    else:
        print(f"\n[apply_refactor_cleanup] === Phase 7f: stale "
              f"for-website JSON ===", file=sys.stderr, flush=True)
        try:
            from solve_chapter import (                          # type: ignore
                _chapter_folder_for, ensure_subsection_folder,
            )
            chap = _chapter_folder_for(args.refactor_data)
            n_deleted = 0
            for row in rows:
                section = row.get("section", "")
                ref = row.get("ref")
                if not ref:
                    continue
                sub = ensure_subsection_folder(chap, section)
                p = sub / "tex" / f"{ref}_for_website.json"
                if p.exists():
                    print(f"  - delete {p.relative_to(REPO_ROOT)}",
                          file=sys.stderr)
                    if not args.dry_run:
                        p.unlink()
                        n_deleted += 1
            print(f"  {n_deleted} stale website JSON file(s) deleted "
                  f"(next batch run will regenerate)", file=sys.stderr)
        except Exception as e:                                   # noqa: BLE001
            print(f"  WARNING: phase 7f errored: {e}", file=sys.stderr)

    # =================================================================
    # Phase 7g: workspace cleanup
    # =================================================================
    if args.skip_workspace_cleanup:
        print(f"\n[apply_refactor_cleanup] === Phase 7g: SKIPPED "
              f"(--skip-workspace-cleanup) ===", file=sys.stderr)
    else:
        print(f"\n[apply_refactor_cleanup] === Phase 7g: workspace cleanup ===",
              file=sys.stderr, flush=True)
        try:
            from solve_chapter import (                          # type: ignore
                _chapter_folder_for, ensure_subsection_folder,
            )
            chap = _chapter_folder_for(args.refactor_data)
            n_deleted = 0
            for row in rows:
                section = row.get("section", "")
                ref = row.get("ref")
                if not ref:
                    continue
                sub = ensure_subsection_folder(chap, section)
                p = sub / f"workspace_{ref}.md"
                if p.exists():
                    print(f"  - delete {p.relative_to(REPO_ROOT)}",
                          file=sys.stderr)
                    if not args.dry_run:
                        p.unlink()
                        n_deleted += 1
            print(f"  {n_deleted} workspace file(s) deleted",
                  file=sys.stderr)
        except Exception as e:                                   # noqa: BLE001
            print(f"  WARNING: phase 7g errored: {e}", file=sys.stderr)

    # =================================================================
    # Phase 7h: archive refactor folder
    # =================================================================
    if args.skip_archive:
        print(f"\n[apply_refactor_cleanup] === Phase 7h: SKIPPED "
              f"(--skip-archive) ===", file=sys.stderr)
    else:
        print(f"\n[apply_refactor_cleanup] === Phase 7h: archive "
              f"refactor folder ===", file=sys.stderr, flush=True)
        cur_folder = args.refactor_data.parent
        marker = "BUILDFAIL" if build_failed else "DONE"
        archive_name = f"{cur_folder.name}_{marker}_{today}"
        archive_path = cur_folder.parent / archive_name
        # Same-day collision: append _v2, _v3, … so a re-run never
        # silently skips the archive (and downstream
        # `_find_archived_refactor_folder` always finds the most recent
        # one for `today`).
        if archive_path.exists():
            n = 2
            while (cur_folder.parent /
                   f"{archive_name}_v{n}").exists():
                n += 1
            archive_path = cur_folder.parent / f"{archive_name}_v{n}"
            print(f"  NOTE: {archive_name} already exists; using "
                  f"{archive_path.name} instead", file=sys.stderr)
        print(f"  - rename {cur_folder.relative_to(REPO_ROOT)} -> "
              f"{archive_path.relative_to(REPO_ROOT)}", file=sys.stderr)
        if not args.dry_run:
            shutil.move(str(cur_folder), str(archive_path))

    # ----- Done ------------------------------------------------------
    print(f"\n[apply_refactor_cleanup] DONE "
          f"({'dry-run' if args.dry_run else 'applied'}"
          f"{'; BUILD FAILED' if build_failed else ''}).",
          file=sys.stderr, flush=True)
    if args.dry_run:
        print(f"  Re-run without --dry-run to apply.", file=sys.stderr)
    if build_failed:
        print(f"  Lake build FAILED in phase 7b. Folder archived under "
              f"_BUILDFAIL_; the merged branch will not compile until "
              f"the Lean error is fixed.", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
