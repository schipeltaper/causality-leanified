"""Process the human-filled initialization decision table.

Reads ``leanification/Chapter{N}_*/initialization_table.md`` (filled
in by the human), extracts each subtlety's **Decision** plus the
**Additional notes (global)** section, and folds the result into
``data.json`` under each row's ``addition_to_the_LN`` field.

Per-subtlety decisions are attached to the row that *observed* the
subtlety (``observed_by_ref`` in the register entry). Global notes
are appended to every row's ``addition_to_the_LN`` with a ``[global]``
prefix.

**Incremental processing.** The table carries a moving marker line
``<!-- --- processed until here --- -->``. Each invocation of this
script parses decisions strictly **below** the marker, stops at the
first ``TODO`` / blank decision, folds the filled decisions into
``data.json``, and moves the marker to just before the first unfilled
entry. The operator can fill the table in increments and re-run as
they go; no need to finish everything in one sitting.

Decision values:

- ``NONE`` (case-insensitive) — no addition recorded for this entry.
  Nothing is appended to the row's ``addition_to_the_LN`` on this
  subtlety's behalf. ``NONE`` is *not* a directive like "use the
  exact LN wording"; it is simply the absence of any extra information.
  (When a row's full set of decisions is ``NONE`` and no global notes
  are written, the row's ``addition_to_the_LN`` ends up empty; the
  equivalence-checker workers then treat the literal LN as the spec,
  which is the natural fallback rather than a positive instruction.)
- Anything else — treated as the clarifying clause; appended to the
  observed row's ``addition_to_the_LN`` (one paragraph per subtlety,
  prefixed with the subtlety id for traceability).
- ``TODO`` (or blank) — unfilled. Processing stops here; the marker
  lands just before this section so the next invocation resumes from
  the same point. No data.json change for this entry.

Idempotency:

- Per-row clauses (``[<sid>] …``) are appended on top of whatever's
  already in ``addition_to_the_LN`` from prior runs. A clause whose
  ``[<sid>]`` prefix is already present is skipped, so re-processing
  the same decision is a no-op.
- The global ``[global] …`` paragraph is fully replaced on every run
  (so edits to ``### Notes`` at the bottom of the table propagate
  to every row).

Workflow position::

    [...] --> generate_initialization_table --> [HUMAN fills in table]
        --> process_initialization_table --> data.json

Usage::

    python scaffold/scripts/phase2_initialization/process_initialization_table.py --chapter 3
    python scaffold/scripts/phase2_initialization/process_initialization_table.py --chapter 3 --dry-run
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

# .../scaffold/scripts/phase2_initialization/<this file>
SCRIPT_DIR = Path(__file__).resolve().parent
SCAFFOLD_DIR = SCRIPT_DIR.parent.parent                            # scaffold/
REPO_ROOT = SCAFFOLD_DIR.parent
LEANIFICATION = REPO_ROOT / "leanification"

sys.path.insert(0, str(SCRIPT_DIR.parent))
import _path_setup                                                # noqa: F401, E402
from subtlety_register import load_register                       # noqa: E402
from solve_chapter import run_claude                              # noqa: E402

INTERPRET_PROMPT_PATH = (
    SCAFFOLD_DIR / "claude_prompts" / "phase2_initialization"
    / "interpret_subtlety_decision.md"
)


# Match one decision block:
#   ### N. `<id>`
#   - **Observed by row:** `<ref>`
#   ... explanation ...
#   **Decision** (replace `TODO` ...):
#   ```
#   <decision body, possibly multi-line>
#   ```
_DECISION_RE = re.compile(
    r"^###\s+\d+\.\s+`(?P<id>[^`]+)`\s*\n"
    r"(?P<between>.*?)"
    r"\*\*Decision\*\*[^\n]*\n+"
    r"```\s*\n(?P<decision>.*?)\n```",
    re.DOTALL | re.MULTILINE,
)

# Match the global notes section: everything after `### Notes` up to
# the next top-level heading or end-of-file.
_GLOBAL_NOTES_RE = re.compile(
    r"###\s+Notes\s*\n+(?P<body>.*?)(?:\n##\s|\Z)",
    re.DOTALL,
)

# Stripped from the global notes body (the html comment in the template).
_TEMPLATE_COMMENT_RE = re.compile(r"<!--.*?-->", re.DOTALL)

# Marker line written into the table by the processor. Everything ABOVE
# this line in initialization_table.md has already been processed into
# data.json; everything BELOW is pending. Each processing run reads
# decisions from below the marker, stops at the first TODO/blank, and
# moves the marker to just before that unfilled section. Lets the
# operator fill the table in increments and process as they go without
# needing to finish everything first.
PROCESSED_MARKER = "<!-- --- processed until here --- -->"
_MARKER_LINE_RE = re.compile(
    r"^" + re.escape(PROCESSED_MARKER) + r"[ \t]*\n",
    re.MULTILINE,
)


def _find_chapter_folder(chapter: int) -> Path:
    for child in sorted(LEANIFICATION.iterdir()):
        if child.is_dir() and child.name.startswith(f"Chapter{chapter}_"):
            return child
    raise FileNotFoundError(
        f"no leanification folder for chapter {chapter}")


def _strip_marker(text: str) -> tuple[str, int]:
    """Remove the marker line from ``text``. Returns
    ``(text_without_marker, position_where_marker_was)``. If the marker
    is absent, returns ``(text, 0)`` -- i.e. processing starts at the
    top of the file."""
    m = _MARKER_LINE_RE.search(text)
    if not m:
        return text, 0
    return text[:m.start()] + text[m.end():], m.start()


def _insert_marker(text: str, position: int) -> str:
    """Insert the marker line at ``position``, prefixing/suffixing with
    newlines so it lands on its own line."""
    prefix = text[:position]
    suffix = text[position:]
    # Ensure there's a blank line above the marker and the marker line
    # ends with a newline.
    pre_pad = "" if prefix.endswith("\n\n") or prefix == "" else (
        "\n" if prefix.endswith("\n") else "\n\n"
    )
    return prefix + pre_pad + PROCESSED_MARKER + "\n\n" + suffix


def _parse_decisions_until_unfilled(
    text: str, start_offset: int = 0
) -> tuple[dict[str, str], str | None, int | None]:
    """Parse decisions in ``text`` starting from ``start_offset``,
    stopping at the first unfilled entry (``TODO`` or blank). Returns
    ``(filled_decisions, first_unfilled_id, first_unfilled_section_start)``.

    - ``filled_decisions``: ``{subtlety_id: decision_text}`` for every
      entry encountered with a non-TODO, non-blank decision, in order
      until the stop.
    - ``first_unfilled_id`` / ``first_unfilled_section_start``: the id
      of the first unfilled entry and the offset (within ``text``) of
      its ``### N. `<id>`` header. Both are ``None`` if no unfilled
      entry exists below ``start_offset``.
    """
    out: dict[str, str] = {}
    for m in _DECISION_RE.finditer(text, start_offset):
        sid = m.group("id").strip()
        decision = m.group("decision").strip()
        if not decision or decision.upper() == "TODO":
            return out, sid, m.start()
        out[sid] = decision
    return out, None, None


def _parse_global_notes(text: str) -> str:
    """Return the body of the 'Additional notes (global)' section
    with the template comment stripped. Empty string if absent."""
    m = _GLOBAL_NOTES_RE.search(text)
    if not m:
        return ""
    body = _TEMPLATE_COMMENT_RE.sub("", m.group("body")).strip()
    return body


def _interpret_decision_via_worker(sid: str,
                                   register_entry: dict,
                                   row: dict,
                                   user_response: str,
                                   global_notes: str) -> str:
    """Spawn the ``interpret_subtlety_decision`` worker on a single
    operator-filled decision. Returns the agent's self-contained
    clarification clause.

    Reads the worker template (instructions only) and appends an
    INPUTS block with the subtlety id, the subtlety explanation
    (verbatim from ``initial_subtlety_register.json``), the row's LN
    tex block, the operator's response, and the project-wide global
    notes (context only). The worker returns a single paragraph
    formal clause that goes into ``addition_to_the_LN`` under the
    ``[<sid>] …`` prefix.

    If the prompt file is missing, falls back to the raw operator
    response with a stderr warning so the operator can fix the setup
    without losing progress.
    """
    if not INTERPRET_PROMPT_PATH.exists():
        print(f"WARNING: interpreter prompt missing at "
              f"{INTERPRET_PROMPT_PATH}; falling back to verbatim "
              f"operator response for `{sid}`.", file=sys.stderr)
        return user_response.strip()
    template = INTERPRET_PROMPT_PATH.read_text(encoding="utf-8")
    inputs_block = (
        "\n\n---\n\n"
        "## INPUTS\n\n"
        f"### Subtlety id\n\n`{sid}`\n\n"
        "### Subtlety explanation "
        "(what the wording-check worker had to say)\n\n"
        f"{(register_entry.get('explanation') or '').strip()}\n\n"
        "### LN tex block (the row being clarified)\n\n"
        "```latex\n"
        f"{(row.get('tex_block') or '').strip()}\n"
        "```\n\n"
        "### Operator's response (informal; may assume context)\n\n"
        f"{user_response.strip()}\n\n"
        "### Project-wide global notes "
        "(context only; do NOT include in your output)\n\n"
        f"{global_notes.strip() if global_notes else '(no global notes)'}\n"
    )
    prompt = template + inputs_block
    print(f"  [{sid}] running interpreter worker ...",
          file=sys.stderr, flush=True)
    text, _sess = run_claude(prompt, label=f"interpret_{sid}")
    return text.strip()


def _strip_existing_clauses(addition: str) -> str:
    """Remove every ``[<sid>] …`` and ``[global] …`` paragraph from an
    existing ``addition_to_the_LN`` value, leaving any free-form text
    the operator may have added by hand untouched. Used by
    ``--reprocess-all`` to clear prior agent outputs (or prior
    verbatim fallback outputs) before a fresh run."""
    parts: list[str] = []
    for p in (addition or "").split("\n\n"):
        p = p.strip()
        if not p:
            continue
        if re.match(r"\[[^\]]+\]", p):
            continue                                # bracket-prefixed paragraph
        parts.append(p)
    return "\n\n".join(parts)


def _merge_row_addition(existing: str,
                        new_per_row: list[tuple[str, str]],
                        global_notes: str) -> str:
    """Compose the row's updated ``addition_to_the_LN`` by appending
    new per-row clauses to ``existing`` and replacing the row's
    ``[global] …`` portion (if any) with the current ``global_notes``.

    - Existing ``[<sid>] …`` paragraphs are preserved (prior runs).
    - Existing ``[global] …`` paragraph (if any) is stripped; the
      current ``global_notes`` text is re-appended afterwards.
    - New per-row clauses are appended in input order. Idempotent: if
      a ``[<sid>] …`` clause already exists, the new one is skipped.
    - ``NONE`` decisions append nothing.
    """
    parts: list[str] = []
    seen_sids: set[str] = set()
    for p in (existing or "").split("\n\n"):
        p = p.strip()
        if not p:
            continue
        if p.startswith("[global]"):
            continue                                    # will re-add below
        parts.append(p)
        m = re.match(r"\[([^\]]+)\]", p)
        if m:
            seen_sids.add(m.group(1))
    for sid, decision in new_per_row:
        if decision.upper() == "NONE":
            continue
        if sid in seen_sids:
            continue                                    # idempotent
        parts.append(f"[{sid}] {decision.strip()}")
        seen_sids.add(sid)
    if global_notes:
        parts.append(f"[global] {global_notes.strip()}")
    return "\n\n".join(parts)


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(
        description="Process the filled-in initialization decision "
                    "table into data.json's addition_to_the_LN column. "
                    "Incremental: each run processes from the "
                    "`<!-- --- processed until here --- -->` marker to "
                    "the first TODO/blank decision, then moves the "
                    "marker just past the last processed entry. "
                    "Re-run after filling in more entries.")
    parser.add_argument("--chapter", type=int, required=True,
                        help="chapter number, e.g. 3")
    parser.add_argument("--dry-run", action="store_true",
                        help="print what would change but do not write "
                             "data.json or move the marker in the table")
    parser.add_argument("--verbatim", action="store_true",
                        help="skip the interpreter worker and dump the "
                             "operator's raw response into "
                             "addition_to_the_LN. Faster (no Claude "
                             "calls) but the downstream equivalence "
                             "checker sees casual phrasing without "
                             "the subtlety explanation as context. "
                             "Useful for testing / quick iteration.")
    parser.add_argument("--reprocess-all", action="store_true",
                        help="reset the marker to the top of the table "
                             "AND strip every `[<sid>] …` and "
                             "`[global] …` paragraph from every row's "
                             "addition_to_the_LN before processing. "
                             "Use this after the table semantics have "
                             "changed (e.g. enabling the interpreter "
                             "worker) and you want every prior decision "
                             "re-processed under the new rules.")
    args = parser.parse_args(argv)

    chapter_folder = _find_chapter_folder(args.chapter)
    table_path = chapter_folder / "initialization_table.md"
    data_path = chapter_folder / "data.json"
    if not table_path.exists():
        print(f"ERROR: {table_path} not found. Run "
              f"`generate_initialization_table.py --chapter {args.chapter}` "
              f"first.", file=sys.stderr)
        return 1
    if not data_path.exists():
        print(f"ERROR: {data_path} not found.", file=sys.stderr)
        return 1

    table_text = table_path.read_text(encoding="utf-8")

    # 1. Strip the marker (if any). Decisions below the (former) marker
    # position are what we'll consider for this run; everything above
    # has already been processed in prior runs. With --reprocess-all,
    # treat the marker as if it were at the top so every decision is
    # re-considered (the row-side addition_to_the_LN is also cleared
    # below to make the re-processing actually overwrite).
    text_without_marker, marker_pos = _strip_marker(table_text)
    if args.reprocess_all:
        print(f"[process_initialization_table] --reprocess-all: "
              f"resetting marker to top and stripping prior "
              f"`[<sid>] …` / `[global] …` paragraphs from every row.",
              file=sys.stderr)
        marker_pos = 0

    # 2. Parse decisions below the marker, stopping at the first
    # unfilled entry.
    decisions, first_unfilled_id, first_unfilled_pos = (
        _parse_decisions_until_unfilled(text_without_marker,
                                        start_offset=marker_pos))

    # 3. Compute the new marker position.
    #    - If a first unfilled entry was found: just before its section.
    #    - Else (all remaining filled): just before the
    #      `## Additional notes (global)` section, or at end of file.
    if first_unfilled_pos is not None:
        new_marker_pos = first_unfilled_pos
    else:
        notes_match = re.search(
            r"^---\s*\n+##\s+Additional notes",
            text_without_marker,
            re.MULTILINE,
        )
        if notes_match:
            new_marker_pos = notes_match.start()
        else:
            new_marker_pos = len(text_without_marker)

    # 4. Parse the current global notes (always read fresh; their
    # content can change between runs).
    global_notes = _parse_global_notes(text_without_marker)

    # 5. Short-circuit: nothing new to process.
    if not decisions:
        if first_unfilled_id is None:
            print(f"Nothing to process: marker is at the bottom of the "
                  f"decision list and no unfilled entries remain. "
                  f"Initialization table for chapter {args.chapter} is "
                  f"fully processed.",
                  file=sys.stderr)
        else:
            print(f"Nothing to process: the first entry below the "
                  f"marker (`{first_unfilled_id}`) is still unfilled "
                  f"(TODO or blank). Fill it in and re-run.",
                  file=sys.stderr)
        # Even with no per-row changes, global notes may have been
        # edited; we still update them across all rows. Fall through.

    # 6. Map subtlety id -> observed_by_ref via the initial register.
    register = load_register("initial")
    id_to_ref: dict[str, str] = {
        e.get("id"): e.get("observed_by_ref")
        for e in register if e.get("id")
    }
    register_by_id: dict[str, dict] = {
        e.get("id"): e for e in register if e.get("id")
    }

    # Load data.json early so we can attribute decisions to rows
    # before invoking the interpreter worker (worker needs the row's
    # tex_block).
    data = json.loads(data_path.read_text(encoding="utf-8"))
    rows = data.get("rows", [])
    columns = list(data.get("columns") or [])
    if "addition_to_the_LN" not in columns:
        columns.append("addition_to_the_LN")
    data["columns"] = columns
    row_by_ref: dict[str, dict] = {r["ref"]: r for r in rows if r.get("ref")}

    # 7. For each filled decision, either (a) dump verbatim
    # (--verbatim) or (b) spawn the interpret_subtlety_decision worker
    # with the subtlety explanation, the row's tex_block, the operator's
    # response, and the global notes for context. The worker returns a
    # self-contained formal clarification clause; the orchestrator wraps
    # it with the `[<sid>]` prefix at merge time.
    by_ref: dict[str, list[tuple[str, str]]] = {}
    unattributed: list[str] = []
    if decisions:
        mode = "verbatim (no agent)" if args.verbatim else "via interpreter worker"
        print(f"[process_initialization_table] chapter={args.chapter}, "
              f"processing {len(decisions)} new decision(s) {mode}; "
              f"global notes "
              f"{'present' if global_notes else 'absent'}",
              file=sys.stderr)
    for sid, user_response in decisions.items():
        ref = id_to_ref.get(sid)
        if ref is None:
            unattributed.append(sid)
            continue
        row = row_by_ref.get(ref)
        register_entry = register_by_id.get(sid) or {}
        if not row:
            print(f"WARNING: subtlety `{sid}` attributed to row `{ref}`, "
                  f"but no such row in data.json. Skipping.",
                  file=sys.stderr)
            continue
        if args.verbatim or user_response.upper() == "NONE":
            clause = user_response
        else:
            try:
                clause = _interpret_decision_via_worker(
                    sid, register_entry, row, user_response, global_notes)
            except Exception as e:                       # noqa: BLE001
                print(f"WARNING: interpreter worker on `{sid}` failed "
                      f"({type(e).__name__}: {e}); falling back to "
                      f"verbatim operator response.",
                      file=sys.stderr)
                clause = user_response
        by_ref.setdefault(ref, []).append((sid, clause))
    if unattributed:
        print(f"WARNING: {len(unattributed)} decision id(s) have no "
              f"matching register entry (the register has been changed "
              f"since the table was generated?): {unattributed}",
              file=sys.stderr)

    # 8. Merge into data.json. Per-row clauses are APPENDED to existing
    # additions; global notes replace any prior `[global] …` paragraph.
    # Under --reprocess-all, every row's prior bracket-prefixed clauses
    # are stripped first so the new agent-generated clauses fully
    # replace any verbatim ones from prior runs.
    changed = 0
    for row in rows:
        ref = row.get("ref")
        if not ref:
            continue
        existing = row.get("addition_to_the_LN") or ""
        if args.reprocess_all:
            existing = _strip_existing_clauses(existing)
        new_per_row = by_ref.get(ref, [])
        addition = _merge_row_addition(existing, new_per_row, global_notes)
        if addition != existing:
            row["addition_to_the_LN"] = addition
            changed += 1
            if args.dry_run:
                print(f"  [{ref}] would set addition_to_the_LN to:\n"
                      f"    {addition!r}", file=sys.stderr)

    # 8. Re-insert the marker at the new position.
    new_table_text = _insert_marker(text_without_marker, new_marker_pos)

    if args.dry_run:
        print(f"[process_initialization_table] DRY RUN: would update "
              f"{changed} row(s); would move marker to byte {new_marker_pos}. "
              f"No write performed.",
              file=sys.stderr)
        return 0

    data_path.write_text(
        json.dumps(data, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
    table_path.write_text(new_table_text, encoding="utf-8")

    print(f"[process_initialization_table] wrote {data_path} "
          f"({changed} row(s) updated)", file=sys.stderr)
    if first_unfilled_id:
        print(f"[process_initialization_table] marker moved to just "
              f"before `{first_unfilled_id}`. Fill in that entry "
              f"(and any below it) and re-run to continue.",
              file=sys.stderr)
    else:
        print(f"[process_initialization_table] all decisions processed; "
              f"marker is now at the bottom of the decision list.",
              file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
