#!/usr/bin/env python3
"""Non-destructive audit sweep over a chapter's solved rows.

For every row in the chapter that has ``solved == "yes"``, runs the
strict equivalence checker (and, if requested, the property-based
example verifier). Logs every result -- PASS, FAIL, EXAMPLE_GENERATION
+ examples-PASS/FAIL, ERROR -- to ``leanification/Chapter<N>/audit.json``.

**Non-destructive.** Never modifies:
- the row's ``solved`` / ``proven`` / ``formalized`` flags;
- the row's Lean files or tex files;
- the row's ``agent_registry`` (the auditor uses ``register_on_row=False``
  semantics by virtue of calling the audit-helper dispatchers, which
  don't touch the registry).

What it MAY modify (additive only):
- ``leanification/Chapter<N>/audit.json`` (created if missing; appended
  per-row results in row order).
- ``leanification/deviations.json`` (global) -- each FAIL whose
  ``deviation_class`` is CONTENT triggers a draft deviation entry (the
  auditor proposes; the human can edit / approve the JSON before
  another worker consumes it).

Usage:
    python extras/audit_chapter.py <chapter>
    python extras/audit_chapter.py <chapter> --rows <i>,<j>,<k>      # subset
    python extras/audit_chapter.py <chapter> --resume                # skip rows already in audit.json

Examples:
    python extras/audit_chapter.py 3
    python extras/audit_chapter.py 3 --rows 0,1,33
    python extras/audit_chapter.py 3 --resume
"""

from __future__ import annotations

import argparse
import json
import re
import sys
import time
from datetime import datetime, timezone
from pathlib import Path

SCAFFOLD = Path(__file__).resolve().parent.parent / "scaffold"
SCRIPTS = SCAFFOLD / "scripts"
sys.path.insert(0, str(SCRIPTS))
import _path_setup                                              # noqa: F401, E402

from solve_chapter import (                                    # type: ignore  # noqa: E402
    LEANIFICATION_DIR,
    find_chapter_data_path,
    load_data,
)
from audit_helpers import audit_one_row                         # type: ignore
from deviations import (                                        # type: ignore
    load_register, register_deviation,
)


def _audit_path(chapter_folder: Path) -> Path:
    return chapter_folder / "audit.json"


def _load_audit(audit_path: Path) -> list[dict]:
    if not audit_path.exists():
        return []
    try:
        return json.loads(audit_path.read_text(encoding="utf-8"))
    except json.JSONDecodeError:
        return []


def _save_audit(audit_path: Path, entries: list[dict]) -> None:
    audit_path.write_text(
        json.dumps(entries, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )


def _draft_register_entry_from_audit(row: dict, audit_entry: dict
                                     ) -> dict | None:
    """If the audit result indicates a CONTENT deviation, propose a
    register entry. Auto-fills what it can from the worker's feedback;
    leaves the longer-form fields for the human to refine.

    Returns ``None`` if the audit result doesn't warrant a register entry.
    """
    strict = audit_entry.get("strict") or {}
    examples = audit_entry.get("examples") or {}
    overall = audit_entry.get("overall_verdict")
    if overall != "FAIL":
        return None
    # Prefer the strict checker's feedback if it FAILed directly; else
    # the example verifier's.
    if strict.get("verdict") == "FAIL":
        feedback = strict.get("feedback", "")
    else:
        feedback = examples.get("feedback", "")
    # Make an id slug from the row's ref + a short descriptor.
    short = re.sub(r"[^a-z0-9]+", "_",
                   (feedback.split(".")[0] or "deviation").lower())[:40].strip("_")
    entry_id = f"{row['ref']}_{short}" if short else f"{row['ref']}_deviation"
    return {
        "id":                entry_id,
        "introduced_by_ref": row["ref"],
        "introduced_at":     datetime.now(timezone.utc).date().isoformat(),
        "breaks":            feedback.splitlines()[0][:240] if feedback else "(see feedback below)",
        "preserves":         "(auditor draft -- please edit)",
        "at_risk_pattern":   "(auditor draft -- please edit)",
        "tags":              ["auditor-draft"],
        "notes":             f"Drafted by audit_chapter.py from row {row['ref']}.\n\n"
                             f"Full audit feedback:\n{feedback}",
    }


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("chapter", type=int)
    parser.add_argument("--rows", type=str, default=None,
                        help="comma-separated row indices to audit "
                             "(default: every solved row in order)")
    parser.add_argument("--resume", action="store_true",
                        help="skip rows whose ref already has an entry "
                             "in audit.json")
    parser.add_argument("--no-register-drafts", action="store_true",
                        help="don't append auto-drafted entries to "
                             "deviations.json (still logs to audit.json)")
    args = parser.parse_args(argv[1:])

    data_path = find_chapter_data_path(args.chapter)
    chapter_folder = data_path.parent
    data = load_data(data_path)
    audit_path = _audit_path(chapter_folder)
    audit_log = _load_audit(audit_path)
    seen_refs = {e["ref"] for e in audit_log}

    # Build the row order.
    if args.rows:
        indices = [int(s) for s in args.rows.split(",") if s.strip()]
    else:
        indices = [i for i, r in enumerate(data["rows"])
                   if r.get("solved") == "yes"]
    if args.resume:
        indices = [i for i in indices
                   if data["rows"][i].get("ref") not in seen_refs]

    print(f"[audit] chapter {args.chapter}: {len(indices)} row(s) to audit",
          flush=True)

    t0_batch = time.monotonic()
    for i, idx in enumerate(indices, start=1):
        row = data["rows"][idx]
        ref = row["ref"]
        print(f"\n[audit] === {i}/{len(indices)}: {ref} "
              f"({row.get('def_or_claim')}, section {row.get('section')}) "
              f"===", flush=True)
        t0_row = time.monotonic()
        try:
            result = audit_one_row(row)
        except Exception as e:                              # noqa: BLE001
            print(f"[audit] audit_one_row raised: {e}; logging ERROR.",
                  flush=True)
            result = {
                "ref":             ref,
                "strict":          {"verdict": "ERROR", "deviation_class": None,
                                    "feedback": f"audit_one_row raised: {e}",
                                    "raw_tail": ""},
                "examples":        None,
                "overall_verdict": "ERROR",
            }
        result["audited_at"]    = datetime.now(timezone.utc).isoformat(timespec="seconds")
        result["elapsed_sec"]   = round(time.monotonic() - t0_row, 1)

        # Replace any prior audit for this ref (--resume skips above, so
        # this fires only when the user re-runs without --resume).
        audit_log = [e for e in audit_log if e["ref"] != ref]
        audit_log.append(result)
        _save_audit(audit_path, audit_log)

        # Maybe draft a register entry.
        if not args.no_register_drafts:
            draft = _draft_register_entry_from_audit(row, result)
            if draft:
                # Skip if any existing entry has the same id (the helper
                # would raise otherwise).
                existing_ids = {e.get("id") for e in load_register()}
                if draft["id"] not in existing_ids:
                    register_deviation(draft)
                    print(f"[audit] drafted deviation register entry: "
                          f"{draft['id']}", flush=True)

        print(f"[audit] {ref} -> overall_verdict={result['overall_verdict']} "
              f"in {result['elapsed_sec']}s "
              f"(batch elapsed {(time.monotonic()-t0_batch)/60:.1f} min)",
              flush=True)

    print(f"\n[audit] DONE: {len(indices)} row(s) audited in "
          f"{(time.monotonic()-t0_batch)/60:.1f} min", flush=True)
    print(f"[audit] log: {audit_path.relative_to(LEANIFICATION_DIR.parent)}",
          flush=True)
    print(f"[audit] deviation register: "
          f"{(LEANIFICATION_DIR / 'deviations.json').relative_to(LEANIFICATION_DIR.parent)} "
          f"({len(load_register())} entries)", flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
