"""Two global registers for LN-wording subtleties.

A *subtlety* is a documented oddity inside the LN's own wording --
ambiguity, an unintended-looking corner case admitted by the literal
reading, internal inconsistency, an arbitrary or unclear phrase.
**Subtleties are distinct from deviations:**

- ``deviations.json`` records mismatches between a Lean encoding and
  the LN's literal statement (used during row-solving).
- The subtlety registers record issues *internal to the LN wording*,
  independent of how anything is Lean-encoded.

Two phases, two register files:

- ``leanification/initial_subtlety_register.json`` — written by
  ``scaffold/scripts/phase2_initialization/initial_subtlety_checker.py`` during the chapter
  initialization phase. Every row's tex block is passed through the
  ``check_ln_wording`` worker; any subtleties surface here. The
  initialization-phase table generator then asks the human to
  decide-and-resolve each entry, and the processor folds the human's
  answers into the chapter's ``data.json`` as the
  ``addition_to_the_LN`` column.

- ``leanification/working_subtlety_register.json`` — written during
  the row-solving phase via the manager's ``register_ln_subtlety``
  action. Captures wording oddities a manager notices mid-row that
  weren't surfaced (or weren't resolved) at initialization.

Both registers share an entry schema::

    {
      "id":              "<unique_snake_case_id>",
      "explanation":     "<free-form, as long as needed>",
      "observed_by_ref": "<ref or 'initial_subtlety_checker'>"
    }

Both registers are informational. Writes never halt the solver.
They serve as a paper trail for debugging -- when a future row's
manager hits an unexplained tension, grepping the registers for the
relevant definition is a quick first lead at the root cause.
"""

from __future__ import annotations

import json
from pathlib import Path

# .../scaffold/scripts/utils/<this file> -> repo root is three levels up.
REPO_ROOT = Path(__file__).resolve().parent.parent.parent.parent
LEANIFICATION = REPO_ROOT / "leanification"

INITIAL_REGISTER_PATH = LEANIFICATION / "initial_subtlety_register.json"
WORKING_REGISTER_PATH = LEANIFICATION / "working_subtlety_register.json"


def _path_for(phase: str) -> Path:
    if phase == "initial":
        return INITIAL_REGISTER_PATH
    if phase == "working":
        return WORKING_REGISTER_PATH
    raise ValueError(f"phase must be 'initial' or 'working'; got {phase!r}")


def load_register(phase: str) -> list[dict]:
    """Return entries in insertion order. Missing/empty/corrupt file
    is treated as an empty register. ``phase`` is ``'initial'`` or
    ``'working'``."""
    path = _path_for(phase)
    if not path.exists():
        return []
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError:
        return []
    if not isinstance(data, list):
        return []
    return data


def save_register(phase: str, entries: list[dict]) -> None:
    """Overwrite the register for ``phase``. Pretty-printed UTF-8."""
    path = _path_for(phase)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(entries, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )


def find_by_id(phase: str, entry_id: str) -> dict | None:
    """Return the entry with the given id in ``phase``, or ``None``."""
    for e in load_register(phase):
        if e.get("id") == entry_id:
            return e
    return None


def register_subtlety(phase: str, entry: dict) -> dict:
    """Append a single subtlety. Required fields: ``id`` and
    ``explanation``. Optional: ``observed_by_ref``.

    Raises ``ValueError`` if a required field is missing. Raises
    ``KeyError`` if the id is already in the register -- callers
    decide how to handle (the orchestrator refuses once with a nudge,
    then on retry registers under a mangled id).
    """
    entry = dict(entry)
    if not entry.get("id"):
        raise ValueError("entry missing required field `id`")
    if not entry.get("explanation"):
        raise ValueError("entry missing required field `explanation`")
    existing = load_register(phase)
    if any(e.get("id") == entry["id"] for e in existing):
        raise KeyError(f"id {entry['id']!r} already in the {phase} register")
    existing.append(entry)
    save_register(phase, existing)
    return entry


def mangle_id(phase: str, base: str) -> str:
    """Return a unique id derived from ``base`` by suffixing ``_v2``,
    ``_v3``, ... until no collision in ``phase``'s register."""
    if find_by_id(phase, base) is None:
        return base
    n = 2
    while find_by_id(phase, f"{base}_v{n}") is not None:
        n += 1
    return f"{base}_v{n}"


if __name__ == "__main__":
    import sys
    phase = sys.argv[1] if len(sys.argv) > 1 else "initial"
    print(f"{phase} subtlety register: {_path_for(phase)}")
    entries = load_register(phase)
    print(f"  entry count: {len(entries)}")
    for e in entries:
        print(f"  [{e.get('id')}]  observed_by_ref={e.get('observed_by_ref')}")
        expl = (e.get("explanation") or "").strip()
        for line in expl.splitlines():
            print(f"    {line}")
        print()
