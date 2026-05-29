"""Standalone dispatchers for the strict equivalence checker and the
property-based example verifier.

These are *not* wired into ``solve_chapter.py`` yet. They are the
building blocks for ``extras/audit_chapter.py``, which sweeps over
already-solved rows non-destructively. Integration into the main
orchestrator loop is a separate, later step.

Each dispatcher:
- builds the prompt for its worker (row context + the prompt markdown);
- spawns a ``claude -p`` subprocess via ``solve_chapter.run_claude``;
- parses the worker's reply for its verdict block;
- returns a structured ``dict`` with the verdict + any feedback.

Failures (timeout, exec error, malformed verdict) are returned as a
verdict of ``"ERROR"`` in the dict so the audit script can log them
without crashing.
"""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path

SCAFFOLD = Path(__file__).resolve().parent
sys.path.insert(0, str(SCAFFOLD))

from solve_chapter import (                                    # type: ignore
    REPO_ROOT,
    WORKERS_DIR,
    read_worker_prompt,
    run_claude,
    WorkerTimeoutError,
)
from deviations import load_register                            # type: ignore


# ---------------------------------------------------------------------------
# Shared: build the row-context block used by both workers
# ---------------------------------------------------------------------------

def _read_or_empty(p: Path) -> str:
    try:
        return p.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError):
        return ""


def _row_context_block(row: dict, include_lean: bool = True,
                       include_tex_block: bool = True) -> str:
    """Render a multi-line context block describing the row, suitable
    for pasting at the bottom of either worker's prompt."""
    parts: list[str] = ["# Row context (auditor-supplied)"]
    for k in ("ref", "title", "type", "def_or_claim", "section"):
        parts.append(f"- {k}: {row.get(k)}")
    parts.append(f"- main_lean_file: {row.get('main_lean_file')}")
    parts.append(f"- lean_files: {row.get('lean_files')}")
    if include_tex_block:
        tex_block = row.get("tex_block") or ""
        parts.append(f"\n## LN tex block (verbatim, from data.json)\n"
                     f"```latex\n{tex_block}\n```\n")
    if include_lean:
        for lf in (row.get("lean_files") or [row.get("main_lean_file")]):
            if not lf:
                continue
            content = _read_or_empty(REPO_ROOT / lf)
            if content:
                parts.append(f"\n## Lean file: {lf}\n"
                             f"```lean\n{content}\n```\n")
    return "\n".join(parts)


def _deviation_register_block() -> str:
    """Render the current deviation register as a Markdown section to
    paste into the worker prompts so they can recognise inherited
    deviations."""
    entries = load_register()
    if not entries:
        return ("\n## Deviation register\n"
                "(empty -- no deviations recorded yet)\n")
    out = ["\n## Deviation register (existing entries)\n"]
    for e in entries:
        out.append(
            f"- **{e.get('id')}** (introduced by `{e.get('introduced_by_ref')}`, "
            f"tags={e.get('tags')})\n"
            f"  - breaks: {e.get('breaks')}\n"
            f"  - preserves: {e.get('preserves')}\n"
            f"  - at_risk_pattern: {e.get('at_risk_pattern')}\n"
        )
    return "\n".join(out)


# ---------------------------------------------------------------------------
# Verdict parsing
# ---------------------------------------------------------------------------

_STRICT_VERDICT_RE = re.compile(
    r"^VERDICT:\s*(PASS|FAIL|EXAMPLE_GENERATION)\s*$",
    re.MULTILINE,
)
_DEVIATION_CLASS_RE = re.compile(
    r"^DEVIATION_CLASS:\s*(CONTENT|PRESENTATION|NONE|UNCERTAIN)\s*$",
    re.MULTILINE,
)
_FEEDBACK_RE = re.compile(
    r"BEGIN\[feedback\]\s*\n(.*?)\n\s*END\[feedback\]",
    re.DOTALL,
)
_EXAMPLES_VERDICT_RE = re.compile(
    r"^VERDICT:\s*(PASS|FAIL)\s*$",
    re.MULTILINE,
)
_INSTANCES_RE = re.compile(
    r"^INSTANCES_CHECKED:\s*(\d+)\s*$",
    re.MULTILINE,
)


def _parse_strict_reply(reply: str) -> dict:
    m_v = _STRICT_VERDICT_RE.search(reply)
    m_c = _DEVIATION_CLASS_RE.search(reply)
    m_f = _FEEDBACK_RE.search(reply)
    return {
        "verdict":        m_v.group(1) if m_v else "MISSING",
        "deviation_class": m_c.group(1) if m_c else None,
        "feedback":       m_f.group(1).strip() if m_f else "",
        "raw_tail":       reply[-1200:],
    }


def _parse_examples_reply(reply: str) -> dict:
    m_v = _EXAMPLES_VERDICT_RE.search(reply)
    m_n = _INSTANCES_RE.search(reply)
    m_f = _FEEDBACK_RE.search(reply)
    return {
        "verdict":           m_v.group(1) if m_v else "MISSING",
        "instances_checked": int(m_n.group(1)) if m_n else 0,
        "feedback":          m_f.group(1).strip() if m_f else "",
        "raw_tail":          reply[-1200:],
    }


# ---------------------------------------------------------------------------
# Strict equivalence checker
# ---------------------------------------------------------------------------

def build_strict_equivalence_prompt(row: dict) -> str:
    return (
        f"{read_worker_prompt('verify_equivalence_strict.md')}\n\n"
        f"{_row_context_block(row, include_lean=True, include_tex_block=True)}\n"
        f"{_deviation_register_block()}\n"
    )


def run_strict_equivalence_checker(row: dict) -> dict:
    """Spawn the strict-equivalence worker on this row. Returns a
    structured dict: ``{verdict, deviation_class, feedback, raw_tail}``.

    Verdict is one of ``PASS`` / ``FAIL`` / ``EXAMPLE_GENERATION`` /
    ``MISSING`` (the worker emitted no parseable verdict) /
    ``ERROR`` (the subprocess failed).
    """
    label = f"audit_strict_eq_{row['ref']}"
    try:
        reply, _sess = run_claude(
            build_strict_equivalence_prompt(row), label=label)
    except WorkerTimeoutError as e:
        return {"verdict": "ERROR", "deviation_class": None,
                "feedback": f"worker timed out: {e}", "raw_tail": ""}
    except Exception as e:                                 # noqa: BLE001
        return {"verdict": "ERROR", "deviation_class": None,
                "feedback": f"worker errored: {e}", "raw_tail": ""}
    return _parse_strict_reply(reply)


# ---------------------------------------------------------------------------
# Example-based verifier
# ---------------------------------------------------------------------------

def build_example_verifier_prompt(row: dict,
                                  strict_reason: str | None = None) -> str:
    extra = ""
    if strict_reason:
        extra = (
            "\n## Why the strict checker requested examples\n"
            f"```\n{strict_reason}\n```\n"
        )
    return (
        f"{read_worker_prompt('verify_with_examples.md')}\n\n"
        f"{_row_context_block(row, include_lean=True, include_tex_block=True)}\n"
        f"{_deviation_register_block()}\n"
        f"{extra}"
    )


def run_example_verifier(row: dict, strict_reason: str | None = None
                         ) -> dict:
    """Spawn the property-based example verifier. Returns a dict:
    ``{verdict, instances_checked, feedback, raw_tail}``.

    Verdict is ``PASS`` / ``FAIL`` / ``MISSING`` / ``ERROR``.
    """
    label = f"audit_examples_{row['ref']}"
    try:
        reply, _sess = run_claude(
            build_example_verifier_prompt(row, strict_reason=strict_reason),
            label=label)
    except WorkerTimeoutError as e:
        return {"verdict": "ERROR", "instances_checked": 0,
                "feedback": f"worker timed out: {e}", "raw_tail": ""}
    except Exception as e:                                 # noqa: BLE001
        return {"verdict": "ERROR", "instances_checked": 0,
                "feedback": f"worker errored: {e}", "raw_tail": ""}
    return _parse_examples_reply(reply)


# ---------------------------------------------------------------------------
# Convenience: combined audit of one row
# ---------------------------------------------------------------------------

def audit_one_row(row: dict) -> dict:
    """Run the strict checker. If it requests examples, also run the
    example verifier. Returns a flat dict ready to log into audit.json.

    Schema::

        {
          "ref":               <row ref>,
          "strict": {verdict, deviation_class, feedback, raw_tail},
          "examples": {verdict, instances_checked, feedback, raw_tail} | None,
          "overall_verdict":   "PASS" | "FAIL" | "ERROR" | "MISSING",
        }

    ``overall_verdict``:
    - PASS if strict PASS, or strict EXAMPLE_GENERATION + examples PASS.
    - FAIL if strict FAIL, or strict EXAMPLE_GENERATION + examples FAIL.
    - MISSING / ERROR propagate from either layer.
    """
    out: dict = {"ref": row["ref"]}
    strict = run_strict_equivalence_checker(row)
    out["strict"] = strict
    out["examples"] = None
    v = strict.get("verdict")
    if v == "PASS":
        out["overall_verdict"] = "PASS"
    elif v == "FAIL":
        out["overall_verdict"] = "FAIL"
    elif v == "EXAMPLE_GENERATION":
        examples = run_example_verifier(
            row, strict_reason=strict.get("feedback") or "")
        out["examples"] = examples
        ev = examples.get("verdict")
        out["overall_verdict"] = ev if ev in ("PASS", "FAIL") else "MISSING"
    else:
        out["overall_verdict"] = v or "MISSING"
    return out


if __name__ == "__main__":
    if len(sys.argv) != 3:
        print("usage: audit_helpers.py <chapter> <row_index>",
              file=sys.stderr)
        sys.exit(1)
    chapter = int(sys.argv[1])
    row_index = int(sys.argv[2])
    from solve_chapter import (                                # type: ignore
        find_chapter_data_path, load_data,
    )
    dp = find_chapter_data_path(chapter)
    data = load_data(dp)
    row = data["rows"][row_index]
    print(f"[audit] running on row {row_index}: {row['ref']}", flush=True)
    result = audit_one_row(row)
    print(json.dumps(result, indent=2, ensure_ascii=False))
