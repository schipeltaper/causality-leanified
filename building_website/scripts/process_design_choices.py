#!/usr/bin/env python3
"""Generate the `design_choices` field for one row by asking Claude to
read the Lean comments around the row's marker-wrapped statement.

For a given `ref`, this script:

1. Locates the row in `data.json` and its `main_lean_file`.
2. Slices the Lean file to find the `-- <ref> -- start statement` /
   `-- <ref> -- end statement` block(s).
3. Captures the *surrounding* comments — every line preceding the
   first start marker that is itself a Lean comment (`--` / `/- … -/`
   / `/-- … -/`), back until the previous non-comment, non-blank
   line. These pre-statement comments are where the formalize worker
   documents design choices.
4. Sends the gathered comment text + the statement to Claude with a
   focused prompt that produces a polished Markdown design-choices
   article.
5. Writes the result into `building_website/website/data/<ref>.json`
   under the `design_choices` field (preserving every other field
   produced by fetch_row.py).

Usage:
    python3 building_website/scripts/process_design_choices.py def_3_1
    python3 building_website/scripts/process_design_choices.py def_3_1 --force
    python3 building_website/scripts/process_design_choices.py --all

Requires `pip install anthropic` and `ANTHROPIC_API_KEY` in the env.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from fetch_row import find_row, REPO_ROOT, WEBSITE_DATA, REF_RE  # noqa: E402

MODEL      = "claude-opus-4-7"
MAX_TOKENS = 2048

PROMPT = """\
You're producing the "Design choices" panel for one row of a Lean 4
formalization site (Forré–Mooij Causality lecture notes).

## Row

  ref:     {ref}
  kind:    {kind}
  section: {section}
  title:   {title}

## The Lean statement (the canonical declaration this row formalises)

```lean
{statement}
```

## Comments preceding the statement in the Lean file

These are the formalize worker's notes — anything from a brief
sentence to a multi-paragraph design discussion. Some rows have rich
design-choice notes here; some have almost nothing.

```
{comments}
```

## Your task

Produce a polished Markdown article — no headings, just flowing
paragraphs — that distils the **design choices** the formalize worker
made for this row. Each meaningful choice is one paragraph beginning
with a bolded one-line summary, then a short explanation of the
alternative(s) considered and why they were rejected.

If the comments contain little or no design-choice content (e.g. a
single-line summary, or just a docstring), output exactly the literal
text `_No notable design choices._` — do not invent material.

Constraints:

- Audience: a reader who knows Lean 4 basics.
- Do NOT restate the lecture-notes definition or the Lean signature.
- Do NOT include raw Lean comment syntax (`--`, `/-`, `-/`, `/--`).
- Inline code references in `` `backticks` ``; math expressions in
  `$…$` (KaTeX will render).
- ~100-400 words for substantive rows; one short line if there's
  truly nothing to say.

Output STRICTLY a JSON object on one line, no other text:

{{"design_choices": "…"}}
"""


def _gather_preceding_comments(text: str, ref: str) -> str:
    """Walk backwards from the row's first `-- <ref> -- start statement`
    marker and collect every preceding line that's a Lean comment
    (`--` line, or text inside a `/- … -/` block). Stops on the first
    non-comment, non-blank line. Returns the comments in source order."""
    start_marker = re.compile(
        r"^[ \t]*--[ \t]+" + re.escape(ref) + r"[ \t]+--[ \t]+start[ \t]+statement[ \t]*$",
        re.MULTILINE,
    )
    m = start_marker.search(text)
    if not m:
        return ""
    lines = text[:m.start()].splitlines()
    # Walk backwards.
    collected: list[str] = []
    in_block = False
    for line in reversed(lines):
        stripped = line.rstrip()
        if not stripped.strip():
            # Blank line: include it if we're still inside the comment
            # block, otherwise it terminates the gather (the formalize
            # worker writes a blank between the comment block and the
            # marker but tightly packs the comments themselves).
            if collected:
                collected.append(stripped)
                continue
            else:
                continue
        # We treat a line as "comment" if:
        #   - it's a `--` line, OR
        #   - it ends a `/- … -/` block (saw `-/`), OR
        #   - we're walking back inside a `/- … -/` block we haven't
        #     yet exited.
        if in_block:
            collected.append(stripped)
            if "/-" in stripped:
                in_block = False
            continue
        if stripped.lstrip().startswith("--"):
            collected.append(stripped)
            continue
        if "-/" in stripped:
            collected.append(stripped)
            if "/-" not in stripped or stripped.find("/-") > stripped.find("-/"):
                in_block = True
            continue
        # Non-comment, non-blank — stop.
        break
    collected.reverse()
    # Drop trailing blank lines so we don't open with empty space.
    while collected and not collected[-1].strip():
        collected.pop()
    while collected and not collected[0].strip():
        collected.pop(0)
    return "\n".join(collected)


def _extract_statement(text: str, ref: str) -> str:
    """First statement block, source order."""
    pat = re.compile(
        r"^[ \t]*--[ \t]+" + re.escape(ref) + r"[ \t]+--[ \t]+start[ \t]+statement[ \t]*\n"
        r"(?P<body>.*?)"
        r"^[ \t]*--[ \t]+" + re.escape(ref) + r"[ \t]+--[ \t]+end[ \t]+statement[ \t]*$",
        re.DOTALL | re.MULTILINE,
    )
    m = pat.search(text)
    return m.group("body").rstrip("\n") if m else ""


def call_claude(ref: str, kind: str, section: str, title: str,
                statement: str, comments: str) -> str:
    try:
        import anthropic  # type: ignore
    except ImportError:
        sys.exit("error: pip install anthropic")
    client = anthropic.Anthropic()
    prompt = PROMPT.format(
        ref=ref, kind=kind, section=section, title=title,
        statement=statement, comments=comments,
    )
    msg = client.messages.create(
        model=MODEL,
        max_tokens=MAX_TOKENS,
        messages=[{"role": "user", "content": prompt}],
    )
    text = "".join(b.text for b in msg.content if getattr(b, "type", None) == "text").strip()
    m = re.search(r"\{.*\}", text, re.DOTALL)
    if not m:
        sys.exit(f"error: model did not return JSON; got:\n{text}")
    try:
        obj = json.loads(m.group(0))
    except json.JSONDecodeError as e:
        sys.exit(f"error: malformed JSON from model: {e}\n{text}")
    if "design_choices" not in obj:
        sys.exit(f"error: missing design_choices key in model response: {obj}")
    return obj["design_choices"]


def process_one(ref: str, force: bool) -> bool:
    path = WEBSITE_DATA / f"{ref}.json"
    if not path.exists():
        print(f"[{ref}] error: {path} missing — run fetch_row.py first", file=sys.stderr)
        return False
    data = json.loads(path.read_text(encoding="utf-8"))
    if data.get("design_choices") and not force:
        print(f"[{ref}] already populated — use --force to regenerate")
        return True

    row, _ = find_row(ref)
    main_lean = REPO_ROOT / row["main_lean_file"]
    text = main_lean.read_text(encoding="utf-8")
    comments  = _gather_preceding_comments(text, ref)
    statement = _extract_statement(text, ref)

    if not statement:
        print(f"[{ref}] no statement marker block found in {row['main_lean_file']}", file=sys.stderr)
        return False
    if not comments.strip():
        print(f"[{ref}] no preceding comments — writing the no-choices placeholder")
        data["design_choices"] = "_No notable design choices._"
    else:
        print(f"[{ref}] calling {MODEL}…")
        data["design_choices"] = call_claude(
            ref, row["def_or_claim"], row.get("section", ""), row.get("title", ""),
            statement, comments,
        )

    path.write_text(json.dumps(data, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(f"[{ref}] wrote {path.relative_to(REPO_ROOT)}", file=sys.stderr)
    return True


def all_refs() -> list[str]:
    return sorted(
        p.stem for p in WEBSITE_DATA.glob("*.json")
        if p.stem != "manifest" and REF_RE.match(p.stem)
    )


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("ref", nargs="?")
    ap.add_argument("--all", action="store_true")
    ap.add_argument("--force", action="store_true")
    args = ap.parse_args()

    refs = all_refs() if args.all else ([args.ref] if args.ref else [])
    if not refs:
        ap.error("provide a ref or use --all")
    if not os.environ.get("ANTHROPIC_API_KEY"):
        sys.exit("error: set ANTHROPIC_API_KEY")
    ok = True
    for r in refs:
        ok = process_one(r, args.force) and ok
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
