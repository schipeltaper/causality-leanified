#!/usr/bin/env python3
"""Generate the `lean_explanation` field for one row by asking Claude to
explain only the *non-obvious* parts of the Lean code — naming choices
that aren't self-explanatory and Mathlib / Lean idioms whose meaning
isn't clear from the call site.

Companion to `process_design_choices.py`. For a given `ref`, the
script:

1. Loads `building_website/website/data/<ref>.json` (written by
   `fetch_row.py`).
2. Re-walks the row's `main_lean_file` to gather:
   - the statement marker block(s) — the canonical declaration(s),
   - the helper marker block(s),
   - the formalize worker's comments preceding the first start marker
     (same shape as design choices, but used here for naming context).
3. Calls Claude with a prompt focused only on Lean explanation
   (Mathlib idioms, identifier naming, anything not obvious from the
   code itself), writes the markdown back into the JSON under
   `lean_explanation`. Idempotent (`--force` to overwrite), `--all`
   for batch.

Usage:
    python3 building_website/scripts/process_lean_explanation.py def_3_1
    python3 building_website/scripts/process_lean_explanation.py --all
    python3 building_website/scripts/process_lean_explanation.py def_3_1 --force

Requires `pip install anthropic` and `ANTHROPIC_API_KEY`.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from fetch_row import (  # noqa: E402
    REPO_ROOT, WEBSITE_DATA, REF_RE,
    find_row, extract_lean_statement, extract_lean_helpers,
)
from process_design_choices import _gather_preceding_comments  # noqa: E402

MODEL      = "claude-opus-4-7"
MAX_TOKENS = 2048

PROMPT = """\
You're writing the "Lean explanation" panel for one row of a Lean 4
formalization site (Forré–Mooij Causality lecture notes).

## Row

  ref:     {ref}
  kind:    {kind}
  section: {section}
  title:   {title}

## The Lean code as the reader will see it

```lean
{code}
```

## The formalize worker's comments preceding the statement

(for context — these may name Mathlib lemmas, explain naming, etc.)

```
{comments}
```

## Your task

Produce a polished Markdown article — no headings, just flowing
paragraphs — that explains **only the parts of the code that are not
immediately obvious from their names**. Specifically:

- Naming: when an identifier's purpose is not clear from its name, say
  what it stands for. Skip identifiers whose meaning is plain from the
  name itself.
- Lean / Mathlib functions and operators: when a call site uses a
  Mathlib construct (e.g. `Disjoint`, `×ˢ` = `Set.prod`, `⦃ ⦄`
  instance-implicit binders, `Quotient`, `Finset.image`, …) that the
  reader is not certain to recognise, give a brief one-sentence
  explanation. Skip the trivially familiar (`Set`, `Nat`, basic
  syntax).

Audience: a reader who knows the basics of Lean 4 (`def`, `theorem`,
`structure`, `where`, `:= by`, basic typeclasses, etc.) but is not a
Mathlib expert and is not (yet) familiar with this project's
conventions.

Constraints:

- DO NOT restate the lecture-notes definition or the Lean signature.
- DO NOT include raw Lean comment syntax (`--`, `/-`, `-/`, `/--`).
- Inline code in `` `backticks` ``; math expressions in `$…$`.
- Concise. One short sentence per item is fine; a paragraph at most.
- ~80–300 words total for substantive rows.
- If there's truly nothing to explain (everything is self-evident from
  the code), output exactly: `_Names and operations are self-evident
  from the code._`

Output STRICTLY a JSON object on one line, no other text:

{{"lean_explanation": "…"}}
"""


def call_claude(ref: str, kind: str, section: str, title: str,
                code: str, comments: str) -> str:
    try:
        import anthropic  # type: ignore
    except ImportError:
        sys.exit("error: pip install anthropic")
    client = anthropic.Anthropic()
    prompt = PROMPT.format(
        ref=ref, kind=kind, section=section, title=title,
        code=code, comments=comments,
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
    if "lean_explanation" not in obj:
        sys.exit(f"error: missing lean_explanation key in model response: {obj}")
    return obj["lean_explanation"]


def process_one(ref: str, force: bool) -> bool:
    path = WEBSITE_DATA / f"{ref}.json"
    if not path.exists():
        print(f"[{ref}] error: {path} missing — run fetch_row.py first", file=sys.stderr)
        return False
    data = json.loads(path.read_text(encoding="utf-8"))
    if data.get("lean_explanation") and not force:
        print(f"[{ref}] already populated — use --force to regenerate")
        return True

    row, _ = find_row(ref)
    main_lean = REPO_ROOT / row["main_lean_file"]
    text = main_lean.read_text(encoding="utf-8")

    # Re-assemble the code the website renders: helpers first (across
    # every file in lean_files), then main statement(s).
    helper_codes: list[str] = []
    seen: set[str] = set()
    for path_rel in [row["main_lean_file"], *row.get("lean_files", [])]:
        if path_rel in seen:
            continue
        seen.add(path_rel)
        p = REPO_ROOT / path_rel
        if not p.exists():
            continue
        helper_codes.extend(extract_lean_helpers(p, ref))
    main_codes = extract_lean_statement(main_lean, ref)
    if not main_codes:
        print(f"[{ref}] no statement marker found in {row['main_lean_file']}", file=sys.stderr)
        return False
    code = "\n\n".join(helper_codes + main_codes)
    comments = _gather_preceding_comments(text, ref)

    print(f"[{ref}] calling {MODEL}…")
    data["lean_explanation"] = call_claude(
        ref, row["def_or_claim"], row.get("section", ""), row.get("title", ""),
        code, comments,
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
