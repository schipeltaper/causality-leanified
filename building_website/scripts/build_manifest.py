#!/usr/bin/env python3
"""Generate the sidebar manifest the website uses to build its left nav.

The manifest mirrors the chapter → section → row tree, but only for the
rows we want to expose. For the MVP we expose chapter 3 / section 3.1
only; extending coverage is just a matter of editing `SCOPE`.

Each row in the manifest carries:
  - `ref`         — primary key, matches `data/<ref>.json`
  - `kind`        — "def" | "claim"
  - `label`       — short user-facing label, e.g. "def 3.1 — CDMG"
  - `available`   — true if `building_website/website/data/<ref>.json`
                    exists (so the UI can grey-out missing entries)

Usage:
    python3 building_website/scripts/build_manifest.py
"""

from __future__ import annotations

import hashlib
import json
import re
import sys
from pathlib import Path

REPO_ROOT     = Path(__file__).resolve().parents[2]
WEBSITE       = REPO_ROOT / "building_website" / "website"
WEBSITE_DATA  = WEBSITE / "data"
MANIFEST_PATH = WEBSITE_DATA / "manifest.json"


def stamp_assets() -> None:
    """Cache-bust `app.js` / `style.css` in index.html.

    GitHub Pages serves assets with a 10-minute cache; a browser holding
    a stale `app.js` against freshly-deployed `data/*.json` renders blank
    panes. Appending a content-hash `?v=` query string forces a refetch
    whenever either asset actually changes. Runs in CI on every deploy,
    so the stamp always matches the deployed bytes."""
    index = WEBSITE / "index.html"
    h = hashlib.sha256()
    for name in ("assets/app.js", "assets/style.css"):
        h.update((WEBSITE / name).read_bytes())
    ver = h.hexdigest()[:10]
    html = index.read_text(encoding="utf-8")
    html = re.sub(r"assets/app\.js(\?v=[0-9a-f]+)?",   f"assets/app.js?v={ver}",   html)
    html = re.sub(r"assets/style\.css(\?v=[0-9a-f]+)?", f"assets/style.css?v={ver}", html)
    index.write_text(html, encoding="utf-8")
    print(f"stamped index.html assets with ?v={ver}", file=sys.stderr)

# Edit this to expand coverage. Keys are chapter numbers; values list the
# sections to include (None = all sections in that chapter).
SCOPE: dict[int, list[str] | None] = {
    3: ["3.1"],
}


def chapter_data_path(chapter: int) -> Path | None:
    for p in (REPO_ROOT / "leanification").glob(f"Chapter{chapter}_*/data.json"):
        return p
    return None


def row_label(row: dict) -> str:
    kind = row["def_or_claim"]
    section = row["section"]
    # Renumber within the section by recovering n from the ref.
    # ref is e.g. "def_3_1" or "claim_3_10"; we display the human-friendly
    # form "def 3.1 — CDMG" (n is the within-chapter counter, not within-section,
    # which matches how the LN cites them).
    ref = row["ref"]
    n = ref.split("_")[-1]
    return f"{kind} {section.split('.')[0]}.{n} — {row['title']}"


def main() -> None:
    chapters_out: list[dict] = []
    for chapter, sections in SCOPE.items():
        data_path = chapter_data_path(chapter)
        if data_path is None:
            print(f"warning: chapter {chapter} not found, skipping", file=sys.stderr)
            continue
        data = json.loads(data_path.read_text(encoding="utf-8"))
        section_buckets: dict[str, list[dict]] = {}
        for row in data["rows"]:
            if sections is not None and row["section"] not in sections:
                continue
            section_buckets.setdefault(row["section"], []).append(
                {
                    "ref":       row["ref"],
                    "kind":      row["def_or_claim"],
                    "label":     row_label(row),
                    "title":     row["title"],
                    "available": (WEBSITE_DATA / f"{row['ref']}.json").exists(),
                }
            )
        chapters_out.append(
            {
                "chapter": chapter,
                "title":   data.get("title", f"Chapter {chapter}"),
                "sections": [
                    {"section": s, "rows": section_buckets[s]}
                    for s in sorted(section_buckets.keys(), key=lambda x: tuple(int(p) for p in x.split(".")))
                ],
            }
        )

    MANIFEST_PATH.parent.mkdir(parents=True, exist_ok=True)
    MANIFEST_PATH.write_text(
        json.dumps({"chapters": chapters_out}, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
    print(f"wrote {MANIFEST_PATH.relative_to(REPO_ROOT)}", file=sys.stderr)
    stamp_assets()


if __name__ == "__main__":
    main()
