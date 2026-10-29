#!/usr/bin/env python3
"""Validate the 65-problem catalogue, using only Python's standard library."""
from __future__ import annotations

import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parent
IDS = [f"GC{i:02d}" for i in range(1, 66)]
STATUSES = {"candidate", "scoping", "literature_checked", "open_verified",
            "partially_resolved", "resolved", "withdrawn"}
REVIEWS = {"not_reviewed", "initial_review", "focused_review", "independent_review"}


def slug(text: str) -> str:
    """Slug for the ASCII-only problem headings."""
    return re.sub(r"\s+", "-", re.sub(r"[^\w\s-]", "", text.lower()).strip())


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def check_fences(path: Path) -> None:
    """Catch open Markdown math/code fences."""
    opening = None
    for number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        if re.match(r"^\s*\x60{3}", line):
            opening = number if opening is None else None
    require(opening is None, f"{path}: unclosed fence at line {opening}")


def main() -> None:
    registry = json.loads((ROOT / "problem_registry.json").read_text(encoding="utf-8"))
    entries = registry["entries"]
    require([e["id"] for e in entries] == IDS, "Registry must contain GC01..GC65 in ascending order")
    formal = (ROOT / "FORMAL_PROBLEMS.md").read_text(encoding="utf-8")
    headings = re.findall(r"^## (GC\d\d): (.+)$", formal, re.MULTILINE)
    require([i for i, _ in headings] == IDS, "Formal statements must have exactly GC01..GC50")
    title_map = dict(headings)

    readme = (ROOT / "README.md").read_text(encoding="utf-8")
    status = (ROOT / "STATUS.md").read_text(encoding="utf-8")
    valid_anchors = {slug(f"{i}-{title}") for i, title in headings}
    anchors = re.findall(r"FORMAL_PROBLEMS\.md#(gc\d\d-[a-z0-9-]+)", readme)
    require(set(anchors) == valid_anchors, "README links must cover all 65 problem sections exactly")
    require(len(set(anchors)) == 65, "Expected 65 unique catalogue links")
    status_ids = re.findall(r"^\| (GC\d\d) \|", status, re.MULTILINE)
    require(status_ids == IDS, "STATUS rows must cover GC01..GC65 exactly once, in order")

    count_featured = 0
    for entry in entries:
        i = entry["id"]
        require(entry["title"] == title_map[i], f"{i}: inconsistent title")
        require(entry["status"] in STATUSES, f"{i}: invalid status")
        require(entry["literature"] in REVIEWS, f"{i}: invalid review stage")
        require(isinstance(entry["novelty_established"], bool), f"{i}: invalid novelty flag")
        require(isinstance(entry["claimed_kernel_verified_resolution"], bool), f"{i}: invalid verification flag")
        if entry["status"] == "open_verified":
            require(entry["literature"] == "independent_review",
                    f"{i}: cannot call verified open without independent review")
        dossier = entry.get("dossier")
        if entry["flagship"]:
            count_featured += 1
            require(dossier == f"flagship/{i}.md", f"{i}: missing dossier path")
            require((ROOT / dossier).is_file(), f"{i}: missing dossier")
            require(f"./{dossier}" in readme, f"{i}: README missing dossier link")
        else:
            require(dossier is None, f"{i}: unexpected dossier path")
        require(f"| {i} |" in status, f"{i}: missing status row")
    require(count_featured == 5, "Expected exactly five flagship dossiers")

    for path in [*ROOT.glob("*.md"), *ROOT.glob("flagship/*.md")]:
        check_fences(path)

    required = ["METHOD.md", "LITERATURE.md", "NOTEBOOK.md", "CONTRIBUTING.md",
                "SCREENING.md"]
    for path in required:
        require((ROOT / path).is_file(), f"Missing {path}")
    require((REPO / ".github/ISSUE_TEMPLATE/grand_challenge.yml").is_file(),
            "Missing GitHub issue template")

    print("PASS: 65 statement headings, registry entries, and status rows;")
    print("      65 anchors, five dossier links, balanced Markdown fences, workflow files.")
    print("NOTE: This does not check mathematical validity, novelty, or open status.")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError, TypeError, json.JSONDecodeError) as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        sys.exit(1)
