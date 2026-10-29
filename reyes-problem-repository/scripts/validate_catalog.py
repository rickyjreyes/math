#!/usr/bin/env python3
"""Validate the 300-question Reyes Problem Repository with Python's standard library."""
from __future__ import annotations
import json
import re
import sys
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parent
LEGACY = [f"GC{i:02d}" for i in range(1, 66)]
IDS = [f"GC{i:02d}" for i in range(1, 301)]
STATES = {"candidate", "scoping", "literature_checked", "open_verified",
          "partially_resolved", "resolved", "withdrawn"}
REVIEWS = {"not_reviewed", "initial_review", "focused_review", "independent_review"}

def require(ok: bool, message: str):
    if not ok:
        raise ValueError(message)

def read(path: Path) -> str:
    return path.read_text(encoding="utf-8")

def load(path: Path):
    return json.loads(read(path))

def slug(text: str) -> str:
    return re.sub(r"\s+", "-", re.sub(r"[^\w\s-]", "", text.lower()).strip())

def table_ids(text: str) -> list[str]:
    return re.findall(r"^\| (GC\d{2,3}) \|", text, re.MULTILINE)

def check_fences(path: Path):
    opening = None
    for line_number, line in enumerate(read(path).splitlines(), 1):
        if re.match(r"^\s*\x60{3}", line):
            opening = line_number if opening is None else None
    require(opening is None, f"{path}: unclosed Markdown fence at {opening}")

def main():
    registry = load(ROOT / "problem_registry.json")
    entries = registry["entries"]
    require([e["id"] for e in entries] == IDS,
            "Registry must contain exactly GC01..GC300 in ID order")
    formal = read(ROOT / "FORMAL_PROBLEMS.md")
    original_titles = dict(re.findall(r"^## (GC\d{2}): (.+)$", formal, re.MULTILINE))
    require(list(original_titles) == LEGACY,
            "Original formal GC01..GC65 statements must remain ordered")
    roadmap = read(ROOT / "ROADMAP_300.md")
    status = read(ROOT / "STATUS.md")
    readme = read(ROOT / "README.md")
    shortlist = read(ROOT / "FOUNDATIONAL_SHORTLIST.md")
    folder_index = read(ROOT / "problems" / "README.md")
    roadmap_ids = table_ids(roadmap)
    require(len(roadmap_ids) == 300 and set(roadmap_ids) == set(IDS),
            "Roadmap must contain each of GC01..GC300 once; thematic order is allowed")
    require(table_ids(status) == IDS, "STATUS must list all 300 entries exactly once")
    old_anchors = {slug(f"{i}-{title}") for i, title in original_titles.items()}
    found_anchors = set(re.findall(r"FORMAL_PROBLEMS\.md#(gc\d{2}-[a-z0-9-]+)", readme))
    require(found_anchors == old_anchors, "Original 65 README links changed or missing")
    require("./ROADMAP_300.md" in readme and "./problems/README.md" in readme,
            "Main README missing new navigation")
    expansion = load(ROOT / "problems" / "expansion_candidates.json")
    new_items = expansion["entries"]
    require([x["id"] for x in new_items] == IDS[65:],
            "Expansion manifest must contain GC66..GC300 exactly")
    new_map = {x["id"]: x for x in new_items}
    folders = {x["folder"] for x in expansion["folders"]}
    require(len(folders) == 12, "Expected 12 research folders")
    actual = {x.name for x in (ROOT / "problems").iterdir() if x.is_dir()}
    require(actual == folders, "Research folder inventory mismatch")
    counts = Counter()
    priorities = []
    flagship_count = 0
    normalized_titles = []
    for n, e in enumerate(entries, 1):
        i = e["id"]
        require(e["status"] in STATES and e["literature"] in REVIEWS,
                f"{i}: invalid evidence status")
        require(isinstance(e["novelty_established"], bool)
                and isinstance(e["claimed_kernel_verified_resolution"], bool),
                f"{i}: invalid evidence flags")
        if e["status"] == "open_verified":
            require(e["literature"] == "independent_review",
                    f"{i}: independently reviewed status required")
        if e.get("foundational_screening_candidate"):
            priorities.append(i)
        normalized_titles.append(re.sub(r"\W+", " ", e["title"].casefold()).strip())
        path = Path(e["file_path"])
        require(len(path.parts) == 3 and path.parts[0] == "problems"
                and path.name == f"{i}.md" and path.parts[1] in folders,
                f"{i}: malformed problem file path")
        folder = path.parts[1]
        counts[folder] += 1
        file_path = ROOT / path
        require(file_path.is_file(), f"{i}: missing per-problem file")
        content = read(file_path)
        require(content.startswith(f"# {i}: {e['title']}\n"),
                f"{i}: file heading differs from registry")
        require(f"./{path.as_posix()}" in roadmap, f"{i}: missing roadmap link")
        require(f"(./{i}.md)" in read(ROOT / "problems" / folder / "README.md"),
                f"{i}: missing folder link")
        require(f"[{folder}](./{folder}/README.md)" in folder_index,
                f"{i}: folder omitted from index")
        if n <= 65:
            require(e["title"] == original_titles[i],
                    f"{i}: original mathematical title changed")
            require(e["source_class"] == "original_formal_statement",
                    f"{i}: incorrect original source")
            require("**Canonical mathematical statement:**" in content,
                    f"{i}: missing original source reference")
            if e["flagship"]:
                flagship_count += 1
                dossier = e.get("dossier")
                require(dossier == f"flagship/{i}.md"
                        and (ROOT / dossier).is_file()
                        and f"./{dossier}" in readme,
                        f"{i}: original flagship dossier missing")
            else:
                require(e.get("dossier") is None,
                        f"{i}: unexpected dossier")
        else:
            new = new_map[i]
            require(e["source_class"] == "roadmap_candidate"
                    and e["status"] == "candidate"
                    and e["literature"] == "not_reviewed"
                    and e["novelty_established"] is False
                    and e["claimed_kernel_verified_resolution"] is False,
                    f"{i}: new candidate carries unsupported evidence claims")
            require(e["title"] == new["title"]
                    and e["question"] == new["question"]
                    and e["first_test"] == new["first_test"]
                    and folder == new["area"],
                    f"{i}: expansion fields inconsistent")
            require("**Research question.**" in content
                    and "**First decisive target.**" in content,
                    f"{i}: missing research question or falsifiable target")
            require(not e["flagship"] and e["dossier"] is None,
                    f"{i}: new candidate incorrectly treated as an existing flagship")
    require(len(set(normalized_titles)) == 300, "Duplicate problem titles")
    require(all(counts[x] == 25 for x in folders),
            f"Each folder must have 25 problems: {dict(counts)}")
    require(len(list((ROOT / "problems").glob("*/GC*.md"))) == 300,
            "Exactly 300 problem files required")
    require(flagship_count == 5, "Preserve original five flagship dossiers")
    require(len(priorities) == 25 and table_ids(shortlist) == priorities,
            "Foundational screening shortlist must match 25 registry flags")
    for folder in folders:
        directory = ROOT / "problems" / folder
        items = load(directory / "candidates.json")
        expected = {e["id"] for e in entries
                    if e["file_path"].startswith(f"problems/{folder}/")
                    and e["source_class"] == "roadmap_candidate"}
        require({x["id"] for x in items} == expected,
                f"{folder}: candidate manifest inconsistent")
        require((directory / "README.md").is_file(), f"{folder}: index missing")
    for md in ROOT.rglob("*.md"):
        check_fences(md)
    for name in ("METHOD.md", "LITERATURE.md", "NOTEBOOK.md",
                 "CONTRIBUTING.md", "SCREENING.md", "WORKFLOW.md",
                 "EXISTING_WORK.md", "GC65_ADOPTION.md",
                 "CANDIDATE_ACTIVATION.md", "ROADMAP_300.md",
                 "FOUNDATIONAL_SHORTLIST.md"):
        require((ROOT / name).is_file(), f"Missing required file: {name}")
    require((REPO / ".github/ISSUE_TEMPLATE/grand_challenge.yml").is_file(),
            "Missing GitHub issue template")
    print("PASS: 300 registry entries, indexed problem files, status rows, and links.")
    print("      12 folders of 25; 65 preserved formal statements; 235 unreviewed drafts.")
    print("      25 priority screening candidates and 5 original dossiers.")
    print("NOTE: Structural checks do not verify mathematical novelty or validity.")

if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError, TypeError, json.JSONDecodeError) as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        sys.exit(1)
