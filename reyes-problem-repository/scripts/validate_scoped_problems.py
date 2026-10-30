#!/usr/bin/env python3
"""Validate GC65–GC300 scoping inventory, not mathematical correctness or novelty."""
from __future__ import annotations

import json
import re
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
SCOPE = REPO / "scoped"
REGISTRY = REPO / "problem_registry.json"
FIRST, LAST = 65, 300


def validate() -> list[str]:
    failures: list[str] = []
    try:
        data = json.loads(REGISTRY.read_text(encoding="utf-8"))
        registered = {e["id"]: e for e in data["entries"]}
    except (OSError, ValueError, KeyError, TypeError) as exc:
        return [f"Cannot load registry: {exc}"]

    expected = {f"GC{i}" for i in range(FIRST, LAST + 1)}
    if not expected.issubset(registered):
        failures.append(f"Registry missing {sorted(expected - registered.keys())}")
    other = {p.stem for p in SCOPE.glob("GC[0-9]*.md")} - expected
    if other:
        failures.append(f"Unexpected scoped problem files: {sorted(other)}")

    index_path = SCOPE / "README.md"
    if not index_path.is_file():
        failures.append("Scoped index README.md is missing")
        index = ""
    else:
        index = index_path.read_text(encoding="utf-8")
    index_ids = re.findall(r"(?m)^- \[(GC\d{2,3}): ", index)
    if len(index_ids) != LAST - FIRST + 1 or set(index_ids) != expected:
        failures.append("README scoped index does not cover each GC65–GC300 exactly once")

    for i in range(FIRST, LAST + 1):
        gid = f"GC{i}"
        entry = registered.get(gid)
        path = SCOPE / f"{gid}.md"
        if not path.is_file():
            failures.append(f"{gid}: missing scoped file")
            continue
        source = path.read_text(encoding="utf-8")
        if not source.startswith(f"# {gid}: "):
            failures.append(f"{gid}: top-level title/ID mismatch")
        if len(source.strip()) < 600:
            failures.append(f"{gid}: unusually short scope (inspect manually)")
        if len(re.findall(r"(?m)^## ", source)) < 2:
            failures.append(f"{gid}: lacks a separately headed target and acceptance section")
        if re.search(r"\b(?:TBD|TODO|FIXME)\b", source, flags=re.IGNORECASE):
            failures.append(f"{gid}: placeholder remains")
        if entry is not None:
            historical = f"../{entry['file_path']}"
            if f"({historical})" not in source:
                failures.append(f"{gid}: no link to canonical historical file ({historical})")
            if not (REPO / entry["file_path"]).is_file():
                failures.append(f"{gid}: historical source missing ({entry['file_path']})")
    return failures


if __name__ == "__main__":
    issues = validate()
    if issues:
        print("FAIL: scoping inventory problems:")
        for item in issues:
            print(" -", item)
        raise SystemExit(1)
    print(f"PASS: {LAST-FIRST+1} unique GC IDs, scoped files, historical links, sections and index rows")
    print("NOTE: syntax/inventory checks do not prove mathematical rigor, novelty or Lean correctness.")
