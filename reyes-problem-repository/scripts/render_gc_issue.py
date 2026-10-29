#!/usr/bin/env python3
"""Print a draft GC issue body; does not create or modify any GitHub issue.

Usage: python3 reyes-problem-repository/scripts/render_gc_issue.py GC52
Existing linked issues are refused to avoid accidental duplicates.
"""
from __future__ import annotations
import argparse
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BASE = "https://github.com/rickyjreyes/math/blob/main/reyes-problem-repository"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("gc_id", help="GC01 through GC300")
    args = parser.parse_args()
    registry = json.loads((ROOT / "problem_registry.json").read_text(encoding="utf-8"))
    links = json.loads((ROOT / "existing_work_links.json").read_text(encoding="utf-8"))
    entry = next((x for x in registry["entries"] if x["id"] == args.gc_id), None)
    if entry is None:
        parser.error("Unknown GC ID; see ROADMAP_300.md")
    old = next((x for x in links["entries"] if x["id"] == entry["id"]), None)
    if old and old["issue_number"]:
        print(f"{entry['id']} already has research issue #{old['issue_number']}: "
              f"https://github.com/rickyjreyes/math/issues/{old['issue_number']}",
              file=sys.stderr)
        print("Use that issue or review its scope rather than creating a duplicate.",
              file=sys.stderr)
        return 2

    print(f"# [{entry['id']}] {entry['title']}")
    print()
    print("**Issue type:** SCOPING / MILESTONE / WHOLE GC (choose after review)")
    print("**Research stage:** " + entry["status"]
          + "; novel or globally open status not established.")
    print("**Canonical problem file:** " + BASE + "/" + entry["file_path"])
    print("**Workflow:** " + BASE + "/WORKFLOW.md")
    print()
    print("## Proposed research question")
    if entry.get("question"):
        print(entry["question"])
        print()
        print("**Suggested first proof or counterexample target:** "
              + entry.get("first_test", ""))
    else:
        page = (ROOT / entry["file_path"]).read_text(encoding="utf-8")
        for line in page.splitlines():
            if line.startswith(("**Problem.**", "**Resolution criterion.**")):
                print(line)
                print()
    print()
    print("## Pre-existing proof and paper audit")
    if old:
        print("Related Lean files: " + (", ".join(old["related_lean"]) or "not mapped"))
        print("Related papers: " + (", ".join(old["related_papers"]) or "not mapped"))
        print("Research relation: " + old.get("relationship", "unreviewed"))
        print("Candidate Lean declarations: " +
              (", ".join(old.get("anchor_declarations", [])) or "no exact declaration mapped"))
        print("Important unresolved distinction: " +
              old.get("scope_assessment", "not yet audited"))
        print("Issue-to-Lean correspondence: NOT AUDITED")
    else:
        print("Not yet audited. Search the existing Lean, manuscript, and issue inventories.")
    if entry["source_class"] == "roadmap_candidate":
        print("Parent GC questions: " +
              (", ".join(entry.get("parent_problems", [])) or "not indexed"))
        print("**Activation:** SCOPING REQUIRED. Freeze the model, parameters,")
        print("quantifiers, closest literature and an exact theorem or counterexample")
        print("target before calling this a formally specified open problem.")
        print("Guide: " + BASE + "/SCOPING_235.md")
    print("Exact declarations and overlap with this GC: [fill in after audit]")
    print()
    print("## Frozen acceptance criteria")
    print("1. [FIX MODEL, SPACES, PARAMETERS, QUANTIFIERS]")
    print("2. [STATE EXACT PROOF OR COUNTEREXAMPLE OBLIGATION]")
    print("3. [STATE WHAT WOULD REMAIN OPEN]")
    print()
    print("## Lean and paper references")
    print("Exact Lean declaration, commit, successful CI run: [pending]")
    print("Optional manuscript and claim reference: [pending/not required]")
    print("Issue-to-theorem correspondence review: [pending]")
    print()
    print("**Do not close** until the exact scoped claim is kernel-checked and independently")
    print("reviewed for correspondence, or classify this as a scoping-only task.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
