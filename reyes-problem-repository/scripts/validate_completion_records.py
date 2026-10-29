#!/usr/bin/env python3
"""Check GC adoption links and any reviewed issue-to-Lean completion records.

Metadata consistency is NOT a Lean kernel check, scientific novelty test,
review of theorem equivalence, or evidence that an issue is ready to close.
"""
from __future__ import annotations

import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parent
GC_IDS = {f"GC{i:02d}" for i in range(1, 301)}
SHA = re.compile(r"^[0-9a-f]{40}$")
DECL = re.compile(r"^[A-Za-z_][A-Za-z0-9_'.]*(?:\.[A-Za-z_][A-Za-z0-9_']*)*$")
ISSUE = re.compile(r"^https://github\.com/rickyjreyes/math/issues/([1-9][0-9]*)$")
PR = re.compile(r"^https://github\.com/rickyjreyes/math/pull/([1-9][0-9]*)$")
CI = re.compile(r"^https://github\.com/rickyjreyes/math/actions/runs/([1-9][0-9]*)$")


def require(ok: bool, msg: str) -> None:
    if not ok:
        raise ValueError(msg)


def load(path: Path):
    return json.loads(path.read_text(encoding="utf-8"))


def text_field(rec: dict, key: str) -> str:
    value = rec.get(key)
    require(isinstance(value, str) and bool(value.strip()), f"Required text field: {key}")
    return value.strip()


def repo_file(value: str, prefix: str, extension: str) -> Path:
    require(isinstance(value, str), "Invalid file path")
    p = Path(value)
    require(not p.is_absolute() and all(x not in ("..", ".", "") for x in p.parts)
            and p.parts and p.parts[0] == prefix and p.suffix == extension,
            f"Unsafe or incorrect {prefix} file path: {value}")
    file_path = REPO / p
    require(file_path.is_file(), f"Referenced file not found: {value}")
    return file_path


def validate_adoption(data: dict, ids: set[str], registry: dict) -> None:
    require(data.get("schema_version") == 2, "Unexpected adoption schema")
    rows = data.get("entries")
    require(isinstance(rows, list), "Missing adoption list")
    expected = [f"GC{i:02d}" for i in range(1, 66)]
    require([row.get("id") for row in rows] == expected,
            "Adoption map must contain GC01..GC65 exactly once in ID order")
    index = (ROOT / "EXISTING_WORK_65.md").read_text(encoding="utf-8")
    indexed = re.findall(r"^\| \[(GC\d{2})\]", index, re.MULTILINE)
    require(indexed == expected, "65-item readable index differs from adopted GC links")
    lean_inventory = (REPO / "lean" / "formalization.yaml").read_text(encoding="utf-8")
    seen, linked_issues = set(), set()
    for row in rows:
        pid = row.get("id")
        require(pid in ids and pid not in seen, f"Duplicate or invalid GC adoption ID: {pid}")
        seen.add(pid)
        issue_num = row.get("issue_number")
        require(issue_num is None or (isinstance(issue_num, int) and issue_num > 0),
                f"{pid}: invalid issue number")
        require(row.get("issue_scope") in ("milestone", "whole_problem", "not_created"),
                f"{pid}: invalid issue scope")
        require((issue_num is None) == (row["issue_scope"] == "not_created"),
                f"{pid}: inconsistent issue scope and issue number")
        if issue_num is not None:
            require(issue_num not in linked_issues, f"Duplicate adopted issue #{issue_num}")
            linked_issues.add(issue_num)
            official_url = registry[pid].get("discussion_issue")
            if official_url:
                require(official_url == f"https://github.com/rickyjreyes/math/issues/{issue_num}",
                        f"{pid}: adopted issue differs from original catalogue")
        require(row.get("correspondence") == "not_audited",
                f"{pid}: adoption links alone cannot assert proof correspondence")
        relationship = row.get("relationship")
        require(relationship in ("direct_scope_to_review", "adjacent_foundation", "unmapped"),
                f"{pid}: invalid research alignment category")
        text_field(row, "scope_assessment")
        decls = row.get("anchor_declarations")
        require(isinstance(decls, list) and
                all(isinstance(d, str) and DECL.fullmatch(d) and d in lean_inventory
                    for d in decls), f"{pid}: invalid source-inventory Lean declaration")
        if relationship == "direct_scope_to_review":
            require(bool(decls) and bool(row.get("related_lean")),
                    f"{pid}: direct scope needs an identified source and declaration")
        if relationship == "unmapped":
            require(not decls and not row.get("related_lean") and
                    not row.get("related_papers"),
                    f"{pid}: unmapped entry includes unqualified source links")
        page = (ROOT / registry[pid]["file_path"]).read_text(encoding="utf-8")
        require("## Existing research alignment" in page and
                row["scope_assessment"] in page and
                "../../EXISTING_WORK_65.md" in page,
                f"{pid}: per-problem alignment section is missing or stale")
        for item in row.get("related_lean", []):
            repo_file(item, "lean", ".lean")
        for item in row.get("related_papers", []):
            repo_file(item, "papers", ".tex")
    require(len(seen) == len(rows), "Inconsistent adopted problem count")


def validate_completed(rec: dict, ids: set[str], adopted: dict) -> None:
    pid = rec.get("gc_id")
    require(pid in ids, f"Unknown GC ID in completion record: {pid}")
    require(rec.get("issue_scope") in ("milestone", "whole_problem"),
            f"{pid}: invalid issue scope")
    number = rec.get("issue_number")
    require(type(number) is int and number > 0, f"{pid}: invalid issue number")
    issue_url = text_field(rec, "issue_url")
    match = ISSUE.fullmatch(issue_url)
    require(match is not None and int(match.group(1)) == number,
            f"{pid}: issue number and URL disagree")
    if pid in adopted and adopted[pid]["issue_number"] is not None:
        original = adopted[pid]
        if rec["issue_scope"] == original["issue_scope"]:
            require(number == original["issue_number"],
                    f"{pid}: completion does not match the tracked milestone issue")
        else:
            require(original["issue_scope"] == "milestone" and
                    rec["issue_scope"] == "whole_problem" and
                    number != original["issue_number"],
                    f"{pid}: full GC must use a distinct whole-problem issue")
    require(rec.get("outcome") in ("proved", "refuted"), f"{pid}: invalid outcome")
    obligations = rec.get("acceptance_criteria")
    require(isinstance(obligations, list) and len(obligations) > 0 and
            all(isinstance(x, str) and x.strip() for x in obligations),
            f"{pid}: frozen acceptance criteria missing")
    remaining = rec.get("remaining_obligations")
    require(isinstance(remaining, list) and
            all(isinstance(x, str) and x.strip() for x in remaining),
            f"{pid}: remaining obligations must be an explicit list")
    if rec["issue_scope"] == "whole_problem":
        require(not remaining, f"{pid}: whole-problem resolution retains obligations")
    lean_path = text_field(rec, "lean_file")
    source = repo_file(lean_path, "lean", ".lean").read_text(encoding="utf-8")
    full_decl = text_field(rec, "lean_declaration")
    require(DECL.fullmatch(full_decl) is not None,
            f"{pid}: invalid fully qualified Lean declaration name")
    short_decl = full_decl.rsplit(".", 1)[-1]
    require(re.search(r"\b(theorem|lemma|def|instance)\s+" + re.escape(short_decl) +
                      r"(?=\s|\(|\{|:)", source) is not None,
            f"{pid}: referenced Lean declaration was not located in {lean_path}")
    require(SHA.fullmatch(text_field(rec, "proof_commit")) is not None,
            f"{pid}: proof commit must be a 40-character SHA")
    require(CI.fullmatch(text_field(rec, "lean_ci_url")) is not None,
            f"{pid}: exact successful Lean CI run required")
    require(PR.fullmatch(text_field(rec, "review_pr_url")) is not None,
            f"{pid}: reviewed PR URL required")
    require(text_field(rec, "correspondence_review_url").startswith(
            f"https://github.com/rickyjreyes/math/"),
            f"{pid}: issue-to-theorem review must be linked")
    require(text_field(rec, "claim_scope_summary") != "",
            f"{pid}: mathematical correspondence summary missing")
    paper = rec.get("paper_file")
    claim = rec.get("paper_claim_reference")
    if paper is None:
        require(claim is None, f"{pid}: paper claim without optional paper")
    else:
        require(isinstance(paper, str) and paper.startswith(("papers/", "preprints/")),
                f"{pid}: manuscript path must be a project paper/preprint")
        pre = paper.split("/", 1)[0]
        ext = Path(paper).suffix
        require(ext in (".tex", ".md"), f"{pid}: source manuscript must be textual")
        repo_file(paper, pre, ext)
        require(isinstance(claim, str) and claim.strip(),
                f"{pid}: paper requires a precise claim/section reference")


def main() -> None:
    registry = load(ROOT / "problem_registry.json")["entries"]
    lookup = {e["id"]: e for e in registry}
    require(set(lookup) == GC_IDS, "Expected original 300-problem registry")
    adoption = load(ROOT / "existing_work_links.json")
    validate_adoption(adoption, GC_IDS, lookup)
    adopted = {x["id"]: x for x in adoption["entries"]}
    records = load(ROOT / "completion_records.json")
    require(records.get("schema_version") == 1, "Unexpected completion schema")
    rs = records.get("records")
    require(isinstance(rs, list), "Missing completion records array")
    seen = set()
    for row in rs:
        validate_completed(row, GC_IDS, adopted)
        key = (row["gc_id"], row["issue_number"], row["lean_declaration"])
        require(key not in seen, f"Duplicate completion record: {key}")
        seen.add(key)
    kinds = {name: sum(row["relationship"] == name for row in adoption["entries"])
             for name in ("direct_scope_to_review", "adjacent_foundation", "unmapped")}
    print(f"PASS: {len(adoption['entries'])} original GC adoption links "
          f"(direct/adjacent/unmapped={kinds['direct_scope_to_review']}/"
          f"{kinds['adjacent_foundation']}/{kinds['unmapped']}), "
          f"{len(rs)} completion records.")
    print("NOTE: This does not validate CI conclusions or theorem-to-issue semantic equivalence.")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError, TypeError, json.JSONDecodeError) as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        sys.exit(1)
