#!/usr/bin/env python3
"""Reject missing, duplicate, or nonstandard transitive axiom audit results."""
import re
import sys
from pathlib import Path

source = Path(sys.argv[1]).read_text(encoding="utf-8")
output = Path(sys.argv[2]).read_text(encoding="utf-8")
roots = re.findall(r"^#print axioms (\S+)$", source, re.M)
if len(roots) != 12 or len(set(roots)) != 12:
    raise SystemExit("Expected twelve distinct GC03 audit roots")
allowed = {"propext", "Classical.choice", "Quot.sound"}
for root in roots:
    pattern = r"^'" + re.escape(root) + r"' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)\s*$"
    results = re.findall(pattern, output, re.M)
    if len(results) != 1:
        raise SystemExit(f"{root}: missing or duplicate axiom report")
    axioms = {x.strip() for x in results[0].split(",") if x.strip()}
    if not axioms <= allowed:
        raise SystemExit(f"{root}: unexpected axioms {sorted(axioms - allowed)}")
    print(f"PASS {root}: {sorted(axioms)}")
print("GC03 focused axiom audit passed (supporting roots only).")
