#!/usr/bin/env python3
"""Check all 14 GC01/GC06 theorem axiom inventories, without line-prefix filtering."""
from pathlib import Path
import re
import sys

EXPECTED_ROOTS = 14
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}

if len(sys.argv) != 2:
    raise SystemExit("Usage: check_gc_axioms.py gc-audit.log")
text = Path(sys.argv[1]).read_text(encoding="utf-8", errors="replace")
blocks = re.findall(r"depends on axioms:\s*\[([^\]]*)\]", text, flags=re.S)
axiom_free = re.findall(r"does not depend on any axioms", text)
if len(blocks) + len(axiom_free) != EXPECTED_ROOTS:
    raise SystemExit(f"Expected {EXPECTED_ROOTS} audited roots, got "
                     f"{len(blocks) + len(axiom_free)}")
unexpected = sorted({
    axiom.strip() for block in blocks for axiom in block.split(",")
    if axiom.strip() and axiom.strip() not in ALLOWED
})
if unexpected:
    raise SystemExit(f"Unexpected theorem axioms: {unexpected}")
print(f"PASS: checked {EXPECTED_ROOTS} exact GC01/GC06 theorem roots; only standard axioms")
