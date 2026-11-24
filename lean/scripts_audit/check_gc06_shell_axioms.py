#!/usr/bin/env python3
"""Fail unless every exact GC06 root is audited with standard axioms only."""
import re
import sys
from pathlib import Path
ROOTS = ["ReyesMath.GC06ShellBinding.mB_lt_mR","ReyesMath.GC06ShellBinding.gap_refined","ReyesMath.GC06ShellBinding.strict_binding_refined","ReyesMath.GC06ShellBinding.compactness_refined","ReyesMath.GC06ShellBinding.exists_minimizer_refined","ReyesMath.GC06NearZeroShell.exists_stretch","ReyesMath.GC06NearZeroShell.seed_upper","ReyesMath.GC06NearZeroShell.kinetic_gap","ReyesMath.GC06NearZeroShell.strict_binding_near_zero","ReyesMath.GC06NearZeroShell.compactness_near_zero","ReyesMath.GC06NearZeroShell.exists_minimizer_near_zero"]
ROOTS += ["ReyesMath.GC06VirialBinding.stationary_ratio","ReyesMath.GC06VirialBinding.exists_ratio","ReyesMath.GC06VirialBinding.local_comparison","ReyesMath.GC06VirialBinding.chain_strict","ReyesMath.GC06VirialBinding.energy_per_mass_strict","ReyesMath.GC06VirialBinding.strict_binding_virial","ReyesMath.GC06VirialBinding.compactness_virial","ReyesMath.GC06VirialBinding.exists_minimizer_virial","ReyesMath.GC06VirialBinding.exists_minimizer_zero_all_mass","ReyesMath.GC06VirialBinding.energy_per_mass_le_endpoint","ReyesMath.GC06VirialBinding.energy_per_mass_strict_closed","ReyesMath.GC06VirialBinding.strict_binding_closed","ReyesMath.GC06VirialBinding.compactness_closed","ReyesMath.GC06VirialBinding.exists_minimizer_closed"]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
log = Path(sys.argv[1]).read_text(encoding="utf-8", errors="replace")
for root in ROOTS:
    pattern = re.escape(root) + r"'?\s+depends on axioms:\s*\[([^\]]*)\]"
    matches = re.findall(pattern, log, flags=re.S)
    empty = re.findall(re.escape(root) + r"'?\s+does not depend on any axioms", log)
    if len(matches) + len(empty) != 1:
        raise SystemExit(f"Missing or ambiguous exact axiom inventory: {root}")
    for match in matches:
        unexpected = {x.strip() for x in match.split(",") if x.strip()} - ALLOWED
        if unexpected:
            raise SystemExit(f"{root}: unexpected axioms {sorted(unexpected)}")
print(f"PASS: {len(ROOTS)} exact GC06 roots use only allowed standard axioms")
