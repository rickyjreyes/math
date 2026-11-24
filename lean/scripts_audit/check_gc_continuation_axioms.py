"""Reject missing roots and every nonstandard transitive axiom."""
import pathlib
import re
import sys

expected = [
    "ReyesMath.GC16BulkBinding.field_bulk_gap",
    "ReyesMath.GC16BulkBinding.inf_bulk_gap",
    "ReyesMath.GC16BulkBinding.quartic_shift_bound",
    "ReyesMath.GC16BulkBinding.scaled_field_upper",
    "ReyesMath.GC16BulkBinding.inf_scaled_upper",
    "ReyesMath.GC16BulkBinding.strict_split_of_certificate",
    "ReyesMath.GC16BulkBinding.inf_increment_bound",
    "ReyesMath.GC16BulkBinding.strict_split_of_small_bulk_defect",
    "ReyesMath.GC01ExpandedOrbits.isolated_orbit_stability_of_binding",
    "ReyesMath.GC01ExpandedOrbits.binding_of_either",
    "ReyesMath.GC01ExpandedOrbits.exists_minimizer_expanded",
    "ReyesMath.GC01ExpandedOrbits.orbital_stability_expanded",
    "ReyesMath.GC01ExpandedOrbits.isolated_orbit_stability_expanded"
]
allowed = {"propext", "Classical.choice", "Quot.sound"}
data = pathlib.Path(sys.argv[1]).read_text(encoding="utf-8")
found = {}
for name, deps in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", data):
    if name in expected:
        found[name] = {a.strip() for a in deps.split(",") if a.strip()}
for name in re.findall(r"'([^']+)' does not depend on any axioms", data):
    if name in expected:
        found[name] = set()
assert set(found) == set(expected), ("Missing roots", set(expected)-set(found))
for name, deps in found.items():
    assert deps <= allowed, (name, deps)
print(f"PASS: {len(found)} exact roots; only standard axioms")
