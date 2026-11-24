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
    "ReyesMath.GC01ExpandedOrbits.isolated_orbit_stability_expanded",
    "ReyesMath.GC16InterfaceBinding.bulkDensity_pos",
    "ReyesMath.GC16InterfaceBinding.optimized_increment",
    "ReyesMath.GC16InterfaceBinding.strict_split_of_optimized_margin",
    "ReyesMath.GC16InterfaceBinding.mass_bound_to_surface_gap",
    "ReyesMath.GC16InterfaceBinding.inf_surface_gap_of_cell_bound",
    "ReyesMath.GC06SpectralMerging.amp_one",
    "ReyesMath.GC06SpectralMerging.mass_deletion_comparison",
    "ReyesMath.GC06SpectralMerging.mass_exchange_comparison",
    "ReyesMath.GC06SpectralMerging.cubic_linear_nonneg",
    "ReyesMath.GC06SpectralMerging.multiplier_nonpos",
    "ReyesMath.GC06SpectralMerging.common_multiplier_of_equality",
    "ReyesMath.GC06SpectralMerging.low_density_hessian",
    "ReyesMath.GC06SpectralMerging.all_binding_of_pair_exclusion"
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
