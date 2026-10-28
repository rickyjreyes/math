# M6B: exact manuscript-to-Lean proof mapping

**Issue:** [#42](https://github.com/rickyjreyes/math/issues/42) · **PR:** [#49](https://github.com/rickyjreyes/math/pull/49)

Pinned versions: Lean 4.23.0, Mathlib 4.23.0. All eleven pre-existing proof modules through commit `08f52a4d` passed [focused CI](https://github.com/rickyjreyes/math/actions/runs/40633614184) and the [general supporting-theorems workflow](https://github.com/rickyjreyes/math/actions/runs/40633614086). This is **not** validation of later commits.

| Manuscript statement | Exact Lean declarations | Current evidence |
|---|---|---|
| Proposition 1, positivity, node safety, nonzero-field limit, phase invariance | `denominator_pos`, `denominator_at_node`, `curvature_at_node`, `curvature_downarrow_zero`, `curvature_phase_invariant` in `M6BCurvature`/`M6BLimit` | Green at `08f52a4d` |
| Theorem 1, nonunique admissible closure | `curvature_contDiff`, `every_closure_is_admissible`, `two_distinct_admissible_closures`, `infinitely_many_distinct_closures` | Green at `08f52a4d` |
| Theorem 2, two non-phase-related solutions at fixed mass and forcing on open square | `squarePlus_laplace`, `squareMinus_laplace`, `squarePlus_smooth`, `squareMinus_smooth`, `square_fields_dirichlet`, `squarePlus_prescribed_mass`, `squareMinus_prescribed_mass`, `stationary_curvature_equal`, `prescribedForcing_smooth`, `stationary_plus_has_prescribed_forcing`, `stationary_minus_has_prescribed_forcing`, `exact_stationary_counterexample` | Green at `08f52a4d` for iterated-square mass and all-point phase inequivalence |
| Theorem 2, literal product-measure `L²((0,π)²)`, non-phase-equivalence **inside** square, and single fully quantified existential theorem | `squareMass_eq_planarSquareMass`, `squarePlus_planar_prescribed_mass`, `squareMinus_planar_prescribed_mass`, `stationary_not_phase_related_on_square`, `manuscript_stationary_noninjectivity` in new `M6BFubini`/`M6BManuscript` | **Current-head CI not yet reported** |
| Proposition 2, phase invariance but no equivariance | `canonical_curvature_one_nonzero`, `phase_invariant_not_equivariant` in new `M6BPhaseNonEquivariance` | **Current-head CI not yet reported** |

The first theorem is about constitutive closure **nonuniqueness** and the second about stationary-map **noninjectivity**. Neither establishes time-evolution nonuniqueness. A pointwise two-jet theorem is not asserted to solve an arbitrary PDE or to provide arbitrary prescribed forcing.

**Certification policy:** Keep `main_theorem_formalized: false` until the current PR head passes the root `lake build` and focused CI, with the actual new declarations checked. Revalidate the manuscript statement's domain, parameter, and quantifier scope before declaring complete.
