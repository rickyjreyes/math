# M6B: exact manuscript-to-Lean proof mapping

**Issue:** [#42](https://github.com/rickyjreyes/math/issues/42) · **PR:** [#49](https://github.com/rickyjreyes/math/pull/49)

Pinned versions: **Lean 4.23.0 / Mathlib 4.23.0**. All **16 M6B modules** passed both focused kernel checking and a **full root `lake build`** at commit `dff7b31e40d8bf25bac79a9cdeefa25b8b293f1a` in [run 40711828745](https://github.com/rickyjreyes/math/actions/runs/40711828745). The separate full-project [supporting-theorems workflow](https://github.com/rickyjreyes/math/actions/runs/40711983195) passed at the subsequent source-identical commit `a264990a31837fd049a14a47d931137e6a7bd2b7`. The historical baseline `08f52a4d` also passed [focused](https://github.com/rickyjreyes/math/actions/runs/40633614184) and [full](https://github.com/rickyjreyes/math/actions/runs/40633614086) CI.

| Manuscript statement | Exact Lean declarations | Current evidence |
|---|---|---|
| Proposition 1, positivity, node safety, nonzero-field limit, phase invariance | `denominator_pos`, `denominator_at_node`, `curvature_at_node`, `curvature_downarrow_zero`, `curvature_phase_invariant` in `M6BCurvature`/`M6BLimit` | Green at `08f52a4d` |
| Theorem 1, nonunique admissible closure | `curvature_contDiff`, `every_closure_is_admissible`, `two_distinct_admissible_closures`, `infinitely_many_distinct_closures` | Jet-level family green at `08f52a4d` |
| Theorem 2, two non-phase-related solutions at fixed mass and forcing on open square | `squarePlus_laplace`, `squareMinus_laplace`, `squarePlus_smooth`, `squareMinus_smooth`, `square_fields_dirichlet`, `squarePlus_prescribed_mass`, `squareMinus_prescribed_mass`, `stationary_curvature_equal`, `prescribedForcing_smooth`, `stationary_plus_has_prescribed_forcing`, `stationary_minus_has_prescribed_forcing`, `exact_stationary_counterexample` | Green at `08f52a4d` for iterated-square mass and all-point phase inequivalence |
| Theorem 2, literal product-measure `L²((0,π)²)`, non-phase-equivalence **inside** square, and single fully quantified existential theorem | `squareMass_eq_planarSquareMass`, `squarePlus_planar_prescribed_mass`, `squareMinus_planar_prescribed_mass`, `stationary_not_phase_related_on_square`, `manuscript_stationary_noninjectivity` in new `M6BFubini`/`M6BManuscript` | **Kernel-checked: run 40711828745** |
| Proposition 2, phase invariance but no equivariance | `canonical_curvature_one_nonzero`, `phase_invariant_not_equivariant` in new `M6BPhaseNonEquivariance` | **Kernel-checked: run 40711828745** |

The first theorem is about constitutive closure **nonuniqueness** and the second about stationary-map **noninjectivity**. Neither establishes time-evolution nonuniqueness. A pointwise two-jet theorem is not asserted to solve an arbitrary PDE or to provide arbitrary prescribed forcing.

## General-dimensional genuine-field formalization

The new `M6BDimensionalField.lean` imports Mathlib's canonical
`InnerProductSpace.laplacian` and exports the following current-head
declarations:

| Mathematical statement | Exact Lean name | Status |
|---|---|---|
| Define true d-dimensional Laplacian by second Fréchet derivative | `laplacianD` | Kernel-checked: run 40711828745 |
| Constancy of complex phase commutes with the actual Laplacian for all C² fields | `laplacianD_phase` | Kernel-checked: run 40711828745 |
| U(1) invariance of d-dimensional field-level curvature | `fieldCurvatureD_phase_invariant` | Kernel-checked: run 40711828745 |
| Explicit globally smooth quadratic field on ℝ^d | `quadraticFieldD_smooth` | Kernel-checked: run 40711828745 |
| Exact Hessian-trace identity Δ‖x‖²=2d | `squared_norm_laplacian_D` | Kernel-checked: run 40711828745 |
| Explicit quadratic witness jet at the origin | `quadraticFieldD_at_origin`, `quadraticFieldD_laplacian_at_origin` | Kernel-checked: run 40711828745 |
| Distinct closure images on genuine fields in *every* d≥1 | `distinct_closures_on_actual_fields_all_dimensions` | Kernel-checked: run 40711828745 |
| Complete assembled closure theorem with all 5 structural axioms and the field-level witness for every d≥1 | `IsAdmissibleRegularization`, `manuscript_closure_nonuniqueness_all_dimensions` | Kernel-checked: run 40711828745 |

Unlike the two-dimensional sine-field example, this theorem has the original universal `d ≥ 1` quantifier. The entire module is now Lean 4.23.0 kernel-checked.

## Additional field-level and mass-scope work

- `M6BClosureFieldWitness.lean` proves `distinct_closures_on_actual_smooth_field`: distinct admissible regularizations give different outputs on `squarePlus 1` at `(π/2,π/4)`, using the *computed* Laplacian, not an arbitrarily supplied jet. It is imported and **kernel-checked at `dff7b31e`**.
- `M6BFubini.lean` now also states `planarSquareMass_eq_sq_norm`: the actual product-measure mass is the square of the complex `L²` norm integrand, not just an unnamed intensity.
- The new general-dimension module uses the quadratic profile `ψ(x)=1+‖x‖²`, yielding a distinguishing nonzero jet `(1,2d)` for each `d≥1`. Its exact proof has passed the full Lean build at `dff7b31e`. The field-space construction is on all of ℝ^d, whose restriction to any open neighborhood of zero supplies the local manuscript witness.
- Focused M6B + full imported-project verification: [40711828745](https://github.com/rickyjreyes/math/actions/runs/40711828745) **passed**. Separate `Lean supporting theorems` project build: [40711983195](https://github.com/rickyjreyes/math/actions/runs/40711983195) **passed**. Registry/doc-only commits after these validated source revisions require a new run for final-head reproducibility.

**Audit conclusion:** The manuscript has two theorems and two propositions, with no separate corollary. Proposition 1 maps to `denominator_pos`, `curvature_at_node`, `curvature_downarrow_zero` and `fieldCurvatureD_phase_invariant_on_open`; Theorem 1 maps to `manuscript_closure_nonuniqueness_all_dimensions`; Theorem 2 maps to `manuscript_stationary_noninjectivity`; Proposition 2 maps to `phase_invariant_not_equivariant`. `ContDiffOn ℝ 2 ψ Ω` with `IsOpen Ω` ensures phase covariance for genuine C² fields on any open Ω, not only globally smooth functions. The exact mass is with respect to product Lebesgue measure on `(0,π)²`. The forcing `F_m` is smooth and **constructed**, not arbitrary; the operator is stationary, not a time-dependent evolution. These hypotheses match the original assertions.

**Certification policy:** Record `main_theorem_formalized: true` only after the complete pinned CI evidence above; keep the PR unmerged until required checks and review rules are satisfied.
