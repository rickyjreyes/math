# Formalization review — 2026-10-27

The maintained library contains **90 project modules and 1,704 source theorem/lemma
declarations**, including private lemmas. **14 of the 14 original manuscripts are
complete** under the manifest's manuscript-wide criterion, including F09.
The declaration count is an inventory, not a measure of mathematical novelty or
manuscript completeness.

## Corrections found by comparing definitions with the source

1. **Two active v18 parameters had been frozen accidentally.** The previous
   `V18Forward.middleRaw` called a helper with fixed frequencies `5.0632` and
   `9.4062`, ignoring coordinates 10 and 11 of its 31-dimensional input. The
   corrected definition uses both coordinates. Its seven middle-coordinate
   derivative theorems retain that dependence; `frozen_middleRaw` proves the
   specialization to the published frozen values. The old five-variable helper
   remains valid for its explicitly frozen frequencies.
2. **The external certificate's input intervals omitted binary64 rounding.**
   Exact decimal intervals did not enclose every coefficient actually stored in
   the pinned NumPy arrays. The certificate now takes rational hulls enclosing
   both the nominal decimal and stored binary64 values, including heavy-sector
   input ratios. It also checks the heavy outputs' inner light-floor branch.
   The resulting selected determinant remains strictly above 1,116,446, hence
   nonzero. This is an external interval proof about an analytic real model,
   not a Lean theorem or a derivative of floating-point execution.
3. **A frozen-output theorem inherited an irrelevant floor hypothesis.**
   `include h` in the draft clipped-derivative module also applied to the
   aggregate theorem advertised as unconditional at frozen observations.
   `omit h` removes that premise. The floor bound is discharged using
   `every_middle_observable_unclipped` at each of the five observations.
4. **Documentation overstated sequence convergence and retained stale CI text.**
   Compactness supplies a convergent subsequence after translations; it does
   not assert that every entire minimizing sequence converges. The README now
   says so and records the completed F10 integration rather than awaiting it.

## Verification

### F09 completion verified on 2026-10-29

The complete proof revision
[`2e64e34`](https://github.com/rickyjreyes/math/commit/2e64e34023be231d4307b98dd0abb71fe513adf4)
passed all six workflows on Lean/Mathlib **v4.23.0**. It includes the latest
main integration through `117e8c5`, preserving the M6B proofs and the Reyes
Problem Repository rename. The completion count changes only after the
actual theorem chain and the following verification succeeded.

| Verification | Result |
|---|---|
| Full repository `lake build`, all 90 imported project modules | [PASS][completion-ci], 7,306 build jobs including dependencies |
| Focused F09 determinant, derivative, rank and C¹ level-set build | [PASS](https://github.com/rickyjreyes/math/actions/runs/40859515392) |
| Source-pinned analytic Jacobian interval certificate and regressions | [PASS](https://github.com/rickyjreyes/math/actions/runs/40859515507) |
| Exact-rational middle Taylor certificate | [PASS](https://github.com/rickyjreyes/math/actions/runs/40859515382) |
| Manuscript/PDF build | [PASS](https://github.com/rickyjreyes/math/actions/runs/40859515357) |
| M6B continuum counterexample regression build | [PASS](https://github.com/rickyjreyes/math/actions/runs/40859515361) |

The local targeted build, both analytic regression tests, source-pinned
certificate, rational certificate, and complete PDF build also passed. The
PDF script produced 27 paper PDFs, one compendium PDF, and the overview.
The revised F09 PDF was visually checked. A comment/string-aware scan found
no executable `sorry`, `admit`, `axiom`, or `native_decide` in maintained
Lean sources. The ten exported proof dependency audits contain only
`propext`, `Classical.choice`, and `Quot.sound`; no added axiom or `sorryAx`
is present. [F09Audit.lean](../lean/F09Audit.lean) makes the signature and
dependency audit reproducible and is run by the focused workflow.

### Earlier baseline verification

- The combined baseline `main` revision
  [`0e93a9f`](https://github.com/rickyjreyes/math/commit/0e93a9f2a920d779793648ce3f088bf16efca165)
  passed its [full Lean build](https://github.com/rickyjreyes/math/actions/runs/40586171550).
- The corrected F09 source revision
  [`b6af6cd`](https://github.com/rickyjreyes/math/commit/b6af6cdb2db0aca5eafb8c1ee67913eba1404b4f)
  passed the [full 64-module Lean build][review-ci], the targeted F09 build,
  both external certificates, and PDF compilation on Lean/Mathlib **v4.23.0**.
  The focused workflow explicitly builds `V18FullForward` as well as the
  determinant and clipped-derivative modules. The subsequent integration
  preserved the latest main README improvements and passed the combined
  [PR #47 checks](https://github.com/rickyjreyes/math/pull/47/checks).
- The source-bound interval certificate passes with the unchanged source blob
  `d98cfe243c5a90c332c80ca88618b2343e0698f4`, and optimized values
  `alpha = 5.1725333213…`, `epsilon = 5`.
- Regression checks verify that all 29 coefficient enclosures and the relevant
  heavy ratios contain both exact rational interpretations.
- The separate exact-rational Taylor certificate yields
  `18,000,000 < det(M) < 24,000,000`. This external regression is now
  accompanied by the Lean theorem `V18MiddleJacobian.middle_det_bounds`
  in `V18MiddleDeterminant.lean`; that theorem checks the actual matrix
  using rational arithmetic, six-decimal pi bounds, and Taylor remainders.
- The maintained source contains no executable `sorry`, `admit`, `axiom`, or
  `native_decide` token. Passing these scans is supplementary to kernel checking
  and the comparison of theorem statements with their intended definitions.

## Original theorem completion table

All unqualified declaration names below are in the `ReyesMath` namespace.
“Complete” denotes `MAIN_THEOREM_VERIFIED`. The earlier thirteen completed
results also pass in the current [full completion build][completion-ci].

| # | Result | Exported declaration / module | CI | Status | Remaining obligation |
|---|---|---|---|---|---|
| 1 | Strict binding | [`StrictBinding.strict_binding`](../lean/MathProofs/StrictBinding.lean) | [PASS][review-ci] | Complete | None within the stated mass range |
| 2 | Whole-space minimizers | [`WholeSpace.main`](../lean/MathProofs/WholeSpaceMinimizers.lean) | [PASS][review-ci] | Complete | None within the stated mass range |
| 3 | Orbital stability | [`OrbitalStability.main`](../lean/MathProofs/OrbitalStability.lean) | [PASS][review-ci] | Complete | None; full minimizing-set stability, not attraction or uniqueness of a minimizer |
| 4 | UV Sobolev ill-posedness | [`UVIllPosed.wave_torus_unbounded`](../lean/MathProofs/UVIllPosedness.lean), [`wave_whole_unbounded`](../lean/MathProofs/UVWholeSpace.lean) | [PASS][review-ci] | Complete | None in the stated linear sectors |
| 5 | Spectral–phase identity | [`SpectralPhase.sharp_spectral_phase_decomposition`](../lean/MathProofs/SpectralPhaseIdentity.lean) | [PASS][review-ci] | Complete | None |
| 6 | Nonlinear Fourier leakage | [`FourierLeakage.classification`](../lean/MathProofs/FourierLeakageWellPosed.lean) | [PASS][review-ci] | Complete | None for the stated local classical torus flow |
| 7 | Negative constrained energy | [`NegativeEnergy.negative_constrained_energy`](../lean/MathProofs/NegativeEnergy.lean) | [PASS][review-ci] | Complete | None; genuine Sobolev trial proved using a compact bump carrier |
| 8 | Curvature nonattainment | [`Curvature.global_nonattainment`, `strict_spreading`](../lean/MathProofs/CurvatureNonattainment.lean) | [PASS][review-ci] | Complete | None under the manuscript's dimension assumptions |
| 9 | Dispersion minimum | [`Dispersion.exact_positive_wavenumber_minimum`](../lean/MathProofs/DispersionMinimum.lean) | [PASS][review-ci] | Complete | None |
| 10 | S004 constraint count | [`S004.constraint_count`](../lean/MathProofs/S004ConstraintCount.lean) | [PASS][review-ci] | Complete | None for the regular fixed-background sector |
| 11 | Weighted phase locking | [`phase_locking_exact_minimum`](../lean/MathProofs/PhaseLockingContinuous.lean) | [PASS][review-ci] | Complete | None |
| 12 | Global scalar-metric obstruction | [`ManifoldScalarMetric.main`](../lean/MathProofs/ManifoldScalarMetric.lean) | [PASS][review-ci] | Complete | None for the positive-sign tensor construction |
| 13 | Spectral identifiability | [`V18Forward.f09_completion`, `observed_locally_nonidentifiable`](../lean/MathProofs/V18Identifiability.lean), [`conditional_local_level_set`](../lean/MathProofs/LocalLevelSet.lean) | [PASS][completion-ci] | Complete | None for the exact-decimal frozen model on the stated alpha interval and open ambient domain |
| 14 | Fourier-shell exclusion | [`FourierShell.shell_theorem`, `helmholtz`, `poly_dispersion`, `packets`](../lean/MathProofs/FourierShellL2.lean) | [PASS][review-ci] | Complete | None for the F10 manuscript statements |

## F09 completion proof chain

The actual forward map and its Jacobian are defined, and at every point where
that map is differentiable the rank is at most 11 and its kernel dimension is
at least 20. The new middle proofs establish strict floor inactivity and all
seven coordinate derivatives at the five frozen middle observations.
`V18BranchBounds` additionally proves the three light floors strictly inactive
for every nonnegative alpha, the heavy inner light floors strictly active,
and the heavy outer floors strictly inactive. Exact exponential and power
clipping bounds are also checked. The light estimates use rational lower
bounds on exponential Taylor sums and proved logarithm bounds; the heavy
estimates use monotonicity and positivity of real powers. Neighborhood
regularity is now proved by `V18Regularity`: the actual map agrees locally
with the full-parameter smooth formulas. `V18Frechet` proves
`hasFDerivAt_observed_frozen`, `hasFDerivAt_observed_near_frozen`, and
`jacobian_frozen_eq`, with every active parameter retained.

`V18Forward.selectedMinor_frozen_eq` in `V18SelectedJacobian` now identifies all 121 entries
of the eleven-column restriction of this verified derivative with the
3+5+3 block matrix. All six cross-sector blocks vanish at the verified local
branches; in particular, the heavy inner light floor removes the light-to-heavy
coupling. `V18Forward.selectedMinor_det_ne_zero` in `V18Rank`, `jacobian_rank`,
`jacobian_nullity`, and `jacobian_surjective` prove actual selected-minor
nonsingularity, full derivative rank 11, kernel dimension 20, and surjectivity.
The generic block argument is packaged as matrix invertibility before concrete
instantiation, avoiding expansion of the eleven-element permutation list.
These results pass both the focused and full Lean CI builds.

The arithmetic obligation is discharged by the unconditional theorem
`V18MiddleJacobian.middle_det_ne_zero`. Its stronger bound theorem proves
`18,000,000 < middle.det < 24,000,000`. The proof checks ten trigonometric
enclosures and a 60-term exact determinant expansion; Python only generates
Lean proof scripts and supplies no assumptions. The local targeted Lean build
passes on v4.23.0. The full-model rank-11/nullity-20 theorem now follows from the
selected-block identification above.
The conditional proposition is now proved as `ReyesMath.conditional_local_level_set`.
The bridge constructs Mathlib's implicit-function chart, proves the inverse
is C¹, and restricts both sides to open sets of C¹ regularity.
`V18Forward.observed_local_level_set` applies it to the actual observation
map: the chart sends the complete local fiber exactly onto the vertical
slice in its target, with fiber coordinate space the twenty-dimensional
kernel of the actual derivative. `observed_locally_nonidentifiable` proves
that every ambient neighborhood contains a distinct equal-output vector.
`f09_completion` exports the entire chain under `alpha ∈ [5.172,5.173]`
and frozen epsilon 5. Its targeted and full Lean builds pass.

Full-repository validation and signature/dependency review passed. The
original-manuscript count is **14/14** on the completion branch in
[PR #51](https://github.com/rickyjreyes/math/pull/51). The manuscript has
been aligned with the exact certified column selection;
the earlier numerical diagnostic used different light and heavy columns.
The parameter map itself has not been replaced or simplified.

### Manuscript statement correspondence and scope

| Manuscript statement | Exported Lean declaration |
|---|---|
| Minimum first-order nullity and zero directional derivatives | `V18Forward.local_identifiability`, `V18Forward.null_direction`; general form `differential_local_identifiability_obstruction` |
| Exact nullity under exact full row rank | `exact_sensitivity_nullity_of_full_row_rank`; concrete form `V18Forward.jacobian_nullity` |
| Conditional nonlinear local level set | `conditional_local_level_set`, `exists_c1_level_set_chart`, `level_set_chart_image` |
| Concrete frozen fiber and distinct equal-output points arbitrarily near the center | `V18Forward.f09_completion`, `V18Forward.observed_local_level_set`, `V18Forward.observed_locally_nonidentifiable` |

The local chart and its inverse are C¹ on open source and target, and its
image of the entire local fiber is exactly the vertical slice. This is the
ambient-coordinate formulation of a C¹ embedded submanifold, with model
space the actual derivative kernel of dimension 20. The aggregate theorem
retains `alpha ∈ [5.172,5.173]`, frozen epsilon 5, and the published exact
decimal coefficients. The C¹ neighborhood is in the open 31-dimensional
ambient parameter space, not the optimizer's constraint box. Local
non-identifiability supplies nearby equal-output points; it does not
classify distant solutions or the global topology of a fiber. No claim of
NumPy execution equivalence or independent physical prediction is made.
The active-bounds discussion of a possible 29-parameter restriction is a
remark, not an additional exported eighteen-dimensional fiber theorem.

F11 and F12 are additional families outside the original fourteen. Their
separate developments do not change this completion count. The integrated
M6B proofs are also outside the original fourteen and remain checked.

[review-ci]: https://github.com/rickyjreyes/math/actions/runs/40603164974
[completion-ci]: https://github.com/rickyjreyes/math/actions/runs/40859515395
