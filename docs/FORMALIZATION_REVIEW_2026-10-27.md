# Formalization review — 2026-10-27

The maintained library contains **64 project modules and 1,515 source theorem/lemma
declarations**, including private lemmas. **13 of the 14 original manuscripts are
complete** under the manifest's manuscript-wide criterion. F09 remains partial.
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

- The combined baseline `main` revision
  [`0e93a9f`](https://github.com/rickyjreyes/math/commit/0e93a9f2a920d779793648ce3f088bf16efca165)
  passed its [full Lean build](https://github.com/rickyjreyes/math/actions/runs/40586171550).
- The corrected F09 modules build with Lean/Mathlib **v4.23.0**. The focused
  workflow now explicitly builds `V18FullForward` as well as the determinant
  and clipped-derivative modules. Integration requires the full library build
  in [PR #47](https://github.com/rickyjreyes/math/pull/47/checks).
- The source-bound interval certificate passes with the unchanged source blob
  `d98cfe243c5a90c332c80ca88618b2343e0698f4`, and optimized values
  `alpha = 5.1725333213…`, `epsilon = 5`.
- Regression checks verify that all 29 coefficient enclosures and the relevant
  heavy ratios contain both exact rational interpretations.
- The separate exact-rational Taylor certificate yields
  `18,000,000 < det(M) < 24,000,000`. It is explicitly **outside Lean**.
- The maintained source contains no executable `sorry`, `admit`, `axiom`, or
  `native_decide` token. Passing these scans is supplementary to kernel checking
  and the comparison of theorem statements with their intended definitions.

## Original theorem completion table

All unqualified declaration names below are in the `ReyesMath` namespace.
“Complete” denotes `MAIN_THEOREM_VERIFIED`; the F09 row denotes
`KERNEL_VERIFIED_SUPPORTING` with `OPEN_MATHEMATICAL_OBLIGATION`.

| # | Result | Exported declaration / module | Status | Remaining obligation |
|---|---|---|---|---|
| 1 | Strict binding | [`StrictBinding.strict_binding`](../lean/MathProofs/StrictBinding.lean) | Complete | None within the stated mass range |
| 2 | Whole-space minimizers | [`WholeSpace.main`](../lean/MathProofs/WholeSpaceMinimizers.lean) | Complete | None within the stated mass range |
| 3 | Orbital stability | [`OrbitalStability.main`](../lean/MathProofs/OrbitalStability.lean) | Complete | None; full minimizing-set stability, not attraction or uniqueness of a minimizer |
| 4 | UV Sobolev ill-posedness | [`UVIllPosed.wave_torus_unbounded`](../lean/MathProofs/UVIllPosedness.lean), [`wave_whole_unbounded`](../lean/MathProofs/UVWholeSpace.lean) | Complete | None in the stated linear sectors |
| 5 | Spectral–phase identity | [`SpectralPhase.sharp_spectral_phase_decomposition`](../lean/MathProofs/SpectralPhaseIdentity.lean) | Complete | None |
| 6 | Nonlinear Fourier leakage | [`FourierLeakage.classification`](../lean/MathProofs/FourierLeakageWellPosed.lean) | Complete | None for the stated local classical torus flow |
| 7 | Negative constrained energy | [`NegativeEnergy.negative_constrained_energy`](../lean/MathProofs/NegativeEnergy.lean) | Complete | None; genuine Sobolev trial proved using a compact bump carrier |
| 8 | Curvature nonattainment | [`Curvature.global_nonattainment`, `strict_spreading`](../lean/MathProofs/CurvatureNonattainment.lean) | Complete | None under the manuscript's dimension assumptions |
| 9 | Dispersion minimum | [`Dispersion.exact_positive_wavenumber_minimum`](../lean/MathProofs/DispersionMinimum.lean) | Complete | None |
| 10 | S004 constraint count | [`S004.constraint_count`](../lean/MathProofs/S004ConstraintCount.lean) | Complete | None for the regular fixed-background sector |
| 11 | Weighted phase locking | [`phase_locking_exact_minimum`](../lean/MathProofs/PhaseLockingContinuous.lean) | Complete | None |
| 12 | Global scalar-metric obstruction | [`ManifoldScalarMetric.main`](../lean/MathProofs/ManifoldScalarMetric.lean) | Complete | None for the positive-sign tensor construction |
| 13 | Spectral identifiability | [`V18Forward.local_identifiability`, `null_direction`](../lean/MathProofs/V18FullForward.lean) | Supporting proofs verified | Full derivative/block identification, concrete middle determinant in Lean, conditional nonlinear local level-set theorem |
| 14 | Fourier-shell exclusion | [`FourierShell.shell_theorem`, `helmholtz`, `poly_dispersion`, `packets`](../lean/MathProofs/FourierShellL2.lean) | Complete | None for the F10 manuscript statements |

## Exact remaining F09 work

The actual forward map and its Jacobian are defined, and at every point where
that map is differentiable the rank is at most 11 and its kernel dimension is
at least 20. The new middle proofs establish strict floor inactivity and all
seven coordinate derivatives at the five frozen middle observations.

The next analytic obligation is to identify the full Fréchet derivative of
`V18Forward.observed` near `V18Forward.frozen alpha 5`, for the stated alpha
interval, with the 3+5+3 selected block matrix. This includes the light and
heavy clipping branches and their derivative formulas; nonsingularity of
separately defined matrices is insufficient.

The next arithmetic obligation is an unconditional Lean proof of
`V18MiddleJacobian.middle.det ≠ 0`. The exact-rational Taylor certificate gives
concrete bounds to formalize, but its Python execution is not a kernel proof.
After those steps, the full-model rank-11/nullity-20 theorem can be exported.
The manuscript's separate conditional C¹ local level-set proposition still
requires a formal application of the implicit-function/submersion theorem.

F11 and F12 are additional families outside the original fourteen. Their
unmerged developments do not change this completion count.
