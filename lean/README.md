# Lean 4 formalization status

This Mathlib v4.23.0 project integrates main-line supporting modules with newer full H² manuscript formalizations and conditional bridges. All declarations must pass Lean CI on the exact revision before being called kernel-checked. Manuscript-level status (which papers are formalized end to end) is in
[formalization.yaml](formalization.yaml).

The maintained import tree contains **64 project modules and 1,515 theorem/lemma declarations** (including private source lemmas). **13 of the 14 original manuscripts are complete** under the audit criterion; F09 remains partial. Declaration totals do not measure manuscript completeness. The [review and theorem table](../docs/FORMALIZATION_REVIEW_2026-10-27.md) records the remaining obligations.

### Manuscript formalizations

- [PhaseLockingContinuous](MathProofs/PhaseLockingContinuous.lean) — F07, complete:
  exact continuous weighted closed-loop phase-locking minimum for `H¹` phases.
- [DispersionMinimum](MathProofs/DispersionMinimum.lean) — F06, complete: existence,
  explicit formula and uniqueness of the positive-wavenumber dispersion minimum.
- [SpectralPhaseIdentity](MathProofs/SpectralPhaseIdentity.lean) — F03, complete:
  continuous spectral–phase identity, equality case and the 4/5 counterexample.
- [S004ConstraintCount](MathProofs/S004ConstraintCount.lean) — F02, complete: canonical
  Dirac analysis and `N_conf = 4` for the regular S004 scalar.
- [UVIllPosedness](MathProofs/UVIllPosedness.lean),
  [UVWholeSpace](MathProofs/UVWholeSpace.lean) — F02, complete: ultraviolet growth and
  Sobolev ill-posedness on `𝕋^d` and `ℝ^d`.
- [FourierLeakage](MathProofs/FourierLeakage.lean),
  [FourierLeakageWellPosed](MathProofs/FourierLeakageWellPosed.lean) — F04, complete:
  instantaneous leakage, local existence and uniqueness of classical solutions on `𝕋^d`, and
  the classification `E_S` invariant iff `|S| ≤ 1`.
- [SobolevH2](MathProofs/SobolevH2.lean) — `H²(ℝ^d; ℂ)` as the Schwartz closure of
  `(φ, ∇φ, Δφ)`, Parseval on `𝓢`, the 2D Fourier sup-norm estimate, dilations.
- [NegativeEnergy](MathProofs/NegativeEnergy.lean) — F01, complete: `I(m) < 0` at every
  positive mass on `H²(ℝ²)`.
- [StrictBinding](MathProofs/StrictBinding.lean) — F01, complete: explicit strict-binding
  range `0 < m ≤ m_B` and the frozen-parameter corollary.
- [WholeSpaceMinimizers](MathProofs/WholeSpaceMinimizers.lean) — F01, complete: for
  `0 < m ≤ m_B`, every minimizing sequence has a subsequence converging strongly in `H²(ℝ²)` after translations
  (concentration–compactness with a Fourier Hölder estimate, weak compactness, weak closedness
  of `H²` and the Brezis–Lieb lemma), so minimizers exist and `𝒢_m` is compact modulo
  translations.
- [FreeEvolution](MathProofs/FreeEvolution.lean), [H2Algebra](MathProofs/H2Algebra.lean),
  [CubicQuinticFlow](MathProofs/CubicQuinticFlow.lean),
  [OrbitalStability](MathProofs/OrbitalStability.lean) — F01, complete: the free group
  `e^{-it(Δ+k²)²}` on `𝓢`, `L²` and `H²`, the `H²(ℝ²)` algebra and the cubic–quintic
  nonlinearity, global `H²(ℝ²)` well-posedness with continuous dependence and conservation of
  mass and energy (interaction-picture Picard–Lindelöf), and orbital stability of the full
  minimizing set `𝒢_m` for `0 < m ≤ m_B`, including perturbations that change the mass.
- [FourierShellL2](MathProofs/FourierShellL2.lean) — F10, full manuscript formalization:
  Plancherel on `L²`, Fourier integral agreement, essential and distributional
  shell exclusion, Helmholtz and polynomial-multiplier corollaries, and
  fixed-carrier variable-envelope wave packets. Integration CI must pass before certification.
- [CurvatureNonattainment](MathProofs/CurvatureNonattainment.lean) — F05, complete:
  whole-space nonattainment in every dimension and strict spreading for `1 ≤ d ≤ 4`.

### Integrated additional proofs and diagnostics

- [IntrinsicScalarMetric](MathProofs/IntrinsicScalarMetric.lean): intrinsic positive-sign tensor and frame-covariance, but not a globally smooth cotangent tensor section.
- [MinimizerNonvanishing](MathProofs/MinimizerNonvanishing.lean): quantitative quartic nonvanishing for negative-energy near-minimizers.
- [OrbitalStabilityCriterion](MathProofs/OrbitalStabilityCriterion.lean): an abstract, conditional Cazenave–Lions orbital-stability reduction; the unconditional theorem for the cubic–quintic flow is [OrbitalStability](MathProofs/OrbitalStability.lean).
- [L2FourierShellBridge](MathProofs/L2FourierShellBridge.lean): infinite-dimensional L² shell exclusion under a supplied Plancherel equivalence; the canonical transform and the broader F10 corollaries are now encoded in [FourierShellL2](MathProofs/FourierShellL2.lean).
- [Source-pinned v18 analytic Jacobian rank certificate](../docs/SM_V18_ANALYTIC_RANK_CERTIFICATE.md): reproducible interval arithmetic, not Lean.
- Original main-line modules retained: CurvatureUniformBound, PhysicalDispersionMinimum, DispersionCriticalPoint, S004DiracBracket, GaussianTrialAlgebra, VariationalBinding, ContinuousPhaseIntegral, ContinuousPhaseOptimizer, ContinuousSpectralVariance, QuinticConvolution, UVGrowthBound, UVExponentialObstruction, DispersionBranchPositivity and DispersionRealDomain.
- [CurvatureLegacy](MathProofs/CurvatureLegacy.lean) preserves earlier abstract nonattainment and curvature-weight positivity support; full H² results are in CurvatureNonattainment.

- [ManifoldScalarMetric](MathProofs/ManifoldScalarMetric.lean) — full F08 global scalar-gradient manifold tensor and smooth tangent-bundle obstruction: actual mfderiv, bilinear form, positivity, nullity, det=0, covariance and nonnegative multiplets (CI passed).
- [L2Fourier](MathProofs/L2Fourier.lean) — canonical L² Fourier from Schwartz density and Plancherel, plus exact-shell exclusion (kernel-checked together with the F10 corollaries).
- [ExactSensitivityNullity](MathProofs/ExactSensitivityNullity.lean) — conditional exact-nullity-20 corollary for a full-row-rank 31-to-11 derivative (CI passed). The frozen v18 determinant remains externally interval-certified, not Lean-certified.

### Frozen v18 F09 checked partial results

- [V18LightJacobian](MathProofs/V18LightJacobian.lean): exact nonzero source light 3×3 minor.
- [V18HeavyJacobian](MathProofs/V18HeavyJacobian.lean): positive heavy 3×3 minor with rational π bounds.
- [V18BlockJacobian](MathProofs/V18BlockJacobian.lean): generic lower-block-triangular determinant factorization.
- [V18MiddleDerivatives](MathProofs/V18MiddleDerivatives.lean): analytically derives all five selected derivatives of the frozen middle predictor, identifies their matrix entries.
- [V18MiddleJacobian](MathProofs/V18MiddleJacobian.lean): source-specific 5×5 real trigonometric matrix; exact rank-11 reduction is still **conditional** on `middle.det ≠ 0`.
- [V18FullForward](MathProofs/V18FullForward.lean): all 31 real parameters, including both variable middle frequencies; its actual Jacobian and the model-specific structural nullity theorem.
- [V18MiddleFloor](MathProofs/V18MiddleFloor.lean), [V18MiddleClipped](MathProofs/V18MiddleClipped.lean): strict floor inactivity for all five frozen middle observations, and derivatives of the clipped outputs in all seven middle coordinate directions.

**F09 is not complete:** proving the middle determinant's sign inside Lean and formally identifying the complete clipped 31-parameter v18 Jacobian are still required. The conditional nonlinear local level-set proposition also remains unformalized. An external interval certificate does not discharge these kernel obligations.

### Supporting modules

- [Elementary](MathProofs/Elementary.lean) — original elementary algebra.
- [Structural](MathProofs/Structural.lean) — an **actual 11 × 31 matrix**
  kernel-dimension bound; n-dimensional scalar-gradient Gram rank ≤ 2
  and positive semidefiniteness; one-dimensional Fourier cutoff arithmetic;
  a finite weighted-variance identity and inequality.
- [PhaseLocking](MathProofs/PhaseLocking.lean) — finite-sum weighted
  Cauchy–Schwarz phase mismatch lower bound.
- [FourierSupport](MathProofs/FourierSupport.lean) — a.e. zero from
  support on a null set, including the 1D two-point Fourier shell.
- [PhaseMinimizer](MathProofs/PhaseMinimizer.lean) — exact discrete
  weighted phase remainder and sharp gap.
- [StructuralExtensions](MathProofs/StructuralExtensions.lean) — general
  rectangular nullity, arbitrary-carrier Gram rank and positivity,
  and coordinatewise multimode frequency escape in ℤ^d.
- [ModelAlgebra](MathProofs/ModelAlgebra.lean) — S004 acceleration Hessian
  determinant/nondegeneracy and exact dispersion discriminant identity.
- [DispersionMinimizer](MathProofs/DispersionMinimizer.lean) — conditional
  stationary-minimum uniqueness from a rigorous supporting-tangent identity.
- [UVDispersion](MathProofs/UVDispersion.lean) — both exact complex
  characteristic roots; no high-frequency Sobolev growth theorem.
- [LocalIdentifiability](MathProofs/LocalIdentifiability.lean) —
  local derivative-nullity obstruction for arbitrary differentiable
  maps from 31 to 11 real coordinates.
- [ComplexMetric](MathProofs/ComplexMetric.lean) — exact complex
  gradient tensor-to-Gram identity and 4D rank bound.
- [SphereNull](MathProofs/SphereNull.lean) — null Fourier shell and
  zero-a.e. Fourier representative in arbitrary positive Euclidean dimension.
- [ScalarGradientFields](MathProofs/ScalarGradientFields.lean) — rank and
  positive-sign quadratic obstruction using actual Fréchet derivatives of a complex scalar.
- [ChartedScalarMetric](MathProofs/ChartedScalarMetric.lean) — pointwise
  rank/signature obstruction for fields on arbitrary four-coordinate charted spaces.
- [MetricQuadratic](MathProofs/MetricQuadratic.lean) — explicit equality of
  matrix contraction with the directional-derivative sum of squares.
- [SchwartzShell](MathProofs/SchwartzShell.lean) — complete shell-exclusion
  proof for Schwartz-class fields using the actual invertible Fourier transform.

For precise statements and manuscript coverage, see
[formalization.yaml](formalization.yaml).
The build also rejects `sorry`, `admit`, and local `axiom`
declarations. A green check certifies the declarations in these files,
not conclusions from the PDF manuscripts that are not encoded.

## Build

```bash
cd lean
lake update
lake exe cache get
lake build
```

Lean and Mathlib release are pinned to v4.23.0. A dependency lockfile
is not yet committed.

## Gaps

All four F01 manuscripts and the F08 scalar-manifold obstruction are formalized. The frozen-v18 Jacobian rank is source-pinned and interval-certified but not yet Lean formalized. The canonical transform, distributional corollaries and wavepacket theorem now have imported Lean declarations; the combined maintained build has passed Lean CI. F11/F12 also remain outside Lean.

The F08 obstruction on a smooth four-manifold is fully formalized for an actual global complex scalar, including its covariant fiberwise tensor, nonnegativity, rank/nullity, determinant, pullback covariance, and continuous/C^m tangent-bundle evaluation. The model-independent differential nullity core of F09 and its exact-nullity corollary are in Lean, but the source-pinned frozen-v18 transcendental determinant is still a separate numerical interval certificate.

Separate research-grade Lean work lives in [wct-lean](https://github.com/rickyjreyes/wct-lean);
do not conflate its theorem count with this repository.

The canonical `L²` transform is in [L2Fourier](MathProofs/L2Fourier.lean). The complete F10 distributional Helmholtz, polynomial-dispersion and envelope-scale wavepacket statements are in [FourierShellL2](MathProofs/FourierShellL2.lean), checked in the maintained build.

## Completion criterion for each of the 14 tweets

The boolean `main_theorem_formalized` (per manuscript, and per family) stays false until the
**entire theorem as stated in its PDF** is a precise exported Lean declaration
with no `sorry`, `admit`, new axioms, unproved assumptions, or finite surrogate
used in place of the stated infinite-dimensional result. Supporting finite
models, algebraic identities, and theorems with stronger extra assumptions
never count as end-to-end certification of the manuscript.
