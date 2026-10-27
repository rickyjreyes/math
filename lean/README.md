# Lean 4 formalization status

This Mathlib v4.23.0 project integrates main-line supporting modules with newer full H² manuscript formalizations and conditional bridges. All declarations must pass Lean CI on the exact revision before being called kernel-checked. Manuscript-level status (which papers are formalized end to end) is in
[formalization.yaml](formalization.yaml).

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
  `0 < m ≤ m_B`, every minimizing sequence converges strongly in `H²(ℝ²)` after translations
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
- [FourierShellL2](MathProofs/FourierShellL2.lean) — F10, complete: Plancherel's theorem
  (the unitary `L²` Fourier transform, equal to the Fourier integral on `L¹ ∩ L²`), the
  isolated-shell theorem for essential and distributional support, the Helmholtz and
  polynomial-dispersion corollaries, and the wave-packet proposition.
- [TorusFourier](MathProofs/TorusFourier.lean) — F11 (E59 and discrete E62): the Fourier Hilbert
  basis of `L²((ℝ/Lℤ)^d)`, bounded Fourier multipliers, the dominant-annulus projection
  (idempotent, self-adjoint, contraction, orthogonal projection onto the band-limited subspace,
  energy decomposition, best approximation, operator norm), the discrete FFT identity, and the
  discrete spectral energy fraction with its equality cases and remarks.
- [SpectralConcentration](MathProofs/SpectralConcentration.lean) — F11 (E16 and continuous E62):
  the weak realisation of `r − aΔ − bΔ²` on `L²(ℝ^d)`, existence and uniqueness of mild solutions
  with the exact modal power law, concentration of the normalised spectral measure on the
  preferred shell, argmax convergence with the `t^{-1/2}` rate, polar coordinates and the radial
  corollary, the counterexample without spectral access, and the continuous spectral fraction.
- [BandPassFlow](MathProofs/BandPassFlow.lean) — F11 (E13/E14): `H^{2k}` of the flat torus as a
  weighted `ℓ²` space, the Sobolev embedding `H² ⊂ C` for `d ≤ 3`, and the band-pass energy as a
  `C¹` functional on `H²`. It proves the negative Wirtinger gradient-flow identity with exact
  energy dissipation and the balance law, the real-gradient and half-energy normalisations, and
  the centred Swift–Hohenberg form with the exact energy identity. It also covers the preferred
  Fourier shell (linearisation, growing band, ultraviolet damping, lattice maximisers,
  non-invariance of finite shells), the `β > 0` lower bound with finite total dissipation, and
  stationarity of time-periodic solutions.
- [CurvatureNonattainment](MathProofs/CurvatureNonattainment.lean) — F05, complete:
  whole-space nonattainment in every dimension and strict spreading for `1 ≤ d ≤ 4`.

### Integrated additional proofs and diagnostics

- [IntrinsicScalarMetric](MathProofs/IntrinsicScalarMetric.lean): intrinsic positive-sign tensor and frame-covariance, but not a globally smooth cotangent tensor section.
- [MinimizerNonvanishing](MathProofs/MinimizerNonvanishing.lean): quantitative quartic nonvanishing for negative-energy near-minimizers.
- [OrbitalStabilityCriterion](MathProofs/OrbitalStabilityCriterion.lean): an abstract, conditional Cazenave–Lions orbital-stability reduction; the unconditional theorem for the cubic–quintic flow is [OrbitalStability](MathProofs/OrbitalStability.lean).
- [L2FourierShellBridge](MathProofs/L2FourierShellBridge.lean): infinite-dimensional L² shell exclusion under a supplied Plancherel equivalence; the canonical transform is constructed in [FourierShellL2](MathProofs/FourierShellL2.lean).
- [Source-pinned v18 analytic Jacobian rank certificate](../docs/SM_V18_ANALYTIC_RANK_CERTIFICATE.md): reproducible interval arithmetic, not Lean.
- Original main-line modules retained: CurvatureUniformBound, PhysicalDispersionMinimum, DispersionCriticalPoint, S004DiracBracket, GaussianTrialAlgebra, VariationalBinding, ContinuousPhaseIntegral, ContinuousPhaseOptimizer, ContinuousSpectralVariance, QuinticConvolution, UVGrowthBound, UVExponentialObstruction, DispersionBranchPositivity and DispersionRealDomain.
- [CurvatureLegacy](MathProofs/CurvatureLegacy.lean) preserves earlier abstract nonattainment and curvature-weight positivity support; full H² results are in CurvatureNonattainment.

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

All four F01 manuscripts are formalized. The frozen v18 analytic Jacobian rank is separately source-pinned and interval-certified but not Lean formalized. All four F11
manuscripts (E13/E14, E16, E59, E62) are formalized; F12 remains outside Lean.

The local-coordinate rank/signature obstruction (F08) **is formalized** for
actual differentiable complex fields on four-coordinate charted spaces,
including explicit matrix contraction and its positivity. A global bundled
coordinate-invariant tensor construction is not certified. The generic local matrix
nullity core of F09 is formalized but is not a certification of the
11-parameter-observable physical model, its computed Jacobian, or its
published numerical rank.

Separate research-grade Lean work lives in [wct-lean](https://github.com/rickyjreyes/wct-lean);
do not conflate its theorem count with this repository.

F10 is formalized on all of `L²` through the Plancherel transform of
[FourierShellL2](MathProofs/FourierShellL2.lean); the earlier Schwartz-space version is retained.

## Completion criterion for each of the 14 tweets

The boolean `main_theorem_formalized` (per manuscript, and per family) stays false until the
**entire theorem as stated in its PDF** is a precise exported Lean declaration
with no `sorry`, `admit`, new axioms, unproved assumptions, or finite surrogate
used in place of the stated infinite-dimensional result. Supporting finite
models, algebraic identities, and theorems with stronger extra assumptions
never count as end-to-end certification of the manuscript.
