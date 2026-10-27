# Lean 4 formalization status

This Mathlib v4.23.0 project contains 655 formal theorem/lemma declarations
(401 previously verified plus 254 new declarations) in forty imported modules. On any revision,
regard them as kernel-checked only after that exact revision's Lean CI passes:

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
- [DispersionCriticalPoint](MathProofs/DispersionCriticalPoint.lean) — explicit positive critical point and its strict global minimum without assuming stationary-point existence.
- [PhysicalDispersionMinimum](MathProofs/PhysicalDispersionMinimum.lean) — specialization to the original K,T,G,m conditions, proving the unique positive global lower-branch minimum.
- [ContinuousPhaseIntegral](MathProofs/ContinuousPhaseIntegral.lean) — actual continuous weighted-integral gap identity and sharp bound.
- [ContinuousPhaseOptimizer](MathProofs/ContinuousPhaseOptimizer.lean) — explicit continuous optimizer existence and equality-case a.e. uniqueness.
- [VariationalBinding](MathProofs/VariationalBinding.lean) — exact cubic–quintic
  coercive square and the conditional specific-energy-to-strict-binding implication.
- [GaussianTrialAlgebra](MathProofs/GaussianTrialAlgebra.lean) — exact
  anisotropic coefficient signs and optimized negative scalar trial energy.
- [S004DiracBracket](MathProofs/S004DiracBracket.lean) — explicitly
  invertible four-constraint bracket and conditional Dirac count.
- [UVGrowthBound](MathProofs/UVGrowthBound.lean) — high-frequency
  unstable growth-rate lower bound proportional to the wavenumber.
- [ContinuousSpectralVariance](MathProofs/ContinuousSpectralVariance.lean) —
  true integral-level weighted variance identity.
- [QuinticConvolution](MathProofs/QuinticConvolution.lean) — uniqueness
  and nonvanishing of the extremal quintic coefficient, excluding cubic cancellation.
- [CurvatureNonattainment](MathProofs/CurvatureNonattainment.lean) —
  positivity of the corrected curvature weight and an abstract
  nonattainment criterion still requiring the actual H² dilation proof.
- [CurvatureUniformBound](MathProofs/CurvatureUniformBound.lean) — a
  finite, explicit global bound on the *actual* nonlinear weight F(s).
- [DispersionBranchPositivity](MathProofs/DispersionBranchPositivity.lean) —
  both real squared-frequency branches are strictly positive on the
  admissible nonnegative q domain for the physical parameters.
- [DispersionRealDomain](MathProofs/DispersionRealDomain.lean) — exact
  collision endpoint and nonnegative-discriminant domain equivalence.
- [DispersionMinimum](MathProofs/DispersionMinimum.lean) — the full
  original-parameter finite-wavenumber minimum, convexity/second derivative,
  sharp initial slope, minimum-frequency and wavenumber corollaries.
- [PhaseLockingContinuous](MathProofs/PhaseLockingContinuous.lean) —
  continuous H¹ winding-phase minimization, sharp gap and equality case,
  unique minimizing phase modulo additive constants and sector selection.
- [SpectralPhaseIdentity](MathProofs/SpectralPhaseIdentity.lean) —
  polar periodic eigenfunction integral identity, equality conditions,
  the exact 4/5 counterexample, and a geometric planar realization.
- [S004ConstraintCount](MathProofs/S004ConstraintCount.lean) —
  regular fixed-background S004 Legendre-image constraints, genuine
  Poisson/Dirac pairing and multiplier preservation, and 4 configuration DOF.
- [FourierLeakage](MathProofs/FourierLeakage.lean) — actual Fourier
  integral coefficients and nonlinear torus cubic/quintic leakage:
  conditional exit from finite multimode coordinate subspaces for every
  locally existing classical solution; explicit fifth harmonic and
  single-mode solutions. Multimode solution existence remains open in Lean.
- [UVExponentialObstruction](MathProofs/UVExponentialObstruction.lean) —
  growing unstable multiplier exceeds every finite polynomial frequency weight.
- [SobolevH2](MathProofs/SobolevH2.lean) — actual whole-space L² graph-closure
  Sobolev H² construction, Laplacian and gradient identities, 2D estimates,
  and exact mass-preserving dilations.
- [NegativeEnergy](MathProofs/NegativeEnergy.lean) — the complete negative
  constrained-energy theorem for every positive mass using a genuine smooth
  compactly supported anisotropic carrier trial on H²(ℝ²;ℂ).
- [UVIllPosedness](MathProofs/UVIllPosedness.lean) — exact high-frequency
  growing modes and no bounded four-jet Sobolev evolution operator on flat tori.
- [UVWholeSpace](MathProofs/UVWholeSpace.lean) — exact Fourier-packet solutions,
  norms, and no bounded four-jet Sobolev evolution operator on ℝ^d.

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

## Gaps and certified results

**Six of the fourteen requested theorem statements now have end-to-end Lean proofs**:
#4 (UV Sobolev four-jet ill-posedness on torus and whole space), #5 (spectral phase),
#7 (negative constrained energy for all positive masses on a whole-space H² graph
model), #9 (physical dispersion minimum), #10 (regular fixed-background S004
canonical constraint count), and #11 (continuous weighted phase locking).
These claims refer to the precise mathematical hypotheses encoded in Lean,
and do not establish an independent derivation of a healthy physical field theory.

The remaining original eight are: strict binding, whole-space minimizers,
orbital stability, unconditional nonlinear Fourier-flow invariance classification
(current leakage proof assumes an existing classical solution), whole-space
curvature nonattainment, global coordinate-independent metric tensor formulation,
model-specific Jacobian rank certification, and L² Fourier-shell exclusion.

The local-coordinate rank/signature obstruction (F08) **is formalized** for
actual differentiable complex fields on four-coordinate charted spaces,
including explicit matrix contraction and its positivity. A global bundled
coordinate-invariant tensor construction is not certified. Arbitrarily many
nonnegative-weight carriers have positive-semidefinite Gram forms. The generic local matrix
nullity core of F09 is formalized but is not a certification of the
11-parameter-observable physical model, its computed Jacobian, or its
published numerical rank.

Separate research-grade Lean work lives in [wct-lean](https://github.com/rickyjreyes/wct-lean);
do not conflate its theorem count with this repository.

The main theorem and corollaries of **F03 (spectral phase), F06 (finite-scale dispersion), and F07 (continuous phase locking)** are now represented by complete kernel-checked Lean declarations. The **regular fixed-background S004 constraint count** within F02 is independently proved, while F02's separate ultraviolet Sobolev evolution theorem remains open. Across the fourteen requested tweets this certifies #5, #9, #10 and #11, subject to the exact written hypotheses (not unrelated physics claims).

The Schwartz-space version of F10 is now proved end-to-end using Mathlib's
Schwartz Fourier inversion; it is **not** the manuscript's full L² theorem.

## Completion criterion for each of the 14 tweets

A boolean `families.Fxx.main_theorem_formalized` stays false until the
**entire theorem as stated in its PDF** is a precise exported Lean declaration
with no `sorry`, `admit`, new axioms, unproved assumptions, or finite surrogate
used in place of the stated infinite-dimensional result. Supporting finite
models, algebraic identities, and theorems with stronger extra assumptions
never count as end-to-end certification of the manuscript.

## Further Lean proof obligations (October 26, 2026)

- **1–3:** Real H² trial function and exact negative energy are now verified;
  prove the strict infimum-specific-energy gap, concentration–compactness,
  global H² flow and the minimizing-set orbital-stability contradiction.
- **6:** Actual torus Fourier integrals, nonlinear convolution, classical
  solution differentiation and instantaneous leakage are now proved in
  Lean. The missing component for unconditional flow noninvariance is
  smooth local existence and uniqueness for all finite multimode data.
- **8:** The nonlinear curvature weight now has an explicit uniform
  bound in Lean. Implement actual H² mass-preserving spatial dilation,
  integrated energy scaling, and strict positive energy.
- **S004:** The regular pointwise canonical count is now formalized. Full nonlinear field-theoretic or gauge-coupled extensions are separate questions.
