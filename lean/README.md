# Lean 4 formalization status

This Mathlib v4.23.0 project contains 727 `theorem`/`lemma` declarations in 27 imported
modules. On any revision, regard them as kernel-checked only after that exact revision's
Lean CI passes. Manuscript-level status (which papers are formalized end to end) is in
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
- [FourierLeakage](MathProofs/FourierLeakage.lean) — F04, partial: instantaneous leakage
  for every classical solution from multimode trigonometric data; local existence and
  uniqueness (classification corollary) not yet formalized.
- [SobolevH2](MathProofs/SobolevH2.lean) — `H²(ℝ^d; ℂ)` as the Schwartz closure of
  `(φ, ∇φ, Δφ)`, Parseval on `𝓢`, the 2D Fourier sup-norm estimate, dilations.
- [NegativeEnergy](MathProofs/NegativeEnergy.lean) — F01, complete: `I(m) < 0` at every
  positive mass on `H²(ℝ²)`.
- [StrictBinding](MathProofs/StrictBinding.lean) — F01, complete: explicit strict-binding
  range `0 < m ≤ m_B` and the frozen-parameter corollary.
- [CurvatureNonattainment](MathProofs/CurvatureNonattainment.lean) — F05, complete:
  whole-space nonattainment in every dimension and strict spreading for `1 ≤ d ≤ 4`.

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

In F01, the whole-space minimizer manuscript (compactness of minimizing sequences modulo
translations) and the orbital-stability manuscript (global `H²` well-posedness and
stability) are not formalized; strict binding and negative energy are. In F04 the leakage
theorems are proved for every classical solution, but local existence and uniqueness of
classical solutions are not yet formalized. Numerical Jacobian rank claims (F09), the
Plancherel extension from Schwartz class to all `L²` states (F10), and F11/F12 remain
outside Lean.

The local-coordinate rank/signature obstruction (F08) **is formalized** for
actual differentiable complex fields on four-coordinate charted spaces,
including explicit matrix contraction and its positivity. A global bundled
coordinate-invariant tensor construction is not certified. The generic local matrix
nullity core of F09 is formalized but is not a certification of the
11-parameter-observable physical model, its computed Jacobian, or its
published numerical rank.

Separate research-grade Lean work lives in [wct-lean](https://github.com/rickyjreyes/wct-lean);
do not conflate its theorem count with this repository.

The Schwartz-space version of F10 is proved end-to-end using Mathlib's
Schwartz Fourier inversion; it is **not** the manuscript's full L² theorem.

## Completion criterion for each of the 14 tweets

The boolean `main_theorem_formalized` (per manuscript, and per family) stays false until the
**entire theorem as stated in its PDF** is a precise exported Lean declaration
with no `sorry`, `admit`, new axioms, unproved assumptions, or finite surrogate
used in place of the stated infinite-dimensional result. Supporting finite
models, algebraic identities, and theorems with stronger extra assumptions
never count as end-to-end certification of the manuscript.
