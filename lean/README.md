# Lean 4 formalization status

This Mathlib v4.23.0 project contains 51 formal theorem declarations
(38 on the previous verified main commit plus 13 added here) in sixteen imported modules. On any revision,
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

**No full infinite-dimensional PDE result in F01 is kernel-checked**:
strict binding, whole-space minimizer existence, concentration–compactness,
global continuation, and orbital stability remain conventional analytic
proofs. The higher-derivative constraint count and ultraviolet Sobolev evolution (F02), continuous
spectral/phase integral identities (F03, F07), full multidimensional
nonlinear Fourier-mode theorem (F04), curvature nonattainment (F05),
dispersion existence/explicit-minimum theorem under the manuscript assumptions (F06), numerical Jacobian rank claims (F09),
and the Plancherel extension from Schwartz class to all L² states (F10) are
likewise not fully formalized.

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

The Schwartz-space version of F10 is now proved end-to-end using Mathlib's
Schwartz Fourier inversion; it is **not** the manuscript's full L² theorem.

## Completion criterion for each of the 14 tweets

The boolean `families.Fxx.main_theorem_formalized` stays false until the
**entire theorem as stated in its PDF** is a precise exported Lean declaration
with no `sorry`, `admit`, new axioms, unproved assumptions, or finite surrogate
used in place of the stated infinite-dimensional result. Supporting finite
models, algebraic identities, and theorems with stronger extra assumptions
never count as end-to-end certification of the manuscript.
