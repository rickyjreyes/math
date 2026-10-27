# Outstanding end-to-end Lean formalization gates

Repository: `rickyjreyes/math`. Baseline: `main` on 2026-10-26.
This document distinguishes **mathematical manuscript arguments** from
**kernel-checked Lean results on the exact target objects**.

The manuscript proofs are not implicitly imported as axioms into Lean. The
absence of `sorry` or `axiom` does not mean an unformalized theorem is
complete. Check CI against the **exact head commit** before referring to
any newly added Lean declaration as verified.

| Requested theorem | Already formalized on `main` | Remaining acceptance criteria |
|---|---|---|
| 2. Whole-space minimizer | Whole-space H² model; negative energy; strict binding for `0<m≤m_B`. | Prove bounded minimizing sequences modulo translations, vanishing/dichotomy exclusion, nonlinear Brezis–Lieb splitting, strong H² convergence, and attainment **for the actual H² energy**. |
| 3. Orbital stability | Energy algebra, scaling, strict binding. | Formally construct global nonlinear H² flow on ℝ², prove uniqueness, mass/energy conservation, continuity, compactness modulo translations, then Cazenave–Lions set stability; do not assume exact mass of perturbed data. |
| 6. Nonlinear Fourier leakage | Exact Fourier integrals, fifth-harmonic and universal leakage for **any existing classical solution**; single-mode exact solutions. | Prove locally existing and unique classical multimode solutions for the unprojected torus PDE; then remove conditional existence hypothesis in flow-invariance classification. |
| 8. Curvature nonattainment | Positive bounded weight; H² dilations on ℝ^d; nonattainment *criterion*. | Prove weighted Laplacian integrability, exact nonlinear scaling, uniform bound, positivity via absence of nonzero constant L² states, infimum 0, nonattainment, and (in d≤4) strict spreading plus strong dilation continuity. |
| 12. Scalar-metric no-go | Four-chart pointwise actual field derivatives, PSD and rank≤2. | Build global smooth covariant tensor from `mfderiv` on the actual tangent bundle, verify chart-transition law and identification with local formulas. Fiberwise coordinate-free covectors alone are not a complete smooth bundle formalization. |
| 13. 31-parameter identifiability | Any 11-by-31 derivative has kernel dimension≥20. | Encode the **actual frozen v18 piecewise 31-parameter model**, differentiate on an explicitly fixed differentiable active domain, and verify a genuine nonzero 11-by-11 minor (or interval/enclosure certificate) before asserting rank=11. Numerical SVD of finite differences is a diagnostic, not a certificate. |
| 14. Fourier-shell exclusion | Null Euclidean frequency spheres, zero-a.e. Fourier representatives, actual Fourier inversion on Schwartz functions. | Construct the canonical complex-linear unitary Fourier equivalence on L² and prove its agreement with the Schwartz transform; use its injectivity to transfer a.e. spectral zero to the original arbitrary L² state. |

## Additional partial modules introduced in PR #18

- `IntrinsicScalarMetric.lean`: coordinate-free bilinear tensor on arbitrary
  real tangent fibers; rank and nullity from the two differential covectors.
  This does not itself construct the global manifold tensor section.
- `L2FourierShellBridge.lean`: the L² null-shell conclusion for a **supplied
  isometric Fourier equivalence**, with the canonical L² Fourier construction
  explicitly left to do. The pinned Mathlib v4.23.0 does not contain the
  later `Mathlib.Analysis.Fourier.LpSpace` implementation.
- `CurvatureEnergyDilation.lean`: exact H² field dilation of the manuscript's
  **nonlinear** weighted-Laplacian term; no polynomial replacement and no
  unsupported nonattainment claim.

## Acceptance rule

Mark a numbered theorem `main_theorem_formalized: true` in
`formalization.yaml` only once the actual end-to-end target theorem is
proved, imported by `MathProofs.lean`, and CI passes at that commit.
A conditional implication, abstract interface, approximation, or
pointwise algebraic identity is not a substitute.
