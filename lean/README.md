# Lean 4 formalization status

This Mathlib v4.23.0 project contains 18 locally checked declarations
(6 elementary + 9 structural + 1 discrete phase bound + 2 spectral
null-support lemmas) in four imported modules:

- [Elementary](MathProofs/Elementary.lean) — original elementary algebra.
- [Structural](MathProofs/Structural.lean) — an **actual 11 × 31 matrix**
  kernel-dimension bound; n-dimensional scalar-gradient Gram rank ≤ 2
  and positive semidefiniteness; one-dimensional Fourier cutoff arithmetic;
  a finite weighted-variance identity and inequality.
- [PhaseLocking](MathProofs/PhaseLocking.lean) — finite-sum weighted
  Cauchy–Schwarz phase mismatch lower bound.
- [FourierSupport](MathProofs/FourierSupport.lean) — a.e. zero from
  support on a null set, including the 1D two-point Fourier shell.

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
proofs. The higher-derivative constraint analysis (F02), continuous
spectral/phase integral identities (F03, F07), full multidimensional
nonlinear Fourier-mode theorem (F04), curvature nonattainment (F05),
dispersion convexity/minimum (F06), numerical Jacobian rank claims (F09),
and a null-sphere/Plancherel proof in arbitrary dimension (F10) are
likewise not fully formalized.

The algebraic core of the scalar-gradient rank/signature obstruction
(F08) **is formalized** in finite dimensions. The generic local matrix
nullity core of F09 is formalized but is not a certification of the
11-parameter-observable physical model, its computed Jacobian, or its
published numerical rank.

Separate research-grade Lean work lives in [wct-lean](https://github.com/rickyjreyes/wct-lean);
do not conflate its theorem count with this repository.
