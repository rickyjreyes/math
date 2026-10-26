# WCT Mathematical Compendium — Volume I

**Elementary Mathematical Foundations of Wave Confinement Theory**  
**Author:** Richard J. Reyes · **Date:** 2026-10-26

[Compiled PDF](paper.pdf) · [Full LaTeX source](main.tex) · [Compendium catalogue](../README.md) · [Mathematics catalogue](../../CONTENTS.md)

## Scope

One unified reference covering 25 identifiers in the corrected WCT registry, with fully stated hypotheses, mathematical proofs, references and a cross-reference table.

- **§1:** Fourier and Sobolev conventions, corrected regularized curvature operator.
- **§2:** Sharp `H²(Rⁿ) → L∞` threshold and critical-dimension counterexamples.
- **§3:** Shannon entropy, multiplicative pruning, alpha-drop and conditional cardinality bounds.
- **§4:** Laplacian and curvature commutators, logarithmic/Cole–Hopf transformation, phase current.
- **§5:** Quadratic form positivity, second-derivative Euler–Lagrange identity, gradient dissipation, phase-coherence bound and ODE reduction.
- **§6:** Flat product-torus Fourier eigenfunctions, fixed-winding mode and explicit embedded-torus operator error.
- **§7:** Per-registry-ID cross-reference table and bibliography.

The algebraic components are standard or elementary mathematics, not claimed as original results. WCT-specific counting hypotheses, global physical claims and higher-derivative ghost freedom do not follow automatically. In particular, an exponential count `2^((1−η)n)` is **not** subexponential in the standard `2^{o(n)}` sense. The result is not a full Lean formalization.

## Build

From this directory, run:

```bash
pdflatex -halt-on-error -interaction=nonstopmode main.tex
pdflatex -halt-on-error -interaction=nonstopmode main.tex
```

Or from the repository root, run `bash scripts/build_pdfs.sh`. GitHub Actions builds and publishes `paper.pdf` alongside this source.
