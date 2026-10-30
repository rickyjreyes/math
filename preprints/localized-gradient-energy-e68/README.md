# E68 — Localized gradient-energy estimate

[PDF](paper.pdf) · [LaTeX source](../../papers/localized-gradient-energy-e68/main.tex) · [Lean certification](../../lean/MathProofs/E68Certification.lean) · [Lean mapping](../../docs/E68_LEAN_MANUSCRIPT_MAPPING.md)

Manuscript 4 — WCT energy estimate audit. Complete counterexamples and conditional theorems.

- **REFUTED:** The unrestricted $H^1$ localized energy bound in each spatial dimension $n>2$ (fixed singular finite-energy field and smooth concentration family). The all-radius $n=1$ statement also fails.
- **PROVED:** The original bound in dimension $n=2$ with $C=1$.
- **PROVED:** For $n>2$, $\int_{B_R}|\nabla\psi|^2 \le \omega_n^{1-2/n}R^{n-2}\|\nabla\psi\|_{L^n}^2$ when $\nabla\psi\in L^n$.
- **PROVED:** An $H^2$-based version in dimensions 3 and 4, with a scaling obstruction for $n>4$.

Every theorem, proposition, corollary and remark is formalized in Lean 4 (Mathlib v4.23.0), over $H^1$ and $H^2$ defined by weak derivatives; see the certification module and the mapping. No nonlinear WCT existence, stability or physical confinement-lifetime claim is made. The [PDF workflow](../../.github/workflows/pdfs.yml) builds and publishes the PDF from this source.
