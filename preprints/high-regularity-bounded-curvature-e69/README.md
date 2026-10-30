# E69 — Bounded corrected regularized curvature

[PDF](paper.pdf) · [LaTeX source](../../papers/high-regularity-bounded-curvature-e69/main.tex) · [Lean certification](../../lean/MathProofs/E69Certification.lean) · [Lean mapping](../../docs/E69_LEAN_MANUSCRIPT_MAPPING.md)

For fixed $\varepsilon > 0$, every real $\alpha$ and $s > n/2 + 2$, the corrected modulus-squared curvature operator $\Theta_\varepsilon[\psi] = -(\Delta\psi)R_\varepsilon(\psi)$ maps $H^s(\mathbb R^n;\mathbb C)$ to $L^\infty$, with $\|\Theta_\varepsilon[\psi]\|_\infty \le C_{n,s}M_{\varepsilon,\alpha}\|\psi\|_{H^s}$. The regularized reciprocal is bounded on all of $\mathbb C$, including at field zeros.

The theorem and all four remarks are formalized in Lean 4 (Mathlib v4.23.0), over the Fourier-defined $H^s(\mathbb R^n)$ of every real order and the essential-supremum norm, in every dimension; see the certification module and the mapping. The bound is not uniform as $\varepsilon \downarrow 0$ (Lean also proves this), and no PDE well-posedness or dynamical stability claim is made. The [PDF workflow](../../.github/workflows/pdfs.yml) builds and publishes the PDF from this source.
