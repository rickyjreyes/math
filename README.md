# Mathematical manuscripts

Standalone mathematical proofs and research notes by Richard J. Reyes.

## Papers

### Strict subadditivity for a fourth-order cubic–quintic Hamiltonian in two dimensions

[LaTeX source](papers/strict-subadditivity-fourth-order-cubic-quintic/main.tex)

For $u\in H^2(\mathbb R^2;\mathbb C)$, consider

$$
H(u)=\|(\Delta+k^2)u\|_2^2-\frac{\beta}{2}\|u\|_4^4+\frac{\gamma}{3}\|u\|_6^6,
\qquad
I(m)=\inf_{\|u\|_2^2=m}H(u).
$$

The manuscript proves that for $\beta,\gamma,k>0$ and

$$
0<m\le m_B=\frac{3\beta}{\gamma\sqrt{k^4+3\beta^2/(32\gamma)}},
$$

one has $I(m)<I(\mu)+I(m-\mu)$ for every $0<\mu<m$. The proof uses mass-preserving dilation of minimizing sequences and a quantitative energy-per-mass gap; no minimizer is assumed. The mass threshold is sufficient, not asserted optimal.

**Build:** Run \`pdflatex -interaction=nonstopmode main.tex\` twice from the paper directory. The manuscript is self-contained and uses standard LaTeX packages.

**Scope:** This is a two-spatial-dimensional whole-space variational result. It does not itself establish a physical confinement lifetime, uniqueness, spectral stability, or universal all-mass strict binding.

**Related supporting notes:**
- [Strict-binding audit and proof](https://github.com/rickyjreyes/geometry_of_resonance/blob/main/docs/d4_binding/D4_SUBADDITIVITY_PROOF_OR_COUNTEREXAMPLE.md)
- [Energy-per-mass analysis](https://github.com/rickyjreyes/geometry_of_resonance/blob/main/docs/d4_binding/D4_ENERGY_PER_MASS_ANALYSIS.md)

The manuscript is a research draft and has not undergone independent peer review.
