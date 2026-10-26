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

**Build:** Run `pdflatex -interaction=nonstopmode main.tex` twice from the paper directory. The manuscript is self-contained and uses standard LaTeX packages.

**Scope:** This is a two-spatial-dimensional whole-space variational result. It does not itself establish a physical confinement lifetime, uniqueness, spectral stability, or universal all-mass strict binding.

**Related supporting notes:**
- [Strict-binding audit and proof](https://github.com/rickyjreyes/geometry_of_resonance/blob/main/docs/d4_binding/D4_SUBADDITIVITY_PROOF_OR_COUNTEREXAMPLE.md)
- [Energy-per-mass analysis](https://github.com/rickyjreyes/geometry_of_resonance/blob/main/docs/d4_binding/D4_ENERGY_PER_MASS_ANALYSIS.md)

The manuscript is a research draft and has not undergone independent peer review.

### Non-invariance of finite Fourier coordinate subspaces under cubic–quintic evolution

[LaTeX source](papers/finite-fourier-coordinate-subspace-noninvariance/main.tex)

For the unprojected fourth-order cubic–quintic Schrödinger equation on a flat torus, the paper proves that every finite Fourier coordinate subspace with at least two frequencies fails to be invariant. The stronger theorem shows instantaneous out-of-support Fourier generation from every finite multimode trigonometric polynomial. Singleton plane-wave subspaces and the zero subspace are the only invariant finite Fourier coordinate subspaces.

**Build:** Run `pdflatex -interaction=nonstopmode main.tex` twice from the manuscript directory.

**Scope:** This is an exact Fourier-support obstruction, not a failure theorem for controlled Galerkin approximations or general nonlinear invariant manifolds. The argument applies for any real cubic coefficient and a nonzero quintic coefficient.

**Related source:** [Nonlinear model bridge, C1](https://github.com/rickyjreyes/geometry_of_resonance/blob/main/docs/foundational_recovery/NONLINEAR_MODEL_BRIDGE.md).


### Ultraviolet Sobolev ill-posedness for a fourth-order wave equation

[LaTeX source](papers/uv-sobolev-ill-posedness-fourth-order-wave/main.tex)

For the constant-coefficient equation
\[
(\Box-\Box^2-\Delta^2)u=0,\qquad \Box=-\partial_t^2+\Delta,
\]
the manuscript proves that every positive-time four-jet evolution map \(S(t):X_{r+\ell}\to X_r\) is unbounded for all finite \(\ell\ge0\). The exact dispersion roots lead to the growing high-frequency rate
\[
\operatorname{Re}s(k)=\sqrt{\frac{\sqrt2-1}{2}}\,|k|+O(|k|^{-1}).
\]
The proof constructs smooth real solutions on the torus and Fourier packets on the whole space, and extends the argument to the strict-coefficient homogeneous S004 symbol.

**Build:** Run \`pdflatex -interaction=nonstopmode main.tex\` twice from the paper directory. Uses standard LaTeX packages.

**Scope:** This is a linearized homogeneous-sector ill-posedness theorem, not a nonlinear norm-inflation proof or measured physical lifetime.

**Related audit:** [S004 ghost and ultraviolet obstruction](https://github.com/rickyjreyes/geometry_of_resonance/blob/main/docs/foundational/GHOST_AND_CONSTRAINT_ANALYSIS.md).

This manuscript is a research draft and has not undergone independent peer review.
