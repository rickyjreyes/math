# E59 — Dominant-annulus Fourier projection

[Compiled PDF](paper.pdf) · [LaTeX source](../../papers/e59-dominant-annulus-projection/main.tex) · [Manuscript catalogue](../../CONTENTS.md)

**Family:** F11 — Fourier-band dynamics and concentration.  
**Source identifier:** E59 (Manuscript 1 — Self-Emergent Fourier Cymatics).

## Result

On the flat torus, for a **fixed sharp annulus** Α of allowed Fourier modes, define the Fourier multiplier (P_Α) by the indicator (1_Α). The manuscript proves

- **Idempotence:** (P_Α^2=P_Α).
- **Self-adjointness:** (P_Α^*=P_Α).
- **Contraction:** (‖P_Αu‖_2≤‖u‖_2).
- **Orthogonal decomposition and best approximation** of (u) by its selected Fourier-band component.
- **Discrete Fourier-transform version** for a fixed 0/1 mask, plus the associated retained-energy fraction.

These are exact Hilbert-space/Fourier identities for a *fixed mask*. The annulus must be defined symmetrically as ||ξ|−k⋆|≤Δk if the intended selection is a shell.

## Scope

A smooth tapered Fourier multiplier is generally **not** an idempotent projection. Re-selecting an adaptive "dominant band" between applications is a different operation. Idempotence does **not** establish invariance under an unprojected nonlinear PDE, nonzero bound states, localization, confinement, or orbital stability.

**Verification:** Analytical proof; the full theorem is not claimed to be Lean kernel-checked. The [PDF workflow](../../.github/workflows/pdfs.yml) recompiles the LaTeX source and publishes `paper.pdf`.
