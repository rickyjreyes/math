# E16 — Linear spectral concentration and dominant-wavenumber convergence

[PDF](paper.pdf) · [LaTeX source](../../papers/e16-linear-spectral-concentration/main.tex) · [Manuscript catalogue](../../CONTENTS.md)

Family: F11. Manuscript 1 — Self-Emergent Fourier Cymatics. October 26, 2026.

**Precisely proved:** For the linear evolution `∂ₜA=(r−aΔ−bΔ²)A` on ℝᵈ with `a,b>0`, the modal Fourier-power identity `P(ξ,t)=P(ξ,0)e^{2λ(ξ)t}` holds. Its growth rate has a unique maximizing radius `k⋆=√(a/(2b))`. If the initial spectrum has positive integral power in *every* neighborhood of the maximizing shell, the normalized spectral power outside any fixed shell neighborhood tends exponentially to zero. If the initial spectral power has a continuous representative in `C₀(ℝᵈ)`, every maximizer's radius converges to `k⋆`. A quantitative `O(t⁻¹ᐟ²)` bound applies if the initial spectrum is positive at a point on the shell.

**Limits:** No spectral-support hypothesis means no unconditional shell attraction; explicit off-shell counterexample included. The theorem is for a linear flow and does not establish nonlinear persistence, localized bound states, physical confinement, directional selection, or Lean verification.

[Build workflow](../../.github/workflows/pdfs.yml) compiles `main.tex` and publishes the PDF on `main`.
