# M3 + E57 — Swift–Hohenberg Fourier-shell symbol and damping

[Compiled PDF](paper.pdf) · [LaTeX source](../../papers/swift-hohenberg-fourier-shell-damping/main.tex)

**Manuscript:** 1 · **Result IDs:** M3, E57

The proof establishes the exact Fourier multiplier `(|ξ|² − k⋆²)²` of the nonnegative self-adjoint shell operator, the linear dissipative semigroup, a uniform exponential damping estimate away from the preferred Fourier shell, strong whole-space L² decay without a uniform exponential gap, energy dissipation, and the periodic-domain and linear-instability counterparts.

**Scope:** The theorem concerns the **linear** flow `∂ₜu = −a(Δ + k⋆²)²u` with `a > 0`. It does not prove nonlinear pattern persistence, localization of whole-space bound states, or derivation from the physical WCT dynamics. It is classical Swift–Hohenberg spectral theory, not a claim of novelty or physical validation.

**Verification:** Analytic proof in LaTeX, Lean-formalized in full ([E57Certification](../../lean/MathProofs/E57Certification.lean) on [SwiftHohenbergL2](../../lean/MathProofs/SwiftHohenbergL2.lean); `ReyesMath.E57Cert.main_theorem`; see the [certification report](../../docs/ANALYTIC_CERTIFICATION_2026-10-30.md) and [lean/formalization.yaml](../../lean/formalization.yaml)). Not independently peer-reviewed. PDFs are compiled by [scripts/build_pdfs.sh](../../scripts/build_pdfs.sh) and [GitHub Actions](../../.github/workflows/pdfs.yml).
