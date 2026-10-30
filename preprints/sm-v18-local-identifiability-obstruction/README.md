# Spectral parameter-identifiability obstruction

[PDF](paper.pdf) · [LaTeX](../../papers/sm-v18-local-identifiability-obstruction/main.tex)

Family: F09. Research manuscript; not independently peer-reviewed. PDFs are compiled reproducibly by the repository's [build script](../../scripts/build_pdfs.sh) and [workflow](../../.github/workflows/pdfs.yml).

The theorem, proposition, and corollary statements are formalized in Lean 4 / Mathlib v4.23.0. [`ReyesMath.V18Forward.f09_completion`](../../lean/MathProofs/V18Identifiability.lean) connects the exact middle determinant, full clipped-map derivative, rank 11, nullity 20, and C¹ local level-set chart. The concrete result uses exact-decimal frozen coefficients, `alpha ∈ [5.172,5.173]`, `epsilon = 5`, and an open ambient parameter domain. See the [completion audit](../../docs/FORMALIZATION_REVIEW_2026-10-27.md) for verification and scope.
