# E58 — Sharp band-selective Green multiplier

[LaTeX source](../../papers/band-selective-green-kernel-bound/main.tex) · [PDF (published by build workflow)](paper.pdf)

**Manuscript 1 · Self-Emergent Fourier Cymatics.** For `r>0` and `a≥0`, the Fourier multiplier `G(k)=1/[r+a(|k|²−k⋆²)²]` satisfies `0<G(k)≤1/r`. The manuscript includes equality cases, the exact continuum `L²` resolvent norm, a discrete-spectrum qualification, and an explicit sign-changing real-space Green kernel.

This is a self-contained analytic draft, not peer-reviewed. Every statement, including the exact continuum resolvent norm, is Lean-formalized here ([E58Certification](../../lean/MathProofs/E58Certification.lean), [E58GreenFunction](../../lean/MathProofs/E58GreenFunction.lean); see the [certification report](../../docs/ANALYTIC_CERTIFICATION_2026-10-30.md) and [lean/formalization.yaml](../../lean/formalization.yaml)). Scalar E58 bounds also have separate Lean counterparts in [wct-lean](https://github.com/rickyjreyes/wct-lean/blob/main/WCTLean/DerivedAudit.lean).

The repository's [PDF workflow](../../.github/workflows/pdfs.yml) compiles `papers/*/main.tex` and publishes `preprints/*/paper.pdf`.
