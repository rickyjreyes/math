# E18: Exact Lyapunov descent for corrected WCT curvature energy

[PDF](paper.pdf) · [LaTeX source](../../papers/wct-e18-exact-gradient-lyapunov/main.tex)

This proof note establishes nonnegativity, the full complex variational derivative (including differentiation of the nonlinear curvature weight), and exact energy dissipation **for sufficiently regular solutions of the stipulated negative-gradient flow**. Periodic boundary conditions are used; compatible boundary conditions permit extensions.

It does **not** establish local/global existence for arbitrary data, long-time convergence, free-space localization, or that the separate physical-time WCT equations generate this flow. Not peer-reviewed.

Propositions 1–3, Theorem E18 and both corollaries are Lean-formalized in this repository on the Fourier space `H²(𝕋^d)`, `d ≤ 3`, with the manuscript's hypotheses ([E18Certification](../../lean/MathProofs/E18Certification.lean), [mapping](../../docs/E18_LEAN_MANUSCRIPT_MAPPING.md)). The analytic chain rule is derived there, from the proved Fréchet derivative and `L²` representative. The nonperiodic-domain remark is not formalized. The separate [wct-lean E18 algebraic theorem](https://github.com/rickyjreyes/wct-lean/blob/main/WCTLean/DerivedAudit.lean) assumes the negative-square rate identity rather than deriving the analytic chain rule.

Build with [scripts/build_pdfs.sh](../../scripts/build_pdfs.sh); the [PDF workflow](../../.github/workflows/pdfs.yml) publishes compiled PDFs after a successful run.
