# E14 — Band-pass Lyapunov gradient flow

[LaTeX manuscript](../../papers/bandpass-lyapunov-gradient-flow/main.tex) · [PDF](paper.pdf)

**Family:** F11 — Band-pass variational dynamics.

**Claim (analytic, for a declared dissipative model):** On a periodic torus, with (a,b>0), (r\in\mathbb R), (\beta\ge0), and sufficient regularity,
[
\mathcal E[A]=\int[-r|A|^2-a|\nabla A|^2+b|\Delta A|^2+\tfrac\beta2|A|^4]dx
]
generates the complex (L^2)-gradient flow
[
\partial_t A=(r-a\Delta-b\Delta^2)A-\beta|A|^2A
]
and obeys (d\mathcal E/dt=-2\|A_t\|_2^2\le0).
The full proof also derives the centered Swift–Hohenberg representation. When (\beta>0), the periodic-domain energy is bounded below.

**Scope:** These are exact identities for the specified parabolic gradient-flow equation, **not** a derivation of physical damping or nonlinear saturation from the higher-time S004 theory. This manuscript has no Lean kernel formalization and has not undergone independent peer review.

**Original equation registry:** [E13–E14](https://github.com/rickyjreyes/geometry_of_resonance/blob/main/WCT_FULL_EQUATION_LIST_CORRECTED.md). The repository's PDF workflow builds `paper.pdf` from `main.tex` on pushes to main.
