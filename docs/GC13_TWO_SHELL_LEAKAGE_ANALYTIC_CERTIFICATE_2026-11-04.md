# GC13: exact two-shell leakage counterexample to an unconditional zero-transfer bound

**Date:** November 4, 2026  
**Type:** Analytical exact-target corollary of existing [F04 Lean theorems](../lean/MathProofs/FourierLeakage.lean) and [existence proof](../lean/MathProofs/FourierLeakageWellPosed.lean), **not** a newly encoded GC13 Lean theorem.  
**Original problem:** [GC13](../reyes-problem-repository/problems/03-spectral-scattering/GC13.md).  
**Audit lineage:** [Negative-result source-and-scope audit](NEGATIVE_RESULT_SCOPE_AUDIT_2026-11-02.md).

## Frozen PDE and claim

On `T²=(R/2πZ)²`, consider the unprojected fourth-order cubic–quintic Schrödinger equation used in F04:

```math
i\partial_t u=(\Delta+\kappa^2)^2u
-\beta|u|^2u+\gamma|u|^4u,
\qquad \kappa,\beta,\gamma\in\mathbb R,\ \gamma\ne0.
```

For a finite lattice-frequency shell `S_r={n∈Z²:|n|²=r²}`, choose `A=S_1` and `B=S_5`. These are finite, disjoint shells.

GC13 asks whether, for prescribed two disjoint finite shells, an upper bound of the type

```math
\sup_{t\in[0,T]}\sum_{n\in B}|\widehat u_n(t)|^2
\ \le\ F\!\left(T,\|u_0\|_{H^2},
\sum_{n\in B}|\widehat u_n(0)|^2\right)
\quad\text{with }F(T,M,0)=0
```

can hold universally.

## Theorem (refutation for the specified shells when γ ≠ 0)

For any `κ,β∈R`, `γ∈R\{0}`, and `T>0`, there is a smooth classical solution on some positive time interval with initial datum

```math
u_0(x_1,x_2)=\cos x_1
=\tfrac12 e^{ix_1}+\tfrac12 e^{-ix_1}
```

for which

```math
\sum_{n\in B}|\widehat u_n(0)|^2=0,
\qquad
\left.\frac{d}{dt}\widehat u_{(5,0)}(t)\right|_{t=0}
=-\frac{i\gamma}{32}\ne0.
```

Hence there is `0<t<min(T,τ)` with `Σ_{n∈B}|û_n(t)|²>0`, where `τ>0` is a classical existence time. The asserted universal estimate with `F(T,M,0)=0` fails at `M=||cos x₁||_{H²}`.

## Proof and formal-source correspondence

The initial Fourier support is `{(1,0),(-1,0)}⊂A`, so the entire shell `B=S_5` has zero initial energy. The fourth-order linear multiplier acts diagonally on Fourier modes and cannot generate `(5,0)` at first order. The cubic monomial `|u_0|²u_0=cos³x₁` has harmonics of magnitude at most three. The quintic monomial `|u_0|⁴u_0=cos⁵x₁` satisfies

```math
\cos^5 x_1
=\frac{10\cos x_1+5\cos3x_1+\cos5x_1}{16},
\qquad
\widehat{\cos^5 x_1}_{(5,0)}=\frac1{32}.
```

Taking the `(5,0)` coefficient of the PDE at `t=0` therefore yields
`i (d/dt) û_(5,0)(0)=γ/32`, or `(d/dt) û_(5,0)(0)=-iγ/32`. Since the derivative is nonzero and `û_(5,0)(0)=0`, this coefficient is nonzero for all sufficiently small nonzero times. Its squared absolute value is one term in the nonnegative `B` shell energy.

Local classical existence for smooth trigonometric data in arbitrary dimension is proved by `ReyesMath.FourierLeakage.exists_classical_solution` in `FourierLeakageWellPosed.lean`. The existence-backed `universal_leakage_solution` establishes nonzero generated coefficients for finite supports with at least two frequencies in arbitrary `d`; the `fifth_harmonic_solution` theorem identifies `-iγ/32` explicitly in one dimension. The calculation above extends that precise fifth-harmonic coefficient to the `x₂`-independent datum in `d=2`. The exact two-shell energy-bound corollary is **analytical**, not itself a named Lean declaration.

## Classification and exclusions

- **VALID_AND_APPLICABLE:** unconditional zero-transfer bounds with `F(T,M,0)=0` fail for this original GC13 torus PDE, the specified disjoint finite shells `S₁,S₅`, and `γ≠0`. The quantified `T>0` is arbitrary because the leakage is instantaneous.
- **Not proved:** a universal negative claim for *all* disjoint shell choices, a fixed-mass lower bound independent of coefficients, the case `γ=0`, or estimates allowing nonzero source terms, frequency-dependent forcing, flux budgets, or other hypotheses.
- **Not claimed:** a new Lean theorem for the exact GC13 shell sum or a theorem about unrelated WCT field actions.
- **Registry policy:** GC13 retains its original `candidate` status pending classification and formal review; no original problem text or machine record is changed.

This is an exact target counterexample to one strong interpretation of GC13, not a complete classification of interband energy transfer.
