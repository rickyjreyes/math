# Six flagship GC research ledger — 2026-11-24

Status: **analytical progress; candidate Lean code pending CI and correspondence review.**
The original six GC statements remain unchanged. This is not a novelty claim or an accepted resolution record. Related existing work: F01 strict binding, whole-space minimizers and orbital stability; F09 V18 local level sets; M6B (different curvature operator); open draft PR #97 (sufficient parameter region and periodic Fourier-block instability). This branch is independent of #97.

## 1. GC16: all-mass strict binding for k = 0

Let beta,gamma>0, m>0, and u in the repository's exact H²(R²; C).
Write M=||u||₂², D=||Delta u||₂², Q=||u||₄⁴, S=||u||₆⁶,
E=D-beta Q/2+gamma S/3, and I(m)=inf E at M=m.

**Theorem.** For every 0<a<b, I(b)/b<I(a)/a. Consequently
I(m)<I(a)+I(m-a) for every 0<a<m, without a mass ceiling.

**Proof.** For t=b/a>1, v(x)=u(x/sqrt(t)) belongs to H², and a change
of variables yields M(v)=tM(u), D(v)=D(u)/t, Q(v)=tQ(u), S(v)=tS(u).
Hence E(v)=tE(u)-(t-1/t)D(u).

The existing NegativeEnergy theorem gives I(a)<0. Set J=I(a). For a
mass-a near minimizer with E(u)<J/2, positivity of D and S implies
-J<beta Q. The existing Fourier inequality ||u||∞²≤sqrt(MD)/4 implies
Q≤a sqrt(aD)/4. Thus D≥c=16 J²/(beta² a³)>0 uniformly on these near
minimizers. Choose a minimizing sequence eventually obeying E<J/2.
For its stretched fields, I(b)≤tE(u)-(t-1/t)c. Passing to the infimum,
I(b)≤tI(a)-(t-1/t)c<tI(a). Divide by b=ta.
Apply the resulting strict inequality to a and m-a and add, after
multiplying by the respective masses. QED.

No assumption of minimizer attainment is used. This improves the
previous sufficient mass range only in the zero-shell subfamily.
For k≠0 the same stretch gives E(v)-tE(u)=-(t-1/t)D+2k²(t-1)K,
with K=||grad u||₂²; the latter term has the wrong sign. Do not
extrapolate the proof to that case.

Candidate Lean: MathProofs.GC16ZeroShell.exists_stretch,
kinetic_lower, energy_per_mass_strict, strict_binding_all_mass.
Exact declarations use the existing Sobolev.H2 energy and Imin.

## 2. GC06: attainment and compactness for k = 0 at every positive mass

The existing concentration-compactness argument in WholeSpaceMinimizers
uses the mass threshold only to obtain strict binding. Expose this
hypothesis directly without changing the existing sufficient-range API.
Negativity, boundedness, nonvanishing, weak compactness, energy splitting
and exclusion of dichotomy yield a strong H² limit modulo translations
for a subsequence of every minimizing sequence at every m>0, k=0.
In particular the infimum is attained.

Candidate Lean: GC16ZeroShell.compactness_all_mass and
exists_minimizer_all_mass; generic WholeSpace.*_of_binding lemmas.
Remaining: nonzero k outside the existing binding range, sharp parameter
classification including any other permitted signs, and loss-of-compactness
classification in nonbinding regimes.

## 3. GC01: stability for k = 0 at every positive mass

Refactor the existing conservation/compactness stability argument so that
strict binding is its explicit hypothesis; retain the former public theorem
as a corollary. The zero-shell all-mass theorem implies full-set orbital
stability for the exact F01 flow, including perturbations of nearby masses.
This is not individual-orbit stability, excited-state classification,
or a spectral instability theorem. Candidate Lean:
GC16ZeroShell.orbital_stability_all_mass; generic OrbitalStability.*_of_binding.
Next: identify the isolated minimizing-orbit and nondegenerate Hessian
conditions; separate them from general excited-state stability.

## 4. GC08: classification on nonvanishing jets (analytic)

This uses the actual phase-current-divergence operator in GC08, not
the M6B Laplacian quotient.

On a local region where u≠0 write u=r exp(i theta), r>0, and define
p=grad log r, q=grad theta, A=Hess log r, B=Hess theta.
Every such second-order polar jet is realized locally by smooth fields:
choose log r and theta as quadratic polynomials with the prescribed jets.
Translation and constant-phase invariance remove x and theta. Proper
rotations act on p,q as vectors and A,B as symmetric matrices by
orthogonal conjugation (equivalently by the pullback representation).

With w(r)=r²/(epsilon+r²), the exact GC08 curvature is
K=w(r) tr(B)+[2 epsilon r²/(epsilon+r²)²] p dot q.

**Classification theorem.** Among smooth real functions of these polar
2-jets, invariant under SO(d), every admissible closure on nonvanishing
fields is exactly
C=K+p dot V(r,p,q,A,B)+A:U(r,p,q,A,B)+B:W(r,p,q,A,B),
where V is any smooth equivariant vector function and U,W are any smooth
equivariant symmetric-matrix functions. Colon denotes Frobenius pairing.
There is no uniqueness claim for the coefficient representation.

Proof: any closure difference f is smooth invariant and vanishes when
p=A=B=0 for arbitrary r>0 and q, precisely the plane-wave jets.
Apply the fundamental theorem of calculus to
t ↦ f(r,tp,q,tA,tB) on [0,1]. Integrating the partial derivatives
in p,A,B gives V,U,W, respectively; invariant f and orthogonal group
actions imply these gradients transform equivariantly, and integration
preserves equivariance and smoothness. Conversely any such expression is
invariant and vanishes on every plane wave. QED.

This explicitly characterizes the freedom on the open nonvanishing jet
domain. To characterize operators smooth also at u=0, require that the
resulting function of the original complex jet (u,grad u,Hess u) admit
a smooth extension there. If it exists, it is unique by density, and
invariance extends by continuity. A useful stronger result would classify
that extension condition intrinsically on raw jets; no such classification
or exact Lean field correspondence is asserted here. Additional uniqueness
axioms must exclude this freedom. Next: formalize the polar identity,
equivariance and Hadamard integral, then address the zero jets.

## 5. GC26: dimension obstruction and full-rank counterexample (analytic)

For the existing V18 observation model with 11 real outputs and 31
parameters, no point of an open ambient parameter domain has a neighborhood
on which the observation map is injective, provided the map is continuous.
Indeed, were F injective on an open U⊂R³¹, compose with the coordinate
inclusion R¹¹→R³¹ and apply invariance of domain. The image would be open
in R³¹ but lie in a proper linear subspace, a contradiction. This holds
even across continuous clipping boundaries; it does not imply that the
fiber through every point has positive dimension or is nonisolated.
The existing F09 theorem proves that stronger statement at its frozen point.

For the generic question with at least 31 observations, full Jacobian rank
does not imply global injectivity even on a connected open domain:
take U=(R² minus {0})×R²⁹ and
F(x,y,z)=(x²-y²,2xy,z).
The derivative determinant is 4(x²+y²)>0 everywhere, yet F(x,y,z)=
F(-x,-y,z). Extra output coordinates can be zero. Full column rank is a
sufficient local injectivity condition by the inverse function theorem
on an invertible coordinate minor, but is not necessary at singular points
(as x↦x³ illustrates).

Remaining: distinguish local injectivity on a neighborhood from isolation
of the fiber through a point; specify any closed-box/relative boundary
domain and variable-N observation map before claiming a full classification.
The dimension obstruction uses a classical theorem, not a novelty claim.
Next: formalize the dimension obstruction (Mathlib invariance of domain or
a constant-rank argument on analytic open strata) and exact polynomial witness.

## 6. GC03: general coercivity versus supercritical formulation (analytic)

For the actual GC03 pure dispersion equation with integer p≥1,
1<r<s, beta,gamma>0, define the conserved energy with the standard coefficients:
E=||(-Delta)^(p/2)u||₂²/2 - beta||u||_(r+1)^(r+1)/(r+1)
+gamma||u||_(s+1)^(s+1)/(s+1).

Set a=beta/(r+1), b=gamma/[2(s+1)], R=(a/b)^(1/(s-r)).
For every x≥0, a x^(r-1)-b x^(s-1)≤a R^(r-1)=C:
if x≤R, bound the positive term; if x≥R the difference is nonpositive.
Multiply by x² and integrate. Hence
E≥||(-Delta)^(p/2)u||₂²/2+b||u||_(s+1)^(s+1)-C||u||₂².
Every sufficiently regular solution conserving finite energy and mass
therefore has bounded H^p norm on its lifespan. For any local theory with
an H^p blow-up alternative and these conservation laws this yields global
continuation. It is not a proof of that local theory in all dimensions.

When d>2p and s+1>2d/(d-2p), choose d/(s+1)≤lambda<d/2-p.
A smooth cutoff equal to one near zero times |x|^(-lambda) lies in H^p
(local derivatives through order p are square integrable) but not
L^(s+1). Thus H^p data need not have finite energy in the supercritical
case. This is an obstruction to the requested blanket finite-energy
formulation, not a finite-time blow-up construction. The original
dichotomy must distinguish local ill-posedness or lack of finite energy
from actual finite-time blow-up.

Next: freeze solution notion and prove the Sobolev-subcritical local
theory and conservation/continuation in the permitted regularity range;
critical/supercritical regimes remain open in this ledger.

## Verification and next steps

- Candidate Lean code for GC16/GC06/GC01 is included in the maintained
  MathProofs import root and transitive axiom audit. No local Lean toolchain
  or network clone was available in the originating environment.
- CI must run lake build, audit all four new roots, and verify preserved
  F01 API. No kernel-check success is claimed until an actual passing run.
- GC08/GC26/GC03 results above are analytical only, not verified Lean.
- No issue or GC-level status is closed or promoted. Review exact scope,
  run CI, independently check prior art, and then update accepted registry
  evidence through the repository workflow.
