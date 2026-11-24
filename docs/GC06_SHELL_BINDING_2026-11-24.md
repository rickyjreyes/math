# GC06: shell binding, unbounded confinement masses, and the exact compactness obstruction

**Date:** 2026-11-24. **Status:** analytical results and candidate Lean code; CI and independent correspondence review required. The full GC06 classification is not resolved. Stacked on draft PR #99; PR #97 is independently relevant. No claim of literature-wide priority.

## 1. Frozen model and earlier work

Throughout Sections 2–7, k >= 0, beta,gamma > 0, m > 0, and u belongs to H²(R²; C). Write M=||u||₂², D=||Delta u||₂², K=||grad u||₂², T=||(Delta+k²)u||₂², Q=||u||₄⁴, S=||u||₆⁶. Then E=T-beta Q/2+gamma S/3, I(m)=inf E at M=m. Set I(0)=0. All compactness is subsequential strong H² compactness modulo translations.

The original F01 papers prove negative constrained energy for every positive mass and strict binding/attainment/compactness for m<=m_B. PR #97 encodes the polynomial sufficient region and zero-selector defocusing exclusions. PR #99 proposes all-mass strict binding, compactness and attainment at k=0. Its stretching proof does not extend automatically to k>0. The following analytical arguments use the original exact energy, not an alternate PDE.

Write C=3 beta²/(16 gamma), c=C/2. Square completion gives E >= T-C M. Coercivity, ordinary subadditivity (smooth compact-support approximation, exact mass correction and disjoint translations), negativity, mass continuity and the energy/mass splitting identities are as in the F01 manuscripts. For continuity at positive masses, near-minimizers for masses in a compact positive interval are uniformly H² bounded by coercivity and a fixed trial rescaled in amplitude; adjusting amplitude by a factor tending to one changes E by o(1), proving both semicontinuity inequalities.

## 2. Strict improvement of the stationary bound for every k

Set

$$
\sigma_R=\frac{k^2+\sqrt{k^4+2c}}{2},
\qquad m_R=\frac{3\beta}{\gamma\sigma_R}.
$$

**Theorem A.** For every 0<m<=m_R, I(m)<I(a)+I(m-a) for every 0<a<m, I(m) is attained, and every minimizing sequence is precompact subsequentially modulo translations.

Proof. For a mass-a dilation-stationary field, the exact identity is D-k²K-beta Q/4+gamma S/3=0. Square completion gives beta Q/2-2 gamma S/3<=c a. Hence 2D-2k²K<=c a. Retain K<=sqrt(aD) rather than discarding T from the old square identity. With x=sqrt(D/a), 2x²-2k²x<=c, so x<=sigma_R. The existing sharp Fourier inequality gives

$$
S/Q\le\|u\|_\infty^2\le\sqrt{aD}/4\le\sigma_R a/4.
$$

This applies to the dilation-adjusted minimizing sequence at any a>0. If b>a and a+b<2m_R, let t=b/a and h=1-(a+b)/(2m_R)>0. The exact amplitude comparison is

$$
E(\sqrt t\,u)/t-E(u)=(t-1)[-\beta Q/2+\gamma(t+1)S/3]
\le-(t-1)\beta h Q/2\le(t-1)h E(u).
$$

Passing to the infimum yields e(b)<= [1+(t-1)h]e(a)<e(a), where e=I/m, by I(a)<0. For b=m<=m_R this holds for each smaller positive mass, including a=m-a when appropriate. Multiply by the two split masses and add. The original concentration-compactness proof now gives attainment/compactness using this strict binding, as exposed in PR #99.

Strict improvement: sigma_R>k², 2 sigma_R²-2k² sigma_R=c, and sigma_R²+(sigma_R-k²)²=k⁴+c. Therefore sigma_R<sqrt(k⁴+c), and m_R>m_B for every beta,gamma>0. This is not a sharp cutoff; at k=0 use PR #99's all-mass theorem instead.

Candidate exact Lean roots: ReyesMath.GC06ShellBinding.sqrt_MD_refined, mB_lt_mR, gap_refined, strict_binding_refined, compactness_refined, exists_minimizer_refined.

## 3. A growing nonzero-selector region from constant-amplitude stretching

**Theorem B.** Choose a0>0, eta>0 with a0<=m_R, a0<=m, I_(0,beta,gamma)(a0)<-2 eta a0, k⁴<=eta and 2 k² m<4 eta/beta. Then all-split strict binding, attainment and compactness hold at m.

Proof. For t=b/a>0 and v(x)=u(x/sqrt(t)), exact mass and energy identities are

$$
M(v)=tM(u),\quad E_k(v)=tE_k(u)-(t-1/t)D(u)+2k^2(t-1)K(u).
$$

Choose a seed U with M(U)=a0 and E_0(U)<-2 eta a0, without assuming attainment. For a>=a0 use t=a/a0>=1. Since E_k(U)=E_0(U)-2k²K(U)+k⁴a0,

$$
E_k(v)=t(E_0(U)+k^4a_0)-(t-1/t)D(U)-2k^2K(U)<-\eta a.
$$

Thus I_k(a)<=-eta a. For any mass-a near-minimizer with E_k(u)<-eta a/2, positivity of T,S implies beta Q>eta a. The Fourier bound Q<=a sqrt(aD)/4 gives x=sqrt(aD)>=L=4 eta/beta. Also K<=x. If 2k²a<L, then

$$
a(D-2k^2K)\ge x^2-2k^2ax\ge L(L-2k^2a)>0.
$$

The second inequality follows by factoring the difference as (x-L)(x+L-2k²a). For b>a, t=b/a>1, (t-1/t)>=(t-1). Consequently

$$
E_k(v)\le tE_k(u)-(t-1)L(L-2k^2a)/a.
$$

This uniform strictly positive gap survives the minimizing-sequence limit, proving e(b)<e(a) whenever a>=a0 and a<=m with b>a. If 0<a<a0, Theorem A gives e(a0)<e(a); combine with the preceding comparison at b=m (or use b=a0 if m=a0). Therefore e(m)<e(a) for every 0<a<m; strict binding, attainment and compactness follow.

The seed inequality need not depend on unknown numerical minimizers. A normalized isotropic Gaussian at k=0, optimized in its width, gives

$$
I_0(a_0)/a_0\le -\frac{\beta^2a_0^2}{64\pi^2(2+\gamma a_0^2/(9\pi^2))}.
$$

For example choose eta=beta² a0²/[256 pi²(2+gamma a0²/(9 pi²))]. This satisfies the strict seed inequality. For fixed beta,gamma choose a0 strictly below m_R(0), so a0<=m_R(k) for sufficiently small k by continuity. For every prescribed finite target mass m>=a0 the conditions hold for sufficiently small k>0. For m<a0 use Theorem A. At a fixed small k the new upper mass scale is 2 eta/(beta k²) with a strict upper endpoint, and it diverges as k tends to zero. This is not a proof of all masses at one fixed k>0.

Candidate exact Lean roots: ReyesMath.GC06NearZeroShell.exists_stretch, seed_upper, kinetic_gap, energy_per_mass_strict, comparison_near_zero, strict_binding_near_zero, compactness_near_zero, exists_minimizer_near_zero. The Gaussian specialization and continuity corollary remain analytical.

## 4. Shell concentration is excluded at every positive mass

**Theorem C (analytical).** For every fixed positive mass, I(m)>-Cm, I(m)<0, and

$$
I(m)\ge-\beta^2 m^3/64.
$$

Every minimizing sequence has T bounded uniformly away from zero eventually, and no minimizing sequence vanishes locally or concentrates all of its Fourier mass into a shrinking shell with T tending to zero.

Proof. Weighted Fourier inversion and Plancherel give for h>0

$$
\|u\|_\infty^2\le (T+hM)\frac{1}{(2\pi)^2}
\int_{\mathbb R^2}\frac{d\xi}{(|\xi|^2-k^2)^2+h}
=\frac{T+hM}{4\pi\sqrt h}
\left(\frac\pi2+\arctan(k^2/\sqrt h)\right).
$$

The polar integral follows by s=|xi|²-k². It is at most (T+hM)/(4 sqrt(h)). For M>0, T>0 since the exact shell has Lebesgue measure zero and the Fourier transform is L². Set h=T/M:

$$
\|u\|_\infty^2\le\tfrac12\sqrt{MT},\quad
Q\le\tfrac12 M\sqrt{MT}.
$$

Thus E>=T-beta m sqrt(mT)/4>=-beta²m³/64 by completing the square in sqrt(T). At a fixed mass, T→0 implies Q,S→0 and E→0; impossible for a minimizing sequence since I(m)<0. Quantitatively if J=I(m)<0 and E(u)<J/2, then beta Q>-J, so T>=4J²/(beta²m³). If I(m)=-Cm, the exact square completion would force T→0 on every minimizing sequence, contradiction. Finally local vanishing implies Q→0 by the local Sobolev argument of F01 and therefore contradicts I(m)<0. This excludes zero-cost shell escape, not arbitrary anisotropic shape changes with positive kinetic energy.

## 5. Arbitrarily large confinement masses at every fixed selector

**Theorem D (analytical).** For every fixed k>=0, beta,gamma>0, there are arbitrarily large masses m at which strict binding holds at every split and the infimum is attained with full minimizing-sequence compactness modulo translations. In particular no finite upper mass cutoff can exclude all larger masses.

Proof. Let r*=3 beta/(4 gamma), C=3 beta²/(16 gamma). Choose a smooth monotone cutoff chi(s) between zero and one, equal to one for s<=0 and zero for s>=1, and

$$
u_R(x)=\sqrt{r_*}\,\chi(|x|-R)e^{ikx_1},\qquad R\ge1.
$$

Its mass is continuous, strictly increasing and unbounded in R, with M(u_R)~pi r* R². The shifted kinetic term is supported in the unit-width annulus, because the interior carrier is precisely on shell. Its squared integral is O(R) (the derivatives of the cutoff are uniformly bounded there). The nonnegative potential excess from square completion vanishes inside and outside the annulus, and is O(R) too. Thus E(u_R)+C M(u_R)=O(R), and the exact mass can be prescribed for all sufficiently large m by varying R. Hence

$$
-C< e(m)=I(m)/m\le -C+O(m^{-1/2}),
\qquad \lim_{m\to\infty}e(m)=-C .
$$

By Theorem C and I(m)<0, e(m)→0 as m↓0. Continuity at each m>0 was justified in Section 1. For each ell in (-C,0), define m_ell=min{m>0:e(m)<=ell}. The set is nonempty by the large-mass limit, bounded away from zero by the small-mass limit, and closed at its positive infimum. Continuity gives e(m_ell)=ell, and e(a)>ell for every 0<a<m_ell. Therefore I(m_ell)<I(a)+I(m_ell-a) at every interior split. The F01 compactness argument applies. As ell decreases to -C, m_ell tends to infinity: any bounded subsequence would have a positive finite accumulation point where e=-C, contradicting Theorem C. QED.

This does not claim every sufficiently large mass is a first-crossing mass. It gives unbounded attained masses at each nonzero k, not a complete fixed-k classification.

## 6. Necessary and sufficient compactness criterion; finite minimizing clusters

**Theorem E (analytical).** In the frozen focusing/defocusing domain, at each fixed m>0 the following are equivalent:

1. Every mass-m minimizing sequence admits a subsequence strongly convergent in H² modulo translations.
2. Every interior split satisfies I(m)<I(a)+I(m-a).

If compactness fails, it is precisely through finite minimizing clusters, not vanishing. More explicitly, after a subsequence any minimizing sequence has a finite decomposition

$$
u_n=\sum_{j=1}^N U_j(\cdot-y_{j,n})+r_n,\quad
|y_{i,n}-y_{j,n}|\to\infty,\quad \|r_n\|_{H^2}\to0,
$$

where m_j=M(U_j)>0, E(U_j)=I(m_j), sum m_j=m, and sum I(m_j)=I(m). One can take N<=floor(2m/m_R)+1; in any such decomposition with N>=2 every pair satisfies I(m_i+m_j)=I(m_i)+I(m_j), so at most one cluster can have mass <=m_R/2. A nonattained infimum necessarily has N>=2 in every such decomposition. Conversely equality for an interior split yields a noncompact minimizing sequence. Attainment alone may coexist with noncompact sequences; no claim is made that equality by itself rules out an attained minimizer at m.

Proof. Sufficiency is exactly the F01 concentration-compactness argument with Theorem A's or any all-split strict-binding hypothesis. Necessity: ordinary subadditivity and failure of strictness give equality for some split a,b>0. Approximate minimizing sequences at masses a and b by C_c^infty fields, correct their masses exactly, and translate their compact supports to have distance tending to infinity. Their sum has exact total mass and additive energy (all derivative and nonlinear terms local), so is minimizing. For every fixed R, eventually every radius-R ball meets at most one support and therefore contains at most max(a,b)<m mass. Strong L² convergence after translation is impossible.

For finite decomposition, extract a nonzero weak H² profile after translations using coercivity, negativity and local nonvanishing. The Hilbert splitting for M,T and Brezis--Lieb splitting for Q,S are the F01 identities. If the extracted mass is a<m, normalize the remainder to exact limiting mass b=m-a. The normalization tends to one and changes energy by o(1). The bounds E(U)>=I(a), liminf E(remainder)>=I(b), and I(m)<=I(a)+I(b) force equality in each, hence the extracted profile is an attained minimizer and the mass-corrected remainder a minimizing sequence. If a=m, the residual mass and energy tend to zero, Q,S tend to zero by bounded H² and vanishing L² mass, and T→0, hence the residual tends to zero in H². Iterate on any positive-mass remainder, using the raw remainders for the decomposition (normalization is o(1) in bounded H²). A later nonzero profile must have centers diverging from all earlier centers because the residual converges weakly to zero locally at those centers; subtracting a separated translated profile preserves that property. Each finite stage has equality of the sum of cluster infima and residual infimum with I(m). Ordinary subadditivity then forces equality for every pair of already extracted cluster masses, since replacing any pair by their merged mass could only lower the right side. Theorem A excludes any pair whose sum is <=m_R. Hence at most one extracted cluster has mass <=m_R/2 and the extraction must terminate after finitely many stages; otherwise the sum of masses exceeds m. The zero-mass residual argument gives the stated strong H² remainder. This proves the decomposition and bound.

Remaining precise obligation: for each fixed k>0, either prove strict energetic merging for every pair of attained clusters satisfying the mass-split optimality conditions (which would resolve all-mass compactness and attainment), or exhibit a genuine binding equality and investigate whether the combined mass also admits a minimizer. The equality must concern I, not just a finite-separation test profile or the failure of a sufficient inequality.

## 7. A concrete obstruction to the elementary all-mass scaling route

For every k>0, beta,gamma>0 there are negative-energy, dilation-stationary fields W for which both constant-amplitude spatial stretching and amplitude amplification strictly increase energy per mass at every t>1. Thus negativity plus virial stationarity alone cannot establish the desired all-mass monotonicity.

Choose a real smooth compactly supported 0<=f<=1 approximating the indicator of a disk sufficiently well that integral f^6/integral f^4>3/4, and A²=beta/gamma. Let u_R=A f(x/R)e^{ikx_1}. Then M,Q,S scale exactly as R²; Q,S satisfy gamma S/3>beta Q/4, while the nonlinear energy is at most -beta Q/6 because S<=A²Q. T(u_R)=O(1) and E(u_R)<0 for large R. By elementary derivative expansion K/M→k², D/M→k⁴. Optimize the original mass-preserving dilation with z_R=lambda_R²=(k²K+beta Q/4)/(D+gamma S/3). Its limit z∞ is strictly between zero and one since gamma S/3>beta Q/4 at every R. The adjusted W_R has E(W_R)<=E(u_R)<0, exact virial stationarity, and

$$
\frac{D(W_R)-k^2K(W_R)}{M(u_R)}
\longrightarrow z_\infty(z_\infty-1)k^4<0 .
$$

By the virial identity S(W_R)/Q(W_R)>3 beta/(4 gamma) eventually. For t>1 the amplitude defect per t is (t-1)[-beta Q/2+gamma(t+1)S/3]>0. The constant-amplitude stretch defect is (t-1)[2k²K-(1+1/t)D]>0. These are counterexamples to the proposed universal trial-field scaling inequalities, even under negative energy and stationarity. They are not certified minimizing fields and are not nonattainment counterexamples for GC06.

The unresolved step is a genuine variational estimate on near-minimizers or on mutually separated attained profiles, not the algebra of these two elementary scalings. A possible next route is an interaction calculation after mass-normalized superposition of two attained profiles. If an equality split is attained on both sides, variations transferring mass imply a common Lagrange multiplier. For that multiplier lambda, expand E-lambda M about the sum of far-separated profiles; the first-order cross term is proportional to the real part of the pairing of (A²-lambda)U with the translated V, while overlap terms are at least quadratic in the small field on either core. The sign can be selected by a relative constant phase if a suitable dominant nonzero cross pairing is proved. Establishing uniform decay and non-cancellation of that pairing, especially at a shell-threshold multiplier, remains a proof obligation. No bifurcation, tail interaction, or shell rearrangement theorem is assumed here.

## 8. Defocusing extension outside the frozen domain (analytical)

For beta<=0, gamma>=0 and any k>=0, the Hamiltonian is nonnegative. For a real unit-L² smooth compactly supported f, the mass-m carrier trial sqrt(m)/R f(x/R)e^{ikx_1} has T=m R^-4 D(f)+4mk² R^-2 ||partial_1 f||₂², Q=m² R^-2 Q(f), S=m³ R^-4 S(f). Thus I(m)=0. For every positive-mass u, T>0 by the null-measure shell argument, hence no minimizer exists, including the linear endpoint beta=gamma=0. Every minimizing sequence has T→0 and hence sup norm→0 by the shell bound; local mass vanishes at every fixed radius. PR #97 covers narrower formal exclusions; the all-k extension here is analytical only. No statement about gamma<0 is made.

## 9. Scope, literature and Lean correspondence

The exact parameter normalization u(x)=sqrt(beta/gamma) v(x/L), L=(gamma/beta²)^(1/4), maps the original energy to beta²/gamma^(3/2) times the unit-coupling functional with selector k L, and mass to gamma^(-1/2) times the normalized mass. Thus only (k L, sqrt(gamma)m) need be classified; this is a change of variables, not a classification.

Prior-work leads: P.-L. Lions, concentration compactness (1984), and Brézis–Lieb (1983) underlie Section 6. Fernández, Jeanjean, Mandel, Mariş (JDE 330, 2022, DOI 10.1016/j.jde.2022.04.037) study a mixed-dispersion single-power variational problem and nonhomogeneous GN estimates. Ma, Chang, Feng (EJDE 2024 no. 29, DOI 10.58997/ejde.2024.29) study combined-power mixed-dispersion normalized ground states, including local minima and Nehari–Pohozaev arguments. These are relevant comparisons, not a claim that their exact hypotheses coincide with this global cubic–quintic minimization. The cited abstracts and the repository's earlier references are not a complete novelty audit.

The two new candidate Lean modules encode Theorems A and B on the existing Sobolev.H2.energy and Imin. They import the generic compactness machinery of PR #99. Theorems C–E, the scaling counterexample, the explicit Gaussian seed specialization, dimensionless normalization and all-k defocusing extension remain analytical; they are not encoded by those Lean declarations. Full lake build and exact transitive axiom audits are required, and no green build is asserted until observed. No custom axiom, unfinished proof command or circular attainment assumption is intentionally introduced. The scope of the original problem and its registry status remain unchanged; no issue closure or accepted completion record is warranted.

## 10. Virial-ratio extension (new candidate Lean proof)

**Theorem F.** For beta,gamma>0, m>0 and every real k satisfying
\[
k^2m\leq 3\beta/\gamma,
\]
strict binding holds for every interior split; every minimizing sequence is
subsequentially compact modulo translations and the infimum is attained.
In particular k=0 has no mass ceiling. For k≠0 this is the closed interval
0<m≤3 beta/(gamma k²), strictly larger than the explicit interval m≤m_R.
This is sufficient, not a necessary confinement bound.

Proof. Let r*=3 beta/(4 gamma). First assume k²m<3 beta/gamma. Set
d=(r*−k²m/4)/(2+gamma m²/48), c=r*−d and B=beta/4−gamma c/3=gamma d/3.
Then 0<c<r*, B>0, and k²m/4+B m²/16<c.
For any dilation-stationary W of mass a≤m, let x=sqrt(aD).
The exact Sobolev estimates give Q≤ax/4, S≤xQ/4 and K≤x.
If S>cQ, then x>4c>0 (since Q>0).
The virial identity yields D≤k²x+BQ, hence
x²≤(k²a+B a²/4)x and therefore x/4≤k²m/4+B m²/16<c,
a contradiction. Thus S≤cQ uniformly on all these fields.

For mass ratio t>1 with gamma(t+1)c/3<beta/2, set
h=1−2 gamma(t+1)c/(3 beta)>0. Amplitude scaling gives
E(sqrt(t)W)/t≤[1+(t−1)h]E(W), using E(W)≥−beta Q/2.
Adjust near-minimizers to dilation stationarity and take the infimum;
I(ta)/(ta)≤[1+(t−1)h] I(a)/a < I(a)/a because I(a)<0.
For a<b≤m choose l=r*/c>1 and d0=(l−1)a>0.
Any increment y−x≤d0 within [a,b] satisfies y/x≤l and
(y/x+1)c≤r*+c<2r*, so finitely many local increments give
I(b)/b<I(a)/a. This is the real-interval chaining lemma, not a
differentiability assumption on I.

For the equality endpoint b, take q_n=b−(b−a)/(2(n+1)) and
near-minimizers of masses q_n with energy errors 1/(n+1).
They have energies ≤1, and the established coercivity bound yields
a uniform H² bound because q_n≤b. The existing exact mass correction
lemma implies I(b)≤liminf of their energies ≤b I(a)/a. To obtain
strictness, apply this nonstrict comparison starting at (a+b)/2,
and then the strict interior comparison between a and that midpoint.
This proves strict decrease also at the endpoint. Multiplication by
both split masses and addition yield strict binding. Apply the generic
whole-space compactness and attainment results.

Formal correspondence: MathProofs.GC06VirialBinding, with exact roots
stationary_ratio, exists_ratio, local_comparison, chain_strict,
energy_per_mass_strict, strict_binding_virial, compactness_virial,
exists_minimizer_virial, exists_minimizer_zero_all_mass,
energy_per_mass_le_endpoint, energy_per_mass_strict_closed,
strict_binding_closed, compactness_closed, exists_minimizer_closed.
The focused build and strict 25-root axiom gate now include this module.
The earlier two GC06 modules were reported successfully built by the
user with standard axioms only; this new module still requires compilation.
No GC-level status promotion. The counterexample in section 7 still
prevents inferring arbitrary-mass binding from stationarity alone.
