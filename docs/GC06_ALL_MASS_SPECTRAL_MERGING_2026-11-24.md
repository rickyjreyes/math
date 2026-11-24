# GC06 / GC16: all-mass spectral merging and exclusion of the shell threshold

Status: **complete-scope analytical proof candidate; not kernel-verified**. Independent review of the continuum proof and full Lean correspondence are required. This is not a declaration that GC06 is complete. Original F01 Hamiltonian, complex H²(R²), beta,gamma>0, real k, m>0. No mass cap and no change of model.

## 1. Claim and precise dependencies

Let A=Delta+k², M=||u||₂², T=||Au||₂², Q=||u||₄⁴, S=||u||₆⁶, E=T-beta Q/2+gamma S/3, and I(m)=inf_{M=m} E. The proposed theorem is

    I(a+b)<I(a)+I(b)  for every a,b>0.

It implies attainment and compactness modulo translations at every mass by the merged WholeSpace.compactness_of_binding and exists_minimizer_of_binding. For k=0 use merged #99. For k≠0 the proof below uses (i) negativity and ordinary subadditivity, (ii) the finite minimizing cluster decomposition proved analytically in GC06_SHELL_BINDING_2026-11-24.md §6, (iii) standard elliptic regularity, Fourier/complex analysis and the Bessel kernel facts specified below, (iv) the absence of superexponentially decaying eigenfunctions in Herbst–Skibsted, Decay of eigenfunctions of elliptic PDE's I, Adv. Math. 270 (2015), 138–170, preprint https://arxiv.org/abs/1306.6878 (Theorem 1.2). In (iv) take the real elliptic degree-four polynomial Q_symbol(xi)=(|xi|²-k²)², V1=0, V2=-beta|u|²+gamma|u|⁴; exponential decay of u satisfies the required power decay of V2. This is an external analytical theorem, not a new Lean axiom.

No radiality, positivity of the Green function, uniqueness, surface-tension limit, or leading angular amplitude assumed. The proof avoids needing a sharp interface asymptotic. It treats complex profiles throughout.

## 2. Every attained constrained minimizer has strictly negative multiplier

E is C² on H²(R²;C) as a real Banach space, by Sobolev embedding and the polynomial nonlinearity. For a nonzero attained minimizer u, the mass derivative is nonzero, hence the real Lagrange multiplier theorem gives

    A²u + N(u) = lambda u,    N(u)=(-beta|u|²+gamma|u|⁴)u.
    lambda M = T-beta Q+gamma S.

The equation initially holds weakly. Since u in H² is bounded and N(u) in L², the Fourier elliptic estimate gives u in H⁴ (and standard bootstrapping gives smoothness). The continuous representative tends uniformly to zero at infinity: H² embeds in uniformly Hölder continuous functions and L² excludes disjoint balls with a fixed positive lower bound.

First lambda<=0. For 0<t<1, subadditivity and negativity give

    E(u)=I(m)<=I(tm)+I((1-t)m)< E(sqrt(t)u).

The exact polynomial E(sqrt(t)u)=tT-beta t² Q/2+gamma t³ S/3 has left derivative <=0 at t=1. That derivative is lambda m.

**Threshold exclusion (new).** Suppose lambda=0. For every h in H² with Re integral conj(u)h=0, constrained second variation of J=E-lambda M gives

    0 <= H_u(h)
      = ||Ah||₂² + integral [(-beta rho+gamma rho²)|h|²
                       +(-2beta+4gamma rho)(Re(conj(u)h))²],
    rho=|u|².

This is the coefficient of epsilon², not the second derivative itself; it follows by expanding the two real polynomials in |u+epsilon h|² and using a mass-normalized tangent curve and J'(u)=0.

Let kappa=|k|>0. Put d=beta/(4gamma). If {rho>=d} is nonempty, it is compact. Set R0 to its maximum radius (increase to any sufficiently close radius if necessary). By continuity at an outermost point with rho>=d, there is a positive-measure bounded set B outside radius R0 on which rho>=c>0 and rho<=d, with |x|>=R1>R0. More explicitly choose a point just beyond the outermost point in the outward radial direction, then a small open ball there. If the high set is empty, choose a positive-radius ball where rho>0 and choose R0 below its minimum radius. In either case all r>R0 have rho<=d. In the exceptional R0=0 case the high set cannot be a singleton at rho>d; the same outward continuity argument works and the positive-core integral is zero. For any complex h, the potential integrand is <=C0|h|² on r<=R0 (boundedness), and <=-(3beta/4)rho|h|² on r>R0, uniformly in global phase.

Use the smooth entire Helmholtz wave

    phi_n(x)=J_n(kappa r) exp(i n theta),    A phi_n=0,

where J_n is the integer-order Bessel function (equivalently an angular Fourier coefficient of plane waves of wave number kappa). On every bounded radial interval, its series gives J_n(kappa r)=(kappa r/2)^n/n! * (1+O(1/n)), uniformly as n→∞, including r=0 by continuous interpretation of the factored series. Indeed the relative sum of the j>=1 series terms is bounded by exp((kappa R)²/(4(n+1)))-1. Consequently the positive-core integral divided by (kappa/2)^(2n)/(n!)² is at most C R0^(2n), whereas the negative integral over B divided by the same factor has magnitude at least c' R1^(2n). For all sufficiently large fixed n the total potential upper bound is strictly negative. No assertion is made that phi_n is L².

Fix such n. Let h_L=exp(i theta_L) chi(x/L) phi_n(x) with chi smooth, compactly supported, equal to 1 on the unit ball. Choose theta_L so Re integral conj(u) h_L=0 (if the complex inner product vanishes, choose any phase). The potential upper bound stays negative uniformly for large L: the core and B are uncut, and the rest of the exterior contribution is nonpositive. The kinetic term tends to zero since

    A(chi_L phi_n)=2 grad chi_L·grad phi_n+(Delta chi_L)phi_n.

For fixed n the usual real-argument Bessel asymptotic (or stationary phase in the angular plane-wave integral) gives |phi_n|+|grad phi_n|=O(r^(-1/2)) as r→∞. On the cutoff annulus r~L, the squared kinetic integral is O(L^(-1))+O(L^(-3)). Each h_L is an admissible H² tangent direction, though its L² norm need not be uniformly bounded. The second variation is taken at each fixed L first. This contradicts H_u(h_L)>=0.

Thus lambda<0 for every attained minimizer at k≠0. This removes the threshold obstacle in the preceding dossiers. It uses the full constrained Hessian, not virial stationarity alone.

## 3. Equality of two attained clusters forces a shared multiplier

Suppose u,v attain I(a), I(b), respectively, and I(a+b)=I(a)+I(b). For |h|<min(a,b), ordinary subadditivity gives

    E(sqrt(1+h/a) u)+E(sqrt(1-h/b) v)>=I(a+b),

with equality at h=0. The polynomial derivative at zero is lambda_u-lambda_v. Hence lambda_u=lambda_v=lambda<0. No differentiability of the value function I is needed.

## 4. Exponential decay and source noncancellation for negative lambda

Use Fourier convention exp(-i xi·x), ignoring fixed harmless normalization factors (take forward unnormalized, inverse (2pi)^(-2)). Write tau=sqrt(-lambda)>0 and

    P(z)=(z·z-k²)²+tau²,
    s_±=k²±i tau, c_±=sqrt(s_±)=p±i alpha, p,alpha>0.
    alpha=sqrt((sqrt(k⁴+tau²)-k²)/2).

The complex dot product is bilinear, not Hermitian. The two characteristic quadrics z·z=s_± are disjoint smooth complex curves. Their minimum |Im z| is alpha: writing z=x+iy, x·y=±tau/2 and |x|²-|y|²=k² implies |y|²(|y|²+k²)>=tau²/4. Equality holds at z=c_± omega, omega a real unit vector.

**Decay:** the inverse of P(D) is the difference of the two complex Helmholtz resolvents divided by a nonzero constant. In R² each kernel is (2pi)^(-1) K_0(mu r), where mu²=-s_± and Re mu=alpha. The standard K_0 small-argument logarithmic bound and large-argument asymptotic O(r^(-1/2) exp(-alpha r)) give a Green kernel G with exp(q|x|)G in L¹∩L² for every 0<q<alpha. These Bessel facts follow, for example, from DLMF 10.30 and 10.40, https://dlmf.nist.gov/10.30 and https://dlmf.nist.gov/10.40. The resolvent formula is applicable because P(xi)>=tau² on real frequencies.

Here are details that avoid assuming the decay of u: write u=-G*(V u), V=-beta|u|²+gamma|u|⁴ bounded and tending to zero. For w_L=exp(q min(|x|,L)), w_L(x)/w_L(y)<=exp(q|x-y|). Weighted Young gives

    ||w_L u||₂ <= ||exp(q|.|)G||₁
        (||w_L V 1_{|x|<=R}u||₂ + sup_{|x|>R}|V| ||w_L u||₂).

Choose R so the second coefficient is <1/2, independently of L. The first term is bounded by exp(qR)||Vu||₂. Let L→∞; obtain exp(q|x|)u in L². Weighted Cauchy-Schwarz in the convolution using exp(q|.|)G in L² and exp(q|.|)Vu in L² gives |u(x)|<=C_q exp(-q|x|) (everywhere by continuity).

**Noncancellation:** define F_u(z)= Fourier[N(u)](z). It is holomorphic for |Im z|<3q whenever u has the pointwise decay above, and bounded on each smaller closed tube by the weighted L¹ bound. Choose q with alpha/2<q<alpha. We show some F_u(c_± omega) is nonzero.

Suppose F_u vanishes on both characteristic circles, for every real unit omega. On each quadric use w=z1+i z2, v=z1-i z2=s/w with w≠0. Then

    |Im z|²=(|w|²+|s|²/|w|²-2 Re s)/4.

For each tube radius R>alpha its intersection with the quadric is a connected annulus in w, containing the circle |w|=sqrt(|s|) parametrized by c_± omega. The one-variable identity theorem implies F_u vanishes on the entire intersection in its domain. The simple factors of P have nonzero gradient there, so -F_u/P extends holomorphically throughout |Im z|<3q by local holomorphic division. On any smaller closed tube the quotient is O((1+|Re z|)^(-4)) uniformly: away from a bounded real-frequency region this follows from the leading polynomial and bounded F_u, and on the remaining compact region by holomorphy. Its real-axis values are uhat by the profile equation. Fourier inversion and contour shift along the vector b x/|x|, for 0<b<3q, give |u(x)|<=C_b exp(-b|x|). The contour shift is justified by the uniform integrable polynomial decay, using successive coordinate contours and vanishing vertical edges.

In particular take b=2q, improve the source tube to 6q, and repeat. The two original characteristic-circle vanishing assumptions persist by analytic continuation of the same source transform. This proves decay at every exponential rate. Herbst–Skibsted Theorem 1.2 (cited in §1) rules this out for a nonzero eigenfunction of the real elliptic degree-four symbol with this exponentially decaying V. Thus at least one of the two circle traces is nonzero. This argument does not require every directional far-field amplitude to be nonzero.

## 5. Strict merging by a Fourier pole contradiction

Assume the equality pair of §3. Both profiles satisfy §4 for the same alpha. Replace v by an orthogonal spatial rotation and, if necessary, complex conjugation, preserving the original energy, constraint and multiplier. Since Fourier[conj(v)](z)=overline(vhat(-bar(z))), conjugation switches the two characteristic branches (and the same holds for the nonlinear source). Rotations act transitively on each circle. By §4 we can therefore arrange a point z0=c_± omega with

    F_u^*(z0) F_v(z0) != 0,
    F_u^*(z)=overline(F_u(bar(z))).

Define v_y(x)=v(x+y), B(y)=integral conj(N(u)(x)) v_y(x) dx. Its Fourier transform in y satisfies on real xi

    P(xi) Bhat(xi) = -F_u^*(xi) F_v(xi).

This identity follows by Fubini and the profile equation; all functions are exponentially decaying.

Choose alpha/2<q<a0<alpha and use the pointwise estimates with rate a0. Every integral of |u|^i |v_y|^j, i,j>=1, is O(exp(-min(i,j)q|y|)): factor out the exponential using |x|+|x+y|>=|y| and integrate the leftover exponential. Constants are uniform in y and phase.

Let w=u+exp(i theta)v_y, J=E-lambda M. Exact quadratic expansion and the two common-multiplier equations give

    J(w)-J(u)-J(v) = 2 Re(exp(i theta) B(y)) + O(exp(-2q|y|)).

Sign check: the shifted quadratic cross pairing is -B(y). The nonlinear first-order expansion on each core contributes +B(y) in the same real-part convention. Thus one copy remains. Every remaining nonlinear monomial has at least two factors from each field, and the preceding overlap estimate bounds its integral. The equality of the two first-order nonlinear pairings is precisely self-adjointness of A²-lambda. No sign property of G is used.

The mass defect M(w)-(a+b) is O(exp(-q|y|)). For large |y| set t=(a+b)/M(w)=1+O(exp(-q|y|)). The amplitude polynomial J(sqrt(t)w) has first derivative at 1 equal to T(w)-lambda M(w)-beta Q(w)+gamma S(w)=O(exp(-q|y|)): the individual derivatives vanish, the shifted kinetic cross term is controlled by B, and all mixed nonlinear terms have at least one factor of each field. Its second derivative is bounded uniformly for t near 1 by boundedness of Q(w), S(w). Hence exact mass correction changes J only by O(exp(-2q|y|)), uniformly in theta. As a result,

    J(sqrt(t)w)-J(u)-J(v)=2 Re(exp(i theta) B(y))+O(exp(-2q|y|)).

Equality of the infima would require the left side nonnegative for every phase. Choosing the phase giving -|B(y)| forces |B(y)|<=C exp(-2q|y|) for all large |y|, and after changing C for all y.

Thus Bhat is holomorphic in the tube |Im z|<2q, which contains z0 because 2q>alpha. The real-frequency Fourier identity extends holomorphically to this tube (or the common smaller source tube) by uniqueness on the real open plane; one can apply the one-variable identity theorem successively in each coordinate. At z0 its left side is zero and its right side is nonzero, contradiction. The assumed equality of two attained clusters is impossible.

This argument simultaneously covers balanced, intermediate and asymmetric split masses. It does not assert pointwise monotonicity of I/m, which is stronger than what is needed.

## 6. All-mass classification by the earlier finite cluster theorem

If all-split strict binding fails at some positive m, ordinary subadditivity gives an equality split. Translate disjoint compact approximants of the two masses apart to create a noncompact minimizing sequence. Apply the earlier finite minimizing profile theorem (§6 of GC06_SHELL_BINDING_2026-11-24.md). The decomposition must have at least two nonzero attained minimizing profiles, and each pair must saturate ordinary subadditivity. Sections 2–5 contradict every such pair. Hence every split strictly binds. Existing compactness and attainment transfer applies at every positive mass. The k=0 case was previously merged.

Subject to review, this excludes genuine fragmentation equality and nonattainment throughout the stipulated positive beta,gamma domain. It does not address gamma<0, other dimensions, nonlinear excited-state stability, or physical validation. The prior defocusing exclusion remains a separate outside-domain result.

## 7. Verification boundary

The substantive new steps are (a) the high-angular-order threshold Hessian contradiction and (b) Fourier pole noncancellation and phase-optimized strict merging. The needed external spectral theorem is explicitly identified and must be formalized or replaced by a proved in-repository lemma. The finite-cluster decomposition, ordinary subadditivity, Euler–Lagrange differentiability, Bessel/cutoff estimates, complex tube division and inversion, and exact mass-corrected interaction estimates require full Lean formalization. No claim of kernel verification of this analytical chain. Keep GC06 #81 and GC16 #55 open until those obligations and independent review are satisfied. No novelty claim.
