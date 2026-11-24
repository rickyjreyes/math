# GC03: mixed-power polyharmonic Hamiltonian evolution
Richard J. Reyes research program · analytical working manuscript · 2026-11-24

**Scope:** original GC03, pure dispersion on R^d, integer d,p >= 1, real 1<r<s, beta,gamma>0. This is a partial resolution dossier, not a novelty claim or a Lean-certified classification. See issue #100 and PR #99. The original statement is unchanged.

## 1. Model and solution classes

Set A=(-Delta)^p, F_a(z)=|z|^(a-1)z and U(t)=exp(-itA). Consider i u_t=A u-beta F_r(u)+gamma F_s(u). H^p is the inhomogeneous L² Sobolev space; the kinetic quadratic form K=||A^(1/2)u||₂². Define M=||u||₂² and E=K/2-beta||u||_(r+1)^(r+1)/(r+1)+gamma||u||_(s+1)^(s+1)/(s+1). The natural finite-energy domain is X=H^p ∩ L^(s+1), because L² interpolation supplies the lower power. Energy is a real integral on X, not a total real-valued function on all H^p outside the embedding range.

Strong energy well-posedness means a unique distributional u in C(R;H^p) (with finite energy where asserted), initial trace u(0)=u0, continuous data dependence in C([-T,T];H^p) for each finite T, and conservation of M,E. The subcritical proof below actually gives uniqueness among locally essentially bounded H^p distributional solutions with the weakly continuous H^p representative and prescribed trace. This is distinct from weak existence without uniqueness.

Define s_E=∞ for d<=2p, and s_E=1+4p/(d-2p) otherwise. The limiting pure upper-power scaling is u_lambda(t,x)=lambda^(2p/(s-1))u(lambda^(2p)t,lambda x). The corresponding critical regularity is d/2-2p/(s-1). The lower-power term breaks exact scaling of the mixed equation.

## 2. Unconditional energy obstruction to H^p norm blow-up

Let a=beta/(r+1), b=gamma/(2(s+1)), R=(a/b)^(1/(s-r)), C=a R^(r-1). For x>=0,
a x^(r+1) <= b x^(s+1)+C x².
Indeed below R use x^(r-1)<=R^(r-1), above R use b x^(s-r)>=a. Thus
E(u)+C M(u) >= K(u)/2+b||u||_(s+1)^(s+1).
On any trajectory conserving finite M,E, the right-hand quantities are uniformly bounded, hence so is the H^p norm (equivalence with M+K by Plancherel). This holds for every d,p,r,s, with no smallness assumption. For regular solutions conservation follows by pairing u_t=-i(Au+F(u)) with the real energy gradient, and using the reality of <u,Au+F(u)> for mass. Section 3 establishes conservation for rough subcritical solutions rather than assuming it. Boundedness alone is not a critical or supercritical continuation theorem. In particular a counterexample to global well-posedness need not have H^p norm tending to infinity.

## 3. All-real-power energy-subcritical global theorem (analytical proof)

**Theorem.** For every d,p>=1, beta,gamma>0, and 1<r<s<s_E, every u0 in H^p(R^d;C) generates a unique global strong energy solution, conserving M,E and continuously depending on u0. No differentiability of F_a to order p, parity of exponents, radiality or mass bound is required.

Proof uses standard Fourier analysis, the free dispersive and nonendpoint Strichartz estimates, Rellich compactness and the Hilbert triple chain rule. These foundational results are invoked as classical theorems, not asserted to have been formalized in this repository.

### 3.1 Dispersive uniqueness and stability

The free unitary group obeys ||U(t)||_(L¹->L∞)<=C|t|^(-d/(2p)). This follows by scaling its oscillatory kernel and bounding the unit-time integral: for bounded x integrate by parts at large frequency, and for large x rescale frequency by |x|^(1/(2p-1)), apply nondegenerate stationary phase near the unique nonzero critical point and integrate by parts off it. The latter gives a bounded kernel, with decay |x|^(-d(p-1)/(2p-1)). For p=1 use the Gaussian kernel. Apply the abstract Strichartz theorem to this decay and L² unitarity. For a in {r,s}, set b_a=a+1 and q_a=4p(a+1)/(d(a-1)); then 2p/q_a+d/b_a=d/2, q_a>2. In the low-dimensional case the same strict inequality holds for each finite a. Define Y(I)=L∞_t L²_x ∩ L^(q_r)_t L^(b_r)_x ∩ L^(q_s)_t L^(b_s)_x, with the sum norm. The retarded inhomogeneous bounds from each dual pair to each output pair hold since the input time exponent q_a' is <2 and output >=2 (Christ-Kiselev). For any H^p-bounded trajectories u,v, the Sobolev embedding and
|F_a(u)-F_a(v)|<=C_a(|u|^(a-1)+|v|^(a-1))|u-v|
give
||F_a(u)-F_a(v)||_(L^(q_a') L^(b_a')) <= C_a B^(a-1)|I|^(1-2/q_a)||u-v||_(L^(q_a)L^(b_a))
where B bounds their H^p norms. Consequently
||u-v||_Y <= C||u(t0)-v(t0)||₂ + C sum_(a=r,s) B^(a-1)|I|^(1-2/q_a)||u-v||_Y.
All constants may depend on d,p,r,s,beta,gamma. For sufficiently short I (depending only on B), absorb the second term. Iterate on compact intervals. This proves uniqueness and L² stability on bounded H^p families, including weakly continuous solutions from the compactness argument. Their nonlinearities belong to L∞(I;L^(b_a')) and the trajectories to Y(I); distributional Duhamel follows by testing against the free adjoint group (or integrating in H^-p). Strichartz gives the same Duhamel integral as an L²-valued function. No differentiating F_a in x is needed.

### 3.2 Construct the dynamics, not just an a priori estimate

Let P_N be the orthogonal L² Fourier projector to |xi|<=N; it commutes with A and is contractive on H^p and H^-p. Solve in its closed range
i u_N'=A u_N+P_N(-beta F_r(u_N)+gamma F_s(u_N)), u_N(0)=P_N u0.
The range is a Banach space in L²; Bernstein bounds give L∞ control there, A is bounded there, and the pointwise difference estimate gives local Lipschitz continuity of this ODE. P_N u_N=u_N. The derivative of E on this range is its projected Hamiltonian gradient; M and E are constant by the real inner-product calculation, justified since the functions are bandlimited and bounded. L² conservation alone prevents escape from the Banach ODE on bounded time intervals for fixed N. In particular u_N exists for all real times. By the embedding and P_N u0 -> u0 in H^p, initial energies converge. Section 2 therefore supplies uniform-in-N global H^p bounds.

The equation gives uniform bounds for u_N' in H^-p: A:H^p->H^-p, and F_a(u_N) in L^(b_a') embeds in H^-p by dual Sobolev embedding. The P_N are contractive there. Interpolate the H^-p time difference and H^p bound to obtain equicontinuity in L². Rellich on bounded spatial balls plus Arzela-Ascoli and diagonal extraction yields convergence in C([-T,T];L²_loc) for every T, and weak H^p convergence at each time to a weakly H^p-continuous representative. This last assertion follows from local L² convergence and uniform H^p boundedness: every weak subsequence has the same distributional limit; the same reasoning applies at variable times. Extract an a.e. space-time convergent subsequence; on each bounded cylinder strict subcritical interpolation yields strong L^(a+1), hence strong L^((a+1)/a) convergence of F_a. In distribution tests replace P_N phi by phi: the difference tends to zero in H^p hence in L^(a+1), uniformly on compact time support, while the nonlinear dual norms stay bounded. The limit solves the original PDE, has initial datum u0, and lies in L∞(R;H^p). The Hilbert triple H^p⊂L²⊂H^-p chain rule gives C_t L² and conservation of M: the dual pairing of u_t with u has zero real part (A is selfadjoint and each pointwise power pairs to a real integral). This use of the chain rule requires u in L²_t H^p, u_t in L²_t H^-p on each compact interval, as proved above.

### 3.3 Exact energy conservation and strong continuity

Write E+CM=K/2+integral W(|u|), where W(x)=-a x^(r+1)+2b x^(s+1)+Cx²>=0. Weak lower semicontinuity of K, and Fatou on spatial a.e. convergent subsequences at each fixed t, imply E(u(t))+CM(u(t))<=E(u0)+CM(u0). Mass conservation removes the shift. Repeat the entire construction starting from u(t0) at any finite t0, in both time directions. Uniqueness from 3.1 identifies the newly constructed solution with the existing one; applying the energy inequality at time 0 gives the reverse inequality. Hence E(t)=E(0) for every t.

If t_n->t, L² continuity and uniform H^p bound give weak H^p convergence and, by strict subcritical interpolation, strong L^(r+1) and L^(s+1) convergence. Conservation gives convergence of K(t_n) to K(t). Weak convergence and convergence of M+K yield strong H^p convergence. This proves u in C(R;H^p), including the strong initial trace.

For u0_n->u0 in H^p the coercivity estimate supplies a common H^p bound for the corresponding solutions. The short-interval estimate, iterated on [-T,T], gives convergence uniformly in time in L². Strict subcritical interpolation gives uniform L^(a+1) convergence, and energy conservation yields uniform convergence of K. If uniform H^p convergence failed, choose a sequence of times t_n in [-T,T] and extract t_n->t. Weak H^p convergence to u(t) and convergence of M+K imply strong convergence at those times, a contradiction. Thus dependence in C([-T,T];H^p) is continuous. QED.

A local solution in the stated class agrees with the global solution by uniqueness. The usual maximal-lifespan H^p norm continuation criterion in the subcritical regime follows, with no finite lifespan for these parameters. This is a compactness/uniqueness proof rather than a contraction in H^p, avoiding spurious restrictions on low real exponents.

## 4. Critical boundary (d>2p, s=s_E)

All H^p data have finite energy; the coercive bound persists. The same Galerkin construction gives global weakly H^p-continuous distributional solutions, with mass conservation and E(t)<=E(0). For the limiting equation, local strong L² plus the L^(s+1) bound yields a.e. convergence and weak convergence of F_s in L^((s+1)/s) on bounded cylinders (reflexivity and a.e. convergence); thus strong critical embedding is not needed to pass the equation. No strong energy continuity or equality follows just from this compactness step.

At q_s=2 the subcritical time gain vanishes. For two C_t H^p solutions one can nonetheless prove uniqueness on their common interval: write the critical difference as bounded coefficient times |u-v| plus a tail coefficient small in L∞_t L^(d/(2p)) by compactness of the two continuous L^(s+1) trajectories on a compact time interval. Use endpoint Strichartz (decay exponent d/(2p)>1), absorb the small tail in L²_t L^(s+1), and bound the bounded coefficient in L¹_t L² by the interval length times L∞_t L²; the lower power still has the subcritical time gain. This proves uniqueness for existing continuous strong trajectories, not their existence or conservation in arbitrary dimension. In particular bounded H^p does not bound the critical spacetime norm or ensure uniform local existence.

For p=1, d>=3, Theorem 1.1(2) of Tao, Visan and Zhang, "The nonlinear Schrödinger equation with combined power-type nonlinearities" (arXiv:math/0511070, JFA 2007) directly covers the exact coefficients lambda1=-beta, lambda2=gamma and exponents p1=r-1, p2=s-1. It establishes global H¹ well-posedness at and below the upper critical power. This is existing prior art. For p>=2 the all-dimension, all-real-lower-power large-data critical result is not established here. One needs a critical spacetime continuation/stability argument or an exact matching existing theorem. Do not infer it from coercivity or weak existence. Small-data critical results and higher-order special cases require separate hypothesis matching.

## 5. Supercritical: exact finite-energy obstruction for every real power

Suppose d>2p and s>s_E. Choose d/(s+1)<=ell<d/2-p and a compact smooth cutoff chi equal to 1 near zero. Let u0(x)=chi(x)|x|^(-ell), changing its value at zero arbitrarily. Each weak derivative of order j<=p is bounded near zero by C|x|^(-ell-j); its square is integrable because 2(ell+p)<d. The derivative formulas hold distributionally by removing a ball of radius epsilon; boundary terms vanish since ell+p<d/2<d. But the upper-power integral diverges by radial integration (including logarithmic divergence at equality). Thus H^p is not contained in X. The admissible class X is exactly the finite-energy H^p domain. It is a proper dense subset in the supercritical regime (C_c^infty is dense). For all H^p data the conserved finite-real-energy formulation is impossible. This is not a nonexistence proof for every possible distributional solution class and is not a finite-time blow-up example.

Stronger energy discontinuity on smooth data: put a0=d/2-p, take a nonzero smooth compactly supported phi, and v_L=L^(-a)phi(x/L) for d/(s+1)<a<a0. Then ||v_L||_(H^p)->0 but ||v_L||_(s+1)^(s+1)=L^(d-a(s+1))||phi||_(s+1)^(s+1)->infty. The bound in section 2 implies E(v_L)->+infty.

## 6. Supercritical polynomial norm inflation (analytic counterexample)

For odd integers 1<r<s and s>s_E, universal Hadamard well-posedness in H^p is false even restricted to smooth finite-energy data and any flow consistent with classical solutions. This is an extension of the standard small-dispersion argument, not a novelty claim.

Fix a nonnegative real phi in C_c^infty with phi>0 and partial_1(phi^(s-1)) nonzero on an open set. Let a0=d/2-p. Pick eps_n=1/n^p and T_n=n². For fixed n and L->0, set A_L=eps_n L^(-a0), delta_L=L^(-2p)A_L^(-(s-1))->0 and eta_L=A_L^(r-s)->0, since a0(s-1)>2p. Under u(t,x)=A_L v(A_L^(s-1)t,x/L), the exact equation becomes
i v_tau=delta_L (-Delta)^p v+gamma F_s(v)-beta eta_L F_r(v).
The zero-dispersion solution of the limiting upper-power ODE is w(tau,x)=phi(x) exp(-i gamma tau phi(x)^(s-1)). It is smooth and compactly supported in x. For each fixed T_n, choose integer m>max(p,d/2). The polynomial nonlinearities are locally Lipschitz in H^m by its algebra estimate, uniformly for eta in [0,1]. The free group with coefficient delta is unitary in H^m. Subtract the equation for w from the equation for v and use Duhamel with this unitary group. On ||v-w||_(H^m)<=1, Gronwall yields
sup_[0,T_n] ||v-w||_(H^m) <= (delta_L C_n+eta_L C_n) exp(C_n T_n)
where C_n is finite from the H^(m+2p) bounds of w and its polynomial powers on [0,T_n]. For sufficiently small L this is <1/2; the local H^m contraction and bootstrap extend v to T_n. Thus it is legitimate to approximate the ODE arbitrarily closely on each fixed interval, choosing L only after T_n. No uniform-in-n estimate is needed.

By Leibniz, partial_1^p w(T)=exp(-i gamma T phi^(s-1))[( -i gamma T)^p phi(partial_1(phi^(s-1)))^p+O_(L²)(T^(p-1))]. The coefficient of T^p has strictly positive L² norm. Thus ||partial_1^p w(T)||₂ >= c T^p for T sufficiently large. Choose L_n so that the preceding approximation error is <1, L_n<1/n and t_n=T_n A_(L_n)^(-(s-1))<1/n. Exact rescaling gives
||u_n(0)||_(H^p) <= C eps_n ->0,
||u_n(t_n)||_(H^p) >= eps_n(c T_n^p-1) ->infty.
The u_n are strong H^m solutions on [0,t_n] (smooth initial data; higher regularity persistence for polynomial nonlinearities). Hence no common-neighborhood continuous flow into C([0,T];H^p) agreeing with these solutions can exist at zero. This is norm inflation, not one datum blowing up at a finite time. Indeed the conserved energies of the initial data are not uniformly bounded in this sequence, which is consistent with section 2. For arbitrary nonpolynomial supercritical powers this particular H^m-algebra proof does not automatically apply; their norm-inflation classification is open in this dossier.

## 7. Classification and remaining obligations

| Regime | Strong H^p conclusion | Finite energy | Actual H^p norm blow-up |
|---|---|---|---|
| d<=2p, all finite real 1<r<s | Global, unique, continuous dependence (section 3) | All H^p | Excluded |
| d>2p, s<s_E | Same (section 3) | All H^p | Excluded |
| p=1, d>2, s=s_E | Global by Tao-Visan-Zhang | All H^1 | Excluded |
| p>=2, d>2p, s=s_E | Global weak existence; strong uniqueness if existing; general strong global theory not established here | All H^p | Unbounded H^p norm excluded for conserving solutions |
| d>2p, s>s_E, r,s odd integers | Universal continuous H^p classical-consistent flow refuted | Proper dense X | Norm inflation across data, not finite-time blow-up |
| d>2p, s>s_E, other real powers | Universal finite-energy formulation refuted; broader local/strong theory unresolved here | Proper dense X | No blow-up example established; conserving solutions uniformly bounded |

The original requirement to exhibit finite-time blow-up whenever the universal assertion fails is therefore not a justified dichotomy. The exact energy-admissibility threshold is necessary and sufficient for all H^p data to have finite energy. The universal strong well-posedness classification remains incomplete at higher-order critical and nonpolynomial supercritical regimes. Even for supercritical smooth data we do not infer global regularity from a bounded H^p norm. Nonuniqueness and finite-time loss of higher regularity are different questions; no examples of either are claimed here.

## 8. Prior art and verification boundaries

- Tao, Visan, Zhang, arXiv:math/0511070 (Theorem 1.1(2)): exact p=1 case, not higher dispersion. The focusing-lower sign is explicitly permitted, unlike their finite-time blow-up cases with focusing higher power.
- Keel and Tao, Endpoint Strichartz Estimates, AJM 120 (1998), 955–980: abstract dispersive/energy bounds supply section 3 nonendpoint pairs and section 4 endpoint estimates.
- Higher-order free kernel estimates: e.g. https://arxiv.org/abs/2501.02562 (free case discussed in context of finite rank perturbations); the exact pure symbol is used here.
- Christ, Colliander, Tao, arXiv:math/0311048, small dispersion method; related fourth-order NLS ill-posedness https://arxiv.org/abs/1703.00891 and https://arxiv.org/abs/2202.03020. Section 6 gives the mixed-power polynomial adaptation, not a claim of first discovery.
- Existing F01 CubicQuinticFlow.lean proves the exact fourth-order cubic-quintic subcase, including k=0; PR #99 section 6 gave analytical general coercivity and the singular data obstruction.

Candidate Lean module MathProofs.GC03Energy contains the scalar real-power estimate and integrated coercivity on the repository's Fourier L² space, with explicit finite-integrability conditions, plus reuse of the known exact subcase. It does not encode the general evolution, Strichartz, compactness, norm inflation or singular witness. The local environment had no Lean/Lake and could not clone GitHub. All new Lean statements are unverified until actual CI and transitive axiom audit. Do not mark GC03 resolved.
