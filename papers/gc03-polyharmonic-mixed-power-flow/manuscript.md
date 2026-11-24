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


## 9. Follow-up: global weak existence on the exact finite-energy space, all powers

**Theorem (analytical, not Lean-certified).** For every d,p>=1, 1<r<s, beta,gamma>0 and u0 in X=H^p intersect L^(s+1), there exists a global distributional solution with
u in C(R;L²) intersect C_w(R;X) intersect L∞(R;X),
M(u(t))=M(u0), E(u(t))<=E(u0) for every real t.
Here C_w means weak continuity for the Banach space with norm ||u||_H^p+||u||_(s+1). The inequality is relative to the initial time; no monotone energy dissipation or uniqueness is asserted. This also applies in the critical and supercritical cases. The same proof applies with any positive dispersion coefficient delta and with nonnegative lower-power coefficient.

Proof. X is reflexive (closed diagonal subspace of H^p × L^(s+1)) and C_c^infty is dense in X by spatial cutoff and mollification. For initial data choose bandlimited u0,N -> u0 in X: first approximate by smooth compactly supported data f_j, then apply sharp Fourier projections P_N to each f_j with N sufficiently large. For fixed f_j convergence holds in H^p and L∞ (Fourier L¹ tails), thus in L^(s+1) by L²/L∞ interpolation. Take a diagonal sequence with N->∞. It is not necessary to assume that the sharp ball multiplier is uniformly bounded on L^(s+1).

Use the same projected Hamiltonian ODE as in section 3.2. Bernstein, the local Lipschitz pointwise difference estimate, and exact projected mass and energy conservation give global bandlimited solutions. Coercivity and convergence of initial energies imply a uniform L∞_t X bound. Choose an integer m>=p with m>d/2. The equation bounds u_N' in H^-m uniformly: P_N is contractive there, A:H^p->H^-p, and H^m embeds in both L^(r+1) and L^(s+1). Interpolation yields equicontinuity in L² (the time Hölder exponent is p/(p+m)); local Rellich and diagonal Arzela-Ascoli then give convergence in C([-T,T];L²_loc) for each finite T and a.e. space-time convergence. At each fixed t boundedness in X and the local L² limit identify every weak cluster point, including for variable times tending to t, giving the representative C_w(R;X). Nonlinear terms converge weakly in L^((a+1)/a) on compact cylinders, a=r,s, since they are bounded in that reflexive space and converge a.e. The P_N can be transferred to Schwartz test functions and removed using convergence in H^m and hence in both test Lebesgue norms. This proves the distributional equation.

For the limit, Au lies in H^-p and the two nonlinearities in the corresponding dual Lebesgue spaces. Thus u_t belongs to L∞_loc(R;X*) in the dual pairing using L² as pivot. The Hilbert-pivot chain rule for the reflexive Gelfand triple X⊂L²⊂X* gives strong L² continuity and dM/dt=2 Re <u_t,u>=0, since all three Hamiltonian terms pair with u to real quantities before multiplication by -i. The initial trace is u0. By Fatou and weak lower semicontinuity applied to the shifted nonnegative energy integrand in section 3.3, E(u(t))+CM(u(t))<=E(u0)+CM(u0) at every fixed t. The mass identity cancels the shifts. The construction on [-T,T] and diagonal extraction is two-sided, giving the asserted global trajectory. QED.

This theorem does not upgrade the critical weak solution to strong H^p continuity or exact energy conservation. It does prove that finite-energy admissibility is sufficient for global weak evolution even above the critical boundary; a failure of strong well-posedness is not a failure of all global existence.

## 10. Follow-up: all-real-power norm inflation in the energy-admissible class

The polynomial restriction in section 6 is unnecessary for norm inflation within the energy-admissible weak class, and for any stronger flow satisfying the same bounds. The following argument does not require a high-order derivative of the nonlinearities at zero.

### 10.1 Relative-energy stability of the zero-dispersion ODE

Fix nonnegative phi in C_c^infty chosen flat at its support boundary, e.g. phi(x)=exp(-1/(1-|x|²)) for |x|<1 and zero outside. Every positive power of phi is smooth; its first-coordinate derivative is nonzero on an open set. Write A=(-Delta)^p, J=-i as a skew map on the real Hilbert space of complex fields. Let
V(z)=gamma |z|^(s+1)/(s+1), F=grad_R V, W(z)=beta |z|^(r+1)/(r+1), G=grad_R W.
Set w(t)=phi exp(-i gamma t phi^(s-1)), so w_t=JF(w).
For delta in (0,1], eta in [0,1], let v be ANY solution on [0,T] in C_t L² intersect C_w X intersect L∞_t X satisfying
v_t=J(delta A v+F(v)-eta G(v)), v(0)=phi,
M(v(t))=M(phi), E_delta,eta(v(t))<=E_delta,eta(phi),
where E_delta,eta=delta K/2+integral(V-eta W).
Such solutions exist globally by section 9 for every delta>0. Uniformly in delta,eta, the absorption estimate (using eta<=1), the energy inequality and mass imply
sup_t [delta K(v(t))+||v(t)||_(s+1)^(s+1)+||v(t)||₂²] <= C_phi.
Interpolation bounds ||v||_(r+1) as well. No uniform unscaled H^p bound is presumed as delta->0.

Define the Bregman divergence B(z,y)=V(z)-V(y)-F(y) dot_R(z-y). Since s>1, V is C² on R², and
B(z,y)>=c_s,gamma |z-y|^(s+1).
For a direct proof, put e=z-y and use the Hessian integral with weight 1-theta: D²V(y+theta e)[e,e]>=gamma |y+theta e|^(s-1)|e|². On theta in [0,1/2], the set where |y+theta e|<|e|/8 has length at most 1/4 by projection onto e, so the remaining length is at least 1/4 and the weight at least 1/2. This yields the claimed positive constant (e=0 is immediate).

Let e=v-w and define the nonnegative relative functional
R(t)=delta K(v)/2+integral B(v,w)+||e||₂²/2.
For every fixed T there is C_T independent of delta,eta and the choice of energy-admissible v such that
R(t)<=C_T(delta+eta)+C_T integral_0^t R(tau) d tau,
hence sup_[0,T] R<=C'_T(delta+eta).

Here are details for distributional, potentially energy-inequality-only solutions. Let Q(t)=R(t)-eta integral W(v(t))=E_delta,eta(v(t))+L(t), where
L(t)=-integral V(w)-<F(w),v-w>_R+||e||₂²/2.
L is absolutely continuous: the test F(w) is smooth compactly supported in space and smooth in time, v_t is in X*, and the L² difference term uses the same Hilbert-pivot chain rule as in section 9. No derivative of E_delta,eta(v) is used. Using skew symmetry of J, symmetry of DF(w), and w_t=JF(w), its derivative a.e. is
L'=<w_t, delta A v + F(v)-F(w)-DF(w)e -eta G(v)>_R
   +<e,J(delta A v+F(v)-F(w)-eta G(v))>_R.
The dispersion contributions are bounded by C_T delta using <w_t,Av>=<Aw_t,v> and <v,JAv>_R=0, so only smooth w or w_t is differentiated. The eta terms are bounded by C_T eta using uniform L^(r+1) bounds on v and smooth w,w_t. For the mass-difference nonlinear term,
|e dot_R J(F(v)-F(w))| <= C_T (|e|²+|e|^(s+1))
by the first-order pointwise difference estimate and boundedness of w.
For the Taylor remainder term,
|w_t dot_R(F(v)-F(w)-DF(w)e)| <= C_T(|e|²+|e|^(s+1)).
Indeed, if |e|<=|w|/2 and w!=0, D²F on the connecting segment is bounded by C|w|^(s-2); multiplication by |w_t|=gamma|w|^s bounds this by C|w|^(2s-2)|e|². If |e|>|w|/2, the remainder has magnitude at most C|e|^s; multiply by |w_t|<=C min(1,|e|^s) and use 2s>2 for |e|<=1, and s<s+1 for |e|>=1. At w=e=0 the bound is immediate. This treats even 1<s<2 without evaluating D²F at zero.

Integrate L' and use E_delta,eta(v(t))<=E_delta,eta(phi). It follows that
Q(t)<=Q(0)+C_T(delta+eta)+C_T integral_0^t R.
Since Q(0)<=delta K(phi)/2 and eta integral W(v(t))<=C_phi eta, the stated inequality follows. Gronwall applies to the measurable bounded R and gives the uniform estimate. In particular,
sup_[0,T] ||v(t)-w(t)||₂ <= C_T sqrt(delta+eta).
All constants are allowed to depend on the fixed T. This estimate does not claim H^p convergence, strong solution existence or energy equality.

### 10.2 Scaling and norm inflation for every real supercritical pair

Assume d>2p, s>1+4p/(d-2p), 1<r<s. Let a0=d/2-p. For n>=1 choose eps_n=n^(-p), T_n=n², L>0, and amplitude A_L=eps_n L^(-a0). The exact rescaling
u(t,x)=A_L v(A_L^(s-1)t,x/L)
reduces the original GC03 to the equation in section 10.1 with
delta=L^(-2p) A_L^(-(s-1)), eta=A_L^(r-s).
For each fixed n these both tend to zero as L->0. Finite-energy weak solutions of the original equation correspond under this positive rescaling to the class in 10.1: the energy transforms by the common positive factor A_L^(s+1)L^d, and mass by A_L² L^d.

As in section 6, D_n=||partial_1^p w(T_n)||₂ >= c T_n^p for large n. Let H_n=||partial_1^(2p) w(T_n)||₂, finite since the flat bump has smooth positive powers. Distributional integration by parts and Cauchy-Schwarz imply, for ANY v(T_n) in H^p,
||partial_1^p v(T_n)||₂ >= D_n - (H_n/D_n)||v(T_n)-w(T_n)||₂.
To see this, pair partial_1^p v with partial_1^p w, move p derivatives in the difference onto w, and divide by D_n>0. Thus mere L² approximation suffices for a lower bound on the p-th derivative. Choose L_n small enough that C_(T_n) sqrt(delta+eta) H_n/D_n<=1, L_n<1/n, and t_n=T_n A_(L_n)^(-(s-1))<1/n. This is possible for each n independently, with no uniform-in-n constants required. The choice is independent of the solution v by the relative-energy bound.

Now the compact smooth original data u0,n=A_(L_n) phi(x/L_n) obey
||u0,n||_H^p <= C eps_n ->0,
while for every energy-admissible solution with that datum defined through t_n,
||u_n(t_n)||_H^p >= eps_n(D_n-1) -> infinity.
The class is nonempty by section 9. In particular, there cannot be a continuous data-to-solution map at zero into C([0,T];H^p), for any T>0, defined on an H^p-neighborhood of zero even restricted to smooth finite-energy data, whose outputs obey mass conservation and the energy inequality. Indeed the zero datum has only the zero solution in the mass-conserving class and uniform continuity at the origin would contradict the above sequence. More precisely, continuity at zero is contradicted; uniform continuity is not needed.

This is all-real-power norm inflation for energy-admissible weak solutions (with weak H^p continuity at minimum) and an obstruction to every compatible strong energy flow. It does not prove classical strong solutions exist for every nonpolynomial supercritical power. It does not rule out a distributional solution map that does not obey the energy inequality. It does not contradict possible well-posedness in the stronger X topology, since the initial upper-power moments diverge along this sequence. It is not finite-time blow-up of a single solution: each weak trajectory is global and bounded in H^p for its own fixed initial datum.

## 11. Updated exact scope and literature notes

The admissibility threshold is exact, and global weak evolution exists for all finite-energy data in all regimes. Universal strong energy well-posedness in the H^p topology is false for every supercritical real pair by section 10. The sole remaining parameter region for the universal strong energy question is d>2p, p>=2, s=s_E; this statement is about the present dossier, not a claim that no prior theorem treats any of those parameters. General weak uniqueness, general critical strong existence/conservation, and individual-data supercritical strong lifespan or singularity classification remain unresolved. The original blow-up requirement is not logically equivalent to failure of universal strong energy well-posedness.

Prior art checked in follow-up: Christ–Colliander–Tao's small-dispersion work explicitly discusses restrictions from high-order energy methods; Alazard–Carles, "Loss of regularity for supercritical nonlinear Schrödinger equations" (arXiv:math/0701857), uses modulated energy in a second-order integer-power setting. Carles–Gassot, DOI 10.4171/aihpc-126, also discusses norm inflation using global weak solutions. The above relative-energy calculation is for the exact mixed-sign polyharmonic equation and real powers; no novelty priority is claimed. Pausader's radial fourth-order energy-critical theorem (DOI 10.4310/DPDE.2007.v4.n3.a1) and Miao–Xu–Zhao's high-dimensional pure defocusing fourth-order theorem (arXiv:0807.0692) are useful critical perturbation inputs; neither may simply be cited as a proof for all lower focusing powers, dimensions and orders. The Tao–Visan–Zhang combined-power article is in Communications in Partial Differential Equations (2007), not JFA (correction to section 4 bibliography).

New analytical sections 9–10 have not been Lean formalized. Candidate Lean additions encode the exact scalar scaling/admissibility boundary equivalences and trajectory kinetic bound for the real Fourier energy. They are not a surrogate for weak compactness, the Hilbert-pivot chain rule, the relative-energy proof, or a norm-inflation theorem. GC03 remains candidate; no issue closure or accepted formal status promotion.


## 12. Critical strong local theory for all real powers, without high-order chain rules

Throughout sections 12–14 let d>2p, b=s+1=2d/(d-2p), s=1+4p/(d-2p), 1<r<s. All results in these sections are analytical, pending independent review and Lean formalization.

**Theorem 12.1.** For every u0 in H^p, the critical mixed equation has a unique maximal strong distributional solution u in C(I;H^p), I an open interval containing 0. It conserves mass and energy and has continuous dependence in C(J;H^p) for compact J⊂I. Local strong existence is also unique among mass-conserving energy-inequality weak solutions of section 9 on a sufficiently short interval about the common initial time. The lifespan may depend on the initial profile, not only its norm.

**Proof.** Write K=||D^p u||₂² and H(u)=K/2+gamma||u||_b^b/b. First note a compactness principle: if f_n is bounded in H^p, f_n→f in L², and limsup E(f_n)≤E(f), then f_n→f in H^p. Weak H^p convergence follows from the L² limit; the lower moment converges by strict subcritical interpolation. Both terms of H are weakly lower semicontinuous by the continuous critical Sobolev embedding, and limsup H(f_n)≤H(f). Thus the two nonnegative terms converge separately, yielding strong convergence of D^p f_n in L² by Hilbert norm convergence. The same reasoning works for variable f_n and a fixed reference f.

Every global energy-admissible weak solution from section 9 satisfies ||u_t||_H^-p≤C(B) when ||u||_H^p≤B: use the equation, critical Sobolev embedding and the two dual nonlinear bounds. Hence ||u(t)-u(t')||₂≤C(B)|t-t'|^(1/2) by interpolation. This is uniform for weak solutions with common mass and energy upper bounds. The compactness principle now implies strong H^p convergence to the initial profile as t→0. More generally, if a family of such solutions has initial profiles g with ||g-f||₂ small, E(g)≤E(f)+o(1), and uniform H^p bound, then on uniformly short intervals about their initial times they stay arbitrarily close to f in H^p. Otherwise a sequence of violating times and profiles with L² errors and time lengths tending to zero contradicts the compactness principle. This only gives a uniform time near a fixed profile.

For uniqueness, let Y(I)=L∞L² ∩ L²L^b ∩ L^(q_r)L^(r+1), with q_r=4p(r+1)/(d(r-1))>2. The pure dispersive bound and Keel–Tao retarded endpoint estimates (decay exponent d/(2p)>1) apply between these pairs, including the double endpoint; the L¹L² forcing bound follows by Minkowski and the homogeneous estimates. For any two bounded H^p distributional solutions u,v set h=u-v. For R>0 write
T_R(u)=||u 1_(|u|>R)||_b.
The difference bound for F_s, splitting the coefficient |u|^(s-1)+|v|^(s-1) into bounded and high-amplitude parts, gives
||h||_Y ≤ C||h(t0)||₂
 + C[ |I| R^(s-1) + |I|^(1-2/q_r) B^(r-1)
       + esssup_I(T_R(u)^(s-1)+T_R(v)^(s-1)) ] ||h||_Y.
Here the constants include beta,gamma and the fixed exponents; high-amplitude coefficients lie in L∞L^(d/(2p)) because (s-1)d/(2p)=b. The weak trajectories lie in Y on bounded intervals, and the distributional equation gives the Duhamel identity as in section 3.1. The estimate holds from either endpoint. Choose a fixed rho>0 so that if both tail norms are at most rho, their combined coefficient contributes at most 1/4. For finite R and bounded B choose the interval length so that the first two terms contribute at most 1/4. Absorb to obtain an L² stability estimate. For strong trajectories tails are uniformly small on compact time intervals by compactness of the continuous L^b path. For energy-admissible weak solutions initially near a fixed f, the preceding compactness principle gives uniformly small tails on a sufficiently short interval: choose R so T_(R/2)(f) is small and use
T_R(g)≤2||g-f||_b+T_(R/2)(f).
This estimate follows by splitting where |f|≤R/2 and its complement.

Choose a global weak solution u from u0. For each t0 sufficiently close to zero choose another global weak solution v with v(t0)=u(t0). Both satisfy the uniform H^p bound by coercivity, mass M(u0), and E≤E(u0). Both remain uniformly close to u0 in L² for |t|,|t0| small by the uniform time modulus, and thus uniformly close in H^p by the compactness principle. The tail estimate above therefore identifies u and v on the interval joining t0 and 0. Applying the energy inequality of v at time 0 gives E(u0)≤E(u(t0)); the opposite inequality already holds. This proves energy equality on the whole short interval, not just almost everywhere. At every time on that interval, strong L² continuity and equality of energy, with the compactness principle at that time, give strong H^p continuity.

All strong distributional solutions are unique by the endpoint estimate locally, even if conservation was not built into their definition; compare with the just-constructed solution on their common interval and iterate. Thus conservation follows on the maximal strong lifespan by restarting. For continuous dependence, for u0,n→u0 in H^p use the common coercive bound, initial energy convergence and uniform time modulus to choose a common neighborhood of the initial profile on a common short interval. The same endpoint estimate yields uniform L² convergence there. Conservation and compactness then give uniform H^p convergence: otherwise select violating times t_n→t and apply the compactness principle with f=u(t). Finite iteration along any compact segment of the maximal lifespan gives the stated dependence. The maximal solution is the union of locally unique strong solutions. QED.

## 13. Exact critical continuation criterion and positive energy defect

**Theorem 13.1.** Suppose u is the maximal strong solution of Theorem 12.1 with finite upper endpoint T. There is a unique L² trace f=lim_(t↑T)u(t), and u(t) converges weakly in H^p to f. Its mass is M(f)=M(u0), and its energy defect
D=E(u0)-E(f)
is nonnegative. There is a constant D_*>0 depending only on the equation parameters and d,p, not on u0 or T, such that D≥D_* at every genuine finite endpoint. The same holds backward.

Proof. The uniform H^p bound by coercivity and uniform L² modulus give the trace, mass and weak convergence; lower semicontinuity and the strictly subcritical lower term give D≥0. For any sequence t_n↑T, extract a subsequence on which u(t_n)→f almost everywhere (strong L²), and apply the Brezis–Lieb lemma to the b-moment, and the Hilbert-space weak convergence identity to the kinetic term. The r+1 moment converges by interpolation. Hence
D = (1/2)||D^p(u(t_n)-f)||₂² + gamma/b ||u(t_n)-f||_b^b + o(1).
In particular limsup_(t↑T)||u(t)-f||_b^b≤bD/gamma (apply the subsequence argument to a sequence attaining the limsup).

Choose rho as in section 12 and D_*=(gamma/b)(rho/8)^b. If D<D_*, then by choosing R large enough for the tail of f and restricting sufficiently close to T, we obtain sup T_R(u(t))<rho via the tail inequality in section 12. Let v be the local strong solution from f at T. Its tails also satisfy this bound on a sufficiently short interval by strong continuity. The weak extension of u to T has the same L² trace f and obeys Duhamel with terminal value f: integrate the equation to T in H^-p, and use the L² trace and endpoint Strichartz (all dual forcing norms are finite on bounded intervals). Apply the backward endpoint uniqueness estimate to u,v on [T-epsilon,T]. Their initial-at-T difference is zero. Thus u agrees with v, giving a strong extension past T and contradicting maximality. This proves the positive defect bound. The proof for the lower endpoint is identical in the opposite time direction. QED.

The following are therefore equivalent for continuation through a proposed finite endpoint of a strong solution with bounded conserved mass and energy:
(i) strong H^p continuation;
(ii) zero energy defect at the L² trace;
(iii) lim_(R→∞) limsup_(t↑T) T_R(u(t))=0;
(iv) a sufficiently small tail bound (T_R≤rho for some R on a final interval).
For (ii) use the compactness principle and restart, or the defect proof; (iii) implies (iv); (iv) implies continuation by the backward endpoint comparison; and strong continuity implies (ii),(iii). At a genuine finite endpoint, limsup T_R≥rho for every finite R (with rho decreased if necessary), so a positive amount of the critical nonlinear moment concentrates at arbitrarily high amplitude. This is not unbounded H^p norm.

**Corollary 13.2 (small shifted energy).** If E(u0)+CM(u0)<D_*, with C from section 2, the maximal strong solution is global: the lower bound E(f)≥-CM(u0) excludes a defect of size D_* at any finite endpoint. In particular this holds for sufficiently small ||u0||_H^p by Sobolev embedding. No restriction on the lower exponent beyond 1<r<s.

**Corollary 13.3 (finite number of potential strong breakdowns in a weak continuation).** For every critical datum there exists a global mass-conserving, weakly H^p-continuous and strongly L²-continuous evolution, strong and energy-conserving except at a finite set of times in each time direction. Construct it forward by solving the maximal strong problem, and at any finite endpoint restart the local strong problem from its unique L² trace. At every restart the energy decreases by at least D_*; all segments conserve the same mass M. Since E≥-CM, at most floor((E(u0)+CM)/D_*) forward restarts are possible. Construct the backward evolution analogously (energy decreases along reversed time). The concatenated path solves the distributional equation, since the L² traces agree and no distributional jump term appears, and remains bounded in H^p by the same coercive estimate. This is an existence and upper bound on possible singular restarts, not evidence any such restart actually occurs; it does not prove global strong existence. No arbitrary weak solution is claimed to have monotone energy.

## 14. Restricted large-data critical theorem via the pure defocusing flow

**Theorem 14.1 (analytical transfer).** Let d>2p, critical s≥2, and 1+2/d≤r<s. Suppose the pure defocusing equation i w_t=A w+gamma F_s(w) has a global H^p strong flow (in a fixed symmetry class, if desired) whose critical norm ||w||_(L^(2s)(R×R^d)) is bounded uniformly by a function of the initial H^p bound, and whose solutions satisfy the local differentiated Strichartz regularity used below. Then the original mixed-sign equation has global strong energy well-posedness in that class for arbitrary H^p data. The radial class is allowed because the multipliers and nonlinearities preserve radial symmetry. This transfer does not assume global scattering for the mixed equation.

Concrete p=2 instances: Pausader, arXiv:0807.4916 (d=8, cubic, uniform bound via section 5/Corollary 5.1 and the rigidity argument), and Miao–Xu–Zhao, arXiv:0807.0692, Theorem 1.1 (d≥9, uniform critical scattering bound), supply the pure-flow input. Pausader, DOI 10.4310/DPDE.2007.v4.n3.a1, Proposition 8.1 and Theorem 1.1 supply the radial input for d≥5 at pure dispersion. The local Strichartz regularity is part of the respective pure local theory. Their opposite dispersion sign is transformed by time reversal or conjugation, and positive gamma is normalized by multiplying the field by gamma^(1/(s-1)). Thus the transfer gives arbitrary data for p=2, 8≤d≤12, 1+2/d≤r<s=1+8/(d-4), and arbitrary radial data for p=2, 5≤d≤12 with the same exponent restriction. The upper dimension restriction is precisely s≥2. No claim is made for d≥13 or 1<r<1+2/d by this estimate.

Proof details. Write D=|∇|, q=2s, 1/b1=1/q+1/d and k=2d/(d+2). Define
Z_J(z)=||z||_(L^q(J×R^d))+||∇z||_(L^q(J;L^b1)),
S_J(z)=||D^p z||_(L∞(J;L²))+Z_J(z).
The linear estimate for i z_t=A z+G is
S_J(z)≤C(||D^p z(a)||₂+||∇G||_(L²(J;L^k))).
For clarity, this follows from the derivative-gain free bound ||D^(p-1) U(t)h||_(L²_t L^(2d/(d-2))_x)≤C||h||₂. On a unit frequency annulus stationary phase gives dispersive decay (1+|t|)^(-d/2), Keel–Tao gives the Schrödinger endpoint, scaling to frequency N supplies gain N^(p-1), and Littlewood–Paley square summation uses both mixed exponents≥2. Duality yields the full-time L² bound for the D^(p-1) forcing, and the ordinary polyharmonic Strichartz estimate gives the desired output for D^p z. Restriction to retarded integration is allowed by Christ–Kiselev since q>2 (and the L∞L² output directly by duality on truncated intervals). Riesz transforms replace D G by ∇G. Sobolev applied to D^p z in L^q L^a, with 1/a=1/q+p/d, gives both terms of Z; the pair satisfies 2p/q+d/a=d/2. All spatial exponents are strictly between 1 and infinity. This is a derivative gain argument, not an assumed smoothing of the nonlinear equation.

For s≥2 the pointwise first-derivative difference bound gives
||∇(F_s(v)-F_s(w))||_(L²L^k)
≤ C (Z_J(v)+Z_J(w))^(s-1) Z_J(v-w).
Indeed 1/2=s/q and 1/k=(s-1)/q+1/b1; DF_s is locally Lipschitz with difference ≤C(|v|+|w|)^(s-2)|v-w|. For r≥1+2/d, interpolate between L^q L² and L^q L^q for v, and between L^q L² and L^q L^b1 for ∇v, with a common interpolation parameter chosen so the spatial reciprocal sum of r factors equals 1/k. At the low end r/2≥1/k, at the high end (r-1)/q+1/b1<1/k. Hölder in time gives
||∇F_r(v)||_(L²L^k)≤ C |J|^theta (B+Z_J(v))^r,
theta=(s-r)/(2s)>0,
whenever |J|≤1 and ||v||_L∞H^p≤B. Only a first derivative of F_r is used, valid for every r>1. The missing low-r cases cannot be included by this interpolation.

The pure-flow critical bound gives a uniform Z bound L(B): partition its critical L^q norm into finitely many small pieces; apply the linear estimate and ||∇F_s(w)||≤C||w||_L^q^(s-1)||∇w||_L^qL^b1 to absorb the derivative term, using pure positive energy to bound ||D^p w||₂. Sum the finite pieces. This uses the pure local differentiated regularity, not a claim that bounded H^p alone controls Z.

Construct smooth-cutoff approximants to the mixed equation. Let P_N be a real, radial, smooth Fourier cutoff with symbol in [0,1], equal to 1 on |xi|≤N and zero on |xi|≥2N. Use
i u_N'=A u_N+P_N(gamma F_s(P_N u_N)-beta F_r(P_N u_N)),
u_N(0)=P_N u0.
On the bandlimited L² subspace this is a locally Lipschitz ODE; mass is conserved and the Hamiltonian is E_N=K/2+integral[gamma|P_N u_N|^b/b-beta|P_N u_N|^(r+1)/(r+1)]. Both identities use selfadjointness of P_N; it need not be idempotent. The same absorption bound and initial H^p convergence give a uniform H^p bound B' depending only on the datum's H^p bound. The approximants are global. Smooth cutoff convolution operators are uniformly bounded on all the indicated L^a spaces. On every compact time slab each approximant has finite S and the S norm on a growing compact subinterval depends continuously on its right endpoint (including the L∞ kinetic term).

Take w the pure solution with the same initial datum. For a slab [0,h] with h≤1, partition into at most J_*(B) intervals with Z_J(w)≤zeta, where zeta is a small fixed constant. On any such interval subtract the equations and use the two nonlinear estimates and the linear estimate. Let z=u_N-w and let e_N→0 bound ||(P_N-I)w||_Z on the slab and ||∇(P_N-I)F_s(w)||_(L²L^k) there; these converge by the approximate identity property and the pure spacetime norms. One obtains
S_J(z)≤ C||D^p z(a)||₂ + C e_N
 + C(zeta+S_J(z)+e_N)^(s-1)(S_J(z)+e_N)
 + C h^theta(B'+zeta+S_J(z)+e_N)^r.
All constants can be taken independent of the cutoff and the particular pure solution under its uniform bounds; e_N only needs to tend to zero for the fixed w. Choose zeta and a bootstrap ceiling epsilon small enough to absorb the third term whenever S_J(z)≤epsilon. Then under the bootstrap
S_J(z)≤C_0(||D^p z(a)||₂+e_N+h^theta C_B).
Choose h=h(B)>0 so that h^theta C_B is smaller than epsilon/[10(1+C_0)^(J_*+1)] and choose N large so the initial error and e_N satisfy the same inequality. Iterate the estimate over the finitely many pieces and use continuity to close the bootstrap. The result is a uniform bound sup_[0,h]||D^p(u_N-w)||₂≤epsilon. Epsilon can be chosen arbitrarily small before h is fixed, in particular so the homogeneous Sobolev bound makes the L^b difference smaller than rho/8 from section 12. The time h depends only on the initial H^p bound and the equation parameters. No convergence in the differentiated norm is asserted.

Take a weak compactness limit of these approximate solutions as in section 9, now with the smooth cutoff: ||(P_N-I)u_N||₂≤C N^(-p)B', so local convergence and weak nonlinear convergence hold for P_N u_N as well. Transfer the outer cutoff to test functions. The mass chain rule and lower semicontinuity for E_N+CM(u_N) (nonnegative shifted integrand for P_N u_N, with M(u_N)≥M(P_N u_N)) give mass equality and E(u(t))≤E(u0). For each time, weak lower semicontinuity preserves the homogeneous difference bound to w. Hence u stays within rho/8 in L^b of the pure continuous path. Its tails on [0,h] are uniformly small by compactness of w's L^b path and the tail inequality. At each time t0, construct the local strong solution from u(t0) via section 12; its tails are small by continuity on a sufficiently short interval about t0. The endpoint uniqueness estimate identifies the weak limit and this strong solution locally, in both directions. Thus the weak limit is strong and energy-conserving throughout the slab (including strong endpoint traces). Iterating slabs of the uniform length h(B) using the original conserved energy and mass produces global strong dynamics. The backward argument is identical. Continuous dependence on compact time intervals follows from Theorem 12.1. QED.

This proof isolates two genuine outstanding analytical obstructions: for s<2 a Hölder difference derivative requires an appropriate weaker critical perturbation metric; for r<1+2/d the spatial integrability of the one-derivative lower-power source is insufficient for the chosen forcing norm. The transfer also requires a pure-flow uniform bound, not currently supplied for arbitrary p≥3 or nonradial fourth-order d=5,6,7. These cases, and whether any genuine critical singularities exist, remain open in this dossier; no global novelty assertion is made.

## 15. Verification update

The previous seven Lean roots are not yet verified at the current head; the prior head's catalogue and Markdown checks passed, while Lean checks were queued/running or cancelled upon supersession. New candidate Lean lemmas encode the finite energy-drop counting inequality and its application to the actual finite-energy Hamiltonian. The analytic critical local dynamics, endpoint estimates, defect quantization and transfer theorem themselves are not formalized. A full formal solution still requires these and the previous analytic proof chains. No closure or accepted registry promotion.
