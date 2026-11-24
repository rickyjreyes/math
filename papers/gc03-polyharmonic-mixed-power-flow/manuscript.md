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


## 16. Removing the lower-power integrability restriction by time regularity

The restriction r>=1+2/d in section 14 is a limitation of its particular spatial-gradient forcing norm, not a physical or mathematical critical exponent. This section supplies an alternative, using fractional time regularity and the energy bound. All assertions below are analytical and require independent review; no new kernel-certified PDE theorem is asserted.

### 16.1 Sharp obstruction to the unmodified forcing estimate

Let k=2d/(d+2), let phi be a nonzero nonnegative flat smooth compact bump with ∇F_r(phi) not identically zero, and choose disjoint translates phi_j. Set g_N=N^(-1/2) sum_(j=1)^N phi_j. For each integer p the H^p norms of g_N stay bounded by disjoint support of the weak derivatives. For every a>=2, both ||g_N||_a and ||∇g_N||_a stay bounded. In contrast
||∇F_r(g_N)||_k=N^(1/k-r/2)||∇F_r(phi)||_k.
For 1<r<1+2/d the exponent is positive. Taking g_N constant in time also gives a counterexample to the uniform one-derivative forcing estimate on any fixed nonzero time interval, even with all the spatial Z norms of section 14 bounded. This is not a counterexample to well-posedness; these test paths need not solve the equation.

### 16.2 A time-Sobolev Duhamel lemma

Let A=(-Delta)^p, U(t)=exp(-itA), and let J be an interval of length ell<=1. Suppose F:J→L² is in H^(1/2)(J;L²) with sup_J||F||₂≤B_F. Define
[F]_(1/2,J)^2=integral_J integral_J ||F(t)-F(t')||₂²/|t-t'|² dt dt'.
Then
||D^p integral_J U(-t)F(t)dt||₂
 <= C (||F||_(L²(J;L²))+sqrt(ell)[F]_(1/2,J)).
This is an estimate on the interaction-picture increment, not a general smoothing assertion for arbitrary L¹L² forcing.

Proof. By a time translation and scaling to [0,1], and taking the spatial Fourier transform, reduce to the scalar integral against exp(i Lambda tau), Lambda=ell|xi|^(2p). For scalar f∈H^(1/2)(0,1) one has
|integral_0^1 exp(i Lambda tau)f(tau)dtau|
 <= C (1+|Lambda|)^(-1/2)||f||_(H^(1/2)(0,1)).
Indeed extend f to H^(1/2)(R) by bounded reflection extension and smooth cutoff. The zero-extended test 1_[0,1] exp(-i Lambda tau) has H^(-1/2)(R) norm at most C(1+|Lambda|)^(-1/2): its Fourier transform is a translate of the transform of the interval indicator, bounded by C min(1,|omega-Lambda|^-1) up to sign convention. For |Lambda|>=2 split |omega|>=|Lambda|/2, whose weighted integral of the squared transform is O(1/|Lambda|) by Plancherel, and |omega|<|Lambda|/2, whose integral is O(log(2+|Lambda|)/|Lambda|²). For smaller Lambda use the L² bound. Duality proves the scalar estimate. Multiply by ell |xi|^p≤sqrt(ell)(1+|Lambda|)^(1/2) and integrate over xi. Spatial Plancherel and Fubini identify the integrated scalar H^(1/2) norm with ell^-1||F||_(L²(J;L²))²+[F]_(1/2,J)². This proves the claimed increment estimate. The L² increment is bounded directly by ell B_F.

A further elementary estimate supplies the needed fractional time regularity. If u∈L∞(J;H^p) and u_t∈L∞(J;H^-p) with bounds B,K, respectively, then
[u]_(1/2,J;L²) ≤ C sqrt(ell B K).
For rigor, reflect u on J to a periodic interval of length 2ell. The reflected function is in L²_t H^p intersect H¹_t H^-p; reflection introduces no jumps in H^-p by its time continuity. Its normalized Fourier coefficients u_n obey
sum_n |n| ||u_n||₂²
 ≤ C ell (sum_n ||u_n||_(H^p)²)^(1/2)
          (sum_n (|n|/ell)²||u_n||_(H^-p)²)^(1/2)
 ≤ C ell B K.
Here use the pivot inequality ||f||₂²≤||f||_(H^p)||f||_(H^-p), Cauchy–Schwarz, and Parseval for Hilbert-valued periodic functions. The periodic H^(1/2) seminorm controls the interval seminorm (its double-integral kernel is comparable to the inverse square of periodic distance). Equivalently rescale to the fixed unit circle; the order-1/2 seminorm is scale invariant in one time dimension.

If G:C→C is globally Lipschitz with G(0)=0, then F=G(u) satisfies B_F≤Lip(G)B and [F]_(1/2,J)≤Lip(G)[u]_(1/2,J). Consequently for every subinterval J of length ell<=1,
||integral_J U(-t) G(u(t))dt||_(H^p)
 ≤ C Lip(G) [sqrt(ell)B+ell sqrt(BK)].
All statements also hold with u replaced by a uniformly H^p/H^-p bounded Fourier cutoff of u and G(u) followed by an L²-contracting, time-independent Fourier multiplier.

This gives the retarded response L(t)=integral_a^t U(t-t')G(u(t'))dt' in C(I;H^p) for I=[a,a+h], h<=1: the interaction-picture path has H^p increments bounded as above, and U is strongly continuous. It also gives, for every nonendpoint homogeneous Strichartz output norm ||D^p L||_(L^q L^a) with q>2 and 2p/q+d/a=d/2,
||D^p L||_(L^q(I;L^a)) ≤ C Lip(G)(B+sqrt(BK)) sqrt(h).
Here is the triangular decomposition argument. Partition I dyadically. Up to a null set, each pair a<=t'<t<=a+h belongs to a unique pair of adjacent left/right halves of a dyadic interval (their first differing dyadic digit). At level j there are 2^j disjoint right halves of length h/2^(j+1). On each right half the contribution from the paired left half is a free solution with interaction-picture datum integral_left U(-t')F(t')dt'. Its H^p norm is bounded by C sqrt(h/2^(j+1))(B+sqrt(BK))Lip(G). Homogeneous Strichartz and the disjoint time supports give a total level norm bounded by C sqrt(h) 2^(-j(1/2-1/q))(B+sqrt(BK))Lip(G). The geometric series converges precisely for q>2. The sum equals the retarded integral in distributions: finite partial sums omit only the thin diagonal region, whose L∞L² contribution tends to zero by the L∞L² forcing bound. Thus it has the claimed mixed-norm estimate. The L∞H^p bound already follows from the increment estimate. Spatial Sobolev embedding yields both terms of Z_I in section 14 for q=2s>2. This proof neither assumes u is a classical solution nor differentiates G in space.

### 16.3 Splitting the lower nonlinearity

Choose smooth radial amplitude cutoff chi equal to 1 for |z|≤1 and zero for |z|≥2. Put G(z)=chi(z)F_r(z), H(z)=(1-chi(z))F_r(z), so F_r=G+H. G is globally Lipschitz since r>1 and it is C¹ compactly supported, with G(0)=0. Set r0=max(r,1+2/d); in the critical case r0<s, since s-1=4p/(d-2p)>2/d. On the support of H and its derivative, |z|≥1, so |DH(z)|≤C |z|^(r0-1). The high-amplitude gradient estimate of section 14 is now valid for all r, with r0 replacing r:
||∇H(u)||_(L²(I;L^k)) ≤ C h^theta (B+Z_I(u))^r0,
theta=(s-r0)/(2s)>0.
This follows by precisely the interpolation used there; when r0=1+2/d, use its low spatial endpoint r0/2=1/k. For bounded critical H^p weak solutions the equation bounds u_t in H^-p by K(B). This applies uniformly to the smooth-cutoff Galerkin approximants of section 14 as well because P_N is H^-p-contracting, P_N u_N is uniformly H^p-bounded, and the Sobolev dual estimates are uniform. By section 16.2, the low-amplitude response, including its coefficient -beta and factor -i, obeys
||L||_(C(I;H^p))+Z_I(L)≤C_B sqrt(h).
This resolves the low-power forcing obstruction without requiring any artificial spatial integrability of G(u) below L².

### 16.4 Critical differentiated local regularity and continuation for all real powers

For every p>=1, d>2p and 1<r<s=s_E, the maximal strong solution of section 12 has finite Z_J on each compact subinterval J of its lifespan. Here Z is the sum of the two finite-time-exponent norms in section 14. Further, finite Z_[0,T) implies strong continuation at any finite T.

Proof of local differentiated regularity. Use the smooth Fourier cutoff Galerkin Hamiltonian of section 14; it yields uniform H^p bounds B and derivative-in-time H^-p bounds K(B). Its low-amplitude Duhamel response is uniformly bounded in Z by C_B sqrt(h). For a finite interval I=[0,h], the one-derivative linear estimate of section 14, the elementary chain rule ||∇F_s(v)||_(L²L^k)≤C Z_I(v)^s (valid for all s>1), and the high-amplitude estimate give
Z_I(u_N) ≤ Z_I(U(t)P_Nu0)+C Z_I(u_N)^s+C h^theta(B+Z_I(u_N))^r0+C_B sqrt(h).
All cutoff constants are uniform by smooth multiplier boundedness. For fixed u0 the free term tends to zero as h→0 by homogeneous Strichartz and absolute continuity, uniformly for large N by H^p convergence of P_Nu0. Choose a small bootstrap ceiling zeta with C zeta^s≤zeta/4, then h small so the other terms below the ceiling sum to less than zeta/2. Each approximant has finite continuous Z norm on expanding subintervals (bandlimited and H^p-continuous), hence Z_I(u_N)≤zeta. The weak compactness construction of section 14 passes to an energy-admissible weak solution, and reflexivity of the finite-exponent Z spaces preserves its Z bound. Its distributional gradient is identified by local distributional convergence. By section 12 weak-strong comparison near the initial profile, this limit agrees with the strong solution on a possibly shorter interval. Repeat around any time of the strong solution; a compact subinterval is covered by finitely many neighborhoods. This proves local Z regularity without differentiating the low-amplitude nonlinearity.

For the continuation implication, if the solution is bounded in H^p by conservation and Z_[0,T) finite, then ∇F_s(u) and ∇H(u) lie in L²([0,T);L^k). The dual derivative-gain estimate underlying section 14 implies
||D^p integral_a^b U(-t') (gamma F_s(u)-beta H(u))dt'||₂
 ≤ C ||∇(gamma F_s(u)-beta H(u))||_(L²([a,b];L^k)).
This tends to zero as a,b→T by absolute continuity. The low-amplitude increment tends to zero by section 16.2. The interaction-picture kinetic term is therefore Cauchy in L², while the L² trace already exists by section 13. Thus u has a strong H^p trace at T, and section 12 restarts it. This proves the necessary-and-sufficient finite critical spacetime norm criterion (on bounded time intervals). Conversely, a strong continuation gives finite Z on the compact extended interval by the local regularity just proved.

## 17. All-power fourth-order critical global theorem

**Theorem 17.1.** For p=2, every integer d>=8, all real 1<r<s=1+8/(d-4), beta,gamma>0, every H² datum has a unique global strong energy solution, continuously depending on the datum. For every d>=5 the same conclusion holds for radial H² data. The proof uses the uniform pure defocusing critical scattering results plus the time-regularity lemma. It is an analytical theorem pending independent review, not a novelty or Lean claim.

First, for arbitrary p where s>=2, the conditional pure-flow transfer in section 14 no longer needs r>=1+2/d: use the actual strong solutions with local Z regularity, and subtract the pure solution. Include the low-amplitude response as an additive C_B sqrt(h) in the S estimate, and use r0 in the high-amplitude term. The same finite interval subdivision and bootstrap works. Section 16.4 guarantees continuation of the actual strong solution if its Z bound persists to a proposed endpoint, so the argument no longer needs a Galerkin construction at this stage.

For fourth-order s<2 (d>12), use Pausader, "Global Well-Posedness for Energy Critical Fourth-Order Schrödinger Equations in the Radial Case", Dynamics of PDE 4 (2007), 197–225, Proposition 6.1 and (6.3). The stability proposition is not restricted to radial data; with epsilon=0 it supplies a uniform stability threshold depending on the approximate solution's critical Z and kinetic bounds, and yields closeness in W when the residual is small in N=||∇e||_(L²L^(2d/(d+2))) and the initial data agree. W is exactly the gradient part of our Z; homogeneous Sobolev bounds the undifferentiated critical L^(2s) norm by W. For d>12 its conclusion uses a positive Hölder exponent 15/(d-4)^2 in addition to the linear term. The result is used as a published theorem, not proved here. Its opposite sign convention is converted by complex conjugation. Its statement allows any real upper coefficient, so gamma>0 is legitimate after sign conversion, or normalize gamma by field scaling. The pure scattering bound is Miao–Xu–Zhao, JDE 251 (2011), 3381–3402, Theorem 1.1 for d>=9, and Pausader's radial theorem in d>=5. For d=8 use Pausader's cubic paper as in section 14. The pure Z bound including W follows by the partition argument of section 14.

Here are the details of the perturbation with the low-amplitude response removed. Let u be the maximal strong mixed solution, starting at an arbitrary time a, and let w be the pure defocusing solution with the same initial profile. By conservation both have uniform H² bounds in terms of B=||u(a)||_H², with the mixed bound provided by section 2. Let I=[a,a+h] intersected with its strong lifespan, h<=1. Define L to solve the linear equation i L_t=A L-beta G(u), L(a)=0, and v=u-L. By section 16.2, ||L||_C H²+Z_I(L)≤C_B sqrt(h). Then
i v_t=A v+gamma F_s(v)+e,
e=gamma(F_s(u)-F_s(v))-beta H(u).
The derivative of F_s is Hölder of order alpha=min(1,s-1) with the standard weighted difference estimate
|DF_s(x)-DF_s(y)|≤C|x-y|^alpha (|x|+|y|)^(s-1-alpha).
This follows from homogeneity and the derivative formula away from zero, splitting whether |x-y| is at least half of the larger amplitude; if smaller apply the mean-value bound away from zero. Thus
||∇(F_s(u)-F_s(v))||_(L²L^k)
 ≤ C (Z_I(u)+Z_I(v))^(s-1) Z_I(L)
 + C (Z_I(u)+Z_I(v))^(s-1-alpha) Z_I(L)^alpha Z_I(v).
The estimate follows by Hölder with q=2s and 1/k=(s-1)/q+1/b1. Consequently on any subinterval [a,t] with Z_[a,t](u)≤A0 fixed, ||∇e||_(L²L^k) is bounded by
C_(B,A0) (h^theta + sqrt(h) + h^(alpha/2)),
uniformly for all such t. No derivative of G was estimated in the critical forcing space.

Let L_B bound the pure full Z norm (including W) by the cited pure global theorem. Choose A0=2(L_B+1). On a compact initial interval on which the bootstrap Z(u)≤A0 holds, the approximate v has a uniform kinetic bound and critical Z bound A0+1 for h sufficiently small. It starts exactly at u(a). Choose the stability parameter Λ=1 in Proposition 6.1, so the initial mismatch is zero. The stability threshold and output constants may be taken uniform under the stated bounds (as in the proof via finite subdivision of the approximate critical norm). For h=h(B)>0 sufficiently small the residual bound is below this threshold and the resulting W(v-w) is as small as desired. The proposition's exact solution must be w by uniqueness of the pure strong flow. In particular, homogeneous Sobolev gives Z(v-w)<1/2, and Z(L)<1/2 after reducing h. Thus Z(u)<L_B+1<A0. The local regularity of section 16.4 ensures continuity of Z on expanding compact intervals and its vanishing at their initial time, so the bootstrap holds until min(a+h,T_max). If a finite maximal endpoint T_max≤a+h existed, monotone convergence would give finite Z up to T_max, contradicting section 16.4. Hence the mixed solution exists on a uniform slab of length h(B) (and backward as well). Repeat using the uniform conserved-energy H² bound. This proves the theorem for all d>=8 arbitrary data and d>=5 radial data, including the previously excluded very low focusing powers and the high-dimensional Hölder critical nonlinearity.

## 18. Prior-art correction and remaining frontier

A closer existing result was identified: Junyong Zhang and Jiqiang Zheng, "Energy critical fourth-order Schrödinger equations with subcritical perturbations", Nonlinear Analysis 73(4) (2010), 1004–1014, DOI 10.1016/j.na.2010.04.027. The accessible manuscript's Theorem 1.1 states global H² well-posedness for exactly d=8, critical cubic upper term defocusing, arbitrary real lower-power coefficient and lower exponent 0<a<2 in |u|^a u (our r=a+1). This is the exact GC03 d=8 critical slice after sign convention conversion. Credit the prior theorem as stated; do not claim this slice as original research. Its accessible transcription of Lemma 2.2 appears to use a spatial-gradient forcing estimate over the whole lower-power range; section 16.1 shows such an estimate cannot hold uniformly for arbitrary test functions when a<1/4. The typeset publisher proof was not accessible during this review, so no assertion of a published error is made. The independent argument in sections 16–17 does not rely on that estimate. The result in d>=9 or radial d>=5 is a proof transfer from existing pure-flow and stability theorems; novelty remains unassessed.

The fourth-order critical large-data slice is now covered in every dimension with the verified pure uniform critical bound: all d>=8, radial d>=5, every lower real exponent. No matching arbitrary-data pure uniform bound was located for d=5,6,7 in this focused literature search. Higher integer dispersion orders p>=3 still require a suitable pure critical uniform bound (and a higher-order counterpart of the Hölder stability estimate when s<2). The argument of sections 16–17 is conditional for those orders; it does not certify those missing inputs. The general subcritical, weak, and supercritical statements remain as before. Strong supercritical individual-data classification remains unresolved, even though universal energy-class well-posedness fails.

The new time-Sobolev lemma is the key proof contribution of this revision. Its proof and the perturbative transfer require independent mathematical review and are not yet Lean-formalized. The Lean addition only checks the scalar exponent threshold arithmetic behind the separated-bump obstruction and the cutoff exponent. No promotion of GC03, issue closure or novelty claim. CI for the preceding head was queued when checked; local Lean/Lake unavailable.

### References for sections 16–18

- B. Pausader, Dynamics of PDE 4 (2007), 197–225, Proposition 6.1, especially the high-dimensional stability estimate: https://doi.org/10.4310/DPDE.2007.v4.n3.a1
- C. Miao, G. Xu, L. Zhao, J. Differential Equations 251 (2011), 3381–3402, pure defocusing uniform bound d>=9: https://arxiv.org/abs/0807.0692 ; https://doi.org/10.1016/j.jde.2011.08.009
- B. Pausader, The cubic fourth-order Schrödinger equation, JFA 256 (2009), 2473–2517: https://arxiv.org/abs/0807.4916
- J. Zhang, J. Zheng, exact d=8 mixed equation, Nonlinear Analysis 73 (2010), 1004–1014: https://doi.org/10.1016/j.na.2010.04.027 ; accessible manuscript https://doczz.net/doc/7839286/the-energy-critical-fourth-order-schr%C3%B6dinger-equations-with


## 19. General-order critical stability below the Lipschitz derivative threshold

**Analytical result, pending independent review.** The conditional large-data transfer of sections 14 and 17 extends to every integer p>=1, every d>2p, and every 1<r<s=s_E. The only additional pure-flow input needed is a uniform critical spacetime bound for bounded initial H^p data. For s>=2 the earlier first-derivative stability estimate suffices. This section supplies the missing Hölder-critical stability for d>6p, so 0<alpha=s-1=4p/(d-2p)<1. It adapts classical exotic Strichartz and fractional chain-rule methods, rather than claiming novelty of those methods.

Use D=|∇|, U(t)=exp(-it(-Delta)^p), a_*=d/2-p, b_*=2d/(d-2p), q=2s, and k=2d/(d+2). Write Z and S as in section 14, with S=||D^p u||_(L∞L²)+Z. The derivative-gain linear estimate there also controls every nonendpoint admissible output ||D^p u||_(L^Q L^R), Q>2, 2p/Q+d/R=d/2, by initial kinetic norm and ||∇e||_(L²L^k) for a forcing e. The same observation was used in section 16.

### 19.1 Fractional stability metric for every order

Choose sigma=alpha/4 and a number kappa satisfying
0<kappa<min(sigma/(2p),alpha/(2q),1/8).
Set theta=1-kappa and define
A0=alpha/kappa, B0=d alpha/(2p theta),
A=2p/(sigma-p kappa), B=2d/(d-2p theta),
1/C=1/A+kappa, 1/B'=1-1/B.
These choices give A0>q, A>q, 1<C<A<∞, 2<B<∞,
2p/A0+d/B0=a_*,
2p/A+d/B=a_*+sigma,
and alpha/B0=1-2/B, alpha/A0=kappa.
Let B1 and L1 be defined by 1/B1=1/B0+1/d and 1/L1=alpha/B0+sigma/d. Also let 1/Btilde=1/B-sigma/d. All spatial exponents used in the following fractional product and Sobolev estimates are strictly between 1 and infinity: d>6p, sigma<1/4, B0>b_*, and d/B-sigma>0. The scale-invariant norms are
X_I(h)=||D^sigma h||_(L^A(I;L^B)),
Y_I(e)=||D^sigma e||_(L^C(I;L^(B'))),
V_I(v)=||v||_(L^A0(I;L^B0))+||∇v||_(L^A0(I;L^B1)).
In particular V_I(v)<=C ||D^p v||_(L∞L²)^(1-q/A0) Z_I(v)^(q/A0) by time-space interpolation and homogeneous Sobolev. Both components use the same interpolation parameter, since 1/B1=1/B0+1/d.

The free kernel estimate of section 3 implies, by interpolation with L² unitarity,
||U(t)f||_B<=C|t|^(-theta)||f||_(B').
Indeed d/(2p)(1-2/B)=theta. Fractional integration in time of order kappa=1-theta gives
X_I(integral_a^t U(t-t')e(t')dt')<=C Y_I(e).
This holds directly for retarded integration, since the time integrand is dominated by the positive convolution kernel |t-t'|^(-theta), and 1/A=1/C-kappa. It does not need a retarded endpoint estimate or a generalized Foschi theorem. The free initial evolution obeys X_I(U(t-a)h0)<=C||D^p h0||₂: apply the ordinary admissible estimate at time exponent A to D^p h0 and spatial Sobolev of order p-sigma, using 2p/A+d/B=a_*+sigma. The derivative-gain forcing estimate similarly controls X_I of a retarded response by ||∇e||_(L²L^k), even if Y_I(e) is not known. The spatial Sobolev inequality also gives ||h||_(L^A L^Btilde)<=C X_I(h).

For F(z)=|z|^alpha z, its real derivative DF is globally alpha-Hölder and |DF(z)|<=C|z|^alpha. We claim
Y_I(F(v)-F(w))<=C(V_I(v)+V_I(w))^alpha X_I(v-w).
To check this, apply the real fundamental theorem of calculus along the line between v and w; it suffices to estimate DF(z)h with z=w+lambda(v-w) and h=v-w, uniformly in lambda in [0,1]. At each time use the fractional product rule:
||D^sigma(DF(z)h)||_(B')
 <= C ||z||_(B0)^alpha ||D^sigma h||_B
   + C ||D^sigma DF(z)||_(L1) ||h||_(Btilde).
Both exponent identities follow from 1/B'=alpha/B0+1/B and 1/L1+1/Btilde=1/B'. For the second term use the Hölder fractional chain rule of Visan, in the standard formulation with sigma/alpha<tau<1, and take tau=1/2. Put lambda0=sigma/tau=alpha/2, 1/Btau=1/B0+tau/d. The rule gives
||D^sigma DF(z)||_(L1)
 <= C ||z||_(B0)^(alpha-lambda0) ||D^tau z||_(Btau)^lambda0
 <= C ||z||_(B0)^(alpha-lambda0) ||∇z||_(B1)^lambda0.
For the first inequality choose the Hölder exponents P1=B0/(alpha-lambda0), P2=Btau/lambda0; they satisfy 1/P1+1/P2=alpha/B0+sigma/d. The stronger standard condition (1-lambda0/alpha)P1>1 also holds, since its left side is B0/alpha>1. The second inequality is fractional integration of ∇z, with 1/Btau=1/B1-(1-tau)/d. These are precisely the fractional-power hypotheses, not a second derivative bound at zero. Apply spatial Sobolev to h and Hölder in time, using alpha/A0=kappa=1/C-1/A. This proves the claim. Reference: Visan's fractional chain rule for Hölder functions (Appendix A of her energy-critical NLS work; see also the Oberwolfach lecture notes, Lemmas A.6 and A.8, https://www.math.ucla.edu/~visan/Oberwolfach2012.pdf, printed pp. 56–57). The chosen exponents meet even the stronger condition in the original thesis https://www.math.ucla.edu/~visan/thesis.pdf.

### 19.2 Return from fractional to energy stability

Let v,w be respectively an approximate and an exact pure defocusing critical solution on a compact interval I, satisfying the distributional equations
i v_t=Aop v+gamma F(v)+e, i w_t=Aop w+gamma F(w),
where Aop=(-Delta)^p, and assume a common bound Bbig on the sum of their L∞ kinetic norms and Z norms. Suppose ||∇e||_(L²L^k)<=epsilon, and the initial homogeneous H^p mismatch is at most epsilon. The solutions must have strong energy traces and the finite critical norms just stated; for the mixed application these are provided by section 16, not assumed for an unknown supercritical flow.

Partition I into finitely many intervals J on which the sum of the Z norms is small enough that C(V_J(v)+V_J(w))^alpha<=1/2. This is possible with the number of pieces bounded in terms of Bbig and the equation parameters, by interpolation above and additivity of the q-th powers of the finite-time-exponent norms. For h=v-w, the fractional estimate and the linear estimates imply
X_J(h)<=C(||D^p h(a_J)||₂+epsilon).
These norms are finite: apply the derivative-gain estimate for time exponent A to v,w using ||∇F(v)||_(L²L^k)<=C Z(v)^s, and the residual, then spatial Sobolev. Thus the absorption is legitimate.

To control the undifferentiated difference in the original critical norm, choose Q1=(q+2)/2, and 1/R1=(a_*-2p/Q1)/d. Since d>6p, R1 is finite and positive. The derivative-gain estimate and Sobolev give
||h||_(L^Q1 L^R1)<=C_Bbig
on I (assuming epsilon<=1). The underlying D^p admissible spatial reciprocal is 1/R1+p/d, and Q1>2. Interpolate this bound with ||h||_(L^A L^Btilde)<=C X_J(h). Because Q1<q<A and both pairs lie on 2p/Q+d/R=a_*, interpolation gives
||h||_(L^q(J×R^d))<=C_Bbig X_J(h)^nu
for some fixed 0<nu<1.

Use the pointwise Hölder derivative estimate on the difference:
||∇(F(v)-F(w))||_(L²L^k)
 <= C Z_J(v)^alpha Z_J(h)
   + C ||h||_(L^q(J×R^d))^alpha Z_J(w).
Take the subdivision small enough also to absorb the first term in the derivative-gain S estimate. Then
S_J(h)<=C_Bbig (d_J+epsilon+(d_J+epsilon)^(alpha nu)),
where d_J=||D^p h(a_J)||₂.
The endpoint kinetic mismatch for the next interval is bounded by S_J(h). Finite iteration proves a modulus of stability tending to zero with epsilon, uniformly for approximate and exact trajectories obeying Bbig. This gives a genuine small-error stability estimate for all p when s<2, not the invalid direct inequality S<=epsilon+small*S^alpha. No global critical spacetime theorem is being assumed in deriving stability.

Combine this result (and the s>=2 case) with the low-amplitude response subtraction of section 17. For a mixed strong solution, remove L solving iL_t=Aop L-beta G(u) with zero initial value on a slab; its H^p and Z bound is C_B sqrt(h) for h<=1. The adjusted v=u-L has residual with one-gradient norm tending to zero as h→0 under any fixed Z bootstrap ceiling, by the high-amplitude estimate and the pointwise Hölder derivative estimate of section 17. Apply the stability modulus above on the bootstrapped interval, with the pure solution w of the same initial datum. This closes the same Z bootstrap, gives uniform positive slab length whenever the pure flow has a uniform critical bound, and iterates using conservation. Hence for every p>=1 and every critical real lower exponent, the pure-flow uniform critical bound suffices for mixed strong global well-posedness. The earlier missing higher-order Hölder perturbation input has now been reduced to standard fractional calculus plus the linear estimates in this dossier. The missing pure-flow spacetime bounds themselves have not been supplied.

## 20. The uniform mixed-slab property is equivalent to the pure critical spacetime bound

This is a useful exact reduction, not an equivalence between mere pointwise-in-datum global existence of the two equations.

Fix p,d,r,s critical and positive beta,gamma. For bounded sets of initial H^p data (or their radial subsets), consider:
(P) the pure defocusing strong flow exists globally and has a uniform finite Z_R bound on each bounded set;
(M) there exist h(B)>0 and L(B)<∞ such that the mixed strong flow from every datum of H^p norm ≤B exists on [0,h(B)] and has Z_[0,h(B)]≤L(B).
Theorems in sections 17 and 19 imply P=>M, even for 1<s<2. Conversely M=>P, by critical scaling and the same stability argument.

Proof of necessity. For f in the bounded set, choose N→∞ and f_N(x)=N^a_* f(Nx). For N>=1 its H^p norm is bounded by the original H^p bound: the homogeneous kinetic norm is unchanged and mass norm is multiplied by N^-p; equivalently the Fourier inhomogeneous weight decreases after change of variables. Apply (M) to f_N. Rescale the mixed solution back to v_N, defined on [0,N^(2p)h(B)], with initial profile f. Its lower coefficient becomes beta eta_N, where eta_N=N^(-a_*(s-r))→0, and its upper coefficient remains gamma. Both components of Z are invariant under critical scaling; thus Z(v_N)≤L(B), uniformly on its whole rescaled interval. Conservation and the absorption estimate, uniformly for eta_N<=1, give bounded H^p norm in these rescaled variables as well (mass is that of f, not that of f_N).

Let w be the pure maximal strong solution from f (use section 12 with beta=0, whose proof remains valid). For any fixed compact forward interval [0,T] in its lifespan, all large N cover that interval. On unit subintervals the time-Sobolev lemma bounds the low-amplitude response by O(eta_N), and on the whole fixed interval its C H^p and Z norms tend to zero by finite summation and the homogeneous propagation estimate. The high-amplitude residual gradient is also O(eta_N) under the uniform Z and energy bounds. After subtraction of the low-amplitude response the remaining upper-power residual gradient tends to zero by the weighted Hölder derivative estimate of section 17 (for s>=2 use alpha=1 there). Apply section 19 stability or its s>=2 counterpart to the adjusted trajectory and w on [0,T], with constants allowed to depend on T and the finite Z norm of w there. Their initial mismatch is zero. Hence Z_[0,T](w)<=L(B) by passage to the limit. The right side is independent of T and of f in the bounded set. If the pure maximal forward endpoint were finite, this uniform bound and section 16.4 continuation would contradict maximality. Thus it is infinite and Z_[0,∞)(w)<=L(B). Conjugation with time reversal gives the backward estimate, since the coefficients and symbol are real and conjugation preserves the norm and radiality. This proves (P).

Consequently an elementary uniform lifespan bound in the mixed critical energy ball, together with uniform Z control, would also solve the corresponding pure defocusing critical spacetime problem; it is not a shortcut around that problem. Neither (P) nor (M) follows merely from bounded kinetic energy. Nor does failure to establish (M) prove that any individual solution fails to be global.

## 21. General-order concentration and localized mass rigidity

### 21.1 A necessary concentrating profile at a finite strong endpoint

Let u be any maximal mixed critical strong solution from section 12, with finite endpoint T, L² trace f, and bounded H^p norm. The tail criterion of section 13 yields a sequence t_n→T for which ||u(t_n)-f||_(b_*)≥c>0 (choose thresholds tending to infinity; use T_R(g)≤2||g-f||_(b_*)+T_(R/2)(f)). Set g_n=u(t_n)-f. Then ||g_n||₂→0, ||D^p g_n||₂ is uniformly bounded, and ||g_n||_(b_*) is bounded below.

Use a smooth dyadic annular partition P_N with N in 2^Z, and the refined Sobolev inequality
||g||_(b_*) <= C ||D^p g||₂^(2/b_*) [sup_N N^(-a_*)||P_N g||∞]^(1-2/b_*).
For completeness, write B0tilde for the bracket and M for the Hardy-Littlewood maximal operator. At any point where the maximal function of D^p g is finite, split the dyadic sum at N. Its low frequencies are bounded by C B0tilde N^a_* and the high ones by C N^-p M(D^p g), since each annular D^-p multiplier is N^-p times a rapidly decaying convolution kernel dominated by the maximal operator. Optimize over dyadic N. The bound becomes C B0tilde^(p/(a_*+p)) M(D^p g)^(a_*/(a_*+p)). The case B0tilde=0 is trivial, and a vanishing maximal function gives g=0 at the point by the same split. Raising to b_* and using the L² maximal theorem proves the inequality, first on Schwartz functions and by approximation on the homogeneous energy space (or directly by convergence of the dyadic reconstruction in L^(b_*)). This is the usual Gérard–Meyer–Oru refined embedding, not a new Sobolev theorem.

There exist scales N_n and locations x_n such that
N_n^(-a_*) |P_(N_n) g_n(x_n)|≥c1>0.
Bernstein gives the upper bound C N_n^p ||g_n||₂, so N_n→∞. Define
G_n(y)=N_n^(-a_*) g_n(x_n+y/N_n).
The sequence is bounded in homogeneous H^p. Pass to a weakly convergent subsequence G_n⇀G. The linear functional G↦P_1 G(0) is continuous on homogeneous H^p by annular Fourier localization and Cauchy-Schwarz; its values on G_n have modulus ≥c1. Hence G≠0. On bounded balls the lower derivatives of G_n are bounded in L² by homogeneous Sobolev and Hölder, giving local H^p compactness into L² by Rellich. Thus G_n→G in local L² after a subsequence. The rescaled contribution of f tends to zero in local L² (indeed in L^(b_*)) because its b_*-moment is absolutely continuous on sets of shrinking measure, uniformly in the centers x_n.

It follows that a hypothetical finite endpoint necessarily has a nonzero concentration profile extracted from the actual solution, with radii R/N_n→0. For some finite R and c2>0,
liminf_n N_n^(2p) integral_(B(x_n,R/N_n)) |u(t_n,x)|² dx >= c2,
and by Hölder a positive amount of the critical b_*-moment lies in these balls. This does not assert that all energy is captured by that profile, that x_n converges, or that the rescaled profile itself solves a limiting dynamical equation. The latter needs time-dependent profile decomposition and stability.

### 21.2 Localized mass rigidity, any integer order

Consider a nonzero pure critical trajectory on [0,T) with finite T, bounded homogeneous H^p norm B, strong local energy regularity, and the pure Hamiltonian equation. The following also applies to the mixed trajectory whenever it is H^p and the lower term is defined. Let chi be a nonnegative smooth radial cutoff equal to one on the unit ball, zero outside the radius-two ball, with 0<=chi<=1, and let m_R(t)=integral chi((x-x0)/R)|u(t,x)|² dx.

The local mass is absolutely continuous on compact time intervals and
|m_R'(t)| <= C_p,d,chi B²
uniformly in R>0 and x0. To prove this without assuming global L² for the homogeneous pure case, use a smooth auxiliary cutoff identically one on the support of chi_R; it puts u in local H^p and its time derivative in local H^-p by the equation and critical dual Sobolev embedding. The Hilbert-pivot chain rule yields the weighted mass derivative. The nonlinear terms give no real contribution to u_t paired with chi_R u, because all coefficients and chi_R are real. Expand the kinetic form by the multi-index identity
<D^p u,D^p v> = sum_(|mu|=p) (p!/mu!) <partial^mu u,partial^mu v>.
The term with all derivatives on u in partial^mu(chi_R u) is real and vanishes from the imaginary part. Each remaining product, with j>=1 derivatives on chi_R, has magnitude bounded by
C ||partial^mu u||₂ ||partial^(mu-nu)u||_(2d/(d-2j)) ||partial^nu chi_R||_(d/j),
where |nu|=j. The middle norm is controlled by B by homogeneous Sobolev of order j, and the cutoff norm is independent of R by scaling. This gives the asserted bound (d>2p ensures every exponent is legitimate). When u is globally H^p, an alternative bound uses both differentiated factors in L² and cutoff derivatives in L∞, giving O(R^-1)||u||_(H^p)² for R>=1. This proof covers all integer orders, including higher than biharmonic. Compare Pausader's fourth-order local mass identity (Dynamics of PDE 4 (2007), Lemma 7.1), which is a prior-art instance.

Suppose additionally that there is a sequence t_n↑T and centers x_n such that for every epsilon>0 some finite L and all sufficiently large n obey
integral_(|x-x_n|>L/N_n) |u(t_n,x)|^(b_*) dx <= epsilon,
where N_n→∞. This is a full critical-moment concentration hypothesis, satisfied for instance by a trajectory precompact modulo translations and critical dilations along a concentrating sequence. Then for every fixed ball B(x0,2R), its local L² mass tends to zero: the part inside the concentrating ball is bounded by C B² (L/N_n)^(2p) by Hölder, and the part outside it by C_R epsilon^(2/b_*). Send n→∞ and then epsilon→0. Thus m_R(t_n)→0, and the uniform local mass derivative bound yields m_R(t)≤C B²(T-t) for each t<T, independently of R. Taking R→∞ proves that u(t) is globally in L² even in the homogeneous pure formulation, with mass at most C B²(T-t). Now use the improved large-R flux estimate on compact time intervals; the H^p norms are uniformly bounded there since mass was just bounded. Letting R→∞ proves global mass conservation on [0,T). Sending t→T forces this mass to be zero. This contradicts nonzero u.

This rules out a nonzero entire concentrating critical profile with finite lifespan at every integer dispersion order. For an inhomogeneous mixed trajectory it is also immediate from the strong L² trace and conservation once full concentration is assumed. The proof does NOT exclude a finite-time concentration of only part of the critical energy while a nonzero mass-carrying background remains. To use it as a complete rigidity theorem one must first construct a minimal finite-time bad solution with the full concentration property, or exclude background-plus-bubble scenarios by other means. Standard minimal nonscattering compactness is not automatically a minimal finite-time construction; lower-energy global nonscattering profiles can prevent a uniform-spacetime induction. No such missing reduction is assumed here.

## 22. Updated frontier and verification

Sections 19–21 complete the analytic general-order conditional perturbation argument, isolate its necessary uniform pure-flow input, and provide a quantitative inverse-Sobolev concentration and local-mass rigidity step. They do not establish the missing pure critical spacetime bound or the full concentration property for a general hypothetical finite-time endpoint.

Focused literature search: the fourth-order arbitrary-data pure defocusing results in d>=8 (Pausader and Miao–Xu–Zhao) and radial d>=5 remain the matched inputs. The search did not locate a matching arbitrary-data theorem for d=5,6,7, nor an all-order critical uniform theorem for p>=3. A 2026 preprint on fourth-order potential scattering (Nakayama, arXiv:2603.13892) is radial and does not remove these nonradial gaps. This is a search result, not certification that those questions are globally open. The local-mass result has a classical fourth-order antecedent; novelty of general-order formulation is unassessed.

Remaining proof target: develop a critical dynamic profile decomposition and a valid finite-time minimal-element reduction with the mass-carrying background handled, or prove the required pure uniform Z bounds directly. The global classification in previously established parameter regimes is unchanged. Individual-data supercritical strong dynamics and full Lean PDE certification are also open.

No new scalar Lean lemma is added simply to raise declaration counts. Existing eleven candidate audit roots must actually compile before any certification. The maintained lean.yml workflow already runs lake build and the transitive audit with standard-axiom allowlist. The latest inspected head had all its jobs queued; no verified GC03 build or audit exists in this record. This environment has no lean/lake executables and cannot resolve github.com for a local clone; connector commits are not kernel verification. Keep GC03 candidate and issue #100 open.


## 23. Terminal-background subtraction and a faster-than-dispersive concentration scale

All results below concern the exact mixed GC03 critical equation, with integer p>=1, d>2p, b=s+1=2d/(d-2p), 1<r<s, beta,gamma>0. They are analytical, pending independent review and Lean formalization. Denote the pure positive critical energy by P(g)=||D^p g||_2^2/2+gamma||g||_b^b/b.

Suppose a maximal strong solution u has a genuine finite forward endpoint T. Section 13 gives f=lim_(t↑T)u(t) strongly in L² and weakly in H^p, and D=E(u0)-E(f)>=D_*>0. By section 12, there is a strong mixed solution w near T with w(T)=f. Restrict to a compact left neighborhood of T and define h=u-w and m(t)=||h(t)||_2². Then h is uniformly H^p bounded, h→0 in L², and h⇀0 in H^p. Moreover
lim_(t↑T) P(h(t))=D.
For the kinetic term use the Hilbert-space norm expansion, weak convergence of u and strong convergence of w to f. For the critical moment take any time sequence approaching T, extract an a.e. convergent subsequence using L² convergence, apply Brezis–Lieb with f, and replace u-f by h using ||w-f||_b→0. Uniform b-bounds ensure the error in the b-th powers tends to zero. The lower moment converges by strict subcritical interpolation. Since the argument applies to every time sequence, the positive residual energy has the stated full limit, not only a liminf. This identifies the finite endpoint energy defect with the entire residual pure critical energy, after subtracting the regular solution.

### 23.1 Residual mass estimate

For a>1 put F_a(z)=|z|^(a-1)z. The following exact cancellation holds for complex z,y and h=z-y:
Im(conj(h)(F_a(z)-F_a(y))) =
 (|z|^(a-1)-|y|^(a-1)) Im(conj(h)y).
In particular the part of a power nonlinearity acting on h alone contributes no mass derivative. By splitting |h|<=|y|/2 and its complement, the right side is bounded in absolute value by
C_a (|y|^(a-1)|h|²+|y||h|^a).
For 1<a<=2 it is bounded by C_a |y|^(a-1)|h|² alone: on the complement use |h|^(a-2)<=C|y|^(a-2), with y=0 handled separately by the exact identity. The first region uses the scalar mean-value bound away from zero. This avoids any second derivative of F_a at zero.

Apply the H^p⊂L²⊂H^-p chain rule to h on compact subintervals of the strong lifespan. Its kinetic contribution to m' vanishes, while the two nonlinear difference contributions are bounded by the pointwise estimates above with y=w, z=u, and a=r,s. For each a, w is a compact continuous path in L^(a+1) up to T, so sup_t ||w(t)1_(|w(t)|>R)||_(a+1)→0 as R→∞. Also h is uniformly bounded in L^(a+1) by critical Sobolev. On the high-amplitude region of w, Hölder bounds both integrals by constants times powers of this uniformly small tail. On the low-amplitude region the first term is at most R^(a-1)m(t). If a<=2 the improved pointwise bound suffices. If a>2 the second term is at most R||h||_a^a→0 by interpolation of the vanishing L² norm and the bounded L^(a+1) norm. Thus esssup_(t in (T-epsilon,T)) |m'(t)|→0 as epsilon→0. The derivative is bounded near T, the trace of m is zero, and integration gives
m(t)=o(T-t).
This argument controls the difference from the actual backward-evolved background, not necessarily the difference from the time-independent trace f.

In section 21's inverse-Sobolev concentration extraction one can replace u(t_n)-f by h(t_n), because their difference is w(t_n)-f→0 strongly in H^p. Thus some R,c>0 and N_n→∞, x_n∈R^d satisfy
N_n^(2p) integral_(B(x_n,R/N_n)) |h(t_n)|² dx >= c
for all large n. Since this is at most N_n^(2p)m(t_n), the mass estimate implies
N_n^(2p)(T-t_n)→∞.
The natural concentration radius is therefore little-o of (T-t_n)^(1/(2p)). This excludes critical self-similar rates for any nonzero extracted residual concentration profile. It does not exclude faster concentration or a partial bubble.

### 23.2 Bounded terminal background: additional conditional exclusion

If w is uniformly essentially bounded in space on a left neighborhood of T and s<=2, both pointwise bounds reduce to C m(t); hence |m'|<=C m, with m(T)=0. Backward Gronwall yields m identically zero there. Then u=w and the endpoint was not genuine. Therefore a genuine endpoint with 1<s<=2 cannot have a bounded strong backward background. This is a conditional regularity exclusion, not a claim that every H^p terminal trace yields a bounded background. In particular d>=6p is precisely the critical range s<=2.

If w is uniformly bounded and s>2, the same calculation gives |m'|<=C m^(1/(s-1)) for m<=1. Indeed for 2<a<=s, interpolation yields ||h||_a^a<=C m^(1/(a-1)); the bound for a<=2 is linear. Integrate the differential inequality backwards using (m+epsilon)^(1-1/(s-1)) and send epsilon↓0 to get
m(t)<=C (T-t)^((s-1)/(s-2)).
Thus every extracted residual concentration scale in this bounded-background case satisfies
N_n^(-2p)<=C (T-t_n)^((s-1)/(s-2)).
No global regularity theorem is inferred for s>2.

## 24. A nonzero global homogeneous pure weak profile at any finite critical endpoint

Use the residual h and the nonzero profile extraction above. After passing to a subsequence define
h_n(tau,y)=N_n^(-a_*) h(t_n+tau/N_n^(2p),x_n+y/N_n),
w_n(tau,y)=N_n^(-a_*) w(t_n+tau/N_n^(2p),x_n+y/N_n),
a_*=d/2-p.
Because N_n^(2p)(T-t_n)→∞, both endpoints of the rescaled left-neighborhood time interval tend to the corresponding infinities. Hence every fixed compact tau interval lies in the rescaled domains eventually. The rescaled residual equation is
i ∂_tau h_n=A h_n + gamma[F_s(h_n+w_n)-F_s(w_n)]
 - beta N_n^(-a_*(s-r))[F_r(h_n+w_n)-F_r(w_n)].
The energy P(h_n(tau)) tends uniformly on every compact tau interval to D by the full residual energy limit and critical scaling invariance. In particular h_n is uniformly bounded in homogeneous H^p and L^b. On bounded spatial balls this controls local H^p norms, by the homogeneous Sobolev embedding for each derivative of order j<p and local Hölder. The same uniform homogeneous bound holds for w_n. On each fixed compact space-time cylinder, w_n tends to zero in L∞_tau L^b_y: the corresponding physical balls shrink uniformly in their centers, and the continuous L^b path of w is compact and has uniformly absolutely continuous b-th moment. The lower coefficient tends to zero and the lower nonlinear terms are bounded on compact cylinders in L^((r+1)/r).

For completeness, apply a fixed smooth spatial cutoff to h_n. The cutoff functions are bounded in L∞_tau H^p, and their time derivatives are bounded in L∞_tau H^-p by the equation tested against cutoff H^p functions: the kinetic term is estimated using the global homogeneous H^p bound, the critical nonlinear terms by L^(b/s) duality, and the lower terms by local L^((r+1)/r) duality. Interpolation gives equicontinuity in L². Rellich plus Arzela–Ascoli on bounded spatial balls, followed by diagonal extraction over compact time intervals and balls, yields a limit H in C(R;L²_loc) with weakly continuous homogeneous H^p representative. The latter follows from the uniform homogeneous bound, local L² convergence at all times, and uniqueness of any weak limit in the homogeneous space represented in L^b. On compact cylinders take an a.e. convergent subsequence; boundedness and reflexivity yield weak convergence of F_s(h_n+w_n) to F_s(H) in L^(b/s), while F_s(w_n)→0 there. The lower terms vanish in distributions. Thus
i H_tau=(-Delta)^p H+gamma F_s(H)
on all of R×R^d in distributions. At tau=0 the nonzero profile from section 21 is preserved by the local strong L² convergence, so H is not the zero function. For every tau, lower semicontinuity and the rescaled residual energy bounds give P(H(tau))<=D. No assertion of equality, global L² membership, strong homogeneous H^p continuity, or scattering is made for this limiting weak solution.

This is a dynamical extraction from the actual background-subtracted mixed solution, rather than a static concentration witness. Its full time axis follows from the strictly faster-than-dispersive rate, not from assuming a pure global flow. It does not yield a contradiction: a nonzero global weak pure trajectory with bounded homogeneous energy is consistent with defocusing dynamics. A stronger profile decomposition and a no-return/rigidity estimate are still needed to exclude this scenario.

## 25. Pure scattering threshold is a lower bound on every mixed critical endpoint defect

Define E_c as the supremum (possibly infinity) of levels e>0 for which all pure critical defocusing data g∈H^p with P(g)<=e have a global strong flow and a uniform full critical Z_R bound depending only on e and the fixed equation parameters. Equivalently the uniform property can be imposed on forward times and then reflected by conjugation. This is an energy-only property, not a statement that mere individual global existence implies uniform scattering. The levels form a downward-closed set. The small-data positive-energy theory gives a nonempty interval: homogeneous free Strichartz and the Z bootstrap of section 16.4 with beta=0 yield a global small-kinetic Z bound and the continuation criterion, with no mass dependence. If the matched pure global theorem gives uniform bounds for bounded H^p norm, critical scaling of g down to smaller mass without changing kinetic energy or Z implies the energy-only property (using the pure equation's exact scaling and uniqueness).

**Theorem.** At any genuine finite strong endpoint of the mixed critical equation, its defect D satisfies D>=E_c. If E_c=infinity there can be no such endpoint. In particular the mixed strong flow is global whenever E(u0)+C M(u0)<E_c, with C the coercivity constant.

Proof. Suppose D<E_c. Choose e with D<e<E_c for which the pure uniform property holds (downward closure and the definition of supremum). The background w and residual h of section 23 satisfy P(h(t))→D, so P(h(a))<=e for every a sufficiently close to T. For such a let z be the pure strong solution from h(a). Its global Z bound is at most L(e), uniformly as a→T. Its kinetic bound follows from positive pure conservation; its mass equals that of h(a) by pure conservation. Both h and w have bounded H^p near T, and w has finite Z on a compact neighborhood of T with Z_[a,T](w)→0 as a→T.

On [a,t] with a<=t<T, bootstrap Z(h)<=2(L(e)+1). The residual equation before scaling is
i h_t=A h+gamma F_s(h)+gamma [F_s(h+w)-F_s(w)-F_s(h)]
 - beta[F_r(h+w)-F_r(w)].
Split F_r=G+Hhigh as in section 16.3, with globally Lipschitz low component G. Let L solve i L_t=A L-beta[G(h+w)-G(w)] with L(a)=0. Apply the time-Sobolev lemma to u=h+w and w individually, using their uniform H^p and H^-p time derivative bounds. Thus ||L||_(C H^p)+Z(L)<=C sqrt(T-a), uniform over the bootstrap intervals. Set v=h-L. Its equation is pure critical plus a residual e_res, consisting of the upper-power replacement F_s(h)-F_s(v), the upper-power cross term F_s(h+w)-F_s(h)-F_s(w), and the high-amplitude lower differences. Their one-gradient L²_t L^k_x norm tends uniformly to zero as a→T:
* replacement: the weighted Hölder derivative estimate of section 17 with h-v=L and the fixed Z ceiling;
* cross term: the same estimate with (h+w)-h=w, plus ||∇F_s(w)||_(L²L^k)<=C Z(w)^s;
* lower terms: section 16.3 with (T-a)^theta and the bounded Z norms of h+w and w.
All constants are uniform under the H^p bound and the bootstrap ceiling. The approximate solution v starts exactly at h(a), has bounded kinetic norm and Z, and the pure solution z has uniform kinetic and Z bounds. Apply section 19's stability modulus (or the s>=2 estimate) to compare v with z. Taking a sufficiently close to T gives Z(v-z)<1/2, Z(L)<1/2, and hence Z(h)<L(e)+1, strictly below the ceiling. Local Z regularity and continuity on expanding compact intervals close the bootstrap up to T. Therefore Z_[a,T)(u)<=Z(h)+Z(w)<∞, which contradicts the finite endpoint continuation criterion of section 16.4. The backward proof is identical. Finally E(f)>=-C M(f)=-C M(u0) implies D<=E(u0)+C M(u0), proving the small shifted-energy statement relative to the pure threshold.

A useful individual form does not assume a uniform theorem over all pure data: if there exists a sequence a_j↑T such that the pure strong solutions launched from h(a_j) exist through T-a_j and have uniformly bounded Z there, the very same proof excludes the endpoint. Thus any genuine endpoint forces failure of this pure residual-slab bound along every such sequence. It is not necessary to solve the pure scattering problem at the energy of the original mixed solution: it suffices to solve it at the energy actually lost in the weak limit. Nevertheless, if the missing pure threshold is finite, this does not prove that defects >=E_c cannot occur.

## 26. Updated research frontier, prior art and verification

The present revision gives a background-subtracted mass-decay law, a faster-than-dispersive necessary concentration rate, a global homogeneous pure weak profile extracted at an endpoint, and a lower bound on the endpoint defect by the pure critical scattering threshold. The bounded-background exclusion for s<=2 is conditional. No unconditional extension to the remaining large-data critical dimension/order regimes is claimed. The necessary remaining argument is to rule out the pure residual-slab failure above the threshold, or prove the needed pure critical uniform bounds. In particular the global weak profile extracted in section 24 is not an almost-periodic minimal strong solution and cannot be fed into the full-concentration rigidity theorem as though it were one.

A renewed focused literature search located the existing pure d>=9 biharmonic arbitrary-data scattering result (Miao–Xu–Zhao, https://arxiv.org/abs/0807.0692), but not a matching result for nonradial d=5..7 or general integer p>=3. This is not a proof of open-problem status. The background subtraction and type-II-style rate have not undergone independent novelty review. No known supercritical pure blow-up construction can be imported into the exact mixed equation merely by calling the lower term subcritical; a separate robustness proof would be required. General individual-data supercritical strong classification remains unresolved.

A candidate Lean lemma checks the exact complex pointwise cancellation in section 23.1 for arbitrary real coefficients (hence for the power coefficients), with no PDE assumptions. The residual mass chain rule, concentration profile extraction, threshold perturbation and earlier general dynamics remain unformalized. CI was still queued/pending at inspection of the preceding head; no GC03 kernel pass or transitive axiom audit is asserted. Original statement, candidate status and open issue are preserved.


## 27. Translation-invariant interaction rigidity for the pure critical flow

**Theorem 27.1 (analytical, pending independent review).** Let d>2p, p a positive integer, s=1+4p/(d-2p), gamma>0. There is no nonzero strong solution of the pure defocusing equation
i u_t=(-Delta)^p u+gamma F_s(u)
on a forward-infinite time interval whose orbit is precompact in inhomogeneous H^p modulo spatial translations. More explicitly, there cannot be a function x(t) such that the closure in H^p of {u(t,·+x(t)): t≥0} is compact. No assumption on radiality, continuity of x(t), its speed, or its growth in time is needed. The same holds backward by conjugation. This theorem rules out a finite-mass, spatially and spectrally tight soliton-like critical element, not all almost-periodic homogeneous critical solutions.

### 27.1 Two-field commutator

Use relative coordinates r=x-y in R^d×R^d and the product U(t,x,y)=u(t,x)u(t,y). Let A2=(-Delta_x)^p+(-Delta_y)^p. The product solves
i U_t=A2 U+V U,
V(t,x,y)=gamma(|u(t,x)|^(s-1)+|u(t,y)|^(s-1)).
Write M=||u||_2², which is constant and positive if u is nonzero.

Choose a smooth vector function a(r) equal to r on |r|≤1, zero on |r|≥2. Let a_R(r)=R a(r/R), b_R(x,y)=(a_R(r),-a_R(r)), and
L_R=b_R·∇_(x,y)+(div b_R)/2, B_R=-i L_R.
L_R is skew-symmetric, B_R symmetric on smooth compactly supported functions. All derivatives of b_R of positive order up to p+1 are uniformly bounded for R≥1. The interaction action
J_R(t)=Re integral conj(U) B_R U
is well-defined on H^1(R^(2d)), and satisfies |J_R(t)|≤C R ||U||_2 ||∇U||_2+C||U||_2². The product map u↦u⊗u is continuous H^p(R^d)→H^p(R^(2d)) by the multi-index product formula and factorized integrals. In particular the action is bounded by C_B R on an H^p-bounded trajectory.

For smooth data, differentiation gives the kinetic contribution K_R=⟨U,[A2,L_R]U⟩ and the potential contribution -integral |U|² b_R·∇V. The kinetic form extends continuously to H^p: for each x or y multi-index mu of order p, the corresponding summand of K_R, with coefficient p!/mu!, is
2 Re integral conj(∂^mu U)[∂^mu,L_R]U.
Indeed the term involving L_R ∂^mu U has zero real part by skew symmetry. Expand the commutator as the sum over 0<nu≤mu of
binomial(mu,nu) [(∂^nu b_R)·∇∂^(mu-nu) U
                 +(∂^nu div b_R)∂^(mu-nu) U/2].
Every field factor has derivative order ≤p. This formula gives uniform boundedness of the quadratic form on H^p and is independent of the possibly large size of b_R itself. The multinomial expansion of the kinetic Fourier symbol gives exactly the sum of the separate x and y forms, not a mixed full Laplacian.

For the untruncated linear b_infty(x,y)=(x-y,y-x), define K_infty by the same commutator form with constant first derivatives. For Schwartz U, direct Fourier transformation of the dilation generator gives
K_infty(U)=integral∫ (ξ-η)·(∇aop(ξ)-∇aop(η)) |Uhat(ξ,η)|² dξ dη,
aop(ξ)=|ξ|^(2p),
in the angular-frequency Plancherel convention. Equivalently, differentiate the symbol aop(ξ)+aop(η) under the linear dual vector field with blocks (ξ-η,η-ξ). The divergence term cancels the Jacobian term. The integrand is nonnegative by convexity of aop (or integrate its positive semidefinite Hessian along the segment). It is bounded by C_p(|ξ|^(2p)+|η|^(2p))|Uhat|² by Young's inequality, so approximation extends positivity to H^p. No sign is asserted for the full truncated high-order commutator pointwise.

Because b_R and b_infty agree on |x-y|≤R, their differentiated coefficients in the form differ only outside this set. Cauchy–Schwarz on that region yields
|K_R(U)-K_infty(U)| ≤ C_p,a sum_(|mu|≤p) integral_(|x-y|>R) |∂^mu U|².
For an H^p orbit precompact modulo translations, the right side tends uniformly to zero as R→∞. In fact diagonal translation (x,y)↦(x+x(t),y+x(t)) leaves |x-y| unchanged, and the translated products form a precompact set in H^p(R^(2d)). For any compact set in H^p all finitely many derivative L² tails tend uniformly to zero (finite epsilon-net argument). Thus K_R≥-o_R(1) uniformly in time.

### 27.2 Repulsive nonlinear contribution and the rigidity contradiction

Using the real power derivative and integration by parts in x and y, the potential contribution is exactly
N_R=gamma (s-1)/(s+1) integral∫ (div a_R)(x-y)
 [|u(x)|^(s+1)|u(y)|²+|u(x)|²|u(y)|^(s+1)] dx dy.
For example |u(x)|²∇_x |u(x)|^(s-1)=(s-1)/(s+1)∇_x |u(x)|^(s+1). This identity is interpreted after integrating the derivative of the power; no differentiability at zeros of |u|^(s-1) alone is required. In the untruncated case div a_infty=d, so
N_infty=2 gamma d(s-1)/(s+1) M ||u||_(s+1)^(s+1).
The truncated difference is bounded by C times the same two density integrals restricted to |x-y|>R. This tends uniformly to zero under the compactness hypothesis. Indeed the translated orbit is compact in L² and L^(s+1) by critical Sobolev embedding. Both density families have uniformly vanishing spatial tails. On |x-y|>R at least one of the translated coordinates has modulus >R/2, so factorize the two tail bounds. Furthermore inf_t ||u(t)||_(s+1)>0: otherwise a sequence from the translated orbit converges strongly in H^p to a profile with L^(s+1) norm zero but mass M>0. Hence N_infty≥c0>0.

It follows for R sufficiently large but fixed that J_R'(t)≥c0/2 almost everywhere. Integrating over an arbitrarily long interval contradicts the bound |J_R|≤C_B R. This proves the theorem provided the action identity holds for the strong energy solution. The following approximation justifies it without assuming the solution is Schwartz.

### 27.3 Justification at critical energy regularity

On each compact time interval I of the strong pure lifespan, section 16.4 gives finite Z_I(u); the same proof applies with beta=0. Use the smooth Fourier cutoff P_N of section 14 and u_N=P_Nu. Then u_N→u in C(I;H^p) and in both Z components (uniform convergence on the compact C_t H^p path and approximate identities on the finite-exponent spaces). It satisfies a forced pure equation with e_N=gamma[P_N F_s(u)-F_s(u_N)]. The pointwise difference estimate gives e_N→0 in C(I;L^(b/s)), where b=s+1. The first-derivative difference estimate from section 17, valid with alpha=min(1,s-1), and the approximate identity property give ∇e_N→0 in L²(I;L^k), k=2d/(d+2). Indeed ∇F_s(u) belongs to this space by Hölder and the first-derivative chain rule. No high-order differentiation of F_s is used.

For each fixed N, u_N is spatially bandlimited, has arbitrary Sobolev regularity and is differentiable in L² with derivative in all Sobolev spaces, by the cutoff equation and dual energy estimate. In particular U_N=u_N⊗u_N has the regularity needed for the kinetic commutator computation. The nonlinear power term can be evaluated directly in the derivative of the action by the real first-derivative chain rule for F_s, which is C¹ for s>1, followed by integration by parts on the density |u_N|^(s+1). For example the real part of the two potential terms involving L_R(VU_N) and L_R U_N combines to -|U_N|² b_R·∇V in the region where u_N is nonzero; the combined expression extends as the derivative of the power density also at zeros. Alternatively expand the force gamma F_s(u_N)⊗u_N+gamma u_N⊗F_s(u_N) directly against B_R U_N; its integral yields N_R without ever forming an unweighted derivative of |u_N|^(s-1). Spatial integration by parts is justified by the integrable density and its first derivative (bandlimited L² and boundedness), using larger outer cutoffs and sending their radius to infinity.

The extra product force is E_N=e_N(x)u_N(y)+u_N(x)e_N(y). Its action derivative error is bounded after integration in time by C_R times
||∇e_N||_(L²(I;L^k)) ||u_N||_(L²(I;L^(k'))) sup_I||u_N||_2²
 + ||e_N||_(L¹(I;L^(b/s))) sup_I||u_N||_b
    sup_I(||u_N||_2²+||u_N||_2||∇u_N||_2),
where k'=2d/(d-2). To see this, in the e_N(x) term pair with B_R U_N. For the x derivative integrate it by parts onto e_N and b_R, and use spatial Hölder in x and the mass in y; for the y derivative apply Hölder in x and Cauchy–Schwarz to u_N(y)∇u_N(y). The zero-order divergence term is controlled by the second term. The symmetric product term is identical. For fixed R, b_R and its first derivatives are bounded; no product-space Sobolev inequality for exponent b is required. Critical H^p controls L^b and also L^(k') by H^1 embedding, so the bound tends to zero. The differentiated identity for U_N can be integrated in time; the action, kinetic form and potential expression converge uniformly on I by C_t H^p convergence, product continuity and density norm convergence. Passing to the limit gives
J_R(t2)-J_R(t1)=integral_(t1)^t2 [K_R(U(t))+N_R(u(t))]dt.
This completes the energy-regularity justification and the proof. It relies on the local critical theory and derivative-gain estimates of this dossier, which themselves remain analytical and not Lean-certified.

### 27.4 Scope, missing compactness and no shortcut through scaling

The theorem excludes nonzero pure critical traveling or stationary waves in the strong H^p class, since their orbits after a spatial translation and phase rotation are precompact (the phase circle is compact). It also excludes any globally defined pure critical minimal element once inhomogeneous compactness modulo translations has been proved, without any assumption on its center velocity. It does not apply to the mixed equation without additional control of the focusing contribution: that term enters N_R with the opposite sign, and mixed solitary waves are not ruled out.

The distinction between homogeneous and inhomogeneous compactness is essential. For any nonzero smooth compact bump phi, set g_lambda(x)=lambda^(d/2) phi(lambda x) as lambda→0. Then ||g_lambda||_2=||phi||_2 but ||D^p g_lambda||_2=lambda^p||D^p phi||_2→0. The family converges to zero in the homogeneous norm but is not precompact in L² even after arbitrary translations: on every fixed-radius ball its mass is bounded by a constant times lambda^d times the ball volume, uniformly over centers. Adding it to a fixed homogeneous profile leaves the homogeneous limit unchanged but can destroy inhomogeneous compactness. Thus a homogeneous critical profile decomposition is not by itself sufficient for the interaction rigidity theorem.

A precise sufficient upgrade is the following. Suppose a family of H^p profiles is precompact in homogeneous H^p after translations, and its low-frequency mass is uniformly small as the cutoff tends to zero:
lim_(epsilon↓0) sup_t integral_(|ξ|≤epsilon) |uhat(t,ξ)|² dξ=0.
Then it is precompact in H^p after the same translations. For a fixed epsilon, the high-frequency part is precompact in H^p by the bounded map from homogeneous H^p, while the low-frequency part is uniformly small in H^p by the displayed condition. Approximate by a finite epsilon-net and use completeness. More generally homogeneous compactness modulo dilations with scale bounded above and below implies homogeneous compactness modulo translations, since the critical dilation action is jointly continuous on a compact scale interval and a compact set. A uniform negative Sobolev bound ||D^(-a)u||_2≤C with some a>0 would supply the low-frequency mass condition by epsilon^(2a). None of these extra properties has been proved for the missing critical minimal elements, so the theorem does not resolve those cases.

## 28. Additional weak–strong uniqueness in the supercritical finite-energy space

For any integer p,d, any 1<r<s≤2, and X=H^p intersect L^(s+1), let u be a mass-conserving weak solution from section 9 and let w be a distributional solution with the same initial data, both in C_t L² intersect L∞_loc X and with time derivatives in L∞_loc X*. Assume w belongs to L^1_loc in time with spatial amplitude control in the precise sense
integral_I (||w(t)||_infty^(r-1)+||w(t)||_infty^(s-1))dt<∞
on each compact time interval I in its lifespan. Then u=w on the common lifespan interval containing the initial time. The assertion also holds for any two such distributional solutions satisfying the stated bounds; the energy inequality is not needed for the uniqueness step.

Proof. Apply the Hilbert-pivot chain rule on X⊂L²⊂X* to h=u-w; all nonlinear pairings are integrable by X membership, and the kinetic term cancels. The exact pointwise identity and improved bound for a≤2 in section 23.1 give
|d/dt ||h||_2²| ≤ C (||w||_infty^(r-1)+||w||_infty^(s-1)) ||h||_2²
almost everywhere. Gronwall in both directions gives equality of the two solutions from the common trace. This is an actual weak–strong uniqueness statement also in supercritical regimes where 1<s≤2, not a global regularity assertion about w. It strengthens the bounded terminal-background exclusion of section 23.2 by permitting time-integrable rather than uniform amplitude control.

## 29. Prior-art audit and remaining proof obligations

The new interaction argument uses the standard virial commutator method and convexity of the dispersion symbol. Fourth-order interaction Morawetz estimates already exist in the literature, for example Pausader's cubic fourth-order analysis (arXiv:0807.4916) and Miao–Xu–Zhao (arXiv:0807.0692). The present compact-orbit argument does not claim a new global positive interaction Morawetz estimate; its truncated commutator errors vanish only by the explicitly assumed compactness. No novelty or priority claim is made.

The renewed search identified Tarek Saanouni, "A note on the critical nonlinear high-order Schrödinger equation", J. Math. Anal. Appl. (2017), DOI 10.1016/j.jmaa.2017.02.024. Its stated critical scattering theorem (Theorem 2.4) requires small initial data and the paper imposes additional exponent/dimension conditions. Its subcritical global result is in Corollary 2.3. This does not supply the missing arbitrary-data pure critical uniform bound. The March 2026 preprint arXiv:2603.13892 concerns radial fourth-order dynamics with potential, not the missing nonradial dimensions. The focused search did not identify the required unrestricted pure theorem; this does not establish that none exists.

The remaining critical large-data obligations are now (i) obtain an actual minimal strong pure bad element via a homogeneous nonlinear profile decomposition and stability, (ii) exclude finite-time collapse, frequency cascade and/or prove sufficient low-frequency mass tightness, and (iii) apply the interaction rigidity theorem once inhomogeneous compactness is justified. The previous background-subtracted weak profile is not such a minimal strong element. For the mixed endpoint theorem it remains sufficient to control the pure flow at the defect energy. No new unconditional parameter slice is claimed in this revision. Individual-data supercritical strong classification also remains open beyond the weak–strong statement above.

Verification: do not add speculative Lean declarations just to increase counts. The twelve existing candidate GC03 roots have not received a successful kernel build or transitive audit in this record. The previous head's jobs remained queued at inspection. The full Lean workflow already includes this module and its dependency roots. A focused GC03 verification entry point is supplied separately, with explicit root and standard-axiom checking, to avoid depending exclusively on the entire portfolio build. Neither a workflow definition nor an audit script constitutes a successful run.


## 30. No-waste Duhamel and negative Sobolev regularity for general integer order

All results in this section are analytical, pending independent review and Lean formalization. Let p>=1 be an integer, d>2p, s=1+4p/(d-2p), b=s+1, a_*=d/2-p, and gamma>0. Write A=(-Delta)^p, U(t)=exp(-itA), F(z)=gamma |z|^(s-1)z, and P(u)=||D^p u||_2²/2+gamma||u||_b^b/b. A normalized compact orbit means that there exist scales lambda(t)>0 and centers x(t) such that
K=closure_{dot H^p}{ lambda(t)^(-a_*) u(t,x(t)+ · /lambda(t)): t in I }
is compact. The symbol lambda denotes frequency scale here; physical radius is of order 1/lambda. This is precisely the homogeneous compactness assumption, not an assertion of L² compactness. The results below do not construct a minimal element.

### 30.1 No-waste at both infinite endpoints

Suppose u is a global strong homogeneous pure solution, continuous into dot H^p and satisfying the Duhamel identity there on compact time intervals, with compact normalized orbit. Then
U(-T)u(T) ⇀ 0 in dot H^p as T→+∞ and as T→-∞.

Proof. It suffices to test against phi with smooth compact Fourier support in an annulus away from zero; these are dense in dot H^p. The homogeneous norm of u(T) is uniformly bounded by compactness and scaling. For any tolerance epsilon>0, compactness of K gives uniform smallness of its dot H^p Fourier tails near zero and infinity, using a finite net and strong convergence of frequency cutoffs. If lambda(T) is sufficiently small or sufficiently large, the Fourier mass of D^p u(T) on the fixed test annulus is therefore smaller than epsilon, independently of translation. Since U(-T) is unitary and preserves that annulus, the pairing with phi is small.

For the remaining times lambda(T) lies in a compact positive interval. Approximate the normalized profiles by finitely many Schwartz functions in dot H^p to within epsilon, possible by density and compactness. Rescale and translate each approximating function back to physical coordinates. Its L¹ norm is bounded uniformly in the bounded scale interval and is unaffected by translation. For each approximation g_T,
|<U(-T)g_T,phi>_{dot H^p}|=|<g_T,U(T)D^(2p)phi>|
 <= C |T|^(-d/(2p)) ||g_T||_1 ||D^(2p)phi||_1.
Use the polyharmonic dispersive estimate, with either time sign. The error in the pairing is at most epsilon||phi||_{dot H^p}. First send |T|→∞ and then epsilon→0. This proves the assertion, without a lower bound on lambda or any condition on the center's motion.

Consequently the Duhamel identity at each fixed t0 has both one-sided no-waste representations
u(t0)= weak-lim_{T→+∞} i integral_(t0)^T U(t0-t) F(u(t)) dt,
u(t0)= weak-lim_{S→-∞} (-i) integral_S^(t0) U(t0-t) F(u(t)) dt,
in dot H^p. The signs follow from i u_t=A u+F(u); they do not affect the subsequent absolute pairing estimate. These formulas are not asserted for general bounded homogeneous trajectories without compactness.

### 30.2 An exact sufficient integrability condition for negative regularity

**Theorem 30.2.** Under the assumptions of §30.1, suppose that for some 1<=q<2 the nonlinearity obeys
sup_t ||F(u(t))||_q <= B_F,
and put a=d(1/q-1/2). If a>2p, then
sup_t ||D^(-epsilon)u(t)||_2 < infinity
for every 0<epsilon<a-2p. In particular u has finite mass, uniformly tight at low frequencies, and is strongly continuous into H^p.

Proof. Let P_N be real smooth annular Fourier multipliers, N dyadic, with a bounded-overlap partition of unity away from zero and uniform cutoff derivative bounds by scaling. Each P_N maps dot H^p boundedly into L². Apply P_N to the two weak Duhamel representations and pair them in L², using successive weak limits. At t0=0 for convenience, the squared norm is bounded by the limsup of the integral over the forward/past quadrant of
|<P_N F(u(t)), U(t-t') P_N F(u(t'))>_{L²}|, t>=0>=t'.
The formula on finite rectangles is justified by the localized Duhamel identity, since P_N maps L^q into L² uniformly for fixed N. Measurability follows from the space-time representative of u and the finite-q integrability hypothesis. There are two bounds for this integrand:
C B_F² N^(2a), by the L^q-to-L² Bernstein estimate and unitarity;
C B_F² |t-t'|^(-a/p), by interpolation of the L¹-to-L∞ dispersive bound and L² unitarity, with smooth annular cutoffs uniformly L^q bounded.
Equivalently use the L^q-to-L^(q') bound on U(t-t')P_N². Both estimates include q=1 by Young's inequality and the L¹-to-L∞ dispersive estimate. Absolute integration of their minimum on the quadrant gives
||P_N u(0)||_2²
 <= C B_F² integral_0^∞ R min(N^(2a),R^(-a/p)) dR
 <= C_(a,p) B_F² N^(2a-4p).
The second integral converges because a/p>2; the crossover is R=N^(-2p). This absolute bound also justifies taking the two successive weak limits without exchanging an uncontrolled pair of limits. By time translation the result holds uniformly at every t0.

For N<=1 the bound on the L² norm is C B_F N^(a-2p); the squared dyadic sum after multiplying by N^(-epsilon) is finite for epsilon<a-2p. For N>1 the sum is controlled by the uniform homogeneous H^p norm, since N^(-2epsilon)<=N^(2p). Littlewood-Paley equivalence in L² then gives the stated homogeneous negative norm, using the canonical dot H^p representative in L^b (no polynomial component). In particular
integral_(|xi|<=delta)|uhat(t,xi)|² dxi <= delta^(2epsilon) ||D^(-epsilon)u(t)||_2²
uniformly in t. Interpolation between the negative norm bound and strong dot H^p continuity proves strong L² continuity; for a difference v use
||v||_2 <= ||D^(-epsilon)v||_2^(p/(p+epsilon)) ||D^p v||_2^(epsilon/(p+epsilon)).
Thus u is strongly H^p-continuous, and the mass and energy conservation arguments of the local critical theory apply. QED.

A sufficient condition expressed only on u is a uniform L^ell bound with
s<=ell<2ds/(d+4p).
Set q=ell/s; the upper restriction is exactly a>2p and the lower is q>=1. This is an explicit integrability improvement that would upgrade a homogeneous compact critical element to finite mass. It has not been proved automatically for all such elements. The interval is nonempty precisely when d>4p. For d<=4p this particular estimate cannot obtain a>2p from any q>=1; the argument does not prove that negative regularity is false there. At d=4p and q=1 the displayed global dispersive integral has a logarithmically divergent tail. Even improved annular time decay by stationary phase would not produce a positive low-frequency power from the same scaling bound at d=4p.

### 30.3 Finite mass supplies the required integrability for d>4p

Suppose the global normalized-compact trajectory in §30.1 already belongs to C_t H^p, with conserved mass M and bounded positive pure energy. Then it is uniformly L² and L^b bounded. If s>=2 choose q=1, since 2<=s<b gives ||F(u)||_1=gamma||u||_s^s bounded by interpolation. Here a=d/2, so a>2p exactly for d>4p. If 1<s<2 choose q=2/s in (1,2), since ||F(u)||_(2/s)=gamma||u||_2^s. Then
a=d(s-1)/2=2pd/(d-2p)>2p.
Thus, in every d>4p, Theorem 30.2 applies to every global finite-mass normalized-compact pure strong solution. The admissible negative exponent can be any
0<epsilon<d/2-2p for 4p<d<=6p,
0<epsilon<4p²/(d-2p) for d>6p.
The two expressions agree at d=6p. This result uses no additional spatial integrability hypothesis for the finite-mass class.

## 31. Exclusion of all compact finite-mass pure critical elements when d>4p

**Theorem 31.1.** Let u be a maximal strong pure critical H^p solution with compact normalized orbit on its maximal lifespan I and positive energy. For any d>2p, no finite endpoint of I is possible and inf_I lambda(t)>0. For d>4p no such nonzero solution exists, even if I is the full time axis. The assertion is conditional on the compact normalized orbit, not on a minimal-element theorem.

Proof of the lower scale bound. Positive conserved pure energy and homogeneous Sobolev give a positive lower bound for ||D^p u(t)||_2: if this norm tended to zero, both terms of P(u) would tend to zero. By compactness of K, choose a fixed frequency annulus [c,C] in normalized variables containing at least a fixed positive amount of kinetic norm squared for every member of K. In physical variables its frequencies are [c lambda(t),C lambda(t)]. On that annulus the kinetic norm squared is at most (C lambda(t))^(2p) M. Since M is finite, lambda(t) is bounded below. This argument works without negative regularity.

Proof of finite endpoint exclusion. If T is a finite forward endpoint and there is a sequence t_n↑T with lambda(t_n) bounded above, the linear critical Z norm on [t_n,t_n+h] is uniformly small for sufficiently small h>0. Indeed in normalized coordinates it is the linear Z norm on [0,h lambda(t_n)^(2p)], by the exact critical scaling and translation invariance. Homogeneous free Strichartz bounds and a finite net of the compact set K give uniform absolute continuity of the Z norm on shrinking intervals. The pure nonlinear estimate of §16.4 gives
Z_[t_n,t](u)<=Z_[t_n,t](U(·-t_n)u(t_n))+C Z_[t_n,t](u)^s.
For small linear norm, continuity of Z on compact subintervals and vanishing at t_n close the small-norm bootstrap on [t_n,min(t_n+h,T)). This implies finite Z up to T for all sufficiently large n, contradicting continuation in §16.4. Hence lambda(t)→∞ as t↑T. Compactness of K in dot H^p and critical Sobolev imply uniform L^b spatial tails in normalized coordinates. At the diverging scales the physical solution therefore satisfies the full critical-moment concentration hypothesis in §21.2, which contradicts nonzero conserved mass. The backward case follows by conjugation. Thus I=R for every d>2p in this finite-mass compact class. This step does not use double Duhamel.

Proof of upper scale bound for d>4p. With I=R, §30.3 supplies uniform negative Sobolev regularity. Suppose lambda(t_n)→∞ along any sequence. Fix 0<delta<L<∞. Compactness of K makes
integral_(|xi|<=L) |xi|^(2p)|uhat(t_n,xi)|² dxi→0,
since in normalized variables the cutoff L/lambda(t_n) tends to zero. Split the conserved mass into three regions. On |xi|<=delta it is at most C delta^(2epsilon), by negative regularity. On delta<|xi|<=L it is at most delta^(-2p) times the kinetic integral just shown to vanish. On |xi|>L it is at most L^(-2p) sup_t||D^p u(t)||_2². Sending n→∞, then delta→0 and L→∞, gives M=0, a contradiction. Therefore sup_I lambda(t)<∞. This excludes arbitrary unbounded frequency-scale excursions, not only a monotone cascade limit.

Finally, the compact scale interval and compact normalized orbit imply precompactness in dot H^p modulo translations, by continuity of the critical scaling action on a compact product of scale interval and K. The uniform low-frequency mass tightness of Theorem 30.2 upgrades this to H^p precompactness modulo translations, by §27.4. Apply Theorem 27.1 to exclude the resulting nonzero global compact pure orbit. QED.

### 31.1 Conditional implication for the homogeneous minimal-element problem

For d>4p a global homogeneous pure strong compact element with the additional uniform L^ell bound of §30.2 becomes an H^p strong trajectory, so the preceding rigidity applies and excludes it. A homogeneous finite-endpoint compact trajectory with diverging scale is already excluded by the local mass argument in §21.2 (provided it satisfies the stated local strong homogeneous regularity and full concentration). But neither the existence of a homogeneous minimal strong bad element nor the required global L^ell improvement has been derived in this dossier. In particular, one cannot conclude arbitrary-data global critical scattering or mixed global well-posedness merely from the finite-mass compact rigidity theorem. Homogeneous weak profiles from §24 are not automatically strong, compact or finite-mass.

## 32. Exact remaining obstructions and verification state

The present revision closes the full compact-orbit rigidity step for finite-mass critical pure strong solutions in d>4p and the finite-time full compactness obstruction in every d>2p in that class. The remaining dimensions 2p<d<=4p still require a different negative-regularity or frequency-cascade mechanism, and all dimensions require a valid construction and regularity upgrade of any homogeneous minimal bad element before a general large-data pure theorem can be concluded.

The double-Duhamel approach is established prior art: see Killip–Visan, arXiv:0804.1018 and Clay lecture notes on NLS at critical regularity (https://www.math.ucla.edu/~visan/ClayLectureNotes.pdf), Miao–Xu–Zhao arXiv:0807.0692 for d>=9 fourth-order energy-critical scattering, and Miao–Zheng arXiv:1211.4668 for fourth-order scattering theory. Those works use negative regularity and cascade exclusion. The present section adapts that estimate to general integer p with explicit finite-mass and integrability hypotheses; it makes no novelty claim and does not import their fourth-order minimal-element result as a general-order theorem. The dimensional restriction in the double-Duhamel estimate is a proof-method restriction.

No new unconditional parameter region of the original mixed equation is claimed. Individual-data supercritical strong classification remains open. The twelve candidate Lean roots and focused audit workflow from the preceding revision are unchanged: at inspection of head b9d09142cf8e7240d0e783b3c8fee324a22d0638 the workflow API returned no runs. This is not a pass, failure, or proof that the workflow executed. The no-waste Duhamel, negative regularity and compact-rigidity arguments above are not Lean-formalized. No issue closure, registry promotion or kernel certification.
