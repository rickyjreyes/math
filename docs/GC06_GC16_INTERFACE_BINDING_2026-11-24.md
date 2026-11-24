# GC06 / GC16: surface-order bulk energy and square-root fragment exclusion

Date: 2026-11-24. Original whole-space cubic-quintic Hamiltonian, no substituted dispersion operator. Analytical proof candidate, independent mathematical review required. The new Lean module formalizes the finite increment and algebraic transfer, not yet the local elliptic compactness and lattice counting proof. No complete GC resolution or novelty claim.

## 1. Exact excess energy

Fix real k and beta,gamma>0. Let rho=|u|^2, r=3 beta/(4 gamma), C=3 beta^2/(16 gamma). For u in H^2(R^2; C) put

\[
 {\cal F}(u)=E(u)+CM(u)=\int_{\mathbb R^2}
 \left(|(\Delta+k^2)u|^2+V(\rho)\right),\quad
 V(q)=\frac\gamma3 q(q-r)^2.
\]

Write F(m)=I(m)+Cm, f(m)=F(m)/m. These equal the original constrained infimum and its excess; M is the mathematical L^2 mass. The exact square completion and uniform finite-mass positive gap are already established in PR #109. The prior disc carrier upper trial gives F(m)<=K sqrt(m) for all sufficiently large m, at each fixed tuple. We prove a matching order lower bound without assuming attainment.

## 2. Local two-phase rigidity at small excess

Use unit closed squares Q_i=i+[0,1]^2, i in Z^2 (ignore boundaries in integrations), expanded open squares B_i=i+(-1,2)^2 and intermediate closed squares D_i=i+[-1/2,3/2]^2. Write e_i=int_{B_i} (|(\Delta+k^2)u|^2+V(|u|^2)). Fix a threshold d=r/4.

**Local lemma.** There exists eps>0 depending only on k,beta,gamma such that if e_i<eps then throughout D_i either rho<d or |rho-r|<d, with the continuous representative of u.

Proof by contradiction. Translate i to zero. If e_i tends to zero on a violating sequence, use the elementary pointwise bound q<=2r+(3/(gamma r^2))V(q) for q>=0: when q<=2r this is trivial, and when q>2r, V(q)>=(gamma/3) r^2 q. Thus the local L^2 norms on B_0 are uniformly bounded. Since Delta u=(Delta+k^2)u-k^2 u, the Laplacians are bounded in L^2(B_0). The standard interior elliptic estimate for the Laplacian on nested bounded squares implies a uniform H^2 bound on an open square containing D_0 compactly inside B_0 (e.g. (-3/4,7/4)^2). Rellich and the dimension-two Sobolev/Morrey embeddings give a subsequence converging uniformly on D_0 (for example through H^{2-s} with 0<s<1 on an intermediate Lipschitz square). Hence V(|u_n|^2) converges uniformly there. Its integral tends to zero, so the continuous limit has squared modulus in {0,r} everywhere on D_0, including its boundary by continuity. The connectedness of D_0 forces the squared modulus to be a single constant, 0 or r. Uniform convergence puts the sequence in the claimed alternatives for large n, contradicting violation. This proves existence of eps; no numerical value or global uniqueness of Helmholtz fields is needed.

## 3. Counting cells proves the lower bound

Call a cell bad if e_i>=eps; otherwise it is good-low or good-high according to the lemma. These two alternatives are disjoint. Adjacent good cells cannot have different labels since their D_i overlap and the allowed density intervals are disjoint. For N_B the number of bad cells, the bounded-overlap property of B_i gives eps N_B<=9 cal F(u) (a.e. each coordinate lies in exactly three expanded intervals). Thus the bad set is finite. Every good-high unit cell has rho>3r/4 and hence mass at least 3r/4; the high set H is finite because u is L^2.

Let N_H=|H|. For each nonempty lattice row of H choose its rightmost high cell. Its right neighbor is not high and cannot be good-low, so it is bad. Distinct rows produce distinct bad cells. Hence the number of occupied rows is <=N_B. The identical argument with the topmost high cell of each occupied column gives at most N_B occupied columns. Consequently N_H<=N_B^2 (including H empty). No assumption of connectedness of H is used.

On good-low Q_i we have rho<r/4 and V(rho)>=(gamma/3)(3r/4)^2 rho; hence their total mass is at most L_0 cal F(u), with L_0=3/(gamma(3r/4)^2). On bad squares use the pointwise bound in section 2 to obtain mass <=2r N_B+3/(gamma r^2) cal F(u). On high squares use rho<5r/4, giving mass <=(5r/4)N_H. Summing on the partition,

\[
 M(u)\le (L_0+3/(\gamma r^2)+18r/\epsilon){\cal F}(u)
       +(5r/4)(9/\epsilon)^2{\cal F}(u)^2.
\]

In particular some L>0, depending only on the tuple, satisfies M<=L(cal F+cal F^2) for all u. For M=m>0 and cal F<=1 this yields cal F>=m/(2L); for cal F>=1 it yields cal F>=sqrt(m/(2L)). Taking the infimum,

\[
 \boxed{F(m)\ge\min\{m/(2L),\sqrt{m/(2L)}\}>0.}
\]

In conjunction with the existing upper trial,

\[
 0<c_1\sqrt m\le F(m)\le c_2\sqrt m
\]
for all sufficiently large m. This is an order estimate, not existence of a limiting surface-tension constant. It holds for every fixed k (including zero), and does not require radiality, minimizers, a positivity-preserving Green function, a diameter bound or a priori profile geometry.

For later use, choose c=min(1/(2L),1/sqrt(2L))>0. For every a>0 we have f(a)>=c/sqrt(max(1,a)) by the preceding minimum formula.

## 4. Optimized finite increment and square-root fragment window

The exact finite increment estimate of PR #109 gives, for 0<a<=b and any delta>0,

\[
 [I(a+b)-I(b)]/a
 \le -C+2Ca/b+(7+4\beta/\delta)f(b)+4C\delta/\beta .
\]

Because f(b)>0, choose delta=beta sqrt(f(b)/C). This yields

\[
 [I(a+b)-I(b)]/a
 \le -C+2Ca/b+7f(b)+8\sqrt{Cf(b)} .\tag{1}
\]

Thus strict binding holds for the split (a,b) if 2Ca/b+7f(b)+8 sqrt(C f(b))<f(a). The new Lean module GC16InterfaceBinding uses the exact verified finite-increment result to encode the optimized inequality and certificate. It also exposes a precise statement transferring the fieldwise cell-counting bound of section 3 to I; that transfer has the cell estimate as an explicit hypothesis, not an extra global axiom.

**Square-root exclusion theorem.** For each fixed admissible tuple there exist eta>0 and M0 such that for every m>=M0 and every 0<a<=eta sqrt(m),

\[
 I(m)<I(a)+I(m-a).
\]

Proof. For fixed eta and m large, b=m-a>=m/2, a<=b, eta sqrt(m)>=1. The upper bound f(b)<=K/sqrt(b) gives
2Ca/b+7f(b)+8 sqrt(C f(b))
<= (4C eta+7 K sqrt(2))/sqrt(m)+8 sqrt(C K sqrt(2))/m^(1/4).
But f(a)>=c/sqrt(max(1,a))>=c/(sqrt(eta)m^(1/4)).
Choose eta>0 sufficiently small that c/sqrt(eta)>8 sqrt(C K sqrt(2))+1. Increase M0 until the first error term is less than m^(-1/4), and the other large-mass conditions hold. Then (1) gives strict binding for every stated a uniformly. This improves the previously proved window a<=m^theta, theta<1/8, to a positive multiple of sqrt(m), including arbitrary small fragments. In any finite minimizing-cluster decomposition at these masses, each cluster must have mass greater than eta sqrt(m) (unless it is the single full-mass profile). The number of clusters is consequently O(sqrt(m)).

## 5. What remains for balanced splits

Surface-order bounds alone are insufficient: if F(m)/sqrt(m) merely stays between two positive constants, it can still oscillate and the two-sided estimate need not imply strict subadditivity. If one additionally establishes a common asymptotic F(m)=sigma sqrt(m)+o(sqrt(m)) with sigma>0, then for each fixed d in (0,1/2) all splits a/m in [d,1-d] strictly bind at sufficiently large m. Indeed the normalized excess gap tends uniformly on that interval to sigma(sqrt(a/m)+sqrt(1-a/m)-1), whose minimum is strictly positive. This is conditional on proving the leading coefficient, not a claimed theorem of the Hamiltonian. Even that limit would not by itself settle intermediate fragment scales sqrt(m)<<a<<m or the finite-mass gaps. A rigorous surface-tension limit requires accounting for complex phase, orientation and oscillatory shell modes; scalar double-well rearrangements cannot simply be imported.

A separate route remains strict merging of equal-chemical-potential localized profiles via the exact tail interaction of the fourth-order operator. No non-cancellation or sign assumption is made. GC06 all-mass attainment follows from universal binding if proved, while GC01 requires genuine classification of individual excited/degenerate orbits. Neither is declared resolved.

## 6. Lean correspondence and verification

Preserve PR #109's 13 locally verified theorem roots and exact source files, now carried onto current main without removing the GC08 imports. New candidate roots in GC16InterfaceBinding: bulkDensity_pos, optimized_increment, strict_split_of_optimized_margin, mass_bound_to_surface_gap, inf_surface_gap_of_cell_bound. The last root is conditional on the fieldwise cell estimate proved analytically in sections 2–3. Local elliptic compactness, lattice counting, upper trial asymptotics, and the quantified square-root fragment theorem still need full formalization. No kernel claim about these analytic arguments, no automatic registry promotion, no full challenge closure, no novelty claim. The new five-root audit and integrated build require actual successful Lean verification.
