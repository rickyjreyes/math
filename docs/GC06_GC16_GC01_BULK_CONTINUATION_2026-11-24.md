# GC06 / GC16 / GC01 continuation: finite-mass bulk gap, exclusion of small fragments, and expanded orbital stability

Date: 2026-11-24. Original model only. This document contains analytical results and candidate Lean correspondence, not a complete Grand Challenge resolution or a literature-priority claim. Builds of the new modules are pending.

## 1. Setting

For beta,gamma>0, real k, and u in H^2(R^2; C), write M=||u||_2^2, T=||(Delta+k^2)u||_2^2, Q=||u||_4^4, S=||u||_6^6, E=T-beta Q/2+gamma S/3, I(m)=inf_{M=m} E. Set

\[
C=3\beta^2/(16\gamma),\qquad r_*=3\beta/(4\gamma),\qquad f(m)=I(m)/m+C.
\]

Use the merged original-model Fourier bound from GC16ShellFourier: for every eta>0,

\[
\|u\|_\infty^2\le (T+\eta M)/(4\sqrt\eta).
\]

The exact bulk completion gives E>=T-CM. The earlier analytical large-disc carrier trial (GC06_SHELL_BINDING_2026-11-24.md, section 5) gives f(m)=O(m^{-1/2}) and f(m)>=0 for all sufficiently large m, at each fixed parameter tuple. The latter asymptotic is not Lean-certified here.

## 2. Quantitative finite-mass bulk gap

**Theorem 1.** Let a,s>0 with beta s a<=2C. Then

\[
 I(a)\ge (-C+\min(s^2,C/2))a.
\]

Proof: If a trial U of mass a has T>=s^2 a, the bulk completion suffices. Otherwise choose eta=s^2 in the Fourier bound. Then ||U||_infty^2<=sa/2, Q<=sa^2/2, and E>=-beta Q/2>=-Ca/2. Both cases imply the bound; take the infimum. For each fixed A>0 choose s=2C/(beta A) and g_A=min(s^2,C/2)>0. It follows uniformly that f(a)>=g_A for 0<a<=A. This improves the previous qualitative strict gap I(a)>-Ca to an explicit positive gap, uniform in k.

Lean candidate roots: field_bulk_gap, inf_bulk_gap in GC16BulkBinding.

## 3. Exact mass-increment estimate from a shifted attractive coupling

Let delta>0 and C_delta=3(beta+delta)^2/(16gamma). The lower bound for the Hamiltonian with coupling beta+delta, evaluated on the very same U, yields

\[
 (\delta/2)Q\le E+C_\delta M.
\]

For t>=1, amplitude scaling V=sqrt(t)U gives

\[
 E(V)=t^3 E-(t^3-t)T+(\beta/2)(t-1)t^2Q .
\]

Dropping the nonpositive kinetic correction and applying the shifted-coupling bound gives

\[
 I(tb)\le [t^3+(t-1)t^2\beta/\delta]I(b)
 +(t-1)t^2(\beta/\delta)C_\delta b.
\]

There is no attainment assumption: take a minimizing sequence at b and pass the inequality to its limit. For a>0, b>=a, and t=1+a/b, this implies

\[
 \frac{I(a+b)-I(b)}{a}
 \le -C +2C a/b +(7+4\beta/\delta)f(b)+4C\delta/\beta. \tag{1}
\]

To check the algebra, the exact upper bound before replacing t-dependent factors is
-C+C(t^2-t)+(t^2+t+1+t^2 beta/delta)f(b)+t^2 C delta/beta, because (beta/delta)(C_delta-C)=2C+C delta/beta. Now 1<=t<=2 and f(b)>=0. This is a finite-difference bound, not a derivative or a smoothness claim about I.

Lean candidate roots: quartic_shift_bound, scaled_field_upper, inf_scaled_upper, strict_split_of_certificate, inf_increment_bound, strict_split_of_small_bulk_defect in GC16BulkBinding. The last root uses a checkable strict scalar margin against the finite-mass bulk gap to certify a specific split.

## 4. All bounded fragments are excluded at sufficiently large total mass

**Theorem 2.** For each fixed admissible parameter tuple and each A>0 there exists M_A>=2A such that for every m>=M_A and every 0<a<=A,

\[
 I(m)<I(a)+I(m-a).
\]

Proof: choose the s and g_A of Theorem 1; set delta=beta g_A/(16C)>0. For b sufficiently large, b>=A and 2CA/b<=g_A/4, while (7+4beta/delta)f(b)<=g_A/4 by the prior analytical bulk limit. Also 4C delta/beta=g_A/4. Equation (1) then gives I(a+b)-I(b)<=(-C+3g_A/4)a<(-C+g_A)a<=I(a). Choose M_A=A plus a uniform lower threshold for b, so b=m-a qualifies for every 0<a<=A. QED.

The conclusion excludes all fixed bounded-mass satellites, including arbitrarily tiny a, without assuming that I is differentiable or monotone per mass. It does not exclude splits with both masses unbounded. In the finite minimizing-cluster decomposition of the earlier GC06 note, a cluster of mass a<=A would force I(m)=I(a)+I(m-a) by ordinary subadditivity; thus for m>=M_A every cluster must have mass>A.

A quantitative growing window follows from the previous trial rate f(b)<=K b^{-1/2}. For a fixed exponent 0<theta<1/8 and sufficiently large m, set A=m^theta. Then g_A=4C^2/(beta^2 A^2) eventually, delta=beta g_A/(16C), b>=m/2 for a<=A, and the three errors divided by g_A have orders O(m^{3theta-1}), O(m^{4theta-1/2}), and 1/4 respectively. The first two tend to zero. Hence strict binding holds for every 0<a<=m^theta at sufficiently large m. No balanced-split or complete large-mass claim follows.

The asymptotic quantifiers in this section depend on the analytical bulk-limit construction, which has not yet been formalized. The finite criterion and algebra leading to (1) are the candidate Lean scope.

## 5. Analytical extension strictly past the current explicit mass ceilings

Let k be nonzero and let
\[
 M_0=\max(2\sqrt3/\sqrt\gamma,\ 3\beta/(\gamma k^2)).
\]
There exists epsilon>0 (depending on the tuple) such that I(b)/b is strictly decreasing on 0<b<=M_0+epsilon, and hence strict binding and compactness hold there. This is an existence result for an extension, not an explicit new uniform numerical ceiling.

Proof: the merged shell and virial results give strict per-mass decrease below and through M_0 (for the shell case use gap_shell for a+b<2 mShell). In particular all minimizing sequences at M_0 are compact modulo translations. Every minimizing profile U of mass M_0 is dilation-stationary. Write x=S(U)/Q(U), well-defined since Q>0. We prove x<r_*.

If the shell ceiling is the larger one, T<C M_0 because E(U)=I(M_0)<0 and E>=T-CM. The Fourier estimate with eta=C then yields ||U||_infty^2<(sqrt C/2) M_0=r_*. Consequently x<r_*.

If the virial ceiling is the larger one, suppose x>=r_*. The stationary identity D-k^2K-beta Q/4+gamma S/3=0 implies D<=k^2K. For nonzero H^2 functions, D>0 and K<sqrt(MD): equality in Fourier Cauchy-Schwarz would force the Fourier transform to be supported on a constant-radius circle, a null set. Thus D<k^2 sqrt(M_0 D), which implies sqrt(M_0 D)<k^2 M_0. The previously established sup bound ||U||_infty^2<=sqrt(M_0 D)/4 now contradicts x>=r_*=k^2 M_0/4.

There is a uniform strict margin x<=c<r_* on every sufficiently accurate near-minimizer of masses sufficiently close to M_0. Otherwise there would be a sequence a_n->M_0, U_n of masses a_n and energies E(U_n)-I(a_n)->0, with ratios approaching or exceeding r_*. Coercivity gives uniform H^2 bounds; mass-correct U_n to M_0 (the correction tends to identity). Continuity of I on positive masses by the standard amplitude comparison, and continuity of E on bounded H^2 sets, give a minimizing sequence at M_0. The established compactness after translations and strong L^4,L^6 convergence yield a minimizer with x>=r_*, a contradiction. The uniform margin now yields the local amplitude comparison used in the GC06 virial proof: choose a neighborhood sufficiently short that gamma(b/a+1)c/3<beta/2 for any a<b in it. Then I(b)/b<I(a)/a by amplitude scaling of the near-minimizing sequence, using I(a)<0 to make the gap strict. Compare any a below this neighborhood with M_0 by the existing strict per-mass decrease, then with b above M_0 using the new local comparison. This proves the extension. At k=0 no extension is needed because all masses already bind.

The same compactness argument gives a precise obstruction to an attempted continuation of strict per-mass decrease: if the maximal initial interval of strict decrease ends at a finite m_*, continuity and the midpoint comparison give strict decrease from every a<m_* to m_*. Hence strict binding and compactness hold at m_*. If every minimizer there satisfied S/Q<r_*, the preceding uniform-margin argument would extend that interval, a contradiction. Thus a finite endpoint of this strategy requires an attained minimizing profile with S/Q>=r_*. This does not imply that strict binding itself fails beyond m_*.

Section 5 is analytical only, pending Lean correspondence including strict Fourier Cauchy-Schwarz and continuity of the value function. The compactness theorem is the exact merged original-model result.

## 6. GC01 individual-orbit stability at all established binding masses

The existing GC01IndividualOrbit.isolated_orbit_stability proof invokes stable_core only to keep the evolving trajectory near the full minimizing set. The proof works without any prescribed mass ceiling once that call is replaced with stable_core_of_binding. All other steps use the original global whole-space H^2 solution, conservation, continuity, the isolated phase-translation orbit hypothesis, and an intermediate-value argument.

The candidate new theorem isolated_orbit_stability_of_binding has the original dynamical conclusion for any mass where all-split strict binding holds. Specializing with the merged shell and closed virial bounds gives isolated_orbit_stability_expanded. It includes every positive mass at k=0, subject to isolation, as well as the union of the nonzero-k bounds. The corresponding full minimizing-set stability and attainment results are exposed in orbital_stability_expanded and exists_minimizer_expanded. This does not establish isolation of all minimizers and does not classify excited states. In particular a negative constrained Hessian direction or a Morse-index lower bound alone is not a proof of Hamiltonian nonlinear instability.

## 7. Remaining precise obligations

GC16: resolve splits with both component masses large at nonzero k, or produce an actual equality split of the constrained infima. The present comparison rules out bounded satellites and extends the known interval analytically but does not settle large balanced splits.

GC06: the original all-mass attainment and compactness question remains. In the frozen positive-coefficient domain, strict binding implies attainment/compactness; failure of strictness produces a noncompact minimizing sequence but does not by itself imply nonattainment. The existing analytical finite-profile decomposition still needs full Lean correspondence.

GC01: classify actual individual phase-translation orbits, including non-isolated ground states, excited and degenerate profiles. The present result extends a sufficient criterion, not a necessary-and-sufficient classification.

No issue closure or registry status promotion. Full pinned Lean build and exact standard-axiom audit required before claiming any new kernel-verified result. Compare against mixed-dispersion ground-state literature referenced in the prior GC06 dossier before any external novelty claim.
