# GC08: global Cartesian jet classification (2026-11-24)

Status: analytical theorem; candidate algebraic Lean core, not built or independently reviewed.
Scope: original GC08, d >= 2, epsilon > 0; smooth real differential operators of order at most two, meaning smooth functions of all real Cartesian second-order jet coordinates. No M6B substitution. No novelty claim.

Sources: [original statement](../reyes-problem-repository/problems/02-confinement-curvature/GC08.md), [scope audit](NEGATIVE_RESULT_SCOPE_AUDIT_2026-11-02.md), [PR #99](https://github.com/rickyjreyes/math/pull/99), section 4 of its research ledger. The external general theorem used below is G. W. Schwarz, "Smooth functions invariant under the action of a compact Lie group", Topology 14 (1975), 63–68, Thm. 1. This is an application of classical invariant theory, not a new general invariant-theory theorem.

## 1. Exact operator and realization

Write J=(z,g,H) in V=C ⊕ C^d ⊕ Sym_d(C). Every symmetric jet is realized at zero by the polynomial u(x)=z+g·x+(1/2)x^T H x. Thus identities on smooth fields are equivalent to identities on these jets. Translation covariance removes the explicit spatial basepoint. The remaining group is G=U(1)×SO(d), with action (e^{iθ}z,e^{iθ}Rg,e^{iθ}RHR^T); the transpose convention for pullbacks is equivalent.

Put rho=|z|². Differentiating the phase current gives
K(J)=Im(conj(z) tr H)/(epsilon+rho)
 -2 sum_i Re(conj(z)g_i) Im(conj(z)g_i)/(epsilon+rho)^2.
Indeed, Im(conj(g_i)g_i)=0 and ∂_i rho=2Re(conj(z)g_i). All contractions are rotation and constant-phase invariant. The strictly positive denominator gives global smoothness. At z=0, K=0 regardless of g,H.

A plane-wave jet is (z,iz ξ,-z ξξ^T) with z≠0 and ξ real. K vanishes there. The correction L=Delta rho=2(||g||²+Re(conj(z)tr H)) also vanishes there. The real affine field u(x)=1+x_1 has K identically zero and L=2, so K+lambda L are pairwise distinct as operators on actual globally smooth fields. The field u=x_1 has z=0, L=2 at the origin, proving that admissibility does not require vanishing at nodes.

## 2. Finite invariant coordinates and exact global normal form

The action is orthogonal on a finite-dimensional real space using the real Euclidean and Frobenius inner products. The invariant polynomial algebra admits finitely many generators by compact-group invariant theory. Choose them multihomogeneous in the three blocks z,g,H: decompose any finite generators into their multihomogeneous components, which remain invariant because the action respects the blocks. Include s=|z|², t=||g||², h=||H||_F². Write the remaining generators as P=(P_1,...,P_N) and the full Hilbert map as σ=(s,t,h,P).

For every multihomogeneous generator of block degrees (a,b,c), restrict to the plane jet (r,ir k e_1,-r k² e_1e_1^T). The result is a constant times r^n k^w with n=a+b+c and w=b+2c. The phase -1 forces n even for a nonzero restriction; a proper rotation reversing e_1 (possible for d≥2) forces w even. Write n=2m, w=2l with 0≤l≤2m. Choose nonnegative integers A,B,C with A+B+C=m and B+2C=l (e.g. C=floor(l/2), B=l mod 2). Thus the restriction is p_j(s,t,h)=constant*s^A*t^B*h^C. A zero restriction uses p_j=0. This gives a finite prescription for each generator; no minimal generating set is required. A generating set can also be obtained by spanning each invariant multidegree with Reynolds averages of coordinate monomials, and taking sufficiently many degrees by finite generation. The use of SO(d), not O(d), preserves possible orientation-sensitive invariants.

Define D_j=P_j-p_j(s,t,h), and Q={(s,t,h)≥0: sh=t²}. The plane-wave image in the three coordinates is exactly Q∩{s>0}. Its closure is Q: at s=0 one must have t=0, and any h≥0 is approached using s>0 and t=sqrt(sh).

THEOREM. The admissible globally smooth closures are exactly
C(J)=K(J)+F(s,t,h)+sum_j D_j(J) A_j(σ(J)),
where F is smooth on R³ and vanishes on Q, and the A_j are arbitrary smooth functions on R^(3+N). Coefficients need not be unique. More abstractly the correction space is the ideal of invariant smooth functions vanishing on the closed plane-wave jet set.

Proof: Schwarz's theorem gives C-K=G(s,t,h,P) with G smooth on all of R^(3+N). Set F(s,t,h)=G(s,t,h,p(s,t,h)). The plane-wave condition forces F=0 on Q∩{s>0}, hence Q. For every X=(s,t,h), Y=P, the fundamental theorem of calculus on the segment p(X)+τ(Y-p(X)) yields
G(X,Y)=F(X)+sum_j (Y_j-p_j(X)) ∫_0^1 ∂_{Y_j}G(X,p(X)+τ(Y-p(X))) dτ.
The integrals are globally smooth coefficients by differentiation under a compact integration interval. Conversely arbitrary coefficients and F as specified give smooth invariant functions and vanish on every plane jet after subtracting K. This proves necessity and sufficiency, including all singular strata. The residual ideal on Q is specified by a concrete scalar closed cone, not by the original differential operator or its symmetries.

## 3. Nodal plane-wave closure and polar extension

The closure of the plane-wave jet set in V adds exactly the nodal jets (0,0,H) with H=λ v v^T, λ complex and v real unit (also H=0). For a convergent sequence with |z|→0, ||H||=|z| |ξ|² is bounded and ||g||²=|z| ||H||→0. The unit direction ξ/|ξ| admits a subsequence if nonzero, and the bounded complex coefficient -z|ξ|² admits a limit. Conversely for H=λ vv^T nonzero choose z_n=-λ/n² and ξ_n=n v. For H=0 choose ξ=0 and z→0. Thus all admissible closures vanish on this nodal subset, but not necessarily other nodal jets.

On z≠0 write r=|z|, p=grad log r, q=grad θ, A=Hess log r, B=Hess θ. Then
p_i+iq_i=g_i/z;
A_ij+iB_ij=H_ij/z-g_i g_j/z².
The polar K is w tr B + 2epsilon r²/(epsilon+r²)² p·q with w=r²/(epsilon+r²).
PR #99 classified the nonvanishing correction by p·V+A:U+B:W with smooth equivariant coefficients.

EXTENSION THEOREM. For an admissible polar correction f, define its Cartesian pullback f_cart on z≠0 by the above formulas. It extends smoothly to all V iff either equivalent condition holds:
(i) f_cart equals the restriction of the normal form correction in section 2 for smooth F,A_j as stated;
(ii) for every real coordinate multi-index α, ∂^α f_cart admits a continuous extension to V (equivalently, finite path-independent limits as every raw nodal jet is approached, locally continuous on the nodal set).
Necessity is immediate. For sufficiency of (ii), use the fundamental theorem along any coordinate segment, translating its complex z-coordinate slightly so the segment avoids z=0. Such translations exist since the removed plane in the z-coordinate has real codimension two; the forbidden translations are contained in a line segment or point. Pass to the limit using continuity and compactness of a neighborhood of the segment. The extended functions satisfy the integral identity for each coordinate derivative. The fundamental theorem implies the extension is C¹ with the specified partials; induction gives C∞. Uniqueness and symmetry follow by density. The plane-wave condition is retained, so section 2 applies. Condition (i) is sufficient directly and necessary by that theorem. This criterion is about the total polar correction, not individual coefficient limits, which can cancel.

Example of a smooth polar correction without continuous extension: |p|². Take z=r>0, g=e_1, H=0 as r→0; |p|²=r^-2 diverges at the finite nodal jet (0,e_1,0).

## 4. Additional independent admissibility axioms and uniqueness

A physically interpretable choice is local phase-response covariance and conjugation oddness. For every smooth real φ require
C(e^{iφ}u)=C(u)+div(w(|u|) grad φ), w=r²/(epsilon+r²).
This law follows for K because the current changes by |u|² grad φ, including at nodes. Separately require C(conj u)=-C(u), or more weakly C(v)=0 for every smooth real field v.

THEOREM. In the original smooth local class these two axioms determine K uniquely.
Proof: for F=C-K the phase-response law gives F(e^{iφ}u)=F(u). At any nonzero field point a smooth local phase removes the phase, leaving the positive real amplitude. A global smooth phase agreeing near the point is obtained by a smooth cutoff; a global smooth real field agreeing locally with the amplitude likewise exists. By locality and real-field normalization, F vanishes at every nonzero point/jet. By smoothness and density of z≠0 it vanishes on all jets. Conversely K satisfies both axioms, directly from the current and conjugation. The stronger oddness implies real-field normalization.

The pair is independent (irredundant, not a claim of absolute minimality among all logically equivalent axiom systems): K+lambda Delta rho with lambda≠0 satisfies the phase-response law but not real-field normalization or conjugation oddness; 2K satisfies conjugation oddness and real-field normalization but fails the prescribed local phase-response law, e.g. u=1, φ=x_1²/2. Even smoothness, original symmetries, conjugation oddness and node-vanishing together leave all scalar multiples of K. Phase response alone classifies the remaining freedom as phase-insensitive smooth corrections, determined on nonzero jets by amplitude jets; global smoothness still requires section 3. No uniqueness follows from plane-wave calibration by itself.

## 5. Verification ledger

- Global invariant classification, nodal closure, extension theorem and field-level uniqueness: analytical arguments above; depend on classical Schwarz theorem and elementary calculus. No claim of new general invariant theory or physics validation.
- Candidate Lean module GC08Cartesian: real-coordinate rational formula, denominator positivity, zero-field evaluation, plane-wave algebra, density-Laplacian witness and scalar phase-response uniqueness core. It uses a coordinate jet container allowing arbitrary matrices (the identities restrict to symmetric Hessians). The formal derivative correspondence, full SO(d)/U(1) action and invariance, exact field realization, Schwarz theorem, Hadamard integral factorization, smooth extension proof and full field gauge theorem remain unformalized.
- Local Lean/lake unavailable and network clone failed. Run pinned lake build and lake env lean scripts_audit/DependencyAudit.lean in CI; inspect transitive axioms for new roots. Do not mark verified or close GC08 until independent correspondence and required kernel checks.

## 6. Continuation: exact phase action and continuum derivative correspondence

Candidate modules GC08Gauge and GC08Field supplement the initial algebraic core. All claims below remain pending a pinned kernel check.

For a real phase with value zero at the base point, gradient v and Hessian W, the complex jet transforms as
z'=z, g'=g+i z v, H'_{ij}=H_{ij}+i(g_i v_j+g_j v_i+z W_{ij})-z v_i v_j.
The derivative response is
R(J,v,W)=sum_i [rho W_ii/(epsilon+rho)+2epsilon Re(conj(z)g_i)v_i/(epsilon+rho)^2].
GC08Gauge states and supplies candidate proofs of curvature_rotate, curvature_gauge, exists_real_gauge, unique_nonzero and unique_all_jets. The local phase law uses the actual rational response, not a stipulated equality to the operator difference. The uniqueness argument chooses c=a/r, s=-b/r, r=sqrt(a²+b²), rotates to value r, takes v=-q/r and W_ij=-(B_ij+p_i v_j+p_j v_i)/r. These choices annihilate all imaginary slots. At a nodal jet a=0, the proof uses only continuity of t↦C(J[a:=t])-K(J[a:=t]) at t=0. This is weaker than global smoothness, and is not a circular premise. The jet transformation is presently algebraic; the full symmetric-field/jet realization and smooth phase multiplication correspondence for arbitrary mixed derivatives still need formalization.

GC08Field defines the continuum normalized current along each coordinate line with actual deriv, its coordinate divergence, and the diagonal derivative slots. Candidate theorem lineCurrent_deriv proves the product/quotient rule from ordinary HasDerivAt hypotheses. fieldCurvature_eq_cartesian sums these identities; fieldCurvature_at_zero applies them at any actual field node. The diagonal representation suffices for K but does not formalize the full mixed Hessian of arbitrary closures. The candidate theorem field_closure_family_distinct computes the actual density Laplacian of the smooth complex field u(x)=1+x_1 on R² and proves pairwise distinct continuum closure evaluations.

Full global invariant factorization via Schwarz, the general smooth-extension classification, complete symmetry and actual mixed-jet realization remain unformalized. Build/audit claims must be based on observed CI logs. Status remains partial.

### Exact polynomial plane-wave locus and symmetric-jet refinement

A globally nonsingular, finite polynomial test for the closed plane-wave jet set is available. Write over complex Cartesian coordinates:
(1) Re(conj(z) g_i)=0 for every i;
(2) z H_ij=g_i g_j for every i,j;
(3) every two-by-two minor of H is zero;
(4) Im(conj(H_ij) H_kl)=0 for every i,j,k,l.
These conditions are equivalent to membership in the closed plane-wave jet set of section 3 (for symmetric H).

Proof: all are satisfied on plane waves and preserved under limits. Conversely, if z≠0, (1) yields g_i=i z ξ_i with ξ_i real and (2) yields H_ij=-z ξ_i ξ_j. If z=0, (2) with i=j yields g_i²=0 and g=0. If H is nonzero, choose a nonzero entry c; (4) implies every entry of H/c is real. This real symmetric matrix T has rank one by (3). Some diagonal T_ii is nonzero, since otherwise a nonzero off-diagonal entry would give a nonzero principal two-by-two minor. The minors give T_jk=T_ji T_ik/T_ii, so H is a complex multiple of vv^T for a real unit vector v. Section 3 proves all these nodal jets are plane-wave limits. The zero matrix is included.

Thus the sum of squared Euclidean/Frobenius norms of the four residual tensors is a single nonnegative invariant real polynomial with precisely this zero set; the minor tensor is the exterior square of H, equivariant under the induced orthogonal action. This is a constructive global membership criterion, not a claim that the smooth vanishing ideal is generated by this single squared polynomial. For example, smooth corrections can vanish to first order at regular plane jets while that polynomial vanishes to at least second order.

GC08PlaneLocus formalizes the candidate polynomial equivalence on nonzero jets in real coordinates, using rho² A_ij=-a m_i m_j and rho² B_ij=-b m_i m_j with m_i=a q_i-b p_i and a p_i+b q_i=0. Its converse constructs k_i=m_i/rho. These particular equations by themselves do not resolve the nodal locus; the additional nodal constraints above remain analytical.

GC08Gauge also now states unique_symmetric_jets, requiring the response and normalization axioms only for symmetric Hessians and symmetric phase Hessians. Symmetrizing the successful phase Hessian preserves the real normalization. This removes the need to assume axioms on unrealizable nonsymmetric Hessians. All new Lean roots are registered for audit; full kernel checks pending.

## 7. Candidate kernel proofs of the closed locus, rotation contractions and smooth Hadamard step

GC08ClosedPlane uses the actual normed product C × C^d × C^(d×d) and proves the candidate theorem closed_plane_iff_equations, including Hessian symmetry. The nodal converse factors every nonzero aligned complex symmetric rank-one matrix as c vv^T with real v; the zero matrix uses c=1 and v=0. A continuous polynomial path (-ct²,-ictv,cvv^T) is a nonzero plane jet for t≠0 and approaches the node at t=0. This is an actual topological closure proof target rather than a stipulated closure relation. vanishes_on_closed_plane targets extension of plane calibration by continuity.

GC08Spatial develops the finite-sum contraction identity for orthogonal matrices, and candidate rotation invariance of the original rational curvature and density-Laplacian counterexample family. Orthogonality is sufficient for these particular operators; arbitrary admissible closures are only required to respect proper rotations. Field translation and mixed-jet transformation correspondence still need formalization.

GC08Hadamard supplies candidate proofs of compact parameter integration preserving every finite C^n order (hence C∞), using the pinned Mathlib dominated differentiation theorem and actual compact local bounds. It then proves the segment formula f(y)-f(x)=A(x,y)(y-x), smoothness of A even at x=y, and simultaneous equivariance for all linear symmetries preserving f and commuting with the smooth base map p. The graph version requires f(p(x))=0, and derives the coefficient rather than assuming it. In logarithmic amplitude coordinates the nonvanishing polar plane locus is exactly such a base projection. This isolates the analytic factorization step independently of Schwarz, but does not yet prove the full polar-to-field correspondence or Schwarz invariant generator factorization. All new roots are included in the dependency audit.

### Polynomial correction ideal (analytical strengthening)

For the subclass of invariant polynomial corrections D=C-K, the global normal form has polynomial coefficients and its residual cone term is divisible by sh-t². In fact, polynomial invariant factorization gives a polynomial G(s,t,h,P); the telescoping graph difference is polynomial, so F(s,t,h)=G(s,t,h,p(s,t,h)) is polynomial and vanishes on Q. Divide F by the monic polynomial t²-sh in t, with coefficients in R[s,h]. Its remainder is U(s,h)+tV(s,h). Substituting s=x², h=y², t=xy for x,y>0 gives a polynomial vanishing on an open set; its even-even and odd-odd monomials are disjoint. Hence U=V=0. Conversely the residual invariant generators P_j-p_j and sh-t² vanish on all plane waves. Thus the polynomial correction ideal in the invariant polynomial algebra is generated by these finitely many explicitly described residuals. This is not an assertion that the unrestricted smooth vanishing ideal admits the same finite polynomial generators; the smooth class has the cone-vanishing term described earlier.

Verification boundary: the originating environment has no lean or lake and cannot resolve github.com for a clone. Initial catalogue and Markdown checks passed on the earlier head; its full Lean check was still running when this continuation began. The new modules are candidate code, not a successful kernel certificate. The smooth-extension theorem across nodes, full mixed-jet realization and Schwarz factorization remain analytical. No status promotion or issue closure.

## Local verification record (November 24, 2026)

The supplied Lean 4.23.0 local build and focused `GC08Audit.lean` output at commit `4d05257cf49f4f4d8d9ccf54a33ed36b63d3343d` establish that all seven modules compile and all 24 audited roots use only `propext`, `Classical.choice`, and `Quot.sound`. This supersedes earlier candidate-only build status statements; the remaining analytical-only obligations are unchanged. No full-GC completion is claimed.
