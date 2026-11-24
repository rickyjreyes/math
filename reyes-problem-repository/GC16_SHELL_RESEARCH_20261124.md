# GC16 nonzero-shell research ledger (2026-11-24)

**Status:** analytical extension; Lean candidates pending kernel verification. Stacked on PR #99. GC16 and GC06 remain candidate problems; no all-mass nonzero-shell resolution or novelty claim.

## Exact model

For complex H²(R²), k >= 0, beta,gamma > 0, define M=||u||₂², D=||Delta u||₂², K=||grad u||₂², T=||(Delta+k²)u||₂², Q=||u||₄⁴, S=||u||₆⁶, E=T-beta Q/2+gamma S/3, I(m)=inf_{M=m} E. These are the actual F01 quantities. The existing theorem proves I(m)<0 for each m>0, and binding up to m_B=3 beta/(gamma sqrt(k⁴+3 beta²/(32 gamma))). No attainment is assumed below.

## 1. Audit zero shell

PR #99's analytical argument is valid. For t=b/a>1, v(x)=u(x/sqrt(t)), M(v)=tM(u) and E_0(v)=tE_0(u)-(t-1/t)D. If J=I_0(a)<0 and E_0(u)<J/2 then beta Q>-J, while Q<=a sqrt(aD)/4. Therefore D>=16 J²/(beta² a³)>0 uniformly. Passing to the infimum proves I_0(b)/b<I_0(a)/a at every 0<a<b. This implies every split binds. The PR's Lean code must be checked at its exact head; no local Lean executable is available here.

For nonzero k the exact same transformation yields E_k(v)-tE_k(u)=-(t-1/t)D+2k²(t-1)K. The added term cannot be discarded. For k>0, choose a nonzero smooth Fourier profile supported in a sufficiently thin annulus about |2pi xi|²=k². Then D/K approaches k² as the annulus shrinks; for any t>1 the difference is positive once D/K<2k²/(1+1/t). This is a counterexample to universal stretch improvement, not to strict binding of infima.

## 2. Shifted-shell Sobolev estimate

In the repository Fourier convention q=|2pi xi|², Plancherel gives T=int (q-k²)² |hat u|² and M=int |hat u|². For eta>0, polar coordinates with z=|2pi xi|² give

    A = int_R² 1/((q-k²)²+eta) dxi
      = [pi/2+arctan(k²/sqrt(eta))]/(4pi sqrt(eta))
      <= 1/(4 sqrt(eta)).

Fourier inversion and Cauchy-Schwarz thus yield

    ||u||_infty² <= (T+eta M)/(4 sqrt(eta)).

Prove first on Schwartz functions and pass by H² approximation, or observe hat u is integrable by the weighted estimate and use its inverse representative. For M>0, T>0 because the zero set of q-k² has Lebesgue measure zero. Choosing eta=T/M gives

    ||u||_infty² <= sqrt(MT)/2,
    Q <= M sqrt(MT)/2, S <= Q sqrt(MT)/2.

This is independent of k, and the factor 1/2 accounts for the full shell rather than the half-line at k=0. The exact weighted constant also recovers the existing k=0 bound 1/4 after optimizing.

## 3. A k-independent binding range

Let C=3 beta²/(16 gamma). The pointwise square completion gives E>=T-C M. For a negative-energy field of mass a, T<=C a and therefore

    S/Q <= a sqrt(C)/2 = sqrt(3) beta a/(8 sqrt(gamma)).

For 0<a<b, t=b/a, amplitude scaling gives

    E(sqrt(t)u)/t - E(u)
      = (t-1)[-beta Q/2 + gamma(t+1) S/3].

Set m_* = 2 sqrt(3)/sqrt(gamma). If a+b<2m_*, then h=1-(a+b)/(2m_*)>0. The preceding bound implies the bracket <= -beta h Q/2 <= h E(u), because T,S>=0. Consequently E(sqrt(t)u)/t <= [1+(t-1)h] E(u). A negative minimizing sequence exists since I(a)<0, and taking its infimum gives

    I(b)/b <= [1+(t-1)h] I(a)/a < I(a)/a.

For any 0<a<m<=m_* both a+m and (m-a)+m are strictly below 2m_*. Add the two strict per-mass inequalities. Hence every split binds for m<=m_*, including the endpoint. Together with existing m_B, every mass <=max(m_B,m_*) binds. This improves the old sufficient range when k⁴>21 beta²/(32 gamma) (square the positive constants). It is not claimed to be sharp.

## 4. Finite mass energy barrier and arbitrarily large binding masses

Cauchy-Schwarz gives S>=Q²/m. The shifted-shell bound gives T>=4Q²/m³ for any mass-m field. Set z=Q/m. Then

    E/m >= (4/m²+gamma/3) z² - beta z/2
        >= -beta²/[16(4/m²+gamma/3)].

Thus for every finite m>0,

    -C < -beta²/[16(4/m²+gamma/3)] <= e(m)=I(m)/m < 0.

In particular e(m)->0 as m->0+. For the opposite limit, let c²=3 beta/(4 gamma) and take a real smooth compactly supported cutoff chi, 0<=chi<=1, approximating a disk indicator in L²,L⁴,L⁶. The carrier trial u_R=c exp(ik x_1) chi(x/R) has mass c² R² int chi². Its shifted kinetic energy per mass is O(R^-2)+O(R^-4), since the carrier cancels the k² term and the real and imaginary derivative terms have zero cross term. Its potential energy per mass is

    -beta c²/2 (int chi⁴/int chi²) + gamma c⁴/3 (int chi⁶/int chi²).

Fix chi, choose R to realize every sufficiently large mass exactly, take limsup, and then approximate the indicator. This proves lim_{m->infty} e(m)=-C.

Continuity of I on (0,infty): in a compact positive mass interval, approximate minimizers with E<=1 have uniformly bounded T by square completion, hence bounded H² by D^(1/2)<=T^(1/2)+k² M^(1/2). The existing H² sup bound gives uniformly bounded Q,S. Amplitude scaling a mass-a approximate minimizer by sqrt(b/a) changes its energy by O(|b-a|), uniformly in that interval. Compare both directions and pass to infima. Thus I is locally Lipschitz, as is e.

For any target A>0, the lower bound above gives e(m)>=L(A)>-C for 0<m<=A. Pick a level ell strictly between -C and L(A). Continuity, the small-mass limit, and the large-mass limit imply a first crossing b=inf{m>0:e(m)<=ell}>A with e(b)=ell. Every 0<a<b has e(a)>ell and e(b-a)>ell. Multiplying by the masses and adding proves strict binding at b for EVERY split. This establishes an unbounded set of binding masses for each fixed admissible tuple, not necessarily an entire tail or a monotone e.

By the concentration-compactness argument generalized in PR #99, these binding masses also have attained infima and compactness modulo translations (analytical consequence; Lean verification not claimed here). In particular no finite upper mass ceiling beyond which all masses fail to bind can exist.

## 5. Remaining exact obstruction

No proof that e decreases strictly at every nonzero-shell mass, nor any exact equality split, is obtained. The first-crossing argument cannot rule out non-record masses that might bind or fail to bind. Anisotropic carrier stretching works on narrow packets but not automatically on arbitrary near-minimizers with angularly broad Fourier support. One must control the nonzero shell without a priori symmetry, a prescribed carrier, or assuming the very attainment being proved. Preserve the original GC16 status; distinguish the new analytical claims from the existing kernel-verified sufficient bound.

Literature context (not a proof of the new claims): Fernández, Jeanjean, Mandel, Mariş, JDE 330 (2022), DOI 10.1016/j.jde.2022.04.037 (single focusing power); Ma, Chang, Feng, EJDE 2024(29), DOI 10.58997/ejde.2024.29 (combined powers, different hypotheses). No priority claim.
