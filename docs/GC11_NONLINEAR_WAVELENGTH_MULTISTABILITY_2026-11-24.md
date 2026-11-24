# GC11: Nonlinear wavelength multistability in the original Hamiltonian

**Status:** analytical counterexample in the specified affine/carrier energy topology; Lean algebra submitted for checking, continuum correspondence not yet kernel formalized. Do not close #82 or change the GC registry on this basis alone.

## 1. Source and model freeze

The original GC11 in reyes-problem-repository/FORMAL_PROBLEMS.md is the fourth-order cubic–quintic Schrödinger flow on R², not E13/E14's complex dissipative band-pass flow. Preserve the exact F01 Hamiltonian and equation:

    i u_t = (Δ + k0²)² u + f(|u|²) u,
    f(x) = -β x + γ x²,   β, γ, k0 > 0.

Its kinetic symbol is h(K)=(|K|²-k0²)². H = ∫ |(Δ+k0²)u|² + F(|u|²), where F(x)=-βx²/2+γx³/3. The vacuum has real temporal frequencies, not a finite band of exponential growth. The linear oscillatory minimum in DispersionMinimum.lean concerns a separate quadratic dispersion, and BandPassFlow.lean/SwiftHohenbergL2.lean concern the dissipative model. PR #98's equal-frequency algebra is not a stability proof. Issue #76 remains a separate integrated morphogenesis challenge.

## 2. Exact solutions and the stable stationary interval

Set q=|K|², δ=q-k0² and ρ>0. Then

    U(K,ρ;t,x)=sqrt(ρ) exp(i(K·x-ωt)),
    ω=h(K)+f(ρ).

The exact invariant single-mode amplitude ODE is i a'=(h(K)+f(|a|²))a, so |a| is conserved; there is no dissipative amplitude saturation. Static equilibria have ω=0 and

    ρ±(q)=[β ± sqrt(β²-4γ(q-k0²)²)]/(2γ).

The upper branch exists for |q-k0²|≤β/(2 sqrt(γ)). On

    k0² < q < k0² + sqrt(3) β/(4 sqrt(γ)),

it satisfies ρ+>3β/(4γ), hence the globally coercive criterion below. In fact the local coercivity argument extends the open interval to q<k0²+β/(2 sqrt(γ)).

Concrete static witnesses at β=γ=k0=1:

    q1=7/5, ρ1=4/5; q2=13/10, ρ2=9/10.

Both have ω=0, q>1 and ρ>3/4. Their radii differ, so neither translation, phase nor rotation identifies them. There is a continuous branch of such witnesses with nearby radii and amplitudes, not merely two frequency-degenerate modes.

## 3. Exact Bloch/sideband calculation on R²

Factor out the plane wave; write the residual complex perturbation as η. Its real-linear linearization is

    i η_t = [h(K+D)-h(K)]η + c(η+conj η),
    D=-i∇, c=ρ f'(ρ)=ρ(-β+2γρ).

For p∈R², put s=|p|², t=K·p. The paired modes ηhat(p), conj ηhat(-p) obey the matrix

    [[O+E+c, c], [-c, O-E-c]],
    E=s²+2δs+4t², O=4t(δ+s).

Characteristic polynomial (z-O)²-E(E+2c); frequencies O±sqrt(E(E+2c)).
The linearization has no exponentially growing sideband iff E(E+2c)≥0 for every p.

* c>0, δ≥0: all sidebands real.
* c>0, δ<0: take p perpendicular to K with s>0 small. Then E=s(s+2δ) lies in (-2c,0), hence exponential growth.
* c<0: choose a transverse s with E in (0,-2c). For δ≥0 take s small; for δ<0 take s just above -2δ. This gives exponential growth.
* c=0: all frequencies real, but spectral reality alone is not nonlinear stability.

These statements cover the exact continuum sideband discriminant for plane waves, not all periodic profiles. At p=0 the phase mode is neutral; real frequencies are not a uniform semigroup bound in the unmodulated H² norm. The longitudinal/transverse branches are exact, not a near-onset approximation. On a fixed torus only lattice p are allowed, and the discriminant test is correspondingly discrete; a continuum unstable sideband need not be available on a small torus.

## 4. Nonlinear energy theorem

**Theorem.** Fix β,γ,k0>0, K∈R² with q>k0², ρ>β/(2γ). On either the fixed flat square torus (K a lattice vector) or R² with perturbations of the affine form described below, the exact plane wave is orbitally stable in the following topology. On the torus use H² distance to its constant-phase orbit after carrier removal. On R² use the carrier energy distance

    dρ(z)=||∇z||_{H¹}+|||z|²-ρ||₂,

for z=√ρ+η, η∈H²(R²), modulo constant phase (allow η after the corresponding phase adjustment). Global H² evolution is asserted for the affine perturbation η, not uniform boundedness of its L² norm for all time. Stability means for every ε>0 there is d0>0 such that initial distance <d0 implies distance <ε for all t. If ρ>3β/(4γ), the energy bound is global rather than merely local.

**Proof.** First remove carrier and temporal frequency and translate by the group velocity v=∇h(K)=4δK: z(t,y)=exp(-i(K·(y+vt)-ωt))u(t,y+vt). This is a change of variables, not an alteration to the PDE. Then

    i z_t = g(D) z + [f(|z|²)-f(ρ)]z,
    g(p)=h(K+p)-h(K)-v·p
        = (s+2t)²+2δs.

The multiplier annihilates constants, is real, and grows at fourth order. On R² use the affine realization η=z-√ρ; on the torus use the full z. Define the finite relative energy (Parseval normalized consistently)

    L(z)= ∫ g(p)|ηhat(p)|² dp + ∫ Wρ(|z|²) dx,
    Wρ(x)=F(x)-F(ρ)-f(ρ)(x-ρ)
          =(x-ρ)²[γ(x+2ρ)/3-β/2].

On the torus replace the Fourier integral by the series for z (constant mode has coefficient g(0)=0). This is the Hamiltonian in the moving frame, renormalized by the background chemical potential. Differentiating gives 2 Re ⟨g(D)z+[f(|z|²)-f(ρ)]z,z_t⟩=0 for sufficiently smooth solutions. For H² data use the local H² solution and smooth approximation as below; all terms of L are continuous in the affine H² norm.

Kinetic coercivity: g≥2δs, and using t²≤qs,

    s² ≤ 2g + (4k0²+4q)s.

Thus the kinetic term controls ||∇z||_{H¹}², with positive constants depending only on δ and q. For ρ>3β/(4γ) the potential globally satisfies Wρ(x)≥(2γρ/3-β/2)(x-ρ)² for x≥0. This proves L≥C dρ(z)² (with the constant absorbing the squared sum).

For the sharper local range ρ>β/(2γ), let a=γρ-β/2>0. The same coefficient is a+(γ/3)(x-ρ), so it stays ≥a/2 for |x-ρ|≤3a/(2γ). Small dρ implies this uniform density condition: on unit balls, ||z||²_L² ≤ρ|B|+|B|^(1/2)|||z|²-ρ||₂; local H² embedding bounds ||z||∞ using this and the global derivative terms. Product differentiation now gives

    || |z|²-ρ ||_{H²}
      ≤ C [ || |z|²-ρ ||₂ + ||z||∞ ||∇z||_{H¹}
                                   + ||∇z||₄² ].

The last norm is bounded using H¹→L⁴ in two dimensions. The global H²→L∞ embedding for the density residual (or its periodic version) makes the density deviation uniformly small as dρ→0. Hence L≥C dρ² on a fixed small distance neighborhood. Conversely L≤C' dρ² there by the polynomial formula and g≤C(s+s²). Choose the initial distance so that L(z0) is smaller than the coercive bound on the boundary of the neighborhood. Continuity and conservation prevent first exit. This is Lyapunov stability, not convergence to an attractor.

Local existence in the affine H² class follows directly from the unitary Fourier group exp(-it g(D)) and contraction on C([-T,T];H²). The forcing N(η)=[f(|√ρ+η|²)-f(ρ)](√ρ+η) is a polynomial in η and conj η with zero constant term, hence locally Lipschitz by the two-dimensional H² algebra property. The torus uses the identical proof with Fourier series. Smooth data persist locally at higher regularity by the polynomial Sobolev tame estimate on bounded H² balls, giving conservation by approximation and local continuous dependence. In the stable neighborhood, the uniform ||z||∞ estimate above and density control give ||N(η)||₂≤C|||z|²-ρ||₂. Duhamel and unitarity bound ||η(t)||₂≤||η(0)||₂+C|t| on each existence interval. The derivative terms stay bounded, so the H² continuation criterion rules out finite-time termination. The proof also works backward in time. No use is made of the localized F01 whole-space mass conservation for the non-L² plane wave itself.

On a fixed torus, Poincaré controls z minus its mean in H² via the derivative terms. The density residual controls |mean(z)|²-ρ because the spatial variance is already small. Taking the phase of the mean then controls the H² distance to the constant-phase orbit. The reverse small-distance implication follows by the periodic Sobolev algebra estimate. Translation in the moving frame does not change these norms. This proves the stated torus result.

On R², dρ is an energy distance, not the affine H² norm. It identifies global phase and controls derivatives and density; it does not bound the total L² phase perturbation. Different K are not close in the unmodulated uniform norm nor in a single fixed-carrier affine H² chart. A precise common topology allowing nearby periodic equilibria is the disjoint union of affine carrier charts with parameters (K,ρ) and product topology: distance to the orbit at (K0,ρ0) is |K-K0|+|ρ-ρ0|+dρ(z), with z obtained by removing its own carrier. Equivalently compare derivative profiles modulo constant phase and density residuals, together with the parameters. These labels are uniquely determined for a nonzero affine background, and preserved by the constructed evolution. The estimates above are uniform on a compact neighborhood strictly inside q>k0², ρ>β/(2γ), so each equilibrium is stable in this common topology as well. The exact static branch is continuous in it, and in C^j_loc for every finite j, so no stable member is locally isolated in wavelength in this explicitly stated class. This does not prove stability against arbitrary uniformly local perturbations that lack an affine finite-energy carrier.

## 5. Finite-domain witness and conditional uniqueness

On the same fixed torus of side L=40π at β=γ=k0=1, take K=(21/20,0) and K'=(22/20,0), lattice indices 21 and 22. Both satisfy 0<q-1<sqrt(3)/4, so their upper static density branches are stable by the global coercive theorem. They have different wavelengths on one domain. They are distinct states, not necessarily arbitrarily close in that fixed torus H² norm. On larger tori the spacing of available radii tends to zero. The exact discrete sideband discriminant also applies to all perturbations on the given torus, not only perturbations along the carrier direction.

There is a meaningful restricted uniqueness statement: on a torus whose lattice contains the preferred shell, at fixed mass density ρ>3β/(4γ), the global Hamiltonian minimizers all lie on |K|=k0 and have constant modulus. Indeed subtract F(ρ)+f(ρ)(|u|²-ρ), integrate using the mass constraint, and apply global Wρ≥C(|u|²-ρ)² and the nonnegative shell kinetic energy. A shell plane wave attains the lower bound, and every minimizer must saturate both nonnegative terms. This selects the radius, not direction or general dynamically stable states. Off-shell waves remain locally stable via the momentum-tilted energy. A Hamiltonian equation has no dissipative selection mechanism; exact initial pure modes stay in their own mode. No general mode-competition dynamics, front selection, or attraction theorem is implied.

The full nonlinear stability at the marginal boundaries q=k0² and ρ=β/(2γ), other nonlinear periodic profiles, all finite-domain parameter classifications, and stability in broader uniformly local spaces remain open here. Nonlinear stability inside the open region and the explicit counterexample suffice to refute universal uniqueness in the declared class.

## 6. Prior art and formal scope

* Cross & Hohenberg, Pattern formation outside of equilibrium, Rev. Mod. Phys. 65 (1993), DOI 10.1103/RevModPhys.65.851: standard dissipative pattern stability bands/Eckhaus theory, different evolution law.
* Bifurcation structure and the Eckhaus instability, Phys. Rev. Lett. 63 (1989), DOI 10.1103/PhysRevLett.63.2048: finite-domain Swift–Hohenberg stability, not the Hamiltonian model.
* Modulation instability, solitons, and interactions in one-dimensional competing cubic-quintic nonlinear media with fourth-order diffraction, Phys. Rev. A (2025), DOI 10.1103/xmsj-ktq7: closely related sideband methods, not automatically the present two-dimensional shifted dispersion or its affine nonlinear energy theorem.
* Global well-posedness of the Gross–Pitaevskii and cubic–quintic nonlinear Schrödinger equations with non-vanishing boundary conditions, arXiv:1112.1354: precedent for nonzero-background energy methods in second-order NLS, different dispersion/dimensions.

These are relevant comparisons, not an exhaustive priority search. Plane-wave substitution, paired sideband analysis and Lyapunov stability are established methods. The model-specific shifted-symbol coercivity, density threshold and explicit static branch together are a repository contribution; mathematical novelty beyond that has not been certified.

Lean GC11Coercivity.lean reuses RemainingCores.shellSymbol and encodes the shifted kinetic identity, pointwise kinetic/density bounds, sideband characteristic algebra, a sufficient discriminant condition, and exact distinct stationary data. GC11StaticWave.lean additionally submits the exact classical one-coordinate stationary differential equation for the two concrete waves, with the 2D embedding interpreted analytically. The actual 2D Fourier/Bloch correspondence, affine PDE existence/conservation and nonlinear orbital stability are not yet encoded. A Lean build checks only these exact algebraic statements. No sorry/axiom declarations are intended. Continue with the TorusFourier and BandPass Fourier Sobolev infrastructure for the periodic bridge, and H2Algebra/CubicQuinticFlow for the affine whole-space bridge. The original finite-mass F01 solver cannot directly be invoked for non-L² states.

### Integrated torus milestone (follow-up)

GC11TorusEnergy.lean now defines the carrier kinetic symbol on the actual 2D Fourier lattice, proves summability of both kinetic and derivative energies using BandPass.InH, and integrates the pointwise density bound over the continuous H² representative BandPass.Phi. The theorem integrated_coercivity is an inequality for all H² fields, not a Galerkin truncation. conserved_energy_bound uses an explicit conservation hypothesis for trajectories; the Hamiltonian conservation and orbital-distance bridge are not asserted as kernel-proved. Focused CI is pending. The normalized Haar measure convention multiplies both energy and squared distances by the same constant relative to Lebesgue measure.

### Sharp sideband and stationary family milestones

GC11SidebandClassification.lean now submits necessity as well as sufficiency of the nonnegative discriminant criterion: for every real s≥0 and t, the discriminant is nonnegative iff c=0 or (q≥k0² and c>0). Necessity is witnessed by a transverse positive radius using the exact roots of s²+2δs. It also parameterizes q=k0²+sqrt(βρ−γρ²) and proves exact stationarity and strict decrease with ρ on the upper branch. These are algebraic results; a two-dimensional Bloch/Fourier correspondence is still required.

### Shell endpoint on a fixed torus: analytical individual-orbit stability

Suppose the preferred shell contains a lattice vector and ρ>3β/(4γ). At fixed mass density ρ the entire minimizer set consists exactly of finitely many constant-phase circles of pure shell modes. To see this, equality in the density and kinetic lower bounds forces constant modulus and Fourier support on the finite shell. A finite Fourier polynomial of constant nonzero modulus is a monomial: if two or more coefficients are nonzero, choose a real linear functional on the frequency lattice with distinct values on the support. The difference of the extreme frequencies has a unique ordered representation as a difference of support points, so the corresponding Fourier coefficient of |u|² is a nonzero product, contradicting constant modulus.

Minimizing sequences at this mass are H²-precompact modulo the compact phase circles. The off-shell coefficients tend to zero in H² because the lattice gap gives a bounded ratio (1+|ξ|²)²/(|ξ|²−k0²)² outside the finite shell. The remaining coefficients belong to a bounded finite-dimensional space. Every limit saturates the density and kinetic bounds. The distinct circles have positive separation in H²; continuity of solutions and conservation of energy and mass prevent near-minimizer trajectories from jumping between them. Thus each shell plane wave is individually orbitally stable on the fixed torus at fixed mass. For nearby mass, normalize by sqrt(M0/M) to reduce to the fixed-mass compactness argument: mass conservation fixes the factor, the H² norms are bounded by energy coercivity, and the normalized energies differ by o(1) as M→M0. This extends stability to nearby masses, not just perturbations of exactly prescribed mass. Local and global H² existence follows by the torus Fourier unitary group, polynomial H² algebra, conservation by smooth approximation and the bound of the original energy below by kinetic energy minus a constant depending on mass. The endpoint q=k0² is therefore resolved on a fixed torus at high density analytically, but not for whole-space affine energy topology.

### Additional prior-art check

Jiang, Ge and Shen, *Diffraction managed modulation instability of two-dimensional plane wave in competing cubic-quintic nonlinear media*, Physica Scripta 100 (2025), DOI 10.1088/1402-4896/ad9ef3, is a particularly close two-dimensional fourth-order diffraction reference; compare its diffraction-management coefficients and linear analysis before claiming novelty of the sideband theorem. The nonlinear carrier energy and exact frozen stationary interval require separate comparison. No novelty certificate is claimed.

### Quantitative phase-orbit bridge on the actual Fourier H² torus

GC11TorusOrbit.lean submits a direct estimate for the H² Hilbert-space distance to the constant-phase orbit in the carrier frame. Put d=(2π/L)² and Cgap=2+1/d. For any nonzero Fourier lattice index, s=|ξ_n|²≥d and (1+s)²≤Cgap(s+s²). Hence the weighted nonzero-mode coefficient tail T_H² is at most Cgap times the derivative energy D. The L² tail T_L² is at most T_H². Writing a=|c_0| and R=sqrt(ρ), choose the phase of c_0 (arbitrary if zero); the squared H² distance to that constant is exactly T_H²+(a-R)². Since (a-R)²≤|a²-ρ|≤|M-ρ|+T_L², we get the quantitative estimate
    dist_H²(c, phaseOrbit ρ)² ≤ |M-ρ| + 2 Cgap D.
Combined with integrated_coercivity and explicit mass/relative-energy conservation, this proves the uniform-in-time bound
    dist_H²(c(t), phaseOrbit ρ)² ≤ |M(0)-ρ| + 2 Cgap Ckin L_rel(c(0)).
In particular, no exact fixed-mass restriction is required. orbit_near_of_small_mass_energy states the epsilon-level conclusion given small initial mass-energy defect. The formal bridge from initial H² proximity to small initial defect and the actual Hamiltonian PDE conservation/solution construction remain open in Lean. All newly added declarations await a successful focused kernel build; this is not a verified status change.

### Initial proximity and quantified stability implication

GC11TorusInitial.lean submits the converse smallness bridge: the exact Fourier continuous representative of a constant coefficient vector is the constant field itself. For H² distance e≤1 to any phase representative of modulus sqrt(ρ), the Fourier kinetic energy is at most (2+10q)e², and the Sobolev embedding gives pointwise density defect at most S(2sqrt(ρ)+S)e, where S is the existing torus H² embedding constant. Integrating gives the mass defect O(e) and relative potential O(e²), uniformly in the phase. Thus the initial defect in the previous orbit bound is O(e). The theorem orbital_stability_conserving supplies the full epsilon/delta statement for all trajectories in the actual H² space with explicit conservation of mass and relative energy. The remaining torus PDE obligation is to prove that its original Hamiltonian dynamics, after carrier removal, produces such conserving trajectories; no conservation or well-posedness is asserted by this theorem. Focused CI pending.
