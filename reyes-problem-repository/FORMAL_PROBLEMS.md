# The Reyes Problem Repository: Mathematical Problem Statements

**Original mathematically scoped collection:** GC01–GC65. The full living [300-problem roadmap](./ROADMAP_300.md) contains GC66–GC300 as preliminary research-question sketches, not yet formally quantified mathematical statements. **Status:** Proposed precisely scoped research problems, **not** claims of novelty, unsolved status, difficulty, or independence. Several are classification problems, some have known elementary answers or obstructions, and several require additional modeling choices before a definitive theorem can be stated. The word “determine” explicitly permits a negative answer or a counterexample. Mathematical statements are research specifications, not verified results. Literature reviews are pending.

**Shared notation:** $\mathbb R^d$ is Euclidean space, $\mathbb T^d=(\mathbb R/2\pi\mathbb Z)^d$, $\Delta$ is the Laplacian, $H^s$ denotes the $L^2$ Sobolev space, and all solutions use the natural strong/mild solution concept where it exists. Parameters and operators not fixed by a question must be frozen in its dedicated problem dossier before attempting a proof.

## GC01: Universal orbital stability

**Problem.** Classify all standing waves φ∈H²(R²) of $i\partial_t u=(\Delta+k^2)^2u-\beta|u|^2u+\gamma|u|^4u$, β,γ>0, whose phase-translation orbits are stable in H². Give necessary and sufficient spectral/variational conditions, including excited states.

**Resolution criterion.** Supply a theorem with all quantifiers, domains, topologies and parameters fixed, together with a proof or an explicit counterexample. Compare against existing results and verify only the exact encoded claims in Lean where applicable.

## GC02: Long-time asymptotic stability

**Problem.** For the same equation, characterize standing waves for which every sufficiently small localized perturbation decomposes as a modulated wave plus a remainder converging to zero in a specified local norm as t→+∞; determine the sharp dispersive assumptions.

**Resolution criterion.** Supply a theorem with all quantifiers, domains, topologies and parameters fixed, together with a proof or an explicit counterexample. Compare against existing results and verify only the exact encoded claims in Lean where applicable.

## GC03: Global existence versus blow-up

**Problem.** For $i\partial_tu=(-\Delta)^pu-\beta|u|^{r-1}u+\gamma|u|^{s-1}u$ on R^d, p∈N, 1<r<s, β,γ>0, classify (d,p,r,s) for which every H^p datum generates a global solution, and exhibit finite-time blow-up whenever the universal claim fails.

**Resolution criterion.** Supply a theorem with all quantifiers, domains, topologies and parameters fixed, together with a proof or an explicit counterexample. Compare against existing results and verify only the exact encoded claims in Lean where applicable.

## GC04: Stable multi-wave interactions

**Problem.** For the fourth-order cubic–quintic equation on R², determine whether there exist solutions with two distinct, nonzero localized profiles separating linearly as t→∞ and stable under sufficiently small H² perturbations.

**Resolution criterion.** Supply a theorem with all quantifiers, domains, topologies and parameters fixed, together with a proof or an explicit counterexample. Compare against existing results and verify only the exact encoded claims in Lean where applicable.

## GC05: Breather existence and classification

**Problem.** Determine whether the fourth-order cubic–quintic equation on R² admits a spatially localized, genuinely time-periodic H² solution not equivalent to a standing wave under phase and spatial symmetries; classify all such solutions if they exist.

**Resolution criterion.** Supply a theorem with all quantifiers, domains, topologies and parameters fixed, together with a proof or an explicit counterexample. Compare against existing results and verify only the exact encoded claims in Lean where applicable.

## GC06: Self-confinement criteria

**Problem.** For $E(u)=\int_{\mathbb R^2}\left(|(\Delta+k^2)u|^2-\frac\beta2|u|^4+\frac\gamma3|u|^6\right)\,dx$ at fixed ∥u∥²₂=m, determine exactly which (k,β,γ,m) admit an attained infimum and characterize loss of compactness.

**Resolution criterion.** Supply a theorem with all quantifiers, domains, topologies and parameters fixed, together with a proof or an explicit counterexample. Compare against existing results and verify only the exact encoded claims in Lean where applicable.

## GC07: Curvature-induced localization

**Problem.** Let $H_V=(\Delta+k^2)^2+V(x)$ on L²(R²), with real smooth V(x)→0. Characterize potentials V for which H_V has a nonzero exponentially decaying eigenfunction with eigenvalue strictly below its essential spectrum.

**Resolution criterion.** Supply a theorem with all quantifiers, domains, topologies and parameters fixed, together with a proof or an explicit counterexample. Compare against existing results and verify only the exact encoded claims in Lean where applicable.

## GC08: Admissible curvature closures

**Problem.** Fix a dimension $d\ge 2$ and a regularization parameter $\varepsilon>0$. For a smooth complex field $u:\mathbb R^d\to\mathbb C$, define the regularized curvature functional

```math
K_{\varepsilon}(u) = \nabla \cdot \left( \frac{\mathrm{Im}(\overline{u}\,\nabla u)}{\varepsilon + |u|^2} \right)
```

Let $C$ be a real-valued local differential operator of order at most two on smooth complex fields. Assume that $C$ is invariant under constant phase rotations, translations, and proper spatial rotations:

```math
C(e^{i\theta}u)=C(u),\qquad
C(u(\,\cdot-a))(x)=C(u)(x-a),
```

```math
C(u\circ R)(x)=C(u)(Rx),
\qquad
\theta\in\mathbb R,\ a\in\mathbb R^d,\ R\in SO(d).
```

Require agreement with $K_\varepsilon$ on every nonvanishing constant-amplitude plane wave

```math
u(x)=A e^{i(\xi\cdot x+\theta_0)},
\qquad A>0,\quad \xi\in\mathbb R^d.
```

**Determine whether these conditions uniquely characterize $K_\varepsilon$. If not, construct inequivalent operators $C$ satisfying all conditions and characterize the resulting freedom under explicitly stated regularity and locality assumptions.**

**Initial counterexample check.** The plane-wave condition alone cannot establish uniqueness: on every constant-amplitude plane wave, both $K_\varepsilon(u)$ and $\Delta(|u|^2)$ vanish. Consequently, for every real constant $\lambda$,

```math
C_\lambda(u)=K_\varepsilon(u)+\lambda\,\Delta(|u|^2)
```

satisfies the stated symmetry and plane-wave conditions. The uniqueness version of the problem is therefore **refuted** for this unrestricted operator class. The remaining classification problem is to identify additional admissibility axioms that narrow the class, and determine whether any such axioms yield uniqueness.

**Resolution criterion.** State the exact operator class and additional axioms, classify all admissible operators or prove a sharp uniqueness theorem, and distinguish analytic proofs from any corresponding Lean formalization.

## GC09: Topological confinement protection

**Problem.** For continuous u:R³→C with |u(x)|→a>0 as |x|→∞, determine whether nontrivial winding of u/|u| on loops can enforce a positive lower bound on an explicitly chosen coercive wave energy and preclude decay through finite-energy evolution.

**Resolution criterion.** Supply a theorem with all quantifiers, domains, topologies and parameters fixed, together with a proof or an explicit counterexample. Compare against existing results and verify only the exact encoded claims in Lean where applicable.

## GC10: Dimensional localized-energy classification

**Problem.** For $E_d(u)=\int_{\mathbb R^d}(|\Delta u|^2+|u|^2-|u|^4+|u|^6)\,dx$, determine dimensions d and constraints m>0 for which there exists a nonzero finite-energy minimizer of E_d on {∥u∥²₂=m}.

**Resolution criterion.** Supply a theorem with all quantifiers, domains, topologies and parameters fixed, together with a proof or an explicit counterexample. Compare against existing results and verify only the exact encoded claims in Lean where applicable.

## GC11: Nonlinear finite-wavelength selection

**Problem.** For the fourth-order cubic–quintic Schrödinger flow on R², determine whether a stable nonconstant periodic pattern has a uniquely selected spatial frequency among all nearby periodic equilibria, and identify parameter conditions or counterexamples.

**Resolution criterion.** Supply a theorem with all quantifiers, domains, topologies and parameters fixed, together with a proof or an explicit counterexample. Compare against existing results and verify only the exact encoded claims in Lean where applicable.

## GC12: Nonlinear spectral-gap persistence

**Problem.** Let $L=-(1+\Delta)^2+\mu-3u_*^2+5u_*^4$ be the linearization at a periodic stationary solution u_* of $\partial_tu=\mu u-(1+\Delta)^2u-u^3+u^5$. Determine when a spectral gap in a fixed Floquet fiber persists under all sufficiently small periodic perturbations of u_*.

**Resolution criterion.** Supply a theorem with all quantifiers, domains, topologies and parameters fixed, together with a proof or an explicit counterexample. Compare against existing results and verify only the exact encoded claims in Lean where applicable.

## GC13: Interband nonlinear energy transfer

**Problem.** For the cubic–quintic Schrödinger equation on the torus T², partition Fourier modes into two disjoint finite shells A,B. Determine whether a universal bound sup_{t∈[0,T]}∑_{n∈B}|û_n(t)|² ≤ F(T,∥u₀∥H²,∑_{n∈B}|û_n(0)|²) exists with F(T,M,0)=0; prove or refute.

**Resolution criterion.** Supply a theorem with all quantifiers, domains, topologies and parameters fixed, together with a proof or an explicit counterexample. Compare against existing results and verify only the exact encoded claims in Lean where applicable.

## GC14: Spectral concentration versus localization

**Problem.** For u∈L²(R^d), characterize all nonzero functions that are exponentially localized in physical space and have Fourier transform supported in a compact annulus. Determine whether such functions can exist.

**Resolution criterion.** Supply a theorem with all quantifiers, domains, topologies and parameters fixed, together with a proof or an explicit counterexample. Compare against existing results and verify only the exact encoded claims in Lean where applicable.

## GC15: Finite-mode invariant manifolds

**Problem.** For the cubic–quintic Schrödinger flow on T², determine whether any finite-dimensional subspace spanned by more than one Fourier mode is invariant under the full nonlinear flow for all initial data in that subspace; classify all such subspaces.

**Resolution criterion.** Supply a theorem with all quantifiers, domains, topologies and parameters fixed, together with a proof or an explicit counterexample. Compare against existing results and verify only the exact encoded claims in Lean where applicable.

## GC16: Strict binding across masses

**Problem.** For the energy in GC06, determine all masses m>0 satisfying strict subadditivity $I(m)<I(a)+I(m-a)$ for every 0<a<m, where $I(m)=\inf_{\|u\|_{L^2}^2=m}E(u)$.

**Resolution criterion.** Supply a theorem with all quantifiers, domains, topologies and parameters fixed, together with a proof or an explicit counterexample. Compare against existing results and verify only the exact encoded claims in Lean where applicable.

## GC17: Constrained-minimizer uniqueness

**Problem.** For the energy in GC06, determine whether every fixed-mass minimizer is unique up to phase and translation; either prove uniqueness for a specified parameter region or exhibit two inequivalent minimizers.

**Resolution criterion.** Supply a theorem with all quantifiers, domains, topologies and parameters fixed, together with a proof or an explicit counterexample. Compare against existing results and verify only the exact encoded claims in Lean where applicable.

## GC18: Symmetry-breaking thresholds

**Problem.** For the energy in GC06, determine whether there is a mass m_* at which every minimizer changes from radially symmetric (up to translation) to nonsymmetric, and rigorously classify any such bifurcation.

**Resolution criterion.** Supply a theorem with all quantifiers, domains, topologies and parameters fixed, together with a proof or an explicit counterexample. Compare against existing results and verify only the exact encoded claims in Lean where applicable.

## GC19: Critical compactness failures

**Problem.** Determine the exact set of masses m for which every minimizing sequence for I(m) in GC16 is precompact in H² modulo translations; construct dichotomizing sequences at every failure.

**Resolution criterion.** Supply a theorem with all quantifiers, domains, topologies and parameters fixed, together with a proof or an explicit counterexample. Compare against existing results and verify only the exact encoded claims in Lean where applicable.

## GC20: Metastable energy landscapes

**Problem.** For the gradient flow $\partial_tu=-\delta E/\delta u$ associated with $E(u)=\int_{\mathbb T^2}(|(\Delta+1)u|^2-\frac\mu2u^2+\frac14u^4)\,dx$, characterize all non-global local minima and compute whether arbitrarily long metastable lifetimes occur for bounded-energy initial data.

**Resolution criterion.** Supply a theorem with all quantifiers, domains, topologies and parameters fixed, together with a proof or an explicit counterexample. Compare against existing results and verify only the exact encoded claims in Lean where applicable.

## GC21: Ghost-free higher-derivative dynamics

**Problem.** For real scalar Lagrangians $L(\phi,\partial\phi,\partial^2\phi)$ polynomial of total degree ≤4 and invariant under spacetime translations, classify nondegenerate models with bounded-below canonical Hamiltonian after all constraints; establish whether any genuinely fourth-order time dynamics remain.

**Resolution criterion.** Supply a theorem with all quantifiers, domains, topologies and parameters fixed, together with a proof or an explicit counterexample. Compare against existing results and verify only the exact encoded claims in Lean where applicable.

## GC22: UV well-posedness classification

**Problem.** For linear constant-coefficient scalar PDEs $P(\partial_t,\nabla)u=0$ of temporal order ≤4 and spatial order ≤4, give an algebraic necessary and sufficient condition on the polynomial symbol for Hadamard well-posedness in a specified Sobolev energy space.

**Resolution criterion.** Supply a theorem with all quantifiers, domains, topologies and parameters fixed, together with a proof or an explicit counterexample. Compare against existing results and verify only the exact encoded claims in Lean where applicable.

## GC23: Physically stable wavelength selection

**Problem.** For a translation-invariant quadratic scalar field theory with positive Hamiltonian and finite-order local spatial derivatives, determine the minimal derivative order permitting a stable dispersion relation $\omega^2(q)>0$ whose unique global minimum occurs at $q>0$.

**Resolution criterion.** Supply a theorem with all quantifiers, domains, topologies and parameters fixed, together with a proof or an explicit counterexample. Compare against existing results and verify only the exact encoded claims in Lean where applicable.

## GC24: Hamiltonian constraint classification

**Problem.** For $L=\frac12\partial_\mu\phi\partial^\mu\phi-\frac a2(\Box\phi)^2-V(\phi)$, a≠0, compute the full Dirac constraint structure after introducing auxiliary variables and determine whether the reduced Hamiltonian is bounded below for any smooth V.

**Resolution criterion.** Supply a theorem with all quantifiers, domains, topologies and parameters fixed, together with a proof or an explicit counterexample. Compare against existing results and verify only the exact encoded claims in Lean where applicable.

## GC25: Consistent parent theories

**Problem.** Determine whether a Lorentz-invariant, local, finite-field, second-order-in-time parent Lagrangian can reproduce a prescribed fourth-order effective scalar dispersion relation on a nonempty low-frequency interval without introducing negative-energy physical modes.

**Resolution criterion.** Supply a theorem with all quantifiers, domains, topologies and parameters fixed, together with a proof or an explicit counterexample. Compare against existing results and verify only the exact encoded claims in Lean where applicable.

## GC26: Local versus global identifiability

**Problem.** For an analytic map $F:\Theta\subset\mathbb R^{31}\to\mathbb R^N$ representing a fixed clipped spectral observation model, characterize the points θ where F is locally injective, and decide whether generic full-rank Jacobian implies global injectivity on Θ.

**Resolution criterion.** Supply a theorem with all quantifiers, domains, topologies and parameters fixed, together with a proof or an explicit counterexample. Compare against existing results and verify only the exact encoded claims in Lean where applicable.

## GC27: Minimal parameter-recovery observations

**Problem.** For the fixed 31-parameter clipped spectral model F, determine the smallest N and an explicit choice of N observation coordinates for which F is locally injective on a nonempty open parameter set; prove minimality.

**Resolution criterion.** Supply a theorem with all quantifiers, domains, topologies and parameters fixed, together with a proof or an explicit counterexample. Compare against existing results and verify only the exact encoded claims in Lean where applicable.

## GC28: Curvature-map noninjectivity

**Problem.** For the curvature map K_ε in GC08 on smooth complex fields over T², classify all pairs u,v with K_ε(u)=K_ε(v) but v not related to u by constant phase or translation; decide whether fibers are generically infinite-dimensional.

**Resolution criterion.** Supply a theorem with all quantifiers, domains, topologies and parameters fixed, together with a proof or an explicit counterexample. Compare against existing results and verify only the exact encoded claims in Lean where applicable.

## GC29: Noise-stable reconstruction

**Problem.** For the clipped spectral map F of GC26, determine whether there exist C,α>0 such that $\|\theta-\theta'\|\le C\|F(\theta)-F(\theta')\|^\alpha$ on a prescribed compact identifiable subset; find optimal α or prove no uniform estimate.

**Resolution criterion.** Supply a theorem with all quantifiers, domains, topologies and parameters fixed, together with a proof or an explicit counterexample. Compare against existing results and verify only the exact encoded claims in Lean where applicable.

## GC30: Partial-data spectral uniqueness

**Problem.** For a fourth-order elliptic operator $H=(\Delta+k^2)^2+V$ on a bounded smooth domain, determine whether eigenvalues measured on a specified boundary subset uniquely determine smooth real V; construct counterexamples if uniqueness fails.

**Resolution criterion.** Supply a theorem with all quantifiers, domains, topologies and parameters fixed, together with a proof or an explicit counterexample. Compare against existing results and verify only the exact encoded claims in Lean where applicable.

## GC31: Nonlinear Swift–Hohenberg attractors

**Problem.** For $\partial_tu=\mu u-(1+\Delta)^2u-u^3$ on T², characterize the global attractor in H² for μ>0, including its finite-dimensionality and whether every complete bounded trajectory converges to a stationary state.

**Resolution criterion.** Supply a theorem with all quantifiers, domains, topologies and parameters fixed, together with a proof or an explicit counterexample. Compare against existing results and verify only the exact encoded claims in Lean where applicable.

## GC32: Coarsening versus wavelength locking

**Problem.** For $\partial_tu=\mu u-(1+\Delta)^2u-u^3$ on T², determine whether every solution starting sufficiently near a stripe equilibrium converges to a stripe of the same wavelength or may undergo wavelength-changing defects.

**Resolution criterion.** Supply a theorem with all quantifiers, domains, topologies and parameters fixed, together with a proof or an explicit counterexample. Compare against existing results and verify only the exact encoded claims in Lean where applicable.

## GC33: Pattern robustness under disorder

**Problem.** For the Swift–Hohenberg equation on T² with bounded stationary potential V(x)u, determine a sharp norm threshold on V that guarantees persistence of a specified hyperbolic stationary stripe modulo its broken symmetries.

**Resolution criterion.** Supply a theorem with all quantifiers, domains, topologies and parameters fixed, together with a proof or an explicit counterexample. Compare against existing results and verify only the exact encoded claims in Lean where applicable.

## GC34: Defect nucleation and annihilation

**Problem.** For the Swift–Hohenberg equation on a two-dimensional torus, determine whether finite-energy solutions can create or annihilate phase-dislocation pairs from smooth initial data without leaving the regularity class of the global semiflow.

**Resolution criterion.** Supply a theorem with all quantifiers, domains, topologies and parameters fixed, together with a proof or an explicit counterexample. Compare against existing results and verify only the exact encoded claims in Lean where applicable.

## GC35: Infinite-domain pattern selection

**Problem.** For $\partial_tu=\mu u-(1+\Delta)^2u-u^3$ on R², determine whether there exist finite-energy perturbations of a periodic stripe that converge locally to a stripe with a uniquely determined wavelength independent of the perturbation.

**Resolution criterion.** Supply a theorem with all quantifiers, domains, topologies and parameters fixed, together with a proof or an explicit counterexample. Compare against existing results and verify only the exact encoded claims in Lean where applicable.

## GC36: Stable knotted wave configurations

**Problem.** For smooth $u:\mathbb R^3\to\mathbb C^2$ approaching a fixed unit vector at infinity, normalize to S³ and consider its Hopf degree after an explicitly fixed projection to S². Determine whether a coercive local energy with fourth-order gradients admits a stable stationary solution of each nonzero Hopf class.

**Resolution criterion.** Supply a theorem with all quantifiers, domains, topologies and parameters fixed, together with a proof or an explicit counterexample. Compare against existing results and verify only the exact encoded claims in Lean where applicable.

## GC37: Discrete particle-like solutions

**Problem.** For the energy in GC06, determine whether a sequence of localized minimizers has a discrete set of possible masses or frequencies after quotienting by phase and translation; prove discreteness or construct a continuous branch.

**Resolution criterion.** Supply a theorem with all quantifiers, domains, topologies and parameters fixed, together with a proof or an explicit counterexample. Compare against existing results and verify only the exact encoded claims in Lean where applicable.

## GC38: Quantized winding conservation

**Problem.** For smooth nonvanishing complex fields $u:\mathbb T^2\to\mathbb C\setminus\{0\}$, determine whether winding numbers along the two fundamental cycles are conserved by the cubic–quintic Schrödinger flow for as long as the solution remains nonvanishing, and whether winding can change at a finite-energy zero.

**Resolution criterion.** Supply a theorem with all quantifiers, domains, topologies and parameters fixed, together with a proof or an explicit counterexample. Compare against existing results and verify only the exact encoded claims in Lean where applicable.

## GC39: Coherent-state interaction laws

**Problem.** For the fourth-order cubic–quintic Schrödinger equation, determine whether asymptotically separated localized standing waves admit an effective finite-dimensional Hamiltonian interaction law with a rigorously bounded remainder as separation→∞.

**Resolution criterion.** Supply a theorem with all quantifiers, domains, topologies and parameters fixed, together with a proof or an explicit counterexample. Compare against existing results and verify only the exact encoded claims in Lean where applicable.

## GC40: Topology-changing singularities

**Problem.** For smooth maps $u(t):\mathbb R^3\to S^2$ of finite Skyrme-type energy, determine whether a global smooth energy-decreasing flow can change Hopf degree; if not, characterize the singularity or loss of boundary control required.

**Resolution criterion.** Supply a theorem with all quantifiers, domains, topologies and parameters fixed, together with a proof or an explicit counterexample. Compare against existing results and verify only the exact encoded claims in Lean where applicable.

## GC41: Decidability of PDE stability

**Problem.** Fix a computable encoding of rational-coefficient semilinear polynomial PDEs on T^d and rational smooth initial data. Decide whether an algorithm exists that always determines orbital stability of a specified computable stationary solution in H^s; prove decidability or undecidability for the stated class.

**Resolution criterion.** Supply a theorem with all quantifiers, domains, topologies and parameters fixed, together with a proof or an explicit counterexample. Compare against existing results and verify only the exact encoded claims in Lean where applicable.

## GC42: Complexity of certified wave evolution

**Problem.** Fix a rational spectral Galerkin discretization of the cubic–quintic Schrödinger equation on T², with n modes, input bit length b and target error 2^(−p). Determine asymptotically tight bit-complexity bounds for certified approximation on [0,T].

**Resolution criterion.** Supply a theorem with all quantifiers, domains, topologies and parameters fixed, together with a proof or an explicit counterexample. Compare against existing results and verify only the exact encoded claims in Lean where applicable.

## GC43: Discrete-wave computational universality

**Problem.** Define a one-dimensional finite-alphabet radius-one wave-cell automaton with an explicit reversible local update rule. Determine whether there exists a fixed rule capable of simulating every Turing machine with polynomial overhead under a uniform encoding.

**Resolution criterion.** Supply a theorem with all quantifiers, domains, topologies and parameters fixed, together with a proof or an explicit counterexample. Compare against existing results and verify only the exact encoded claims in Lean where applicable.

## GC44: Sequential-work lower bounds

**Problem.** For the specific finite-alphabet automaton in GC43, determine whether every exact simulator computing the state after T steps requires Ω(T) sequential dependency depth in a precisely stated bounded-fan-in circuit model; prove the bound or exhibit a sublinear-depth simulator.

**Resolution criterion.** Supply a theorem with all quantifiers, domains, topologies and parameters fixed, together with a proof or an explicit counterexample. Compare against existing results and verify only the exact encoded claims in Lean where applicable.

## GC45: Precision and noise limits

**Problem.** For rational initial data of bit length b in a fixed nonlinear wave equation on T², determine the minimal precision p(T,ε,b) required by any certified numerical algorithm to guarantee H² error ≤ε at time T, distinguishing upper from information-theoretic lower bounds.

**Resolution criterion.** Supply a theorem with all quantifiers, domains, topologies and parameters fixed, together with a proof or an explicit counterexample. Compare against existing results and verify only the exact encoded claims in Lean where applicable.

## GC46: Verified infinite-dimensional evolution

**Problem.** Formalize in Lean 4 global existence, uniqueness, continuous dependence, and mass-energy conservation for the exact fourth-order cubic–quintic Schrödinger flow on R² in H², with no axioms beyond Lean and imported Mathlib foundations.

**Resolution criterion.** Supply a theorem with all quantifiers, domains, topologies and parameters fixed, together with a proof or an explicit counterexample. Compare against existing results and verify only the exact encoded claims in Lean where applicable.

## GC47: Formal concentration compactness

**Problem.** Formalize in Lean 4 a concentration-compactness theorem for bounded sequences in H²(R²), including vanishing, dichotomy and compactness modulo translation, with explicit quantifiers and hypotheses.

**Resolution criterion.** Supply a theorem with all quantifiers, domains, topologies and parameters fixed, together with a proof or an explicit counterexample. Compare against existing results and verify only the exact encoded claims in Lean where applicable.

## GC48: Certified spectral semigroups

**Problem.** Formalize in Lean 4 the spectral mapping and resolvent bounds needed to generate a strongly continuous semigroup for $L=-(1+\Delta)^2+\mu$ on L²(R²), including exact Fourier multiplier correspondence.

**Resolution criterion.** Supply a theorem with all quantifiers, domains, topologies and parameters fixed, together with a proof or an explicit counterexample. Compare against existing results and verify only the exact encoded claims in Lean where applicable.

## GC49: Checked PDE counterexamples

**Problem.** Construct and kernel-check in Lean 4 an explicit counterexample to a universal statement asserting that every fixed-mass minimizing sequence of the GC06 energy is compact modulo translations, if such a counterexample exists; otherwise prove the corresponding compactness theorem under explicit assumptions.

**Resolution criterion.** Supply a theorem with all quantifiers, domains, topologies and parameters fixed, together with a proof or an explicit counterexample. Compare against existing results and verify only the exact encoded claims in Lean where applicable.

## GC50: Proof-carrying numerical certificates

**Problem.** Define a rational interval-arithmetic certificate format for Galerkin approximations of the GC01 equation. Prove in Lean 4 that any accepted certificate implies an H² error bound on a stated time interval, with a verified parser and soundness theorem.

**Resolution criterion.** Supply a theorem with all quantifiers, domains, topologies and parameters fixed, together with a proof or an explicit counterexample. Compare against existing results and verify only the exact encoded claims in Lean where applicable.


## New foundational candidates GC51–GC65

**Added 2026-10-29.** These fifteen problems are research specifications with initial first-target models. None has been certified novel, unsolved or complete. Where a model component is still pending, that is explicitly flagged. Related existing GC entries are not proofs of independence or novelty.

## GC51: Soliton resolution and asymptotic completeness

**Problem.** Fix the fourth-order cubic–quintic Schrödinger flow from GC01 on \(\mathbb R^2\), with \(k,\beta,\gamma>0\), for initial data \(u_0\in H^2(\mathbb R^2)\) in a precisely specified invariant mass-energy regime. Determine whether every global solution in that regime has, as \(t\to+\infty\), a decomposition into finitely many modulated solitary waves with mutually diverging centers plus a dispersive remainder, with convergence in an explicitly chosen local or scattering norm. Classify exceptional channels and determine whether the universal assertion is false.

**Resolution criterion.** Supply a quantified decomposition theorem with a fixed class of data, admissible coherent profiles, modulation parameters and radiation norm, or an exact solution violating it. Compare with established soliton-resolution and scattering results before claiming novelty.

**Scope and prior-art caveat.** A general soliton-resolution conjecture already exists in nonlinear dispersive PDE. GC51 differs from GC02 by seeking a fate classification beyond small perturbations of one prescribed standing wave.

**Related existing challenges:** GC01, GC02, GC04, GC05.

## GC52: Rigorous emergence of effective wave equations

**Problem.** Choose a concrete two-dimensional finite-range Hamiltonian lattice with analytic onsite interactions, a carrier branch whose quadratic band curvature vanishes at a specified Bloch wave vector, and a small-amplitude parameter \(\varepsilon\). Determine whether its slowly varying envelope converges to the fourth-order cubic–quintic Schrödinger equation from GC01, under a fully specified amplitude and time scaling. If so, prove an explicit bound \(\sup_{0\le t\le T\varepsilon^{-p}}\|u_{\mathrm{lattice}}(t)-u_{\mathrm{ansatz}}(t)\|_{X_\varepsilon}\le C\varepsilon^\alpha\) for fixed \(T,p,\alpha>0\) and a declared interpolation norm \(X_\varepsilon\); otherwise prove an obstruction in the chosen lattice class.

**Resolution criterion.** Provide the full parent Hamiltonian and couplings, expansion, nonresonance assumptions, scaling, reconstructed ansatz and uniform residual/error estimates, or a rigorous impossibility result. Physical realization is a separate question.

**Scope and prior-art caveat.** A suitable microscopic lattice and scaling are not yet fixed; candidate model construction is a mandatory first milestone. This extends beyond GC25's linear-dispersion matching.

**Related existing challenges:** GC01, GC06, GC21, GC25.

## GC53: Universal confinement and stability thresholds

**Problem.** For the exact GC06 energy on \(\mathbb R^2\), consider all tuples \((k,\beta,\gamma,m)\) with \(k,\beta,\gamma,m>0\). Determine the parameter subsets in which (i) the mass-constrained infimum is attained, (ii) its entire minimizer set is orbitally stable for the GC01 flow, and (iii) loss of compactness occurs. Decide whether, after an explicit dimensionless reduction, these subsets are separated by a single scalar threshold; if not, construct two tuples with the same proposed threshold statistic but different outcomes.

**Resolution criterion.** Either derive sharp necessary-and-sufficient inequalities and prove all three classifications, or rule out the proposed universal single-threshold structure with a precise counterexample.

**Scope and prior-art caveat.** The coexistence of a universal scalar threshold and sharp multi-parameter classification is not assumed. This problem synthesizes GC01, GC06, GC16 and GC19 rather than replacing them.

**Related existing challenges:** GC01, GC03, GC06, GC10, GC16, GC19.

## GC54: Nonlinear scattering and threshold resonances

**Problem.** Let \(H=(\Delta+k^2)^2+V(x)\) on \(L^2(\mathbb R^2)\), with \(k>0\) and real \(V\in C_c^\infty(\mathbb R^2)\). Classify zero-energy threshold eigenfunctions and resonances for \(H\), and determine how each admissible threshold type affects weighted resolvent bounds and local decay of \(e^{-itH}\). For an explicitly fixed small gauge-invariant cubic–quintic perturbation, determine whether the corresponding nonlinear dynamics scatter, produce persistent modes, or admit counterexamples near threshold.

**Resolution criterion.** Freeze the weighted spaces, radiation conditions and nonlinear smallness regime. Prove a threshold resolvent expansion and the claimed time-decay/scattering implications, or construct a counterexample to a proposed classification.

**Scope and prior-art caveat.** Fourth-order spectral and scattering theory already has extensive prior work. The distinction is the specific degenerate nonzero-frequency shell and nonlinear coupling.

**Related existing challenges:** GC02, GC05, GC07, GC12, GC14.

## GC55: Scaling universality and critical phenomena

**Problem.** Compare a specified family of fourth-order focusing–defocusing constrained energies \(E_\lambda\) on \(\mathbb R^d\), with compact parameter set \(\Lambda\), and mass infima \(I_\lambda(m)\). Where a nontrivial critical mass \(m_c(\lambda)>0\) exists, determine whether the binding gap, minimizer width or branch amplitude obeys an asymptotic power law \(A_\lambda(m)\sim c_\lambda(m-m_c(\lambda))^\nu\) as \(m\downarrow m_c(\lambda)\) with exponent \(\nu\) independent of \(\lambda\). Classify parameter changes that alter \(\nu\), or exhibit counterexamples to universality.

**Resolution criterion.** Specify the energy family, order parameter (A_lambda), threshold definition, dimension and topology. Establish the exponent and its uniformity, or show mathematically why no common exponent exists.

**Scope and prior-art caveat.** Critical exponents and universality are extensively studied elsewhere. Existence of a nonzero critical mass and a power law must not be presumed.

**Related existing challenges:** GC06, GC10, GC11, GC16, GC18.

## GC56: Global bifurcation of localized states

**Problem.** For \(k,\beta,\gamma>0\), study nonzero \(H^2(\mathbb R^2)\) solutions of \(\omega\phi=(\Delta+k^2)^2\phi-\beta|\phi|^2\phi+\gamma|\phi|^4\phi\), with \(\omega\) varying in a specified real interval. Determine the connected components of the phase-translation-quotiented solution set, their regularity and continuation, possible folds and secondary symmetry-breaking branches, and whether any branch terminates at the essential-spectrum edge.

**Resolution criterion.** Freeze the interval, quotient topology and profile class; prove a global alternative or a complete classification in an identified parameter regime, or exhibit a branch geometry refuting a proposed universal picture.

**Scope and prior-art caveat.** Global bifurcation and solitary-wave continuation are established subjects; the proposed classification must be distinct from prior results and from the local bifurcation asked in GC18.

**Related existing challenges:** GC06, GC17, GC18, GC37.

## GC57: Stability under stochastic forcing

**Problem.** Take the real Swift–Hohenberg gradient flow of GC20 on \(\mathbb T^2\), perturbed by finite-rank smooth additive noise: \(du=-\nabla_{L^2}E(u)\,dt+\sigma\sum_{j=1}^{J}g_j\,dW_t^j\), with fixed \(J\), \(g_j\in C^\infty(\mathbb T^2)\) and \(\sigma>0\). For an explicitly selected deterministic hyperbolic local minimizer, quantify the first exit time from a neighborhood of its symmetry orbit as \(\sigma\downarrow0\), and characterize whether stationary laws concentrate near that orbit.

**Resolution criterion.** Prove well-posedness and a sharp exit-time or invariant-measure statement with declared noise covariance and symmetry handling, or produce a counterexample to the proposed metastability law.

**Scope and prior-art caveat.** Infinite-time almost-sure persistence is generally inappropriate under nondegenerate noise. Stochastic metastability and large deviations have substantial established theory.

**Related existing challenges:** GC01, GC20, GC33.

## GC58: Multicomponent and vector confinement

**Problem.** For \(u=(u_1,u_2)\in H^2(\mathbb R^2;\mathbb C^2)\), set \(\rho=|u_1|^2+|u_2|^2\) and \(E_\eta(u)=\int_{\mathbb R^2}[\sum_{j=1}^2|(\Delta+k^2)u_j|^2-\frac{\beta}{2}\rho^2+\frac{\gamma}{3}\rho^3+\eta|u_1|^2|u_2|^2]\,dx\). With \(k,\beta,\gamma>0\), \(\eta\in\mathbb R\) and fixed positive component masses \(m_j=\|u_j\|_2^2\), classify parameter regimes with a genuinely two-component attained minimizer versus component segregation, and determine orbital stability under its Hamiltonian flow.

**Resolution criterion.** Give an explicit parameter/mass classification with binding, compactness and vector-to-scalar comparisons, or counterexamples to asserted vector confinement and stability.

**Scope and prior-art caveat.** Coupled NLS and vector solitons are well-established subjects; novel claims require a precise comparison with existing mixed-dispersion and multicomponent theorems.

**Related existing challenges:** GC01, GC06, GC09, GC36.

## GC59: Nonlinear observability and control

**Problem.** For the real Swift–Hohenberg equation on \(\mathbb T^2\), \(\partial_tu=\mu u-(1+\Delta)^2u-u^3+\mathbf1_{\omega}f\), fix \(\mu>0\), a nonempty proper open observation/control region \(\omega\subset\mathbb T^2\) and a finite horizon \(T>0\). Determine whether the time trace \(u|_{(0,T)\times\omega}\) uniquely and stably determines initial data in a specified bounded \(H^2\) class. Separately classify local stabilization of a fixed stationary pattern by controls supported in \(\omega\), including minimal observability or control cost.

**Resolution criterion.** Prove a precisely stated observability inequality or a counterexample, and a feedback/null-control theorem with exact function spaces, cost and locality restrictions.

**Scope and prior-art caveat.** Unique continuation and control of parabolic PDEs are major established areas; observability, exact controllability and stabilization are logically different targets.

**Related existing challenges:** GC26, GC27, GC29, GC31, GC33.

## GC60: Singular limits and multiscale consistency

**Problem.** For the GC01 cubic–quintic fourth-order Schrödinger flow on \(\mathbb T^2\), let \(u_N(t)\) solve the mass-compatible spectral Galerkin truncation with Fourier projector \(P_N\), from initial data \(P_Nu_0\). For \(u_0\) in a bounded \(H^{2+s}\) set with \(s>0\), determine the largest time scales \(T_N\) for which \(\sup_{0\le t\le T_N}\|u(t)-u_N(t)\|_{H^2}\le C N^{-\alpha}\) holds uniformly with explicitly fixed \(\alpha>0\). Determine whether near-conserved effective invariants improve long-time accuracy, or construct solutions preventing a proposed growth law.

**Resolution criterion.** Prove the stated uniform-in-(N) error bounds with fixed regularity, constants and horizons, and matching obstructions or counterexamples where possible.

**Scope and prior-art caveat.** Finite-time spectral convergence is classical. The intended challenge is sharp long-time scaling and nonlinear consistency, not merely reproving standard Galerkin convergence.

**Related existing challenges:** GC42, GC45, GC46, GC50.

## GC61: Formation and breakdown of coherent structures

**Problem.** For the GC01 flow on \(\mathbb R^2\), define a nonperturbative class \(U\subset H^2(\mathbb R^2)\) of initially localized data outside any fixed small neighborhood of the solitary-wave orbits. Determine whether a nonempty open subset of \(U\) admits a forward-time decomposition into one or more nonzero solitary waves plus dispersive radiation in a specified local topology, and classify quantitative criteria for formation, splitting or eventual loss of coherent structures.

**Resolution criterion.** Prove a basin-of-formation theorem with explicit conditions and topology, or show that no such open basin exists under the stated constraints. A numerical localization plot alone is insufficient.

**Scope and prior-art caveat.** Unlike GC02, the initial data are not near one known soliton. Unlike GC51, this asks for concrete nonperturbative formation criteria, not global resolution of all trajectories.

**Related existing challenges:** GC01, GC02, GC05, GC06, GC51.

## GC62: Chaotic dynamics and transport barriers

**Problem.** Fix a rational Fourier–Galerkin truncation with \(N\) modes of the cubic–quintic Schrödinger equation on \(\mathbb T^2\), restricted to a compact regular joint mass-energy level after removing phase symmetry. Determine whether the resulting finite-dimensional Hamiltonian flow has transverse homoclinic intersections or another rigorously specified chaotic invariant set. In the same model, characterize invariant or metastable regions that suppress transfer across a designated Fourier cutoff, and determine which statements persist uniformly as \(N\to\infty\).

**Resolution criterion.** Exhibit a rigorous chaos mechanism and a quantified transport obstruction or passage theorem in an explicit truncation, then prove or disprove the claimed continuum-limit persistence.

**Scope and prior-art caveat.** A nonintegrable Galerkin truncation is not automatically chaotic, and finite-dimensional chaos does not by itself prove continuum PDE transport.

**Related existing challenges:** GC13, GC20, GC32, GC39, GC42.

## GC63: Physical information and energy limits of wave computation

**Problem.** Fix an explicit finite oscillator network implementing the logical transitions of a designated wave-cell automaton from GC43, with Hamiltonian couplings, a specified thermal Langevin bath at temperature \(T_{\mathrm b}>0\), bounded driving protocol and an operational output-error event. For \(n\) logical transitions with failure probability at most \(\delta\), characterize the infimum of expected dissipated work over admissible protocols as a function of \((n,\delta,T_{\mathrm b})\) and switching time, separating logically reversible from irreversible gates.

**Resolution criterion.** Prove nontrivial upper and lower energy/error/time tradeoffs for the fixed physical model, or construct a low-dissipation protocol refuting an asserted universal bound.

**Scope and prior-art caveat.** A reversible abstract automaton has no built-in thermodynamic cost. Do not conflate logical irreversibility, physical dissipation, device noise and information-theoretic precision.

**Related existing challenges:** GC42, GC43, GC44, GC45.

## GC64: Identifiability of competing physical theories

**Problem.** Let \(F:\Theta\to\mathbb R^N\) be the frozen clipped spectral observation map of GC26 and \(G:\Phi\to\mathbb R^N\) an independently specified competing wave model, with compact admissible sets \(\Theta_0\subset\Theta\) and \(\Phi_0\subset\Phi\). For each set \(S\) of permitted measurement coordinates and noise radius \(\sigma>0\), determine whether \(\inf_{\theta\in\Theta_0,\varphi\in\Phi_0}\|P_S F(\theta)-P_S G(\varphi)\|>2\sigma\); identify minimum distinguishing sets or prove that the observation images intersect for every such set.

**Resolution criterion.** Specify the alternative model and all allowable sensors, then prove sharp distinguishability or indistinguishability with quantitative noise margins and explicit witness parameters.

**Scope and prior-art caveat.** The alternative forward map (G) is not frozen yet. A model that is distinguishable by construction is not a deep identifiability theorem; meaningful competing hypotheses must be justified.

**Related existing challenges:** GC25, GC26, GC27, GC29, GC30.

## GC65: Verified mathematical model reduction

**Problem.** For the dissipative Swift–Hohenberg flow \(\partial_tu=\mu u-(1+\Delta)^2u-u^3\) on \(\mathbb T^2\), fix a parameter regime and spectral projector \(P_N\). Determine whether there is a Lipschitz or smoother graph \(\Phi:P_NH^2\to(I-P_N)H^2\) whose graph is invariant and exponentially attracts every bounded forward orbit, so that a finite-dimensional ODE captures the long-term dynamics. Formalize the exact invariant-manifold and tracking theorem, or a rigorous obstruction, in Lean 4 without unproved axioms.

**Resolution criterion.** Prove the exact spectral-gap or alternative hypotheses, invariant graph, attracting/tracking estimate and conjugate reduced dynamics, with a compiling Lean statement faithfully matching the analytic theorem; or give a counterexample to existence in the chosen regime.

**Scope and prior-art caveat.** Existence of an inertial manifold is not guaranteed by a finite-dimensional global attractor. This differs from GC50's numerical error certificates by requiring a dynamically faithful reduction.

**Related existing challenges:** GC31, GC42, GC46, GC48, GC50.

## Mandatory qualification before claiming an open problem

1. Complete a literature and priority review, with citations to closest theorems.
2. Freeze ambiguous terms such as stable, generic, complexity, coercive, and physically admissible.
3. Check trivial cases and counterexamples. A problem may already be solved, false, or ill-posed.
4. Separate analytic, numerical, formal and physical claims. Lean checking is not a novelty test.
5. Maintain an explicit status for each problem: proposed, refined, literature-checked, open, resolved, or withdrawn.
