# Fifty formally stated research problems

**Status:** Proposed precisely scoped research problems, **not** claims of novelty, unsolved status, difficulty, or independence. Several are classification problems, some have known elementary answers or obstructions, and several require additional modeling choices before a definitive theorem can be stated. The word “determine” explicitly permits a negative answer or a counterexample. Mathematical statements are research specifications, not verified results. Literature reviews are pending.

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

**Problem.** Fix ε>0 and $K_\varepsilon(u)=\nabla\cdot\left(\frac{\operatorname{Im}(\bar u\nabla u)}{\varepsilon+|u|^2}\right)$ on smooth complex fields. Classify all local differential operators C(u) of order ≤2 invariant under u↦e^{iθ}u, translation and rotation, agreeing with K_ε on nonvanishing constant-amplitude plane waves; determine uniqueness or give inequivalent examples.

**Resolution criterion.** Supply a theorem with all quantifiers, domains, topologies and parameters fixed, together with a proof or an explicit counterexample. Compare against existing results and verify only the exact encoded claims in Lean where applicable.

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

## Mandatory qualification before claiming an open problem

1. Complete a literature and priority review, with citations to closest theorems.
2. Freeze ambiguous terms such as stable, generic, complexity, coercive, and physically admissible.
3. Check trivial cases and counterexamples. A problem may already be solved, false, or ill-posed.
4. Separate analytic, numerical, formal and physical claims. Lean checking is not a novelty test.
5. Maintain an explicit status for each problem: proposed, refined, literature-checked, open, resolved, or withdrawn.
