# GC65–GC300: preliminary mathematical definition audit

**Review date:** 2026-10-30. **Status:** editorial scoping screen, NOT a proof, novelty opinion, or complete technical peer review.

## Verified inventory and scope

- Checked `main` registry and repository tree: **236 distinct entries GC65–GC300**, all linked files present; GC65 is an original formal-statement entry, GC66–GC300 are **235 roadmap candidates**.
- The machine registry labels **all 236 `candidate`** and **all 236 `novelty_established: false`**.
- The individual candidate files provide a short question and a first target, but routinely defer exact model, quantifiers, function spaces and evidence criteria to future work. A suggested proof target is not a frozen theorem.
- **No entry has been promoted to 'well-defined and formalization-ready' by this review.** This is a screening result, not a claim that every underlying idea is intrinsically ill-posed.

## Decision rules

To mark an item *mathematically frozen*, require: (1) operator/equation/energy fully written, (2) spaces and domain/boundary conditions, (3) coefficient and parameter ranges, (4) all quantifiers and symmetries, (5) precise success and counterexample criteria, (6) nontriviality checks (zero states, scaling, simple classical theorems), (7) literature/overlap comparison, (8) theorem-to-Lean correspondence only when Lean is claimed. A model family or phrase 'specified' is not a specified model.

**P0** = investigate potential logical ambiguity, classical near-solution, category mismatch or important scope collision **before** writing a theorem. **P1** = normal model/quantifier freeze required. The flags are triage priorities, **not** proof that the candidate is false.

## Cross-cutting high-priority mathematical cautions

1. **GC124:** Nonzero periodic patterns on whole-space R² have infinite L² mass. If the intended comparison is against finite-mass localized states, clarify periodic box, mass per cell, or localized modulation.
2. **GC197:** For ordinary continuous maps S³→S², same Hopf number implies the same homotopy class. To obtain a nontrivial knot-type obstruction require constraints beyond arbitrary finite-energy homotopies.
3. **GC200:** With unit-modulus phases on a flat torus and standard Dirichlet energy `E=1/2 ∫|∇θ|²`, the harmonic representative has `E_min=2π²(n_x² L_y/L_x+n_y² L_x/L_y)`. This standard case should be distinguished from a genuinely new nonlinear/weighted problem.
4. **GC212:** For continuous nonvanishing space-time maps, integer topological degree cannot change along a sample path. The substantive probabilistic issue is zero formation/regularity breakdown.
5. **GC177:** A fixed two-torus has discrete sidebands; the usual continuously varying Bloch/Eckhaus description needs the infinite periodic medium or a large-box limiting statement.
6. **GC278:** Threshold detectors are nonlinear measurements; a passive-optics impossibility or universality theorem must account explicitly for detection, external feedback and regeneration.
7. **GC235–GC253:** Distinguish *formalizing established mathematics in Lean* from asserting a novel open mathematics problem. Their value may be formal verification, even where the analytic result is classical.
8. **GC65:** The Swift–Hohenberg flow is named, but the problem still instructs the reader to choose the parameter regime and spectral projector; this is not one fixed yes/no proposition.

## Entry-by-entry first required scoping fix

Each entry has been screened for whether the current prompt already supplies a fixed provable proposition. The table states the **first editorial action**, not an exhaustive independent proof critique. Group-default rows share a typical missing-specification action; starred observations are individually flagged.

| ID | Current status | Priority | First required fix / objection |
|:--|:--|:--|:--|
| [GC65](./problems/10-lean-certified-analysis/GC65.md) | Not frozen | P1* | Fix one Swift–Hohenberg parameter regime, explicit spectral cut-off, gap estimate and invariant-graph tracking norm. |
| [GC66](./problems/01-wave-dynamics/GC66.md) | Not frozen | P1* | Choose an existing excited state and its linearized spectral/Fermi-golden-rule assumptions; define damping observable. |
| [GC67](./problems/01-wave-dynamics/GC67.md) | Not frozen | P1* | Write the moving-wave ansatz and distinguish a speed obstruction from nonexistence due to nonzero carrier frequency. |
| [GC68](./problems/01-wave-dynamics/GC68.md) | Not frozen | P1* | Define collision channels as asymptotic states; fix initial wave family and a norm distinguishing capture from scattering. |
| [GC69](./problems/01-wave-dynamics/GC69.md) | Not frozen | P1 | Freeze the PDE coefficients, target wave branch, function space and temporal asymptotic/stability notion. |
| [GC70](./problems/01-wave-dynamics/GC70.md) | Not frozen | P1 | Freeze the PDE coefficients, target wave branch, function space and temporal asymptotic/stability notion. |
| [GC71](./problems/01-wave-dynamics/GC71.md) | Not frozen | P1 | Freeze the PDE coefficients, target wave branch, function space and temporal asymptotic/stability notion. |
| [GC72](./problems/01-wave-dynamics/GC72.md) | Not frozen | P1 | Freeze the PDE coefficients, target wave branch, function space and temporal asymptotic/stability notion. |
| [GC73](./problems/01-wave-dynamics/GC73.md) | Not frozen | P1* | Specify the base coherent state, nonresonance/small-divisor assumptions and invariant-torus topology. |
| [GC74](./problems/01-wave-dynamics/GC74.md) | Not frozen | P1 | Freeze the PDE coefficients, target wave branch, function space and temporal asymptotic/stability notion. |
| [GC75](./problems/01-wave-dynamics/GC75.md) | Not frozen | P1 | Freeze the PDE coefficients, target wave branch, function space and temporal asymptotic/stability notion. |
| [GC76](./problems/01-wave-dynamics/GC76.md) | Not frozen | P1 | Freeze the PDE coefficients, target wave branch, function space and temporal asymptotic/stability notion. |
| [GC77](./problems/01-wave-dynamics/GC77.md) | Not frozen | P1* | Freeze one excited standing wave, unstable eigenpair, perturbation family and exact departure-radius definition. |
| [GC78](./problems/01-wave-dynamics/GC78.md) | Not frozen | P1* | Specify whether Sobolev norm growth is unbounded in time for a single trajectory or merely over a sequence of data. |
| [GC79](./problems/01-wave-dynamics/GC79.md) | Not frozen | P1 | Freeze the PDE coefficients, target wave branch, function space and temporal asymptotic/stability notion. |
| [GC80](./problems/01-wave-dynamics/GC80.md) | Not frozen | P1* | Specify the unperturbed periodic orbit, perturbation space and what counts as orbit persistence versus radiation. |
| [GC81](./problems/01-wave-dynamics/GC81.md) | Not frozen | P1 | Freeze the PDE coefficients, target wave branch, function space and temporal asymptotic/stability notion. |
| [GC82](./problems/02-confinement-curvature/GC82.md) | Not frozen | P1* | Give the squared curvature integral with exact epsilon, field domain and all energy signs; define 'coercive modulo symmetries'. |
| [GC83](./problems/02-confinement-curvature/GC83.md) | Not frozen | P1* | Define global phase reconstruction on a punctured domain and whether winding/nonvanishing is assumed. |
| [GC84](./problems/02-confinement-curvature/GC84.md) | Not frozen | P1* | Specify vortex profile order, epsilon normalization, distribution space and whether renormalization is required. |
| [GC85](./problems/02-confinement-curvature/GC85.md) | Not frozen | P1* | Clarify 'localized' on compact surfaces; freeze metric/area/energy and whether a concentration parameter varies. |
| [GC86](./problems/02-confinement-curvature/GC86.md) | Not frozen | P1 | Define the curvature map or geometry, exact energy/operator, admissible field space and compactness norm. |
| [GC87](./problems/02-confinement-curvature/GC87.md) | Not frozen | P1 | Define the curvature map or geometry, exact energy/operator, admissible field space and compactness norm. |
| [GC88](./problems/02-confinement-curvature/GC88.md) | Not frozen | P1 | Define the curvature map or geometry, exact energy/operator, admissible field space and compactness norm. |
| [GC89](./problems/02-confinement-curvature/GC89.md) | Not frozen | P1* | State the proposed inequality and exponents before asking for an optimal constant; fix denominator-zero conventions. |
| [GC90](./problems/02-confinement-curvature/GC90.md) | Not frozen | P1 | Define the curvature map or geometry, exact energy/operator, admissible field space and compactness norm. |
| [GC91](./problems/02-confinement-curvature/GC91.md) | Not frozen | P1 | Define the curvature map or geometry, exact energy/operator, admissible field space and compactness norm. |
| [GC92](./problems/02-confinement-curvature/GC92.md) | Not frozen | P1* | Freeze the exact conservation law and class of differential invariants; GC08 already has nonunique closures. |
| [GC93](./problems/02-confinement-curvature/GC93.md) | Not frozen | P1* | Define localization radius operationally (quantile, variance, support, etc.) and the curvature budget. |
| [GC94](./problems/02-confinement-curvature/GC94.md) | Not frozen | P1 | Define the curvature map or geometry, exact energy/operator, admissible field space and compactness norm. |
| [GC95](./problems/02-confinement-curvature/GC95.md) | Not frozen | P1* | Fix function spaces and zero-amplitude conventions for the nonlinear curvature quotient. |
| [GC96](./problems/02-confinement-curvature/GC96.md) | Not frozen | P1 | Define the curvature map or geometry, exact energy/operator, admissible field space and compactness norm. |
| [GC97](./problems/02-confinement-curvature/GC97.md) | Not frozen | P0* | Fix nonvanishing/boundary hypotheses: winding can disappear through field zeros, so a naive winding-energy bound fails. |
| [GC98](./problems/02-confinement-curvature/GC98.md) | Not frozen | P1* | Define measurement map, observation radius, allowed exterior tails and localization threshold. |
| [GC99](./problems/02-confinement-curvature/GC99.md) | Not frozen | P1 | Define the curvature map or geometry, exact energy/operator, admissible field space and compactness norm. |
| [GC100](./problems/02-confinement-curvature/GC100.md) | Not frozen | P1 | Define the curvature map or geometry, exact energy/operator, admissible field space and compactness norm. |
| [GC101](./problems/03-spectral-scattering/GC101.md) | Not frozen | P1* | Define the radial fourth-order operator/domain and the weighted-space notion of threshold resonance. |
| [GC102](./problems/03-spectral-scattering/GC102.md) | Not frozen | P1* | State the exact shifted bi-Laplacian and decay class; embedded eigenvalues depend strongly on admissible potentials. |
| [GC103](./problems/03-spectral-scattering/GC103.md) | Not frozen | P1* | Freeze shell geometry and spectral weight exponents; 'optimal resolvent growth' has no scalar answer without them. |
| [GC104](./problems/03-spectral-scattering/GC104.md) | Not frozen | P1 | Fix the operator, domain, spectral threshold/weights, perturbation class and quantified spectral claim. |
| [GC105](./problems/03-spectral-scattering/GC105.md) | Not frozen | P1* | Fix nonlinear normal form and Fermi-golden-rule resonance; 'irreversible coupling' needs a long-time norm. |
| [GC106](./problems/03-spectral-scattering/GC106.md) | Not frozen | P1 | Fix the operator, domain, spectral threshold/weights, perturbation class and quantified spectral claim. |
| [GC107](./problems/03-spectral-scattering/GC107.md) | Not frozen | P1 | Fix the operator, domain, spectral threshold/weights, perturbation class and quantified spectral claim. |
| [GC108](./problems/03-spectral-scattering/GC108.md) | Not frozen | P1 | Fix the operator, domain, spectral threshold/weights, perturbation class and quantified spectral claim. |
| [GC109](./problems/03-spectral-scattering/GC109.md) | Not frozen | P1 | Fix the operator, domain, spectral threshold/weights, perturbation class and quantified spectral claim. |
| [GC110](./problems/03-spectral-scattering/GC110.md) | Not frozen | P1 | Fix the operator, domain, spectral threshold/weights, perturbation class and quantified spectral claim. |
| [GC111](./problems/03-spectral-scattering/GC111.md) | Not frozen | P1* | Identify the self-adjoint linearized operator; a nonlinear equilibrium alone has no spectral measure. |
| [GC112](./problems/03-spectral-scattering/GC112.md) | Not frozen | P1 | Fix the operator, domain, spectral threshold/weights, perturbation class and quantified spectral claim. |
| [GC113](./problems/03-spectral-scattering/GC113.md) | Not frozen | P1* | State precise weighted Sobolev mapping spaces, spectral parameter domain and limiting-absorption convention. |
| [GC114](./problems/03-spectral-scattering/GC114.md) | Not frozen | P1 | Fix the operator, domain, spectral threshold/weights, perturbation class and quantified spectral claim. |
| [GC115](./problems/03-spectral-scattering/GC115.md) | Not frozen | P1 | Fix the operator, domain, spectral threshold/weights, perturbation class and quantified spectral claim. |
| [GC116](./problems/03-spectral-scattering/GC116.md) | Not frozen | P1 | Fix the operator, domain, spectral threshold/weights, perturbation class and quantified spectral claim. |
| [GC117](./problems/03-spectral-scattering/GC117.md) | Not frozen | P1 | Fix the operator, domain, spectral threshold/weights, perturbation class and quantified spectral claim. |
| [GC118](./problems/03-spectral-scattering/GC118.md) | Not frozen | P1* | Define 'weakly localized resonant mode' and high-frequency counting window before a Weyl law. |
| [GC119](./problems/03-spectral-scattering/GC119.md) | Not frozen | P1 | Fix the operator, domain, spectral threshold/weights, perturbation class and quantified spectral claim. |
| [GC120](./problems/04-variational-solitons/GC120.md) | Not frozen | P1* | Write the exact scale-homogeneous inequality with coefficients and admissible dimensions; otherwise 'best constant' is unspecified. |
| [GC121](./problems/04-variational-solitons/GC121.md) | Not frozen | P1* | Freeze a known minimizer, Hessian domain, constraint tangent space and whether extra gauge/kernel symmetries occur. |
| [GC122](./problems/04-variational-solitons/GC122.md) | Not frozen | P1 | Specify the energy, admissible constraint set, mass/parameter interval, topology and attainment criterion. |
| [GC123](./problems/04-variational-solitons/GC123.md) | Not frozen | P1 | Specify the energy, admissible constraint set, mass/parameter interval, topology and attainment criterion. |
| [GC124](./problems/04-variational-solitons/GC124.md) | Not frozen | P0* | Resolve potential finite-mass conflict: nonzero fully periodic states on R² are not L². Use a periodic box, energy density, or localized modulation. |
| [GC125](./problems/04-variational-solitons/GC125.md) | Not frozen | P1* | Specify a two-component energy and coupling; 'focusing–defocusing' alone does not determine optimal mass allocation. |
| [GC126](./problems/04-variational-solitons/GC126.md) | Not frozen | P1* | Specify the energy, Fourier-shell mode and concentration topology; current task asks to invent a decomposition. |
| [GC127](./problems/04-variational-solitons/GC127.md) | Not frozen | P1 | Specify the energy, admissible constraint set, mass/parameter interval, topology and attainment criterion. |
| [GC128](./problems/04-variational-solitons/GC128.md) | Not frozen | P1* | Define the mass threshold independently of the binding conclusion to avoid circularity. |
| [GC129](./problems/04-variational-solitons/GC129.md) | Not frozen | P1* | Define the Hamiltonian linearization and fold branch; a slope test alone is not a general stability theorem. |
| [GC130](./problems/04-variational-solitons/GC130.md) | Not frozen | P1* | Fix angular momentum functional, spatial dimension, rotation group and whether admissible states can escape to infinity. |
| [GC131](./problems/04-variational-solitons/GC131.md) | Not frozen | P1 | Specify the energy, admissible constraint set, mass/parameter interval, topology and attainment criterion. |
| [GC132](./problems/04-variational-solitons/GC132.md) | Not frozen | P1 | Specify the energy, admissible constraint set, mass/parameter interval, topology and attainment criterion. |
| [GC133](./problems/04-variational-solitons/GC133.md) | Not frozen | P1 | Specify the energy, admissible constraint set, mass/parameter interval, topology and attainment criterion. |
| [GC134](./problems/04-variational-solitons/GC134.md) | Not frozen | P1 | Specify the energy, admissible constraint set, mass/parameter interval, topology and attainment criterion. |
| [GC135](./problems/04-variational-solitons/GC135.md) | Not frozen | P1 | Specify the energy, admissible constraint set, mass/parameter interval, topology and attainment criterion. |
| [GC136](./problems/04-variational-solitons/GC136.md) | Not frozen | P1 | Specify the energy, admissible constraint set, mass/parameter interval, topology and attainment criterion. |
| [GC137](./problems/04-variational-solitons/GC137.md) | Not frozen | P1* | Identify the critical functional and energy quantum; 'nearly critical waves' is not a defined class. |
| [GC138](./problems/04-variational-solitons/GC138.md) | Not frozen | P1 | Specify the energy, admissible constraint set, mass/parameter interval, topology and attainment criterion. |
| [GC139](./problems/05-higher-derivative-fields/GC139.md) | Not frozen | P1* | Give a finite polynomial ansatz and constraints, or 'classify polynomial Lagrangians' is open-ended. |
| [GC140](./problems/05-higher-derivative-fields/GC140.md) | Not frozen | P1* | Specify the nonlinear interaction and primary constraint, since consistency depends on the exact action. |
| [GC141](./problems/05-higher-derivative-fields/GC141.md) | Not frozen | P1 | Write the Lagrangian/operator, constraints/gauge, boundary data, admissible phase space and positivity criterion. |
| [GC142](./problems/05-higher-derivative-fields/GC142.md) | Not frozen | P1* | Freeze 'positive energy' and equivalence under auxiliary-field elimination; Ostrogradsky degrees require careful accounting. |
| [GC143](./problems/05-higher-derivative-fields/GC143.md) | Not frozen | P0* | Distinguish finite support propagation from dispersive off-cone estimates; a generic fourth-order spatial dispersive law has no finite propagation speed. |
| [GC144](./problems/05-higher-derivative-fields/GC144.md) | Not frozen | P1* | Specify first-order reduction and variable-coefficient hyperbolicity notion for a fourth-order temporal symbol. |
| [GC145](./problems/05-higher-derivative-fields/GC145.md) | Not frozen | P1 | Write the Lagrangian/operator, constraints/gauge, boundary data, admissible phase space and positivity criterion. |
| [GC146](./problems/05-higher-derivative-fields/GC146.md) | Not frozen | P1* | Freeze gauge, constraint reduction and Hamiltonian positivity on the physical phase space. |
| [GC147](./problems/05-higher-derivative-fields/GC147.md) | Not frozen | P1 | Write the Lagrangian/operator, constraints/gauge, boundary data, admissible phase space and positivity criterion. |
| [GC148](./problems/05-higher-derivative-fields/GC148.md) | Not frozen | P1* | Specify gauge group, covariant curvature operator and derivative-counting conventions. |
| [GC149](./problems/05-higher-derivative-fields/GC149.md) | Not frozen | P1 | Write the Lagrangian/operator, constraints/gauge, boundary data, admissible phase space and positivity criterion. |
| [GC150](./problems/05-higher-derivative-fields/GC150.md) | Not frozen | P1* | Choose the exact fourth-order elliptic expression and boundary trace form; self-adjointness does not alone imply positive energy. |
| [GC151](./problems/05-higher-derivative-fields/GC151.md) | Not frozen | P1 | Write the Lagrangian/operator, constraints/gauge, boundary data, admissible phase space and positivity criterion. |
| [GC152](./problems/05-higher-derivative-fields/GC152.md) | Not frozen | P1* | State sign/factorization criteria and what 'healthy branches' means in Hamiltonian terms. |
| [GC153](./problems/05-higher-derivative-fields/GC153.md) | Not frozen | P1 | Write the Lagrangian/operator, constraints/gauge, boundary data, admissible phase space and positivity criterion. |
| [GC154](./problems/05-higher-derivative-fields/GC154.md) | Not frozen | P1 | Write the Lagrangian/operator, constraints/gauge, boundary data, admissible phase space and positivity criterion. |
| [GC155](./problems/05-higher-derivative-fields/GC155.md) | Not frozen | P1* | Specify PDE and breakdown criterion before a critical-norm continuation theorem. |
| [GC156](./problems/05-higher-derivative-fields/GC156.md) | Not frozen | P1 | Write the Lagrangian/operator, constraints/gauge, boundary data, admissible phase space and positivity criterion. |
| [GC157](./problems/05-higher-derivative-fields/GC157.md) | Not frozen | P1 | Write the Lagrangian/operator, constraints/gauge, boundary data, admissible phase space and positivity criterion. |
| [GC158](./problems/05-higher-derivative-fields/GC158.md) | Not frozen | P1 | Write the Lagrangian/operator, constraints/gauge, boundary data, admissible phase space and positivity criterion. |
| [GC159](./problems/06-inverse-observation-control/GC159.md) | Not frozen | P1* | Choose the parameterized forward wave model, fixed sampling operator and local Jacobian rank criterion. |
| [GC160](./problems/06-inverse-observation-control/GC160.md) | Not frozen | P1* | State the actual clipped map and complete parameter domain; clipping creates piecewise-stratified equivalence classes. |
| [GC161](./problems/06-inverse-observation-control/GC161.md) | Not frozen | P1 | Give the forward map, parameter set, measurement design, observation/noise model and identifiability norm. |
| [GC162](./problems/06-inverse-observation-control/GC162.md) | Not frozen | P1 | Give the forward map, parameter set, measurement design, observation/noise model and identifiability norm. |
| [GC163](./problems/06-inverse-observation-control/GC163.md) | Not frozen | P1 | Give the forward map, parameter set, measurement design, observation/noise model and identifiability norm. |
| [GC164](./problems/06-inverse-observation-control/GC164.md) | Not frozen | P1 | Give the forward map, parameter set, measurement design, observation/noise model and identifiability norm. |
| [GC165](./problems/06-inverse-observation-control/GC165.md) | Not frozen | P0* | Check overlap with existing F09 clipped-map rank/nullity formalization before presenting a new gap; freeze all clipping cells. |
| [GC166](./problems/06-inverse-observation-control/GC166.md) | Not frozen | P1 | Give the forward map, parameter set, measurement design, observation/noise model and identifiability norm. |
| [GC167](./problems/06-inverse-observation-control/GC167.md) | Not frozen | P1* | Specify complex field class, masks, phase retrieval measurement equations and unavoidable symmetries. |
| [GC168](./problems/06-inverse-observation-control/GC168.md) | Not frozen | P1 | Give the forward map, parameter set, measurement design, observation/noise model and identifiability norm. |
| [GC169](./problems/06-inverse-observation-control/GC169.md) | Not frozen | P1 | Give the forward map, parameter set, measurement design, observation/noise model and identifiability norm. |
| [GC170](./problems/06-inverse-observation-control/GC170.md) | Not frozen | P1 | Give the forward map, parameter set, measurement design, observation/noise model and identifiability norm. |
| [GC171](./problems/06-inverse-observation-control/GC171.md) | Not frozen | P1* | Give actuation and observation operators plus stabilizability assumptions, not just the stripe linearization. |
| [GC172](./problems/06-inverse-observation-control/GC172.md) | Not frozen | P1 | Give the forward map, parameter set, measurement design, observation/noise model and identifiability norm. |
| [GC173](./problems/06-inverse-observation-control/GC173.md) | Not frozen | P1* | Fix probability laws or deterministic uncertainty sets; distinguish mismatch identifiability from a hypothesis-test threshold. |
| [GC174](./problems/06-inverse-observation-control/GC174.md) | Not frozen | P1 | Give the forward map, parameter set, measurement design, observation/noise model and identifiability norm. |
| [GC175](./problems/06-inverse-observation-control/GC175.md) | Not frozen | P1 | Give the forward map, parameter set, measurement design, observation/noise model and identifiability norm. |
| [GC176](./problems/06-inverse-observation-control/GC176.md) | Not frozen | P1 | Give the forward map, parameter set, measurement design, observation/noise model and identifiability norm. |
| [GC177](./problems/07-pattern-formation/GC177.md) | Not frozen | P0* | Distinguish fixed-torus discrete perturbations from continuous Bloch sidebands on R²; a sharp Eckhaus band depends on domain. |
| [GC178](./problems/07-pattern-formation/GC178.md) | Not frozen | P1 | Fix the pattern PDE, spatial domain/BCs, branch, admissible perturbations and stability/selection criterion. |
| [GC179](./problems/07-pattern-formation/GC179.md) | Not frozen | P1 | Fix the pattern PDE, spatial domain/BCs, branch, admissible perturbations and stability/selection criterion. |
| [GC180](./problems/07-pattern-formation/GC180.md) | Not frozen | P1 | Fix the pattern PDE, spatial domain/BCs, branch, admissible perturbations and stability/selection criterion. |
| [GC181](./problems/07-pattern-formation/GC181.md) | Not frozen | P1 | Fix the pattern PDE, spatial domain/BCs, branch, admissible perturbations and stability/selection criterion. |
| [GC182](./problems/07-pattern-formation/GC182.md) | Not frozen | P1* | Define defect density, thermodynamic limit, initial-data ensemble and intended universality quantifier. |
| [GC183](./problems/07-pattern-formation/GC183.md) | Not frozen | P1* | Specify which dynamic selection mechanism and order of large-box versus long-time limits. |
| [GC184](./problems/07-pattern-formation/GC184.md) | Not frozen | P1* | Specify how a finite stripe patch connects to a homogeneous state and the 2D stability space. |
| [GC185](./problems/07-pattern-formation/GC185.md) | Not frozen | P1 | Fix the pattern PDE, spatial domain/BCs, branch, admissible perturbations and stability/selection criterion. |
| [GC186](./problems/07-pattern-formation/GC186.md) | Not frozen | P1 | Fix the pattern PDE, spatial domain/BCs, branch, admissible perturbations and stability/selection criterion. |
| [GC187](./problems/07-pattern-formation/GC187.md) | Not frozen | P1 | Fix the pattern PDE, spatial domain/BCs, branch, admissible perturbations and stability/selection criterion. |
| [GC188](./problems/07-pattern-formation/GC188.md) | Not frozen | P1* | Define the noise SPDE, scaling, rare-event target and observation-time asymptotics. |
| [GC189](./problems/07-pattern-formation/GC189.md) | Not frozen | P1 | Fix the pattern PDE, spatial domain/BCs, branch, admissible perturbations and stability/selection criterion. |
| [GC190](./problems/07-pattern-formation/GC190.md) | Not frozen | P1* | Fix solution domain, topology of quasiperiodic states and orbital-stability perturbation class. |
| [GC191](./problems/07-pattern-formation/GC191.md) | Not frozen | P1 | Fix the pattern PDE, spatial domain/BCs, branch, admissible perturbations and stability/selection criterion. |
| [GC192](./problems/07-pattern-formation/GC192.md) | Not frozen | P1* | Fix field regularity and charge on punctured domains; charge cannot change while all defects stay isolated without boundary flux. |
| [GC193](./problems/07-pattern-formation/GC193.md) | Not frozen | P1 | Fix the pattern PDE, spatial domain/BCs, branch, admissible perturbations and stability/selection criterion. |
| [GC194](./problems/07-pattern-formation/GC194.md) | Not frozen | P1 | Fix the pattern PDE, spatial domain/BCs, branch, admissible perturbations and stability/selection criterion. |
| [GC195](./problems/07-pattern-formation/GC195.md) | Not frozen | P1* | Use excess/interfacial energy for infinite stripes; total whole-plane energy is divergent. |
| [GC196](./problems/08-topology-multicomponent/GC196.md) | Not frozen | P0* | Compare against classical Hopf/Skyrme charge bounds; define normalization and clarify whether 'sharp' is new. |
| [GC197](./problems/08-topology-multicomponent/GC197.md) | Not frozen | P0* | Under S³→S² maps the Hopf invariant classifies homotopy; same-charge maps are homotopic. Require additional restrictions for a nontrivial obstruction. |
| [GC198](./problems/08-topology-multicomponent/GC198.md) | Not frozen | P1 | Specify target manifold, finite-energy field class, invariant, evolution/energy and admissible deformations. |
| [GC199](./problems/08-topology-multicomponent/GC199.md) | Not frozen | P1* | Give the PDE and regularity in space-time; reconnection of nodal sets is distinct from loss of field smoothness. |
| [GC200](./problems/08-topology-multicomponent/GC200.md) | Not frozen | P0* | On a flat torus, pure S¹ Dirichlet-phase energy in fixed winding class is minimized by the harmonic affine phase: likely a standard calculation, not a new open problem. |
| [GC201](./problems/08-topology-multicomponent/GC201.md) | Not frozen | P1 | Specify target manifold, finite-energy field class, invariant, evolution/energy and admissible deformations. |
| [GC202](./problems/08-topology-multicomponent/GC202.md) | Not frozen | P1 | Specify target manifold, finite-energy field class, invariant, evolution/energy and admissible deformations. |
| [GC203](./problems/08-topology-multicomponent/GC203.md) | Not frozen | P1* | Define what is meant by a one-component final state and whether normalized nonvanishing two-component maps carry a Hopf obstruction. |
| [GC204](./problems/08-topology-multicomponent/GC204.md) | Not frozen | P1 | Specify target manifold, finite-energy field class, invariant, evolution/energy and admissible deformations. |
| [GC205](./problems/08-topology-multicomponent/GC205.md) | Not frozen | P1 | Specify target manifold, finite-energy field class, invariant, evolution/energy and admissible deformations. |
| [GC206](./problems/08-topology-multicomponent/GC206.md) | Not frozen | P1 | Specify target manifold, finite-energy field class, invariant, evolution/energy and admissible deformations. |
| [GC207](./problems/08-topology-multicomponent/GC207.md) | Not frozen | P1 | Specify target manifold, finite-energy field class, invariant, evolution/energy and admissible deformations. |
| [GC208](./problems/08-topology-multicomponent/GC208.md) | Not frozen | P1 | Specify target manifold, finite-energy field class, invariant, evolution/energy and admissible deformations. |
| [GC209](./problems/08-topology-multicomponent/GC209.md) | Not frozen | P1* | Fix target space and boundary conditions; scalar-field topological charges depend on these choices. |
| [GC210](./problems/08-topology-multicomponent/GC210.md) | Not frozen | P1 | Specify target manifold, finite-energy field class, invariant, evolution/energy and admissible deformations. |
| [GC211](./problems/08-topology-multicomponent/GC211.md) | Not frozen | P1 | Specify target manifold, finite-energy field class, invariant, evolution/energy and admissible deformations. |
| [GC212](./problems/08-topology-multicomponent/GC212.md) | Not frozen | P0* | If sample paths are jointly continuous and never vanish, topological charge is homotopy-invariant pathwise; make zero hitting and regularity loss the substantive problem. |
| [GC213](./problems/08-topology-multicomponent/GC213.md) | Not frozen | P1 | Specify target manifold, finite-energy field class, invariant, evolution/energy and admissible deformations. |
| [GC214](./problems/08-topology-multicomponent/GC214.md) | Not frozen | P1* | Fix actual moduli space and quotient topology; existence of minimizers is not established just by naming a quotient. |
| [GC215](./problems/09-computability-complexity/GC215.md) | Not frozen | P1* | Define a computable PDE encoding, attractor-basin predicate and finite rational input; otherwise decidability is undefined. |
| [GC216](./problems/09-computability-complexity/GC216.md) | Not frozen | P1* | Supply the specific reversible automaton rule and binary-time representation before asserting a complexity class. |
| [GC217](./problems/09-computability-complexity/GC217.md) | Not frozen | P1* | Fix a single universal rule, Turing simulation encoding and input/space/time measures. |
| [GC218](./problems/09-computability-complexity/GC218.md) | Not frozen | P1 | Fix a concrete rule/input encoding, input-size/precision model, reduction type and uniform resource bound. |
| [GC219](./problems/09-computability-complexity/GC219.md) | Not frozen | P1 | Fix a concrete rule/input encoding, input-size/precision model, reduction type and uniform resource bound. |
| [GC220](./problems/09-computability-complexity/GC220.md) | Not frozen | P1* | Fix concrete CA local rule and target pattern; complexity is not meaningful for an unspecified rule. |
| [GC221](./problems/09-computability-complexity/GC221.md) | Not frozen | P1 | Fix a concrete rule/input encoding, input-size/precision model, reduction type and uniform resource bound. |
| [GC222](./problems/09-computability-complexity/GC222.md) | Not frozen | P1 | Fix a concrete rule/input encoding, input-size/precision model, reduction type and uniform resource bound. |
| [GC223](./problems/09-computability-complexity/GC223.md) | Not frozen | P1* | State arithmetic versus bit complexity, coefficient representation, conditioning and required output tolerance. |
| [GC224](./problems/09-computability-complexity/GC224.md) | Not frozen | P1* | Fix rational lattice energy family and stability predicate; precise decision version may need a promise gap. |
| [GC225](./problems/09-computability-complexity/GC225.md) | Not frozen | P1 | Fix a concrete rule/input encoding, input-size/precision model, reduction type and uniform resource bound. |
| [GC226](./problems/09-computability-complexity/GC226.md) | Not frozen | P1* | Specify the polynomial rule and invariant input representation; global invariance may reduce to finite-field identities. |
| [GC227](./problems/09-computability-complexity/GC227.md) | Not frozen | P1 | Fix a concrete rule/input encoding, input-size/precision model, reduction type and uniform resource bound. |
| [GC228](./problems/09-computability-complexity/GC228.md) | Not frozen | P1* | Freeze bounded-fan-in circuit model, fanout, uniformity and target cellular rule. |
| [GC229](./problems/09-computability-complexity/GC229.md) | Not frozen | P1* | Freeze noise independence, correction overhead and chosen CA/encoding before a fault-tolerance statement. |
| [GC230](./problems/09-computability-complexity/GC230.md) | Not frozen | P1* | Define stability region, perturbation norm and what 'largest guaranteed radius' quantifies. |
| [GC231](./problems/09-computability-complexity/GC231.md) | Not frozen | P1 | Fix a concrete rule/input encoding, input-size/precision model, reduction type and uniform resource bound. |
| [GC232](./problems/09-computability-complexity/GC232.md) | Not frozen | P1 | Fix a concrete rule/input encoding, input-size/precision model, reduction type and uniform resource bound. |
| [GC233](./problems/09-computability-complexity/GC233.md) | Not frozen | P1* | Clarify promise gap, rational input encoding, numerical precision and spectral-gap predicate. |
| [GC234](./problems/09-computability-complexity/GC234.md) | Not frozen | P1* | Specify temperature/bath, work accounting, error tolerance and allowed external controls. |
| [GC235](./problems/10-lean-certified-analysis/GC235.md) | Not frozen | P0* | Primarily a Lean formalization task for established Fourier–Plancherel mathematics; do not frame as novel unsolved theorem. |
| [GC236](./problems/10-lean-certified-analysis/GC236.md) | Not frozen | P1* | Freeze Fourier convention, dimension/Sobolev algebra range, energy domain and exact derivative mapping. |
| [GC237](./problems/10-lean-certified-analysis/GC237.md) | Not frozen | P1* | Separate a conditional direct-method metatheorem from actual concentration-compactness required for wave minimizers. |
| [GC238](./problems/10-lean-certified-analysis/GC238.md) | Not frozen | P1* | Determine whether group orbit-distance is a pseudometric on H² or a metric on the quotient; address noncompact translation orbits. |
| [GC239](./problems/10-lean-certified-analysis/GC239.md) | Not frozen | P1 | State an exact mathematical theorem signature, hypotheses and intended Mathlib/Lean correspondence. |
| [GC240](./problems/10-lean-certified-analysis/GC240.md) | Not frozen | P1* | Fix torus Fourier conventions, ℓ² summability and projector definition; likely known mathematics formalization. |
| [GC241](./problems/10-lean-certified-analysis/GC241.md) | Not frozen | P1 | State an exact mathematical theorem signature, hypotheses and intended Mathlib/Lean correspondence. |
| [GC242](./problems/10-lean-certified-analysis/GC242.md) | Not frozen | P1* | Pin an actual stationary equation and invertibility hypothesis; generic IFT formalization is not itself a research conjecture. |
| [GC243](./problems/10-lean-certified-analysis/GC243.md) | Not frozen | P1 | State an exact mathematical theorem signature, hypotheses and intended Mathlib/Lean correspondence. |
| [GC244](./problems/10-lean-certified-analysis/GC244.md) | Not frozen | P1 | State an exact mathematical theorem signature, hypotheses and intended Mathlib/Lean correspondence. |
| [GC245](./problems/10-lean-certified-analysis/GC245.md) | Not frozen | P1 | State an exact mathematical theorem signature, hypotheses and intended Mathlib/Lean correspondence. |
| [GC246](./problems/10-lean-certified-analysis/GC246.md) | Not frozen | P1 | State an exact mathematical theorem signature, hypotheses and intended Mathlib/Lean correspondence. |
| [GC247](./problems/10-lean-certified-analysis/GC247.md) | Not frozen | P0* | Scattering unitarity under complete wave operators is classical; document as formalization milestone rather than open conjecture. |
| [GC248](./problems/10-lean-certified-analysis/GC248.md) | Not frozen | P0* | Homotopy invariance of winding is classical; substantive novel requirement would be a PDE nonvanishing theorem. |
| [GC249](./problems/10-lean-certified-analysis/GC249.md) | Not frozen | P1 | State an exact mathematical theorem signature, hypotheses and intended Mathlib/Lean correspondence. |
| [GC250](./problems/10-lean-certified-analysis/GC250.md) | Not frozen | P1* | Define a counterexample witness schema, statement parser and trusted kernel boundary; primarily tool specification. |
| [GC251](./problems/10-lean-certified-analysis/GC251.md) | Not frozen | P1 | State an exact mathematical theorem signature, hypotheses and intended Mathlib/Lean correspondence. |
| [GC252](./problems/10-lean-certified-analysis/GC252.md) | Not frozen | P0* | Convergence under compactness and strict Lyapunov hypotheses is standard LaSalle-type theory; distinguish formalization from new result. |
| [GC253](./problems/10-lean-certified-analysis/GC253.md) | Not frozen | P1 | State an exact mathematical theorem signature, hypotheses and intended Mathlib/Lean correspondence. |
| [GC254](./problems/11-physical-emergence-multiscale/GC254.md) | Not frozen | P1* | Write lattice equations, dispersion degeneracy and two-scale ansatz with a rigorously specified error interval. |
| [GC255](./problems/11-physical-emergence-multiscale/GC255.md) | Not frozen | P1* | Choose an interpolation operator from lattice to continuum and a topology ruling out concentration/escape. |
| [GC256](./problems/11-physical-emergence-multiscale/GC256.md) | Not frozen | P1 | Give a microscopic model, continuum scaling, initial-data class, boundary conditions and convergence norm. |
| [GC257](./problems/11-physical-emergence-multiscale/GC257.md) | Not frozen | P1 | Give a microscopic model, continuum scaling, initial-data class, boundary conditions and convergence norm. |
| [GC258](./problems/11-physical-emergence-multiscale/GC258.md) | Not frozen | P1 | Give a microscopic model, continuum scaling, initial-data class, boundary conditions and convergence norm. |
| [GC259](./problems/11-physical-emergence-multiscale/GC259.md) | Not frozen | P1* | Define geometric curvature term; anisotropic stiffness alone does not uniquely determine a curvature operator. |
| [GC260](./problems/11-physical-emergence-multiscale/GC260.md) | Not frozen | P1 | Give a microscopic model, continuum scaling, initial-data class, boundary conditions and convergence norm. |
| [GC261](./problems/11-physical-emergence-multiscale/GC261.md) | Not frozen | P1* | Specify disorder law and scaling; 'threshold beyond which approximation ceases' must be an explicit quantifier. |
| [GC262](./problems/11-physical-emergence-multiscale/GC262.md) | Not frozen | P1 | Give a microscopic model, continuum scaling, initial-data class, boundary conditions and convergence norm. |
| [GC263](./problems/11-physical-emergence-multiscale/GC263.md) | Not frozen | P1 | Give a microscopic model, continuum scaling, initial-data class, boundary conditions and convergence norm. |
| [GC264](./problems/11-physical-emergence-multiscale/GC264.md) | Not frozen | P1 | Give a microscopic model, continuum scaling, initial-data class, boundary conditions and convergence norm. |
| [GC265](./problems/11-physical-emergence-multiscale/GC265.md) | Not frozen | P1* | Specify order of limits in a concrete observable and establish existence of both iterated limits. |
| [GC266](./problems/11-physical-emergence-multiscale/GC266.md) | Not frozen | P1 | Give a microscopic model, continuum scaling, initial-data class, boundary conditions and convergence norm. |
| [GC267](./problems/11-physical-emergence-multiscale/GC267.md) | Not frozen | P1 | Give a microscopic model, continuum scaling, initial-data class, boundary conditions and convergence norm. |
| [GC268](./problems/11-physical-emergence-multiscale/GC268.md) | Not frozen | P1* | Define topological invariant at lattice scale and continuity/nonvanishing of interpolants. |
| [GC269](./problems/11-physical-emergence-multiscale/GC269.md) | Not frozen | P1* | Freeze 3D parent operator, thin-domain scaling and explain why its transverse limit is fourth order in 2D. |
| [GC270](./problems/11-physical-emergence-multiscale/GC270.md) | Not frozen | P1 | Give a microscopic model, continuum scaling, initial-data class, boundary conditions and convergence norm. |
| [GC271](./problems/11-physical-emergence-multiscale/GC271.md) | Not frozen | P1 | Give a microscopic model, continuum scaling, initial-data class, boundary conditions and convergence norm. |
| [GC272](./problems/11-physical-emergence-multiscale/GC272.md) | Not frozen | P1 | Give a microscopic model, continuum scaling, initial-data class, boundary conditions and convergence norm. |
| [GC273](./problems/11-physical-emergence-multiscale/GC273.md) | Not frozen | P1 | Give a microscopic model, continuum scaling, initial-data class, boundary conditions and convergence norm. |
| [GC274](./problems/11-physical-emergence-multiscale/GC274.md) | Not frozen | P1 | Give a microscopic model, continuum scaling, initial-data class, boundary conditions and convergence norm. |
| [GC275](./problems/11-physical-emergence-multiscale/GC275.md) | Not frozen | P1* | Specify hardware phase-to-coupling map and calibrated observable; arbitrary phase shifters do not yield a unique PDE coefficient map. |
| [GC276](./problems/11-physical-emergence-multiscale/GC276.md) | Not frozen | P1* | Specify lattice-envelope spectral relation and exclude unseen high-frequency instability. |
| [GC277](./problems/12-photonic-wave-computing/GC277.md) | Not frozen | P1* | Freeze XOR phase encoding, detector probability model and worst-case versus stochastic robustness. |
| [GC278](./problems/12-photonic-wave-computing/GC278.md) | Not frozen | P0* | Separate passive coherent linear optics from intensity detection/thresholding, which supplies nonlinear readout; define external regeneration and fanout allowances. |
| [GC279](./problems/12-photonic-wave-computing/GC279.md) | Not frozen | P1* | Specify stage-to-stage optical encoding and whether electronic regeneration is permitted. |
| [GC280](./problems/12-photonic-wave-computing/GC280.md) | Not frozen | P1* | Specify stochastic phase/dissipation dynamics, distinguishability and fixed error probability. |
| [GC281](./problems/12-photonic-wave-computing/GC281.md) | Not frozen | P1 | Specify the optical components and encoding, nonlinear resources, power/noise model, measured output and tolerance. |
| [GC282](./problems/12-photonic-wave-computing/GC282.md) | Not frozen | P1* | Choose a specific optical adder architecture and input encoding; bit-width scaling is not architecture-independent. |
| [GC283](./problems/12-photonic-wave-computing/GC283.md) | Not frozen | P1* | Fix photon statistics, error probability, copy mechanism and active regeneration allowance. |
| [GC284](./problems/12-photonic-wave-computing/GC284.md) | Not frozen | P1 | Specify the optical components and encoding, nonlinear resources, power/noise model, measured output and tolerance. |
| [GC285](./problems/12-photonic-wave-computing/GC285.md) | Not frozen | P1 | Specify the optical components and encoding, nonlinear resources, power/noise model, measured output and tolerance. |
| [GC286](./problems/12-photonic-wave-computing/GC286.md) | Not frozen | P0* | Energy accounting/comparative engineering becomes a falsifiable mathematical target only after freezing equipment scope and reference workload. |
| [GC287](./problems/12-photonic-wave-computing/GC287.md) | Not frozen | P1* | Specify saturating optical nonlinearity and symmetry; a 'unique wavelength' is meaningless with unbroken degeneracies. |
| [GC288](./problems/12-photonic-wave-computing/GC288.md) | Not frozen | P1 | Specify the optical components and encoding, nonlinear resources, power/noise model, measured output and tolerance. |
| [GC289](./problems/12-photonic-wave-computing/GC289.md) | Not frozen | P1* | Specify disturbance spectrum, sampled controller and what counts toward feedback bandwidth. |
| [GC290](./problems/12-photonic-wave-computing/GC290.md) | Not frozen | P1* | State optical quantum/classical state encoding, signal photon budget and distinguishability error. |
| [GC291](./problems/12-photonic-wave-computing/GC291.md) | Not frozen | P1 | Specify the optical components and encoding, nonlinear resources, power/noise model, measured output and tolerance. |
| [GC292](./problems/12-photonic-wave-computing/GC292.md) | Not frozen | P1* | Specify resonator coupling matrix, read-out and address decoding tolerance. |
| [GC293](./problems/12-photonic-wave-computing/GC293.md) | Not frozen | P1 | Specify the optical components and encoding, nonlinear resources, power/noise model, measured output and tolerance. |
| [GC294](./problems/12-photonic-wave-computing/GC294.md) | Not frozen | P1* | Define independent fault process, decoder, gate set and how circuit overhead is counted. |
| [GC295](./problems/12-photonic-wave-computing/GC295.md) | Not frozen | P1* | A compiler-correctness task: freeze both source semantics and physical device model before describing a theorem. |
| [GC296](./problems/12-photonic-wave-computing/GC296.md) | Not frozen | P1* | Specify calibration confidence, interval arithmetic and what measurements actually certify. |
| [GC297](./problems/12-photonic-wave-computing/GC297.md) | Not frozen | P1 | Specify the optical components and encoding, nonlinear resources, power/noise model, measured output and tolerance. |
| [GC298](./problems/12-photonic-wave-computing/GC298.md) | Not frozen | P1 | Specify the optical components and encoding, nonlinear resources, power/noise model, measured output and tolerance. |
| [GC299](./problems/12-photonic-wave-computing/GC299.md) | Not frozen | P1* | Fix thermodynamic bath, temperature, reset protocol, precision, allowed irreversibility and photon-loss metric. |
| [GC300](./problems/12-photonic-wave-computing/GC300.md) | Not frozen | P1* | Freeze a concrete circuit, compiler semantics, physical uncertainty set and a compositional correctness claim. |

## Counts and next review stage

- 236 entries screened; 113 entries have an individualized caution; **15 P0** issues need concept-first examination and **221 P1** need ordinary specification.
- This table does **not** certify `0/236` as intrinsically unformulable: it records `0/236` promoted by this screen because the current published descriptions do not document full frozen propositions.
- Do **not** mass-edit the 235 source problem sketches or change the machine registry to `open_verified`. Preserve source text as a historical candidate; add a scoped dossier or a linked issue per selected target.
- For P0 issues first test the alleged logical issue or elementary result rigorously. For P1 issues write a precise frozen theorem/counterexample and inspect closest published work. Repeat the review after each change.
- Recommended next artifact for each item: `statement_v1`, `assumptions`, `failure_cases`, `related_prior_work`, `acceptance_criteria`, `Lean_scope_if_any`, `reviewer_status`.

_Editorial scoping audit, distinct from independent mathematical peer review._
