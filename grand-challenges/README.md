# 50 Grand Challenges in Wave Mathematics

> **Can a wave confine itself, form a stable knot, select its own wavelength, or perform universal computation?**

**50 proposed mathematical research problems. 10 areas of mathematics. Every proposed claim is open to proof, counterexample, or refinement.**

These questions connect nonlinear partial differential equations, variational analysis, spectral geometry, topological fields, computation, and formal verification. They are invitations to investigate, not claims of 50 previously unknown theorems.

**[Explore the 50 formal problem statements](./FORMAL_PROBLEMS.md)** · **[Browse existing papers](../papers)** · **[Explore Lean 4 proofs](../lean/MathProofs)** · **[Open a research discussion](https://github.com/rickyjreyes/math/issues)**

> [!IMPORTANT]
> **Research status:** This is a proposed challenge catalogue, **not** an established list of unsolved problems comparable in standing to the Millennium Prize Problems. No prizes are offered. Novelty and open status have not been established through comprehensive literature review. Some statements have partial results or counterexamples; others require sharper assumptions. See [research standards](#what-counts-as-a-solution).

---

## Start here: five questions worth exploring

### [**GC06 · Can a wave confine itself?**](./FORMAL_PROBLEMS.md#gc06-can-a-wave-confine-itself)

A nonlinear wave may spread, fragment, or remain localized. Find the precise conditions under which localized energy minimizers actually exist without an imposed trapping potential.

*Relevant foundations: [whole-space minimizers](../papers/whole-space-fourth-order-cubic-quintic-minimizers) and [Lean minimizer modules](../lean/MathProofs/WholeSpaceMinimizers.lean).*

### [**GC36 · Can a knot of wave energy survive?**](./FORMAL_PROBLEMS.md#gc36-can-a-knot-of-wave-energy-survive)

Determine whether a nontrivial topological class supports a stable stationary field, or prove an obstruction. A picture of a knot is not itself a stability theorem.

*Research status: proposed model-dependent existence and stability question.*

### [**GC11 · Can a wave select its own wavelength?**](./FORMAL_PROBLEMS.md#gc11-can-a-wave-select-its-own-wavelength)

Linear dispersion can prefer a finite scale. The harder question is whether nonlinear dynamics select and stabilize one wavelength among competing patterns.

*Related foothold: [exact positive-wave-number minimum](../papers/exact-positive-wavenumber-minimum) and [Lean dispersion analysis](../lean/MathProofs/DispersionMinimum.lean).*

### [**GC43 · Can a wave-based rule compute anything?**](./FORMAL_PROBLEMS.md#gc43-can-a-wave-based-rule-compute-anything)

Specify a finite-alphabet local wave-cell model and ask whether a fixed rule can simulate every Turing machine with polynomial overhead.

*Research status: proposed computational model, not a claim about demonstrated physical hardware.*

### [**GC01 · Which waves can survive a disturbance?**](./FORMAL_PROBLEMS.md#gc01-which-waves-can-survive-a-disturbance)

Go beyond stable ground-state minimizers and classify standing waves, including excited states, whose phase-and-translation orbits remain stable.

*Relevant foundations: [orbital stability analysis](../papers/orbital-stability-fourth-order-cubic-quintic) and [Lean stability module](../lean/MathProofs/OrbitalStability.lean).*

---

## One mathematical model behind several challenges

A representative equation in this research program is the fourth-order cubic–quintic nonlinear Schrödinger equation:

```math
i\partial_t u
= (\Delta+k^2)^2u - \beta|u|^2u + \gamma|u|^4u,
\qquad \beta,\gamma>0.
```

The central issue is not merely whether a localized shape can be drawn or simulated. It is whether such a state **exists**, whether it is **stable**, whether it is **unique**, and whether the claim holds for the **exact equation and assumptions stated**.

Related starting points: [orbital stability](../papers/orbital-stability-fourth-order-cubic-quintic), [strict subadditivity](../papers/strict-subadditivity-fourth-order-cubic-quintic), and [whole-space minimizers](../papers/whole-space-fourth-order-cubic-quintic-minimizers). Existing results address particular models and hypotheses, not every question in this catalogue.

---

## The complete challenge catalogue

**Choose a question.** Each title links to its mathematical problem statement, including a proof-or-counterexample resolution criterion. The plain-language prompts below are guides, not replacements for the formal statements.

**Status key:** All entries are **proposed / literature review pending** unless specifically noted. *Related established work* is not a claim that the challenge is solved.

<details open>
<summary><strong>Nonlinear wave dynamics</strong> · 5 challenges</summary>

| Problem | The question |
|:--|:--|
| [**GC01 · Universal orbital stability**](./FORMAL_PROBLEMS.md#gc01-universal-orbital-stability) | Which localized waves remain stable under every sufficiently small disturbance? |
| [**GC02 · Long-time asymptotic stability**](./FORMAL_PROBLEMS.md#gc02-long-time-asymptotic-stability) | Do perturbed solitary waves settle into coherent shapes plus radiation? |
| [**GC03 · Global existence versus blow-up**](./FORMAL_PROBLEMS.md#gc03-global-existence-versus-blow-up) | Which nonlinear wave laws remain regular for all time? |
| [**GC04 · Stable multi-wave interactions**](./FORMAL_PROBLEMS.md#gc04-stable-multi-wave-interactions) | Can distinct localized waves interact and survive? |
| [**GC05 · Breather existence and classification**](./FORMAL_PROBLEMS.md#gc05-breather-existence-and-classification) | Can a localized wave oscillate forever without dispersing? |

</details>

<details open>
<summary><strong>Confinement geometry</strong> · 5 challenges</summary>

| Problem | The question |
|:--|:--|
| [**GC06 · Self-confinement criteria**](./FORMAL_PROBLEMS.md#gc06-self-confinement-criteria) | When does a wave localize without an external trap? |
| [**GC07 · Curvature-induced localization**](./FORMAL_PROBLEMS.md#gc07-curvature-induced-localization) | Can geometry alone produce an exponentially confined state? |
| [**GC08 · Admissible curvature closures**](./FORMAL_PROBLEMS.md#gc08-admissible-curvature-closures) *(nonuniqueness example known)* | Which symmetry-preserving curvature laws are mathematically possible? |
| [**GC09 · Topological confinement protection**](./FORMAL_PROBLEMS.md#gc09-topological-confinement-protection) | Can winding prevent a wave configuration from unwinding? |
| [**GC10 · Dimensional localized-energy classification**](./FORMAL_PROBLEMS.md#gc10-dimensional-localized-energy-classification) | In which dimensions can constrained localized states exist? |

</details>

<details open>
<summary><strong>Spectral mathematics</strong> · 5 challenges</summary>

| Problem | The question |
|:--|:--|
| [**GC11 · Nonlinear finite-wavelength selection**](./FORMAL_PROBLEMS.md#gc11-nonlinear-finite-wavelength-selection) | Can a nonlinear system choose a preferred wavelength? |
| [**GC12 · Nonlinear spectral-gap persistence**](./FORMAL_PROBLEMS.md#gc12-nonlinear-spectral-gap-persistence) | When do spectral gaps survive perturbations of a pattern? |
| [**GC13 · Interband nonlinear energy transfer**](./FORMAL_PROBLEMS.md#gc13-interband-nonlinear-energy-transfer) | When must nonlinear coupling move energy between Fourier bands? |
| [**GC14 · Spectral concentration versus localization**](./FORMAL_PROBLEMS.md#gc14-spectral-concentration-versus-localization) | Can a wave be sharply localized in both space and frequency? |
| [**GC15 · Finite-mode invariant manifolds**](./FORMAL_PROBLEMS.md#gc15-finite-mode-invariant-manifolds) | Can a few Fourier modes form an exactly closed nonlinear system? |

</details>

<details open>
<summary><strong>Variational mathematics</strong> · 5 challenges</summary>

| Problem | The question |
|:--|:--|
| [**GC16 · Strict binding across masses**](./FORMAL_PROBLEMS.md#gc16-strict-binding-across-masses) | At which masses is one bound wave energetically favored over two? |
| [**GC17 · Constrained-minimizer uniqueness**](./FORMAL_PROBLEMS.md#gc17-constrained-minimizer-uniqueness) | Is a minimum-energy confined wave unique up to symmetry? |
| [**GC18 · Symmetry-breaking thresholds**](./FORMAL_PROBLEMS.md#gc18-symmetry-breaking-thresholds) | When do symmetric ground states become asymmetric? |
| [**GC19 · Critical compactness failures**](./FORMAL_PROBLEMS.md#gc19-critical-compactness-failures) | Exactly when can minimizing sequences split or escape? |
| [**GC20 · Metastable energy landscapes**](./FORMAL_PROBLEMS.md#gc20-metastable-energy-landscapes) | Can a wave remain trapped near a non-global energy minimum? |

</details>

<details open>
<summary><strong>Higher-derivative fields</strong> · 5 challenges</summary>

| Problem | The question |
|:--|:--|
| [**GC21 · Ghost-free higher-derivative dynamics**](./FORMAL_PROBLEMS.md#gc21-ghost-free-higher-derivative-dynamics) | Can higher-time-derivative field theories avoid negative-energy modes? |
| [**GC22 · UV well-posedness classification**](./FORMAL_PROBLEMS.md#gc22-uv-well-posedness-classification) | Which high-frequency dispersion laws admit stable evolution? |
| [**GC23 · Physically stable wavelength selection**](./FORMAL_PROBLEMS.md#gc23-physically-stable-wavelength-selection) | Can a positive-energy field theory select a nonzero wave number? |
| [**GC24 · Hamiltonian constraint classification**](./FORMAL_PROBLEMS.md#gc24-hamiltonian-constraint-classification) | Can constraints eliminate apparent higher-derivative instabilities? |
| [**GC25 · Consistent parent theories**](./FORMAL_PROBLEMS.md#gc25-consistent-parent-theories) | Can stable lower-order models reproduce higher-derivative effects? |

</details>

<details open>
<summary><strong>Inverse problems</strong> · 5 challenges</summary>

| Problem | The question |
|:--|:--|
| [**GC26 · Local versus global identifiability**](./FORMAL_PROBLEMS.md#gc26-local-versus-global-identifiability) | When do observations determine a model's parameters uniquely? |
| [**GC27 · Minimal parameter-recovery observations**](./FORMAL_PROBLEMS.md#gc27-minimal-parameter-recovery-observations) | How few measurements suffice to identify a model? |
| [**GC28 · Curvature-map noninjectivity**](./FORMAL_PROBLEMS.md#gc28-curvature-map-noninjectivity) | How many different fields can share the same curvature measurement? |
| [**GC29 · Noise-stable reconstruction**](./FORMAL_PROBLEMS.md#gc29-noise-stable-reconstruction) | Can parameters be reconstructed with error bounds under noise? |
| [**GC30 · Partial-data spectral uniqueness**](./FORMAL_PROBLEMS.md#gc30-partial-data-spectral-uniqueness) | How much spectral information determines an unknown potential? |

</details>

<details open>
<summary><strong>Pattern formation</strong> · 5 challenges</summary>

| Problem | The question |
|:--|:--|
| [**GC31 · Nonlinear Swift–Hohenberg attractors**](./FORMAL_PROBLEMS.md#gc31-nonlinear-swifthohenberg-attractors) | What long-time patterns can a fourth-order flow produce? |
| [**GC32 · Coarsening versus wavelength locking**](./FORMAL_PROBLEMS.md#gc32-coarsening-versus-wavelength-locking) | Do patterns lock to a scale or keep changing it? |
| [**GC33 · Pattern robustness under disorder**](./FORMAL_PROBLEMS.md#gc33-pattern-robustness-under-disorder) | Which patterns survive spatially varying imperfections? |
| [**GC34 · Defect nucleation and annihilation**](./FORMAL_PROBLEMS.md#gc34-defect-nucleation-and-annihilation) | When can a pattern create or remove dislocations? |
| [**GC35 · Infinite-domain pattern selection**](./FORMAL_PROBLEMS.md#gc35-infinite-domain-pattern-selection) | Can infinite-space dynamics select one stripe wavelength? |

</details>

<details open>
<summary><strong>Emergent structures and topology</strong> · 5 challenges</summary>

| Problem | The question |
|:--|:--|
| [**GC36 · Stable knotted wave configurations**](./FORMAL_PROBLEMS.md#gc36-stable-knotted-wave-configurations) | Can a knot in a field become a stable localized structure? |
| [**GC37 · Discrete particle-like solutions**](./FORMAL_PROBLEMS.md#gc37-discrete-particle-like-solutions) | Must confined waves form discrete families, or continuous ones? |
| [**GC38 · Quantized winding conservation**](./FORMAL_PROBLEMS.md#gc38-quantized-winding-conservation) | When are winding numbers protected by evolution? |
| [**GC39 · Coherent-state interaction laws**](./FORMAL_PROBLEMS.md#gc39-coherent-state-interaction-laws) | Can the motion of interacting waves be reduced to effective laws? |
| [**GC40 · Topology-changing singularities**](./FORMAL_PROBLEMS.md#gc40-topology-changing-singularities) | What must fail for a topological charge to change? |

</details>

<details open>
<summary><strong>Computability and complexity</strong> · 5 challenges</summary>

| Problem | The question |
|:--|:--|
| [**GC41 · Decidability of PDE stability**](./FORMAL_PROBLEMS.md#gc41-decidability-of-pde-stability) | Can an algorithm always decide stability for a wave equation? |
| [**GC42 · Complexity of certified wave evolution**](./FORMAL_PROBLEMS.md#gc42-complexity-of-certified-wave-evolution) | How costly is a guaranteed-accurate wave simulation? |
| [**GC43 · Discrete-wave computational universality**](./FORMAL_PROBLEMS.md#gc43-discrete-wave-computational-universality) | Can a fixed local wave-cell rule simulate any Turing machine? |
| [**GC44 · Sequential-work lower bounds**](./FORMAL_PROBLEMS.md#gc44-sequential-work-lower-bounds) | Can local wave evolution be shortcut in parallel? |
| [**GC45 · Precision and noise limits**](./FORMAL_PROBLEMS.md#gc45-precision-and-noise-limits) | What precision does reliable prediction fundamentally require? |

</details>

<details open>
<summary><strong>Formal mathematics</strong> · 5 challenges</summary>

| Problem | The question |
|:--|:--|
| [**GC46 · Verified infinite-dimensional evolution**](./FORMAL_PROBLEMS.md#gc46-verified-infinite-dimensional-evolution) | Can a nonlinear PDE evolution theorem be checked end to end in Lean? |
| [**GC47 · Formal concentration compactness**](./FORMAL_PROBLEMS.md#gc47-formal-concentration-compactness) | Can all compactness alternatives be proved in a proof assistant? |
| [**GC48 · Certified spectral semigroups**](./FORMAL_PROBLEMS.md#gc48-certified-spectral-semigroups) | Can semigroup generation be formally derived from Fourier analysis? |
| [**GC49 · Checked PDE counterexamples**](./FORMAL_PROBLEMS.md#gc49-checked-pde-counterexamples) | Can a false compactness claim be rigorously refuted in Lean? |
| [**GC50 · Proof-carrying numerical certificates**](./FORMAL_PROBLEMS.md#gc50-proof-carrying-numerical-certificates) | Can numerical wave predictions come with machine-checkable proofs? |

</details>

---

## Where the mathematics already begins

The catalogue is grounded in an existing research repository. The links below are **related starting points**, not certificates that the broader challenge has been solved.

| Area | Existing work | Formalization |
|:--|:--|:--|
| Localized wave stability | [Orbital stability and its hypotheses](../papers/orbital-stability-fourth-order-cubic-quintic) | [OrbitalStability.lean](../lean/MathProofs/OrbitalStability.lean) |
| Variational confinement | [Strict subadditivity](../papers/strict-subadditivity-fourth-order-cubic-quintic) | [StrictBinding.lean](../lean/MathProofs/StrictBinding.lean) |
| Wavelength selection | [Exact positive-wavenumber minimum](../papers/exact-positive-wavenumber-minimum) | [DispersionMinimum.lean](../lean/MathProofs/DispersionMinimum.lean) |
| Curvature nonuniqueness | [M6B curvature analysis](../papers/m6b-nonlinear-curvature-nonuniqueness) | [M6BClosureTheorem.lean](../lean/MathProofs/M6BClosureTheorem.lean) |
| Higher-derivative obstructions | [UV Sobolev ill-posedness](../papers/uv-sobolev-ill-posedness-fourth-order-wave) | [UVIllPosedness.lean](../lean/MathProofs/UVIllPosedness.lean) |
| Spectral concentration | [Fourier-shell exclusion](../papers/isolated-fourier-shell-no-l2-bound-state) | [FourierShellL2.lean](../lean/MathProofs/FourierShellL2.lean) |

### A counterexample is a result

For **[GC08: admissible curvature closures](./FORMAL_PROBLEMS.md#gc08-admissible-curvature-closures)**, the broad symmetry and plane-wave assumptions already admit inequivalent operators. In particular, adding a multiple of the Laplacian of the intensity gives a simple nonuniqueness example:

```math
C_{\lambda}(u)
= K_{\varepsilon}(u)+\lambda\,\Delta(|u|^2).
```

That refutes uniqueness under the unrestricted conditions. The interesting remaining work is to classify admissible closures or find extra axioms that make a uniqueness theorem possible. **Disproof, refinement, and impossibility theorems count as progress.**

---

## What counts as a solution?

A challenge is **not completed** by an appealing visualization, a successful numerical run, a Lean lemma about a simplified model, or an argument that assumes the main conclusion.

To resolve a mathematical problem:

1. **State it precisely.** Freeze the equation, function space, domain, parameter ranges, quantifiers, and meaning of stability or computation.
2. **Check the literature and attack it.** Identify closest known results, inspect special cases, seek counterexamples, and distinguish genuine gaps from already settled questions.
3. **Prove or refute the claim.** Give a reproducible mathematical argument with explicit hypotheses. A correct counterexample is a valid resolution.
4. **Formalize when feasible.** Link Lean 4 source to the exact theorem being claimed, without treating formal verification as evidence of novelty or physical realization.
5. **Document the result.** Record the theorem or counterexample, assumptions, limitations, and relevant numerical or experimental checks in a linked paper or issue.

### Want to work on one?

Pick any **GC01–GC50**, read its [formal problem statement](./FORMAL_PROBLEMS.md), and [open a GitHub issue](https://github.com/rickyjreyes/math/issues/new) identifying the challenge ID, relevant prior work, and your proposed proof, counterexample, or sharper formulation. Contributions can include literature corrections and evidence that an item is already known or not well-posed.

**A good challenge is not one that sounds impossible. It is one whose answer changes what we can rigorously say about waves.**

---

*Maintained as a research-question catalogue. Scope and statuses may change as the literature is checked, counterexamples are found, and results are proved.*
