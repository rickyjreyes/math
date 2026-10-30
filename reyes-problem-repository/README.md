# The Reyes Problem Repository

> **Can a wave confine itself, form a stable knot, select its own wavelength, or perform universal computation?**

**An evolving, open-source corpus of 300 mathematical research candidates in 12 subject folders.** GC01–GC65 preserve existing formal question statements; GC66–GC300 originated as research sketches. **Versioned proposed mathematical scopes for every GC65–GC300 entry now appear in [the scoped problem index](./scoped/README.md),** with independent mathematical and prior-art review still required.

The Reyes Problem Repository is a living, version-controlled research collection built around **GitHub issues, research pull requests, existing Lean 4 proofs, optional mathematical papers, and an open invitation to contribute**. The research program continues regardless of outside participation. Problems can grow, branch, be corrected, or be resolved as evidence develops. Its questions connect nonlinear PDEs, variational analysis, spectral geometry, topological fields, computation, and formal verification. No generated conjecture becomes a theorem merely because an LLM proposed it.

**[Browse all 300 questions](./ROADMAP_300.md)** · **[GC65–GC300: 236 precise proposed models and proof targets](./scoped/README.md)** · **[12 research folders](./problems/README.md)** · **[Foundational shortlist](./FOUNDATIONAL_SHORTLIST.md)** · **[Original 65 formal problems](./FORMAL_PROBLEMS.md)** · **[Live research status](./STATUS.md)** · **[Five flagship dossiers](#start-here-five-questions-worth-exploring)** · **[Candidate notebook](./NOTEBOOK.md)** · **[How to contribute](./CONTRIBUTING.md)**

**[GC01–GC65 research and proof links](./GC65_ADOPTION.md)** · **[GC66–GC300 activation](./CANDIDATE_ACTIVATION.md)** · **[Workflow and proof contract](./WORKFLOW.md)** · **[Existing Lean and paper adoption](./EXISTING_WORK.md)** · **[Screening and editorial method](./METHOD.md)** · [Initial literature ledger](./LITERATURE.md) · [Flagship screening](./SCREENING.md) · [Existing papers](../papers) · [Lean 4 source](../lean/MathProofs) · [Submit a research contribution](https://github.com/rickyjreyes/math/issues/new?template=grand_challenge.yml)

> [!IMPORTANT]
> **Research status:** This is a proposed challenge catalogue, **not** an established list of unsolved problems comparable in standing to the Millennium Prize Problems. No prizes are offered. Novelty and open status have not been established through comprehensive literature review. Some statements have partial results or counterexamples; others require sharper assumptions. See [research standards](#what-counts-as-a-solution).

> [!NOTE]
> **Corpus scope:** The 300 entries form a research agenda, not a verified list of 300 unsolved problems. GC01–GC65 retain their canonical archival statements; GC66–GC300 retain their historical drafts. The new [GC65–GC300 scoped collection](./scoped/README.md) supplies concrete candidate models and quantified proof targets, but **these are proposed statements pending independent technical checks and literature clearance**, not automatically correct, novel, or resolved theorems. The [25 foundational candidates](./FOUNDATIONAL_SHORTLIST.md) are only a screening shortlist.

---


## Research like an open-source software project

**Each mathematical research task belongs in a GitHub issue, contributions arrive through PRs, and Lean checks the exact formal theorem.** Existing mathematics is respected: no proof or manuscript needs to be copied, moved, reopened or rewritten to join this workflow. Papers are optional, but claims described as Lean verified must match the underlying theorem and its assumptions.

- **Find existing work first.** The [GC01–GC65 adoption index](./GC65_ADOPTION.md) maps existing proof modules and papers for the original 65 questions, without presenting narrower results as full solutions. The [candidate activation guide](./CANDIDATE_ACTIVATION.md) keeps GC66–GC300 as drafts until selected and mathematically scoped.
- **Choose an existing or carefully scoped issue.** An unreviewed GC entry is not automatically a formally stated open problem. Search for existing GC and Lean formalization issues before creating a duplicate. [Preview a draft issue locally](./WORKFLOW.md).
- **Propose a solution by PR.** Identify the exact theorem or counterexample and its assumptions, Lean declaration, successful existing CI run, and what remains unresolved. A milestone issue may close while its parent GC remains open.
- **Publish when useful.** Link an optional paper with its exact claim reference. Clearly identify any analytical argument, simulation or physical interpretation that was not established by the Lean theorem.
- **Credit the contributor.** Original and external contributors retain attribution for their results; disproofs and corrections advance the research program too.

**Start here:** [Issue, PR, Lean and paper contract](./WORKFLOW.md) · [Existing research adoption](./EXISTING_WORK.md) · [Contribution guide](./CONTRIBUTING.md) · [Open a scoped GC issue](https://github.com/rickyjreyes/math/issues/new?template=gc_problem.yml) · [Submit a research finding](https://github.com/rickyjreyes/math/issues/new?template=grand_challenge.yml).

**Non-regression rule:** Formal verification through the GC process applies to newly claimed GC resolutions; it does not retroactively invalidate or rewrite any earlier manuscript, theorem, or unrelated research issue.

---
## Start here: five questions worth exploring

### [**GC06 · Can a wave confine itself?**](./FORMAL_PROBLEMS.md#gc06-self-confinement-criteria)

A nonlinear wave may spread, fragment, or remain localized. Find the precise conditions under which localized energy minimizers actually exist without an imposed trapping potential.

*Relevant foundations: [whole-space minimizers](../papers/whole-space-fourth-order-cubic-quintic-minimizers) and [Lean minimizer modules](../lean/MathProofs/WholeSpaceMinimizers.lean).*

**Research dossier:** [GC06 · Precise model, known obstructions, and next proof tests](./flagship/GC06.md)

### [**GC36 · Can a knot of wave energy survive?**](./FORMAL_PROBLEMS.md#gc36-stable-knotted-wave-configurations)

Determine whether a nontrivial topological class supports a stable stationary field, or prove an obstruction. A picture of a knot is not itself a stability theorem.

*Research status: proposed model-dependent existence and stability question.*

**Research dossier:** [GC36 · Precise model, known obstructions, and next proof tests](./flagship/GC36.md)

### [**GC11 · Can a wave select its own wavelength?**](./FORMAL_PROBLEMS.md#gc11-nonlinear-finite-wavelength-selection)

Linear dispersion can prefer a finite scale. The harder question is whether nonlinear dynamics select and stabilize one wavelength among competing patterns.

*Related foothold: [exact positive-wave-number minimum](../papers/exact-positive-wavenumber-minimum) and [Lean dispersion analysis](../lean/MathProofs/DispersionMinimum.lean).*

**Research dossier:** [GC11 · Precise model, known obstructions, and next proof tests](./flagship/GC11.md)

### [**GC43 · Can a wave-based rule compute anything?**](./FORMAL_PROBLEMS.md#gc43-discrete-wave-computational-universality)

Specify a finite-alphabet local wave-cell model and ask whether a fixed rule can simulate every Turing machine with polynomial overhead.

*Research status: proposed computational model, not a claim about demonstrated physical hardware.*

**Research dossier:** [GC43 · Precise model, known obstructions, and next proof tests](./flagship/GC43.md)

### [**GC01 · Which waves can survive a disturbance?**](./FORMAL_PROBLEMS.md#gc01-universal-orbital-stability)

Go beyond stable ground-state minimizers and classify standing waves, including excited states, whose phase-and-translation orbits remain stable.

*Relevant foundations: [orbital stability analysis](../papers/orbital-stability-fourth-order-cubic-quintic) and [Lean stability module](../lean/MathProofs/OrbitalStability.lean).*
**Research dossier:** [GC01 · Precise model, known obstructions, and next proof tests](./flagship/GC01.md)


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

## Original 65-question catalogue

**Original problem statements (GC01–GC65).** This section preserves the earlier mathematically scoped catalogue. The expanded [300-problem roadmap](./ROADMAP_300.md) and [folder index](./problems/README.md) include GC66–GC300, whose formulations require further refinement. The plain-language prompts below are guides, not replacements for the formal statements.

**Status key:** All entries remain **candidate research questions** unless specifically documented. **GC08** has a partial negative resolution (the unrestricted uniqueness condition fails). GC51–GC300 are research candidates, and GC66–GC300 are exploratory outlines requiring additional precision. The five featured dossiers include initial literature leads, not exhaustive novelty clearance. [Track all 300 statuses](./STATUS.md) and [see how problems are screened](./METHOD.md).

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


## Fifteen newly proposed foundational directions

**GC51–GC65, added 2026-10-29.** These research candidates extend the original fifty. The questions below lead to full mathematical statements but have **not** passed prior-art clearance or independent novelty review. Some have model choices still to freeze. Every conjecture can be corrected or refuted.

<details open>
<summary><strong>Foundational emergence and scaling</strong> · 5 candidate challenges</summary>

| Problem | The question |
|:--|:--|
| [**GC51 · Soliton resolution and asymptotic completeness**](./FORMAL_PROBLEMS.md#gc51-soliton-resolution-and-asymptotic-completeness) | Does a general finite-energy wave eventually separate into coherent structures and radiation? |
| [**GC52 · Rigorous emergence of effective wave equations**](./FORMAL_PROBLEMS.md#gc52-rigorous-emergence-of-effective-wave-equations) | Can a fourth-order nonlinear envelope equation be derived from an underlying Hamiltonian system? |
| [**GC53 · Universal confinement and stability thresholds**](./FORMAL_PROBLEMS.md#gc53-universal-confinement-and-stability-thresholds) | Can one exact mathematical criterion separate dispersion, localization, and instability? |
| [**GC54 · Nonlinear scattering and threshold resonances**](./FORMAL_PROBLEMS.md#gc54-nonlinear-scattering-and-threshold-resonances) | Which spectral thresholds separate trapped modes from dispersive radiation? |
| [**GC55 · Scaling universality and critical phenomena**](./FORMAL_PROBLEMS.md#gc55-scaling-universality-and-critical-phenomena) | Do different confinement models share the same critical exponents? |

</details>

<details open>
<summary><strong>Extended dynamics and inference</strong> · 5 candidate challenges</summary>

| Problem | The question |
|:--|:--|
| [**GC56 · Global bifurcation of localized states**](./FORMAL_PROBLEMS.md#gc56-global-bifurcation-of-localized-states) | How do branches of confined states appear, fold, and disappear? |
| [**GC57 · Stability under stochastic forcing**](./FORMAL_PROBLEMS.md#gc57-stability-under-stochastic-forcing) | How long can a coherent structure persist when random perturbations never stop? |
| [**GC58 · Multicomponent and vector confinement**](./FORMAL_PROBLEMS.md#gc58-multicomponent-and-vector-confinement) | When do interacting wave components form stable bound states that scalar waves cannot? |
| [**GC59 · Nonlinear observability and control**](./FORMAL_PROBLEMS.md#gc59-nonlinear-observability-and-control) | Can a nonlinear pattern be reconstructed and controlled from measurements on a small region? |
| [**GC60 · Singular limits and multiscale consistency**](./FORMAL_PROBLEMS.md#gc60-singular-limits-and-multiscale-consistency) | How long does a reduced numerical wave model track the original infinite-dimensional system? |

</details>

<details open>
<summary><strong>Information, structure and verification</strong> · 5 candidate challenges</summary>

| Problem | The question |
|:--|:--|
| [**GC61 · Formation and breakdown of coherent structures**](./FORMAL_PROBLEMS.md#gc61-formation-and-breakdown-of-coherent-structures) | Can a localized wave spontaneously emerge from far-from-equilibrium initial data? |
| [**GC62 · Chaotic dynamics and transport barriers**](./FORMAL_PROBLEMS.md#gc62-chaotic-dynamics-and-transport-barriers) | Can nonlinear wave dynamics be chaotic yet suppress long-range energy transport? |
| [**GC63 · Physical information and energy limits of wave computation**](./FORMAL_PROBLEMS.md#gc63-physical-information-and-energy-limits-of-wave-computation) | What are the energy, noise, and reliability costs of computing with physical waves? |
| [**GC64 · Identifiability of competing physical theories**](./FORMAL_PROBLEMS.md#gc64-identifiability-of-competing-physical-theories) | What measurements can definitively distinguish two different wave models? |
| [**GC65 · Verified mathematical model reduction**](./FORMAL_PROBLEMS.md#gc65-verified-mathematical-model-reduction) | Can a finite-dimensional model be proved to represent the dynamics of an infinite-dimensional PDE? |

</details>

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

**Live flagship research discussions:** [GC01 · #54](https://github.com/rickyjreyes/math/issues/54) · [GC06 · #55](https://github.com/rickyjreyes/math/issues/55) · [GC11 · #56](https://github.com/rickyjreyes/math/issues/56) · [GC36 · #57](https://github.com/rickyjreyes/math/issues/57) · [GC43 · #58](https://github.com/rickyjreyes/math/issues/58).

## How this living research repository works

**Capture** ideas in the [candidate notebook](./NOTEBOOK.md). **Screen** them using the [precision and prior-art rubric](./METHOD.md). **Compare** nearby established theorems in the [literature ledger](./LITERATURE.md). **Work** on one of the [five flagship dossiers](#start-here-five-questions-worth-exploring). **Contribute** a proof, counterexample, model correction, or verified Lean theorem through GitHub. **Record** the exact result in the [status register](./STATUS.md), preserving withdrawn and refuted questions.

The registry distinguishes **candidate**, **scoping**, **literature-checked**, **partially resolved**, **resolved**, and **withdrawn** work. This is an evolving mathematical research repository, not a claim that every listed item is a globally recognized open conjecture.

---

## What counts as a solution?

A challenge is **not completed** by an appealing visualization, a successful numerical run, a Lean lemma about a simplified model, or an argument that assumes the main conclusion.

To resolve a mathematical problem:

1. **State it precisely.** Freeze the equation, function space, domain, parameter ranges, quantifiers, and meaning of stability or computation.
2. **Check the literature and attack it.** Identify closest known results, inspect special cases, seek counterexamples, and distinguish genuine gaps from already settled questions.
3. **Prove or refute the claim.** Give a reproducible mathematical argument with explicit hypotheses. A correct counterexample is a valid resolution.
4. **Verify GC completion in Lean.** For a newly claimed GC issue resolution, link the exact Lean theorem or counterexample, a successful full Lean build, and a reviewed correspondence to the issue's frozen acceptance criteria. Preliminary and partial research can be shared without calling the GC resolved.
5. **Document the result.** Record the theorem or counterexample, assumptions, limitations, and relevant numerical or experimental checks in a linked paper or issue.

### Want to work on one?

Pick any **GC01–GC300**, read its [problem file](./ROADMAP_300.md), and [submit a structured research contribution](https://github.com/rickyjreyes/math/issues/new?template=grand_challenge.yml). The [contribution guide](./CONTRIBUTING.md) describes how to document proofs, counterexamples, existing literature, and corrected hypotheses. No prizes or paid services are required. A [versioned JSON register](./problem_registry.json) tracks every entry, and a [standard-library validation script](./scripts/validate_catalog.py) checks catalogue integrity.

**A good challenge is not one that sounds impossible. It is one whose answer changes what we can rigorously say about waves.**

---

*Maintained as a research-question catalogue. Scope and statuses may change as the literature is checked, counterexamples are found, and results are proved.*
