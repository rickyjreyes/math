# Research status | Reyes Problem Repository

**300 research questions · 12 subjects · registry snapshot: November 2, 2026**

**[Browse the 300-question roadmap](ROADMAP_300.md)** · [Formal statements (GC01–GC65)](FORMAL_PROBLEMS.md) · [Existing Lean results](VERIFIED_LEAN_RESULTS.md) · [Contribute](CONTRIBUTING.md)

This page is a **reading view of [problem_registry.json](problem_registry.json)**, not a separate record of scientific completion. It distinguishes entire GC questions from **exact-scope mathematical theorems** that may answer only part of a broader problem. The catalogue is a research program, not a certified inventory of 300 novel unsolved problems.

**Dated correspondence correction, November 2, 2026:** GC08's partial status is retained because its original phase-current operator has an explicit analytical nonuniqueness counterexample. The separate formally proved M6B Laplacian-quotient counterexample is **not** a kernel proof of GC08's exact operator. No original statement or machine status has changed. [Detailed source audit](../docs/NEGATIVE_RESULT_SCOPE_AUDIT_2026-11-02.md).

## At a glance

| Registry outcome | Questions | What it means |
|:--|--:|:--|
| Candidate | **299** | The complete GC question is not accepted as resolved |
| 🟡 Partially resolved | **1: [GC08](#confinement-and-curvature-geometry)** | A scoped curvature-closure nonuniqueness counterexample is established, but classification remains open |
| ✅ Fully resolved | **0** | No GC question is recorded as fully solved |
| Literature screening | **6 initial screens; 294 not reviewed** | Initial screening is not independent novelty or open-status certification |

**Separate mathematical accomplishments:** [20 selected formalized Lean results](VERIFIED_LEAN_RESULTS.md) include ✅ exact-scope theorems and counterexamples. Their completion is **not** equivalent to GC completion. See the [adoption audit](GC65_ADOPTION.md) and [existing-work inventory](EXISTING_WORK.md). There are **zero accepted full-GC completion records** in [completion_records.json](completion_records.json).

**Research review layer:** [All 300 structured GC reviews](formal-reviews/README.md) include source statements, subject-related literature references, falsifiable first milestones and status recommendations. These are *editorial reviews*, not status transitions or 300 certified new open problems.

**Problem formulations:** GC01–GC65 have formal original statements; GC66–GC300 retain their original sketches and have [235 provisional scoped dossiers](scoped/README.md). The later dossiers are still unreviewed candidates. All [difficulty ratings](DIFFICULTY_RUBRIC.md) are low-confidence estimates of research effort, not proof progress.

## Browse by subject

| Research area | Problems | Formal / scoped draft | Partial GC |
|:--|--:|:--|:--|
| [Nonlinear wave dynamics](#nonlinear-wave-dynamics) | 25 | 9 / 16 | — |
| [Confinement and curvature geometry](#confinement-and-curvature-geometry) | 25 | 6 / 19 | 🟡 GC08 |
| [Spectral theory and scattering](#spectral-theory-and-scattering) | 25 | 6 / 19 | — |
| [Variational analysis and solitons](#variational-analysis-and-solitons) | 25 | 6 / 19 | — |
| [Higher-derivative field theory](#higher-derivative-field-theory) | 25 | 5 / 20 | — |
| [Inverse problems, observability and control](#inverse-problems-observability-and-control) | 25 | 7 / 18 | — |
| [Pattern formation and disorder](#pattern-formation-and-disorder) | 25 | 6 / 19 | — |
| [Topology and multicomponent fields](#topology-and-multicomponent-fields) | 25 | 6 / 19 | — |
| [Computability and complexity](#computability-and-complexity) | 25 | 5 / 20 | — |
| [Lean formalization and certified analysis](#lean-formalization-and-certified-analysis) | 25 | 6 / 19 | — |
| [Physical emergence and multiscale limits](#physical-emergence-and-multiscale-limits) | 25 | 2 / 23 | — |
| [Photonic computation and physical information](#photonic-computation-and-physical-information) | 25 | 1 / 24 | — |

### How to read the status tables

- **Candidate · formal** means an original GC01–GC65 research question; **Candidate · scoped draft** means a GC66–GC300 question with a proposed scope-v1 dossier. Both have registry status `candidate`.
- **🟡 Partial** is the single machine-recorded partial resolution. **✅ Evidence** denotes an existing theorem or counterexample for the *stated narrower model*, not a change to the GC status.
- **Initial review** identifies the six entries with a preliminary literature screen. All other entries have `not_reviewed` in the registry.
- The **Difficulty** column reproduces the [roadmap's provisional 1–10 estimates](ROADMAP_300.md). A difficulty rating is not an independent measure of importance, novelty, or completion.

## Status by research subject

## Nonlinear wave dynamics

[Subject overview](problems/01-wave-dynamics/README.md) · [Full roadmap and difficulty notes](ROADMAP_300.md#nonlinear-wave-dynamics)

| ID | Mathematical question | GC stage | Existing mathematical evidence | Difficulty |
|:--|:--|:--|:--|--:|
| GC01 | [Universal orbital stability](FORMAL_PROBLEMS.md#gc01-universal-orbital-stability) · [Dossier](./flagship/GC01.md) · [Issue #54](https://github.com/rickyjreyes/math/issues/54) | Candidate · formal · initial review | ✅ Minimizer-set orbital stability, narrower scope | 9/10 |
| GC02 | [Long-time asymptotic stability](FORMAL_PROBLEMS.md#gc02-long-time-asymptotic-stability) | Candidate · formal | Related source links; scope unaudited | 9/10 |
| GC03 | [Global existence versus blow-up](FORMAL_PROBLEMS.md#gc03-global-existence-versus-blow-up) | Candidate · formal | ✅ Global H² flow for one equation | 8/10 |
| GC04 | [Stable multi-wave interactions](FORMAL_PROBLEMS.md#gc04-stable-multi-wave-interactions) | Candidate · formal | No existing proof mapped | 8/10 |
| GC05 | [Breather existence and classification](FORMAL_PROBLEMS.md#gc05-breather-existence-and-classification) | Candidate · formal | No existing proof mapped | 9/10 |
| GC51 | [Soliton resolution and asymptotic completeness](FORMAL_PROBLEMS.md#gc51-soliton-resolution-and-asymptotic-completeness) | Candidate · formal | Related source links; scope unaudited | 9/10 |
| GC56 | [Global bifurcation of localized states](FORMAL_PROBLEMS.md#gc56-global-bifurcation-of-localized-states) | Candidate · formal | Related source links; scope unaudited | 8/10 |
| GC61 | [Formation and breakdown of coherent structures](FORMAL_PROBLEMS.md#gc61-formation-and-breakdown-of-coherent-structures) | Candidate · formal | Related source links; scope unaudited | 8/10 |
| GC62 | [Chaotic dynamics and transport barriers](FORMAL_PROBLEMS.md#gc62-chaotic-dynamics-and-transport-barriers) | Candidate · formal | No existing proof mapped | 8/10 |
| GC66 | [Internal-mode radiation damping](problems/01-wave-dynamics/GC66.md) · [Scope v1](scoped/GC66.md) | Candidate · scoped draft | Not yet reviewed | 10/10 |
| GC67 | [Traveling-wave velocity bounds](problems/01-wave-dynamics/GC67.md) · [Scope v1](scoped/GC67.md) | Candidate · scoped draft | Not yet reviewed | 8/10 |
| GC68 | [Two-soliton collision outcomes](problems/01-wave-dynamics/GC68.md) · [Scope v1](scoped/GC68.md) | Candidate · scoped draft | Not yet reviewed | 8/10 |
| GC69 | [Excited-state spectral instability index](problems/01-wave-dynamics/GC69.md) · [Scope v1](scoped/GC69.md) | Candidate · scoped draft | Not yet reviewed | 8/10 |
| GC70 | [Nonradial solitary-wave families](problems/01-wave-dynamics/GC70.md) · [Scope v1](scoped/GC70.md) | Candidate · scoped draft | Not yet reviewed | 8/10 |
| GC71 | [Fission thresholds for coherent packets](problems/01-wave-dynamics/GC71.md) · [Scope v1](scoped/GC71.md) | Candidate · scoped draft | Not yet reviewed | 9/10 |
| GC72 | [Nonlinear radiation tail asymptotics](problems/01-wave-dynamics/GC72.md) · [Scope v1](scoped/GC72.md) | Candidate · scoped draft | Not yet reviewed | 8/10 |
| GC73 | [Quasiperiodic localized dynamics](problems/01-wave-dynamics/GC73.md) · [Scope v1](scoped/GC73.md) | Candidate · scoped draft | Not yet reviewed | 10/10 |
| GC74 | [Wavepacket capture versus passage](problems/01-wave-dynamics/GC74.md) · [Scope v1](scoped/GC74.md) | Candidate · scoped draft | Not yet reviewed | 8/10 |
| GC75 | [Phase-dependent interaction forces](problems/01-wave-dynamics/GC75.md) · [Scope v1](scoped/GC75.md) | Candidate · scoped draft | Not yet reviewed | 8/10 |
| GC76 | [Dynamics near an embedded internal eigenvalue](problems/01-wave-dynamics/GC76.md) · [Scope v1](scoped/GC76.md) | Candidate · scoped draft | Not yet reviewed | 8/10 |
| GC77 | [Orbital instability growth rates](problems/01-wave-dynamics/GC77.md) · [Scope v1](scoped/GC77.md) | Candidate · scoped draft | Not yet reviewed | 8/10 |
| GC78 | [High-frequency wave cascade obstruction](problems/01-wave-dynamics/GC78.md) · [Scope v1](scoped/GC78.md) | Candidate · scoped draft | Not yet reviewed | 8/10 |
| GC79 | [Long-time interaction of three solitons](problems/01-wave-dynamics/GC79.md) · [Scope v1](scoped/GC79.md) | Candidate · scoped draft | Not yet reviewed | 9/10 |
| GC80 | [Breather persistence under model perturbations](problems/01-wave-dynamics/GC80.md) · [Scope v1](scoped/GC80.md) | Candidate · scoped draft | Not yet reviewed | 8/10 |
| GC81 | [Uniform stability near a bifurcation endpoint](problems/01-wave-dynamics/GC81.md) · [Scope v1](scoped/GC81.md) | Candidate · scoped draft | Not yet reviewed | 9/10 |

## Confinement and curvature geometry

[Subject overview](problems/02-confinement-curvature/README.md) · [Full roadmap and difficulty notes](ROADMAP_300.md#confinement-and-curvature-geometry)

| ID | Mathematical question | GC stage | Existing mathematical evidence | Difficulty |
|:--|:--|:--|:--|--:|
| GC06 | [Self-confinement criteria](FORMAL_PROBLEMS.md#gc06-self-confinement-criteria) · [Dossier](./flagship/GC06.md) · [Issue #55](https://github.com/rickyjreyes/math/issues/55) | Candidate · formal · initial review | ✅ Minimizers and strict binding on a mass range | 9/10 |
| GC07 | [Curvature-induced localization](FORMAL_PROBLEMS.md#gc07-curvature-induced-localization) | Candidate · formal | No existing proof mapped | 7/10 |
| GC08 | [Admissible curvature closures](FORMAL_PROBLEMS.md#gc08-admissible-curvature-closures) | 🟡 Partial · initial review | Analytical [GC08 phase-current counterexample](problems/02-confinement-curvature/GC08.md); [M6B Lean](../lean/MathProofs/M6BClosureTheorem.lean) is a different operator; classification open | 7/10 |
| GC09 | [Topological confinement protection](FORMAL_PROBLEMS.md#gc09-topological-confinement-protection) | Candidate · formal | No existing proof mapped | 8/10 |
| GC10 | [Dimensional localized-energy classification](FORMAL_PROBLEMS.md#gc10-dimensional-localized-energy-classification) | Candidate · formal | No existing proof mapped | 8/10 |
| GC53 | [Universal confinement and stability thresholds](FORMAL_PROBLEMS.md#gc53-universal-confinement-and-stability-thresholds) | Candidate · formal | Related source links; scope unaudited | 10/10 |
| GC82 | [Curvature energy coercivity](problems/02-confinement-curvature/GC82.md) · [Scope v1](scoped/GC82.md) | Candidate · scoped draft | Not yet reviewed | 8/10 |
| GC83 | [Zero-amplitude phase defects](problems/02-confinement-curvature/GC83.md) · [Scope v1](scoped/GC83.md) | Candidate · scoped draft | Not yet reviewed | 8/10 |
| GC84 | [Vanishing-regularizer curvature limits](problems/02-confinement-curvature/GC84.md) · [Scope v1](scoped/GC84.md) | Candidate · scoped draft | Not yet reviewed | 8/10 |
| GC85 | [Curvature and confinement on curved surfaces](problems/02-confinement-curvature/GC85.md) · [Scope v1](scoped/GC85.md) | Candidate · scoped draft | Not yet reviewed | 8/10 |
| GC86 | [Anisotropic confinement thresholds](problems/02-confinement-curvature/GC86.md) · [Scope v1](scoped/GC86.md) | Candidate · scoped draft | Not yet reviewed | 9/10 |
| GC87 | [Curvature-induced spectral traps](problems/02-confinement-curvature/GC87.md) · [Scope v1](scoped/GC87.md) | Candidate · scoped draft | Not yet reviewed | 8/10 |
| GC88 | [Localization under metric perturbations](problems/02-confinement-curvature/GC88.md) · [Scope v1](scoped/GC88.md) | Candidate · scoped draft | Not yet reviewed | 7/10 |
| GC89 | [Sharp curvature gradient inequality](problems/02-confinement-curvature/GC89.md) · [Scope v1](scoped/GC89.md) | Candidate · scoped draft | Not yet reviewed | 8/10 |
| GC90 | [Quantitative confinement length scales](problems/02-confinement-curvature/GC90.md) · [Scope v1](scoped/GC90.md) | Candidate · scoped draft | Not yet reviewed | 8/10 |
| GC91 | [Domain geometry and edge confinement](problems/02-confinement-curvature/GC91.md) · [Scope v1](scoped/GC91.md) | Candidate · scoped draft | Not yet reviewed | 8/10 |
| GC92 | [Curvature closure selection by locality](problems/02-confinement-curvature/GC92.md) · [Scope v1](scoped/GC92.md) | Candidate · scoped draft | Not yet reviewed | 7/10 |
| GC93 | [Optimal confinement with fixed curvature budget](problems/02-confinement-curvature/GC93.md) · [Scope v1](scoped/GC93.md) | Candidate · scoped draft | Not yet reviewed | 9/10 |
| GC94 | [Geometric confinement under weak disorder](problems/02-confinement-curvature/GC94.md) · [Scope v1](scoped/GC94.md) | Candidate · scoped draft | Not yet reviewed | 8/10 |
| GC95 | [Regularized curvature and Sobolev continuity](problems/02-confinement-curvature/GC95.md) · [Scope v1](scoped/GC95.md) | Candidate · scoped draft | Not yet reviewed | 8/10 |
| GC96 | [Multiple curvature wells and tunneling](problems/02-confinement-curvature/GC96.md) · [Scope v1](scoped/GC96.md) | Candidate · scoped draft | Not yet reviewed | 8/10 |
| GC97 | [Vortex core energy lower bounds](problems/02-confinement-curvature/GC97.md) · [Scope v1](scoped/GC97.md) | Candidate · scoped draft | Not yet reviewed | 9/10 |
| GC98 | [Local curvature data versus global confinement](problems/02-confinement-curvature/GC98.md) · [Scope v1](scoped/GC98.md) | Candidate · scoped draft | Not yet reviewed | 7/10 |
| GC99 | [Dimensional threshold under constrained curvature](problems/02-confinement-curvature/GC99.md) · [Scope v1](scoped/GC99.md) | Candidate · scoped draft | Not yet reviewed | 9/10 |
| GC100 | [Long-range geometric defects](problems/02-confinement-curvature/GC100.md) · [Scope v1](scoped/GC100.md) | Candidate · scoped draft | Not yet reviewed | 8/10 |

## Spectral theory and scattering

[Subject overview](problems/03-spectral-scattering/README.md) · [Full roadmap and difficulty notes](ROADMAP_300.md#spectral-theory-and-scattering)

| ID | Mathematical question | GC stage | Existing mathematical evidence | Difficulty |
|:--|:--|:--|:--|--:|
| GC11 | [Nonlinear finite-wavelength selection](FORMAL_PROBLEMS.md#gc11-nonlinear-finite-wavelength-selection) · [Dossier](./flagship/GC11.md) · [Issue #56](https://github.com/rickyjreyes/math/issues/56) | Candidate · formal · initial review | Related source links; scope unaudited | 7/10 |
| GC12 | [Nonlinear spectral-gap persistence](FORMAL_PROBLEMS.md#gc12-nonlinear-spectral-gap-persistence) | Candidate · formal | Related source links; scope unaudited | 8/10 |
| GC13 | [Interband nonlinear energy transfer](FORMAL_PROBLEMS.md#gc13-interband-nonlinear-energy-transfer) | Candidate · formal | Related source links; scope unaudited | 8/10 |
| GC14 | [Spectral concentration versus localization](FORMAL_PROBLEMS.md#gc14-spectral-concentration-versus-localization) | Candidate · formal | Related source links; scope unaudited | 7/10 |
| GC15 | [Finite-mode invariant manifolds](FORMAL_PROBLEMS.md#gc15-finite-mode-invariant-manifolds) | Candidate · formal | Related source links; scope unaudited | 7/10 |
| GC54 | [Nonlinear scattering and threshold resonances](FORMAL_PROBLEMS.md#gc54-nonlinear-scattering-and-threshold-resonances) | Candidate · formal | Related source links; scope unaudited | 9/10 |
| GC101 | [Threshold resonance multiplicity](problems/03-spectral-scattering/GC101.md) · [Scope v1](scoped/GC101.md) | Candidate · scoped draft | Not yet reviewed | 9/10 |
| GC102 | [Embedded eigenvalues in fourth-order media](problems/03-spectral-scattering/GC102.md) · [Scope v1](scoped/GC102.md) | Candidate · scoped draft | Not yet reviewed | 8/10 |
| GC103 | [Sharp resolvent bounds near band minima](problems/03-spectral-scattering/GC103.md) · [Scope v1](scoped/GC103.md) | Candidate · scoped draft | Not yet reviewed | 9/10 |
| GC104 | [Spectral stability of perturbed periodic stripes](problems/03-spectral-scattering/GC104.md) · [Scope v1](scoped/GC104.md) | Candidate · scoped draft | Not yet reviewed | 8/10 |
| GC105 | [Nonlinear Fermi golden rule at a band edge](problems/03-spectral-scattering/GC105.md) · [Scope v1](scoped/GC105.md) | Candidate · scoped draft | Not yet reviewed | 10/10 |
| GC106 | [Localization near quasi-periodic coefficients](problems/03-spectral-scattering/GC106.md) · [Scope v1](scoped/GC106.md) | Candidate · scoped draft | Not yet reviewed | 7/10 |
| GC107 | [Spectral flow under curvature coupling](problems/03-spectral-scattering/GC107.md) · [Scope v1](scoped/GC107.md) | Candidate · scoped draft | Not yet reviewed | 8/10 |
| GC108 | [Band-gap solitons for finite-amplitude lattices](problems/03-spectral-scattering/GC108.md) · [Scope v1](scoped/GC108.md) | Candidate · scoped draft | Not yet reviewed | 7/10 |
| GC109 | [Energy transfer across sparse Fourier shells](problems/03-spectral-scattering/GC109.md) · [Scope v1](scoped/GC109.md) | Candidate · scoped draft | Not yet reviewed | 8/10 |
| GC110 | [Inverse resonance reconstruction](problems/03-spectral-scattering/GC110.md) · [Scope v1](scoped/GC110.md) | Candidate · scoped draft | Not yet reviewed | 8/10 |
| GC111 | [Spectral measures of localized wave defects](problems/03-spectral-scattering/GC111.md) · [Scope v1](scoped/GC111.md) | Candidate · scoped draft | Not yet reviewed | 7/10 |
| GC112 | [Pseudospectral growth in nonnormal wave linearizations](problems/03-spectral-scattering/GC112.md) · [Scope v1](scoped/GC112.md) | Candidate · scoped draft | Not yet reviewed | 8/10 |
| GC113 | [High-frequency resolvent smoothing](problems/03-spectral-scattering/GC113.md) · [Scope v1](scoped/GC113.md) | Candidate · scoped draft | Not yet reviewed | 8/10 |
| GC114 | [Nonlinear harmonic generation thresholds](problems/03-spectral-scattering/GC114.md) · [Scope v1](scoped/GC114.md) | Candidate · scoped draft | Not yet reviewed | 9/10 |
| GC115 | [Anisotropic shell degeneracy](problems/03-spectral-scattering/GC115.md) · [Scope v1](scoped/GC115.md) | Candidate · scoped draft | Not yet reviewed | 8/10 |
| GC116 | [Scattering by topological wave defects](problems/03-spectral-scattering/GC116.md) · [Scope v1](scoped/GC116.md) | Candidate · scoped draft | Not yet reviewed | 8/10 |
| GC117 | [Spectral pollution under Galerkin truncation](problems/03-spectral-scattering/GC117.md) · [Scope v1](scoped/GC117.md) | Candidate · scoped draft | Not yet reviewed | 8/10 |
| GC118 | [Resonant mode counting under confinement](problems/03-spectral-scattering/GC118.md) · [Scope v1](scoped/GC118.md) | Candidate · scoped draft | Not yet reviewed | 8/10 |
| GC119 | [Nonlinear persistence of embedded solitary modes](problems/03-spectral-scattering/GC119.md) · [Scope v1](scoped/GC119.md) | Candidate · scoped draft | Not yet reviewed | 8/10 |

## Variational analysis and solitons

[Subject overview](problems/04-variational-solitons/README.md) · [Full roadmap and difficulty notes](ROADMAP_300.md#variational-analysis-and-solitons)

| ID | Mathematical question | GC stage | Existing mathematical evidence | Difficulty |
|:--|:--|:--|:--|--:|
| GC16 | [Strict binding across masses](FORMAL_PROBLEMS.md#gc16-strict-binding-across-masses) | Candidate · formal | ✅ Strict binding on a mass range | 8/10 |
| GC17 | [Constrained-minimizer uniqueness](FORMAL_PROBLEMS.md#gc17-constrained-minimizer-uniqueness) | Candidate · formal | Related source links; scope unaudited | 8/10 |
| GC18 | [Symmetry-breaking thresholds](FORMAL_PROBLEMS.md#gc18-symmetry-breaking-thresholds) | Candidate · formal | Related source links; scope unaudited | 9/10 |
| GC19 | [Critical compactness failures](FORMAL_PROBLEMS.md#gc19-critical-compactness-failures) | Candidate · formal | Related source links; scope unaudited | 8/10 |
| GC20 | [Metastable energy landscapes](FORMAL_PROBLEMS.md#gc20-metastable-energy-landscapes) | Candidate · formal | Related source links; scope unaudited | 8/10 |
| GC55 | [Scaling universality and critical phenomena](FORMAL_PROBLEMS.md#gc55-scaling-universality-and-critical-phenomena) | Candidate · formal | Related source links; scope unaudited | 9/10 |
| GC120 | [Sharp mass-energy inequality](problems/04-variational-solitons/GC120.md) · [Scope v1](scoped/GC120.md) | Candidate · scoped draft | Not yet reviewed | 9/10 |
| GC121 | [Ground-state nondegeneracy](problems/04-variational-solitons/GC121.md) · [Scope v1](scoped/GC121.md) | Candidate · scoped draft | Not yet reviewed | 8/10 |
| GC122 | [Binding at the critical mass](problems/04-variational-solitons/GC122.md) · [Scope v1](scoped/GC122.md) | Candidate · scoped draft | Not yet reviewed | 8/10 |
| GC123 | [Orbital stability from quantitative coercivity](problems/04-variational-solitons/GC123.md) · [Scope v1](scoped/GC123.md) | Candidate · scoped draft | Not yet reviewed | 8/10 |
| GC124 | [Competing radial and stripe minimizers](problems/04-variational-solitons/GC124.md) · [Scope v1](scoped/GC124.md) | Candidate · scoped draft | Not yet reviewed | 8/10 |
| GC125 | [Mass partition in vector solitons](problems/04-variational-solitons/GC125.md) · [Scope v1](scoped/GC125.md) | Candidate · scoped draft | Not yet reviewed | 8/10 |
| GC126 | [Concentration-compactness without radial symmetry](problems/04-variational-solitons/GC126.md) · [Scope v1](scoped/GC126.md) | Candidate · scoped draft | Not yet reviewed | 8/10 |
| GC127 | [Barycentric pinning of minimizers](problems/04-variational-solitons/GC127.md) · [Scope v1](scoped/GC127.md) | Candidate · scoped draft | Not yet reviewed | 8/10 |
| GC128 | [Sharp strict-subadditivity transition](problems/04-variational-solitons/GC128.md) · [Scope v1](scoped/GC128.md) | Candidate · scoped draft | Not yet reviewed | 9/10 |
| GC129 | [Soliton branch turning-point stability](problems/04-variational-solitons/GC129.md) · [Scope v1](scoped/GC129.md) | Candidate · scoped draft | Not yet reviewed | 8/10 |
| GC130 | [Constrained minimizers with angular momentum](problems/04-variational-solitons/GC130.md) · [Scope v1](scoped/GC130.md) | Candidate · scoped draft | Not yet reviewed | 8/10 |
| GC131 | [Energy landscape Morse index](problems/04-variational-solitons/GC131.md) · [Scope v1](scoped/GC131.md) | Candidate · scoped draft | Not yet reviewed | 8/10 |
| GC132 | [Mountain-pass localized states](problems/04-variational-solitons/GC132.md) · [Scope v1](scoped/GC132.md) | Candidate · scoped draft | Not yet reviewed | 7/10 |
| GC133 | [Uniform minimizer bounds near zero dispersion](problems/04-variational-solitons/GC133.md) · [Scope v1](scoped/GC133.md) | Candidate · scoped draft | Not yet reviewed | 9/10 |
| GC134 | [Large-mass saturation profiles](problems/04-variational-solitons/GC134.md) · [Scope v1](scoped/GC134.md) | Candidate · scoped draft | Not yet reviewed | 8/10 |
| GC135 | [Variational gap under weak external fields](problems/04-variational-solitons/GC135.md) · [Scope v1](scoped/GC135.md) | Candidate · scoped draft | Not yet reviewed | 8/10 |
| GC136 | [Multiplicity of symmetry-related local minima](problems/04-variational-solitons/GC136.md) · [Scope v1](scoped/GC136.md) | Candidate · scoped draft | Not yet reviewed | 7/10 |
| GC137 | [Energy quantization in concentrating sequences](problems/04-variational-solitons/GC137.md) · [Scope v1](scoped/GC137.md) | Candidate · scoped draft | Not yet reviewed | 8/10 |
| GC138 | [Dynamical stability of constrained excited minima](problems/04-variational-solitons/GC138.md) · [Scope v1](scoped/GC138.md) | Candidate · scoped draft | Not yet reviewed | 8/10 |

## Higher-derivative field theory

[Subject overview](problems/05-higher-derivative-fields/README.md) · [Full roadmap and difficulty notes](ROADMAP_300.md#higher-derivative-field-theory)

| ID | Mathematical question | GC stage | Existing mathematical evidence | Difficulty |
|:--|:--|:--|:--|--:|
| GC21 | [Ghost-free higher-derivative dynamics](FORMAL_PROBLEMS.md#gc21-ghost-free-higher-derivative-dynamics) | Candidate · formal | Related source links; scope unaudited | 10/10 |
| GC22 | [UV well-posedness classification](FORMAL_PROBLEMS.md#gc22-uv-well-posedness-classification) | Candidate · formal | Related source links; scope unaudited | 10/10 |
| GC23 | [Physically stable wavelength selection](FORMAL_PROBLEMS.md#gc23-physically-stable-wavelength-selection) | Candidate · formal | Related source links; scope unaudited | 9/10 |
| GC24 | [Hamiltonian constraint classification](FORMAL_PROBLEMS.md#gc24-hamiltonian-constraint-classification) | Candidate · formal | Related source links; scope unaudited | 10/10 |
| GC25 | [Consistent parent theories](FORMAL_PROBLEMS.md#gc25-consistent-parent-theories) | Candidate · formal | Related source links; scope unaudited | 9/10 |
| GC139 | [Degenerate higher-time-derivative Hamiltonians](problems/05-higher-derivative-fields/GC139.md) · [Scope v1](scoped/GC139.md) | Candidate · scoped draft | Not yet reviewed | 9/10 |
| GC140 | [Constraint preservation under nonlinear evolution](problems/05-higher-derivative-fields/GC140.md) · [Scope v1](scoped/GC140.md) | Candidate · scoped draft | Not yet reviewed | 9/10 |
| GC141 | [Finite-wavelength stability with Lorentz breaking](problems/05-higher-derivative-fields/GC141.md) · [Scope v1](scoped/GC141.md) | Candidate · scoped draft | Not yet reviewed | 8/10 |
| GC142 | [Ghost elimination by auxiliary fields](problems/05-higher-derivative-fields/GC142.md) · [Scope v1](scoped/GC142.md) | Candidate · scoped draft | Not yet reviewed | 9/10 |
| GC143 | [Causal propagation in dispersive field theories](problems/05-higher-derivative-fields/GC143.md) · [Scope v1](scoped/GC143.md) | Candidate · scoped draft | Not yet reviewed | 9/10 |
| GC144 | [Hyperbolicity under parameter continuation](problems/05-higher-derivative-fields/GC144.md) · [Scope v1](scoped/GC144.md) | Candidate · scoped draft | Not yet reviewed | 9/10 |
| GC145 | [Higher-derivative effective field theory cutoff](problems/05-higher-derivative-fields/GC145.md) · [Scope v1](scoped/GC145.md) | Candidate · scoped draft | Not yet reviewed | 9/10 |
| GC146 | [Energy positivity for coupled scalar fields](problems/05-higher-derivative-fields/GC146.md) · [Scope v1](scoped/GC146.md) | Candidate · scoped draft | Not yet reviewed | 9/10 |
| GC147 | [Derivative nonlinearities and local well-posedness](problems/05-higher-derivative-fields/GC147.md) · [Scope v1](scoped/GC147.md) | Candidate · scoped draft | Not yet reviewed | 8/10 |
| GC148 | [Gauge compatibility of phase curvature interactions](problems/05-higher-derivative-fields/GC148.md) · [Scope v1](scoped/GC148.md) | Candidate · scoped draft | Not yet reviewed | 9/10 |
| GC149 | [Hamiltonian reduction near a spectral degeneracy](problems/05-higher-derivative-fields/GC149.md) · [Scope v1](scoped/GC149.md) | Candidate · scoped draft | Not yet reviewed | 9/10 |
| GC150 | [Boundary conditions for fourth-order field energy](problems/05-higher-derivative-fields/GC150.md) · [Scope v1](scoped/GC150.md) | Candidate · scoped draft | Not yet reviewed | 9/10 |
| GC151 | [Nonlocal parent actions and stable effective dispersion](problems/05-higher-derivative-fields/GC151.md) · [Scope v1](scoped/GC151.md) | Candidate · scoped draft | Not yet reviewed | 8/10 |
| GC152 | [Spectral factorization of stable field symbols](problems/05-higher-derivative-fields/GC152.md) · [Scope v1](scoped/GC152.md) | Candidate · scoped draft | Not yet reviewed | 9/10 |
| GC153 | [Vacuum stability under higher-gradient interactions](problems/05-higher-derivative-fields/GC153.md) · [Scope v1](scoped/GC153.md) | Candidate · scoped draft | Not yet reviewed | 9/10 |
| GC154 | [Higher-order Noether currents](problems/05-higher-derivative-fields/GC154.md) · [Scope v1](scoped/GC154.md) | Candidate · scoped draft | Not yet reviewed | 9/10 |
| GC155 | [Quasilinear fourth-order continuation criteria](problems/05-higher-derivative-fields/GC155.md) · [Scope v1](scoped/GC155.md) | Candidate · scoped draft | Not yet reviewed | 9/10 |
| GC156 | [Constrained Hamiltonian numerical integrators](problems/05-higher-derivative-fields/GC156.md) · [Scope v1](scoped/GC156.md) | Candidate · scoped draft | Not yet reviewed | 8/10 |
| GC157 | [Coupled dispersion crossing and mode conversion](problems/05-higher-derivative-fields/GC157.md) · [Scope v1](scoped/GC157.md) | Candidate · scoped draft | Not yet reviewed | 9/10 |
| GC158 | [Physical observables after field redefinitions](problems/05-higher-derivative-fields/GC158.md) · [Scope v1](scoped/GC158.md) | Candidate · scoped draft | Not yet reviewed | 9/10 |

## Inverse problems, observability and control

[Subject overview](problems/06-inverse-observation-control/README.md) · [Full roadmap and difficulty notes](ROADMAP_300.md#inverse-problems-observability-and-control)

| ID | Mathematical question | GC stage | Existing mathematical evidence | Difficulty |
|:--|:--|:--|:--|--:|
| GC26 | [Local versus global identifiability](FORMAL_PROBLEMS.md#gc26-local-versus-global-identifiability) | Candidate · formal | ✅ Rank 11, nullity 20 and local fiber | 6/10 |
| GC27 | [Minimal parameter-recovery observations](FORMAL_PROBLEMS.md#gc27-minimal-parameter-recovery-observations) | Candidate · formal | Related source links; scope unaudited | 7/10 |
| GC28 | [Curvature-map noninjectivity](FORMAL_PROBLEMS.md#gc28-curvature-map-noninjectivity) | Candidate · formal | Related source links; scope unaudited | 7/10 |
| GC29 | [Noise-stable reconstruction](FORMAL_PROBLEMS.md#gc29-noise-stable-reconstruction) | Candidate · formal | Related source links; scope unaudited | 7/10 |
| GC30 | [Partial-data spectral uniqueness](FORMAL_PROBLEMS.md#gc30-partial-data-spectral-uniqueness) | Candidate · formal | No existing proof mapped | 7/10 |
| GC59 | [Nonlinear observability and control](FORMAL_PROBLEMS.md#gc59-nonlinear-observability-and-control) | Candidate · formal | No existing proof mapped | 7/10 |
| GC64 | [Identifiability of competing physical theories](FORMAL_PROBLEMS.md#gc64-identifiability-of-competing-physical-theories) | Candidate · formal | Related source links; scope unaudited | 7/10 |
| GC159 | [Minimal sensor geometry for wave identification](problems/06-inverse-observation-control/GC159.md) · [Scope v1](scoped/GC159.md) | Candidate · scoped draft | Not yet reviewed | 7/10 |
| GC160 | [Global aliasing in clipped spectral measurements](problems/06-inverse-observation-control/GC160.md) · [Scope v1](scoped/GC160.md) | Candidate · scoped draft | Not yet reviewed | 7/10 |
| GC161 | [Robust identifiability under sensor dropout](problems/06-inverse-observation-control/GC161.md) · [Scope v1](scoped/GC161.md) | Candidate · scoped draft | Not yet reviewed | 7/10 |
| GC162 | [Optimal experiment design for competing dispersion laws](problems/06-inverse-observation-control/GC162.md) · [Scope v1](scoped/GC162.md) | Candidate · scoped draft | Not yet reviewed | 8/10 |
| GC163 | [Boundary observation for fourth-order operators](problems/06-inverse-observation-control/GC163.md) · [Scope v1](scoped/GC163.md) | Candidate · scoped draft | Not yet reviewed | 7/10 |
| GC164 | [Inverse recovery of nonlinear coupling strength](problems/06-inverse-observation-control/GC164.md) · [Scope v1](scoped/GC164.md) | Candidate · scoped draft | Not yet reviewed | 7/10 |
| GC165 | [Local uniqueness versus parameter clipping](problems/06-inverse-observation-control/GC165.md) · [Scope v1](scoped/GC165.md) | Candidate · scoped draft | Not yet reviewed | 6/10 |
| GC166 | [Noise amplification near nonidentifiable sets](problems/06-inverse-observation-control/GC166.md) · [Scope v1](scoped/GC166.md) | Candidate · scoped draft | Not yet reviewed | 7/10 |
| GC167 | [Reconstruction from sparse wave interferograms](problems/06-inverse-observation-control/GC167.md) · [Scope v1](scoped/GC167.md) | Candidate · scoped draft | Not yet reviewed | 7/10 |
| GC168 | [Boundary potential recovery with eigenfunction traces](problems/06-inverse-observation-control/GC168.md) · [Scope v1](scoped/GC168.md) | Candidate · scoped draft | Not yet reviewed | 7/10 |
| GC169 | [Stable recovery of curvature regularization](problems/06-inverse-observation-control/GC169.md) · [Scope v1](scoped/GC169.md) | Candidate · scoped draft | Not yet reviewed | 7/10 |
| GC170 | [Control of a localized solitary wave position](problems/06-inverse-observation-control/GC170.md) · [Scope v1](scoped/GC170.md) | Candidate · scoped draft | Not yet reviewed | 6/10 |
| GC171 | [Minimum control energy for pattern stabilization](problems/06-inverse-observation-control/GC171.md) · [Scope v1](scoped/GC171.md) | Candidate · scoped draft | Not yet reviewed | 7/10 |
| GC172 | [Observer design for nonlinear wave modes](problems/06-inverse-observation-control/GC172.md) · [Scope v1](scoped/GC172.md) | Candidate · scoped draft | Not yet reviewed | 7/10 |
| GC173 | [Distinguishing noise from model discrepancy](problems/06-inverse-observation-control/GC173.md) · [Scope v1](scoped/GC173.md) | Candidate · scoped draft | Not yet reviewed | 7/10 |
| GC174 | [Adaptive sensing of solitary-wave bifurcations](problems/06-inverse-observation-control/GC174.md) · [Scope v1](scoped/GC174.md) | Candidate · scoped draft | Not yet reviewed | 7/10 |
| GC175 | [Inverse recovery from scattering phase shifts](problems/06-inverse-observation-control/GC175.md) · [Scope v1](scoped/GC175.md) | Candidate · scoped draft | Not yet reviewed | 7/10 |
| GC176 | [Confidence-certified physical parameter bounds](problems/06-inverse-observation-control/GC176.md) · [Scope v1](scoped/GC176.md) | Candidate · scoped draft | Not yet reviewed | 6/10 |

## Pattern formation and disorder

[Subject overview](problems/07-pattern-formation/README.md) · [Full roadmap and difficulty notes](ROADMAP_300.md#pattern-formation-and-disorder)

| ID | Mathematical question | GC stage | Existing mathematical evidence | Difficulty |
|:--|:--|:--|:--|--:|
| GC31 | [Nonlinear Swift–Hohenberg attractors](FORMAL_PROBLEMS.md#gc31-nonlinear-swifthohenberg-attractors) | Candidate · formal | Related source links; scope unaudited | 8/10 |
| GC32 | [Coarsening versus wavelength locking](FORMAL_PROBLEMS.md#gc32-coarsening-versus-wavelength-locking) | Candidate · formal | Related source links; scope unaudited | 8/10 |
| GC33 | [Pattern robustness under disorder](FORMAL_PROBLEMS.md#gc33-pattern-robustness-under-disorder) | Candidate · formal | Related source links; scope unaudited | 8/10 |
| GC34 | [Defect nucleation and annihilation](FORMAL_PROBLEMS.md#gc34-defect-nucleation-and-annihilation) | Candidate · formal | No existing proof mapped | 8/10 |
| GC35 | [Infinite-domain pattern selection](FORMAL_PROBLEMS.md#gc35-infinite-domain-pattern-selection) | Candidate · formal | Related source links; scope unaudited | 9/10 |
| GC57 | [Stability under stochastic forcing](FORMAL_PROBLEMS.md#gc57-stability-under-stochastic-forcing) | Candidate · formal | Related source links; scope unaudited | 8/10 |
| GC177 | [Stripe stability boundaries in two dimensions](problems/07-pattern-formation/GC177.md) · [Scope v1](scoped/GC177.md) | Candidate · scoped draft | Not yet reviewed | 8/10 |
| GC178 | [Hexagon versus stripe selection](problems/07-pattern-formation/GC178.md) · [Scope v1](scoped/GC178.md) | Candidate · scoped draft | Not yet reviewed | 8/10 |
| GC179 | [Pattern pinning by weak heterogeneity](problems/07-pattern-formation/GC179.md) · [Scope v1](scoped/GC179.md) | Candidate · scoped draft | Not yet reviewed | 8/10 |
| GC180 | [Defect mobility laws](problems/07-pattern-formation/GC180.md) · [Scope v1](scoped/GC180.md) | Candidate · scoped draft | Not yet reviewed | 8/10 |
| GC181 | [Disorder-induced wavelength shift](problems/07-pattern-formation/GC181.md) · [Scope v1](scoped/GC181.md) | Candidate · scoped draft | Not yet reviewed | 8/10 |
| GC182 | [Coarsening exponent classification](problems/07-pattern-formation/GC182.md) · [Scope v1](scoped/GC182.md) | Candidate · scoped draft | Not yet reviewed | 9/10 |
| GC183 | [Finite-box versus infinite-plane pattern selection](problems/07-pattern-formation/GC183.md) · [Scope v1](scoped/GC183.md) | Candidate · scoped draft | Not yet reviewed | 7/10 |
| GC184 | [Localized patches of periodic structure](problems/07-pattern-formation/GC184.md) · [Scope v1](scoped/GC184.md) | Candidate · scoped draft | Not yet reviewed | 7/10 |
| GC185 | [Front speed between competing patterns](problems/07-pattern-formation/GC185.md) · [Scope v1](scoped/GC185.md) | Candidate · scoped draft | Not yet reviewed | 8/10 |
| GC186 | [Phase diffusion coefficient sign changes](problems/07-pattern-formation/GC186.md) · [Scope v1](scoped/GC186.md) | Candidate · scoped draft | Not yet reviewed | 8/10 |
| GC187 | [Nonlinear pattern selection under slow parameter ramps](problems/07-pattern-formation/GC187.md) · [Scope v1](scoped/GC187.md) | Candidate · scoped draft | Not yet reviewed | 8/10 |
| GC188 | [Stochastic creation of phase dislocations](problems/07-pattern-formation/GC188.md) · [Scope v1](scoped/GC188.md) | Candidate · scoped draft | Not yet reviewed | 8/10 |
| GC189 | [Pattern inheritance across interfaces](problems/07-pattern-formation/GC189.md) · [Scope v1](scoped/GC189.md) | Candidate · scoped draft | Not yet reviewed | 8/10 |
| GC190 | [Aperiodic stable textures](problems/07-pattern-formation/GC190.md) · [Scope v1](scoped/GC190.md) | Candidate · scoped draft | Not yet reviewed | 8/10 |
| GC191 | [Gradient-flow convergence rates](problems/07-pattern-formation/GC191.md) · [Scope v1](scoped/GC191.md) | Candidate · scoped draft | Not yet reviewed | 8/10 |
| GC192 | [Topological defect charge balance](problems/07-pattern-formation/GC192.md) · [Scope v1](scoped/GC192.md) | Candidate · scoped draft | Not yet reviewed | 8/10 |
| GC193 | [Pattern memory after forcing removal](problems/07-pattern-formation/GC193.md) · [Scope v1](scoped/GC193.md) | Candidate · scoped draft | Not yet reviewed | 8/10 |
| GC194 | [Coupled pattern synchronization](problems/07-pattern-formation/GC194.md) · [Scope v1](scoped/GC194.md) | Candidate · scoped draft | Not yet reviewed | 8/10 |
| GC195 | [Anisotropic grain-boundary energy](problems/07-pattern-formation/GC195.md) · [Scope v1](scoped/GC195.md) | Candidate · scoped draft | Not yet reviewed | 8/10 |

## Topology and multicomponent fields

[Subject overview](problems/08-topology-multicomponent/README.md) · [Full roadmap and difficulty notes](ROADMAP_300.md#topology-and-multicomponent-fields)

| ID | Mathematical question | GC stage | Existing mathematical evidence | Difficulty |
|:--|:--|:--|:--|--:|
| GC36 | [Stable knotted wave configurations](FORMAL_PROBLEMS.md#gc36-stable-knotted-wave-configurations) · [Dossier](./flagship/GC36.md) · [Issue #57](https://github.com/rickyjreyes/math/issues/57) | Candidate · formal · initial review | No existing proof mapped | 10/10 |
| GC37 | [Discrete particle-like solutions](FORMAL_PROBLEMS.md#gc37-discrete-particle-like-solutions) | Candidate · formal | Related source links; scope unaudited | 9/10 |
| GC38 | [Quantized winding conservation](FORMAL_PROBLEMS.md#gc38-quantized-winding-conservation) | Candidate · formal | No existing proof mapped | 9/10 |
| GC39 | [Coherent-state interaction laws](FORMAL_PROBLEMS.md#gc39-coherent-state-interaction-laws) | Candidate · formal | No existing proof mapped | 9/10 |
| GC40 | [Topology-changing singularities](FORMAL_PROBLEMS.md#gc40-topology-changing-singularities) | Candidate · formal | No existing proof mapped | 9/10 |
| GC58 | [Multicomponent and vector confinement](FORMAL_PROBLEMS.md#gc58-multicomponent-and-vector-confinement) | Candidate · formal | No existing proof mapped | 9/10 |
| GC196 | [Hopf charge and coercive energy bounds](problems/08-topology-multicomponent/GC196.md) · [Scope v1](scoped/GC196.md) | Candidate · scoped draft | Not yet reviewed | 9/10 |
| GC197 | [Knot type versus Hopf degree](problems/08-topology-multicomponent/GC197.md) · [Scope v1](scoped/GC197.md) | Candidate · scoped draft | Not yet reviewed | 7/10 |
| GC198 | [Linked vortex stability](problems/08-topology-multicomponent/GC198.md) · [Scope v1](scoped/GC198.md) | Candidate · scoped draft | Not yet reviewed | 9/10 |
| GC199 | [Topology of nodal lines under evolution](problems/08-topology-multicomponent/GC199.md) · [Scope v1](scoped/GC199.md) | Candidate · scoped draft | Not yet reviewed | 9/10 |
| GC200 | [Minimal energy for fixed winding pair](problems/08-topology-multicomponent/GC200.md) · [Scope v1](scoped/GC200.md) | Candidate · scoped draft | Not yet reviewed | 4/10 |
| GC201 | [Knotted-field symmetry breaking](problems/08-topology-multicomponent/GC201.md) · [Scope v1](scoped/GC201.md) | Candidate · scoped draft | Not yet reviewed | 10/10 |
| GC202 | [Vector-soliton polarization dynamics](problems/08-topology-multicomponent/GC202.md) · [Scope v1](scoped/GC202.md) | Candidate · scoped draft | Not yet reviewed | 9/10 |
| GC203 | [Topological obstruction to scalarization](problems/08-topology-multicomponent/GC203.md) · [Scope v1](scoped/GC203.md) | Candidate · scoped draft | Not yet reviewed | 9/10 |
| GC204 | [Vortex collision and reconnection energy](problems/08-topology-multicomponent/GC204.md) · [Scope v1](scoped/GC204.md) | Candidate · scoped draft | Not yet reviewed | 9/10 |
| GC205 | [Topological mode trapping in waveguides](problems/08-topology-multicomponent/GC205.md) · [Scope v1](scoped/GC205.md) | Candidate · scoped draft | Not yet reviewed | 9/10 |
| GC206 | [Higher Hopf-class minimizer compactness](problems/08-topology-multicomponent/GC206.md) · [Scope v1](scoped/GC206.md) | Candidate · scoped draft | Not yet reviewed | 9/10 |
| GC207 | [Knotted-wave oscillation spectra](problems/08-topology-multicomponent/GC207.md) · [Scope v1](scoped/GC207.md) | Candidate · scoped draft | Not yet reviewed | 10/10 |
| GC208 | [Defect interactions in multicomponent condensates](problems/08-topology-multicomponent/GC208.md) · [Scope v1](scoped/GC208.md) | Candidate · scoped draft | Not yet reviewed | 9/10 |
| GC209 | [Quantization without imposed topology](problems/08-topology-multicomponent/GC209.md) · [Scope v1](scoped/GC209.md) | Candidate · scoped draft | Not yet reviewed | 9/10 |
| GC210 | [Topology-preserving numerical schemes](problems/08-topology-multicomponent/GC210.md) · [Scope v1](scoped/GC210.md) | Candidate · scoped draft | Not yet reviewed | 8/10 |
| GC211 | [Creation of knot pairs under forcing](problems/08-topology-multicomponent/GC211.md) · [Scope v1](scoped/GC211.md) | Candidate · scoped draft | Not yet reviewed | 9/10 |
| GC212 | [Topological charge under weak noise](problems/08-topology-multicomponent/GC212.md) · [Scope v1](scoped/GC212.md) | Candidate · scoped draft | Not yet reviewed | 6/10 |
| GC213 | [Coupled-field vortex lattice phases](problems/08-topology-multicomponent/GC213.md) · [Scope v1](scoped/GC213.md) | Candidate · scoped draft | Not yet reviewed | 9/10 |
| GC214 | [Topology of moduli spaces of confined waves](problems/08-topology-multicomponent/GC214.md) · [Scope v1](scoped/GC214.md) | Candidate · scoped draft | Not yet reviewed | 9/10 |

## Computability and complexity

[Subject overview](problems/09-computability-complexity/README.md) · [Full roadmap and difficulty notes](ROADMAP_300.md#computability-and-complexity)

| ID | Mathematical question | GC stage | Existing mathematical evidence | Difficulty |
|:--|:--|:--|:--|--:|
| GC41 | [Decidability of PDE stability](FORMAL_PROBLEMS.md#gc41-decidability-of-pde-stability) | Candidate · formal | No existing proof mapped | 10/10 |
| GC42 | [Complexity of certified wave evolution](FORMAL_PROBLEMS.md#gc42-complexity-of-certified-wave-evolution) | Candidate · formal | No existing proof mapped | 7/10 |
| GC43 | [Discrete-wave computational universality](FORMAL_PROBLEMS.md#gc43-discrete-wave-computational-universality) · [Dossier](./flagship/GC43.md) · [Issue #58](https://github.com/rickyjreyes/math/issues/58) | Candidate · formal · initial review | No existing proof mapped | 10/10 |
| GC44 | [Sequential-work lower bounds](FORMAL_PROBLEMS.md#gc44-sequential-work-lower-bounds) | Candidate · formal | No existing proof mapped | 9/10 |
| GC45 | [Precision and noise limits](FORMAL_PROBLEMS.md#gc45-precision-and-noise-limits) | Candidate · formal | No existing proof mapped | 8/10 |
| GC215 | [Undecidability of nonlinear attractor membership](problems/09-computability-complexity/GC215.md) · [Scope v1](scoped/GC215.md) | Candidate · scoped draft | Not yet reviewed | 9/10 |
| GC216 | [Prediction hardness for reversible local waves](problems/09-computability-complexity/GC216.md) · [Scope v1](scoped/GC216.md) | Candidate · scoped draft | Not yet reviewed | 7/10 |
| GC217 | [Uniform simulation overhead for local wave rules](problems/09-computability-complexity/GC217.md) · [Scope v1](scoped/GC217.md) | Candidate · scoped draft | Not yet reviewed | 8/10 |
| GC218 | [Communication complexity of wave evolution](problems/09-computability-complexity/GC218.md) · [Scope v1](scoped/GC218.md) | Candidate · scoped draft | Not yet reviewed | 8/10 |
| GC219 | [Parallel prefix shortcuts for homogeneous wave rules](problems/09-computability-complexity/GC219.md) · [Scope v1](scoped/GC219.md) | Candidate · scoped draft | Not yet reviewed | 8/10 |
| GC220 | [P-completeness of local-wave reachability](problems/09-computability-complexity/GC220.md) · [Scope v1](scoped/GC220.md) | Candidate · scoped draft | Not yet reviewed | 9/10 |
| GC221 | [Precision complexity near unstable manifolds](problems/09-computability-complexity/GC221.md) · [Scope v1](scoped/GC221.md) | Candidate · scoped draft | Not yet reviewed | 8/10 |
| GC222 | [Certified integration without global Lipschitz constants](problems/09-computability-complexity/GC222.md) · [Scope v1](scoped/GC222.md) | Candidate · scoped draft | Not yet reviewed | 7/10 |
| GC223 | [Bit complexity of fourth-order spectral solvers](problems/09-computability-complexity/GC223.md) · [Scope v1](scoped/GC223.md) | Candidate · scoped draft | Not yet reviewed | 8/10 |
| GC224 | [Complexity of deciding discrete soliton existence](problems/09-computability-complexity/GC224.md) · [Scope v1](scoped/GC224.md) | Candidate · scoped draft | Not yet reviewed | 8/10 |
| GC225 | [Memory lower bounds for reversible computation](problems/09-computability-complexity/GC225.md) · [Scope v1](scoped/GC225.md) | Candidate · scoped draft | Not yet reviewed | 9/10 |
| GC226 | [Algorithmic verification of invariants](problems/09-computability-complexity/GC226.md) · [Scope v1](scoped/GC226.md) | Candidate · scoped draft | Not yet reviewed | 7/10 |
| GC227 | [Certified stopping rules for dissipative evolution](problems/09-computability-complexity/GC227.md) · [Scope v1](scoped/GC227.md) | Candidate · scoped draft | Not yet reviewed | 7/10 |
| GC228 | [Circuit depth versus locality radius](problems/09-computability-complexity/GC228.md) · [Scope v1](scoped/GC228.md) | Candidate · scoped draft | Not yet reviewed | 7/10 |
| GC229 | [Noise tolerance of universal wave automata](problems/09-computability-complexity/GC229.md) · [Scope v1](scoped/GC229.md) | Candidate · scoped draft | Not yet reviewed | 9/10 |
| GC230 | [Computable stability radius](problems/09-computability-complexity/GC230.md) · [Scope v1](scoped/GC230.md) | Candidate · scoped draft | Not yet reviewed | 8/10 |
| GC231 | [Formal complexity of proof-producing simulation](problems/09-computability-complexity/GC231.md) · [Scope v1](scoped/GC231.md) | Candidate · scoped draft | Not yet reviewed | 8/10 |
| GC232 | [Resource-bounded equivalence of wave models](problems/09-computability-complexity/GC232.md) · [Scope v1](scoped/GC232.md) | Candidate · scoped draft | Not yet reviewed | 8/10 |
| GC233 | [Complexity of exact spectral gap detection](problems/09-computability-complexity/GC233.md) · [Scope v1](scoped/GC233.md) | Candidate · scoped draft | Not yet reviewed | 8/10 |
| GC234 | [Thermodynamic cost versus computational depth](problems/09-computability-complexity/GC234.md) · [Scope v1](scoped/GC234.md) | Candidate · scoped draft | Not yet reviewed | 8/10 |

## Lean formalization and certified analysis

[Subject overview](problems/10-lean-certified-analysis/README.md) · [Full roadmap and difficulty notes](ROADMAP_300.md#lean-formalization-and-certified-analysis)

| ID | Mathematical question | GC stage | Existing mathematical evidence | Difficulty |
|:--|:--|:--|:--|--:|
| GC46 | [Verified infinite-dimensional evolution](FORMAL_PROBLEMS.md#gc46-verified-infinite-dimensional-evolution) | Candidate · formal | ✅ Global evolution proof; full-match audit pending | 6/10 |
| GC47 | [Formal concentration compactness](FORMAL_PROBLEMS.md#gc47-formal-concentration-compactness) | Candidate · formal | Related source links; scope unaudited | 7/10 |
| GC48 | [Certified spectral semigroups](FORMAL_PROBLEMS.md#gc48-certified-spectral-semigroups) | Candidate · formal | Related source links; scope unaudited | 6/10 |
| GC49 | [Checked PDE counterexamples](FORMAL_PROBLEMS.md#gc49-checked-pde-counterexamples) | Candidate · formal | Related source links; scope unaudited | 7/10 |
| GC50 | [Proof-carrying numerical certificates](FORMAL_PROBLEMS.md#gc50-proof-carrying-numerical-certificates) | Candidate · formal | No existing proof mapped | 6/10 |
| GC65 | [Verified mathematical model reduction](FORMAL_PROBLEMS.md#gc65-verified-mathematical-model-reduction) | Candidate · formal | Related source links; scope unaudited | 9/10 |
| GC235 | [Lean-certified Fourier transform on Sobolev spaces](problems/10-lean-certified-analysis/GC235.md) · [Scope v1](scoped/GC235.md) | Candidate · scoped draft | Not yet reviewed | 7/10 |
| GC236 | [Verified nonlinear energy differentiability](problems/10-lean-certified-analysis/GC236.md) · [Scope v1](scoped/GC236.md) | Candidate · scoped draft | Not yet reviewed | 7/10 |
| GC237 | [Certified constrained minimizer existence](problems/10-lean-certified-analysis/GC237.md) · [Scope v1](scoped/GC237.md) | Candidate · scoped draft | Not yet reviewed | 9/10 |
| GC238 | [Lean orbital-distance quotient topology](problems/10-lean-certified-analysis/GC238.md) · [Scope v1](scoped/GC238.md) | Candidate · scoped draft | Not yet reviewed | 6/10 |
| GC239 | [Formal semigroup smoothing estimates](problems/10-lean-certified-analysis/GC239.md) · [Scope v1](scoped/GC239.md) | Candidate · scoped draft | Not yet reviewed | 7/10 |
| GC240 | [Verified Fourier-mode projectors](problems/10-lean-certified-analysis/GC240.md) · [Scope v1](scoped/GC240.md) | Candidate · scoped draft | Not yet reviewed | 7/10 |
| GC241 | [Lean proof of spectral gap persistence](problems/10-lean-certified-analysis/GC241.md) · [Scope v1](scoped/GC241.md) | Candidate · scoped draft | Not yet reviewed | 6/10 |
| GC242 | [Certified local implicit-function branches](problems/10-lean-certified-analysis/GC242.md) · [Scope v1](scoped/GC242.md) | Candidate · scoped draft | Not yet reviewed | 7/10 |
| GC243 | [Verified mass and energy conservation laws](problems/10-lean-certified-analysis/GC243.md) · [Scope v1](scoped/GC243.md) | Candidate · scoped draft | Not yet reviewed | 7/10 |
| GC244 | [Formal concentration radius inequalities](problems/10-lean-certified-analysis/GC244.md) · [Scope v1](scoped/GC244.md) | Candidate · scoped draft | Not yet reviewed | 7/10 |
| GC245 | [Lean Hamiltonian constraint matrix rank](problems/10-lean-certified-analysis/GC245.md) · [Scope v1](scoped/GC245.md) | Candidate · scoped draft | Not yet reviewed | 6/10 |
| GC246 | [Verified parameter identifiability ranks](problems/10-lean-certified-analysis/GC246.md) · [Scope v1](scoped/GC246.md) | Candidate · scoped draft | Not yet reviewed | 6/10 |
| GC247 | [Proof-assistant validated scattering normalization](problems/10-lean-certified-analysis/GC247.md) · [Scope v1](scoped/GC247.md) | Candidate · scoped draft | Not yet reviewed | 6/10 |
| GC248 | [Formal topological winding invariance](problems/10-lean-certified-analysis/GC248.md) · [Scope v1](scoped/GC248.md) | Candidate · scoped draft | Not yet reviewed | 7/10 |
| GC249 | [Certified error propagation for Galerkin ODEs](problems/10-lean-certified-analysis/GC249.md) · [Scope v1](scoped/GC249.md) | Candidate · scoped draft | Not yet reviewed | 6/10 |
| GC250 | [Lean-displayed counterexample provenance](problems/10-lean-certified-analysis/GC250.md) · [Scope v1](scoped/GC250.md) | Candidate · scoped draft | Not yet reviewed | 4/10 |
| GC251 | [Validated spectral eigenvalue enclosures](problems/10-lean-certified-analysis/GC251.md) · [Scope v1](scoped/GC251.md) | Candidate · scoped draft | Not yet reviewed | 7/10 |
| GC252 | [Formal long-time Lyapunov descent](problems/10-lean-certified-analysis/GC252.md) · [Scope v1](scoped/GC252.md) | Candidate · scoped draft | Not yet reviewed | 8/10 |
| GC253 | [Machine-checked model-to-model error theorem](problems/10-lean-certified-analysis/GC253.md) · [Scope v1](scoped/GC253.md) | Candidate · scoped draft | Not yet reviewed | 9/10 |

## Physical emergence and multiscale limits

[Subject overview](problems/11-physical-emergence-multiscale/README.md) · [Full roadmap and difficulty notes](ROADMAP_300.md#physical-emergence-and-multiscale-limits)

| ID | Mathematical question | GC stage | Existing mathematical evidence | Difficulty |
|:--|:--|:--|:--|--:|
| GC52 | [Rigorous emergence of effective wave equations](FORMAL_PROBLEMS.md#gc52-rigorous-emergence-of-effective-wave-equations) | Candidate · formal | No existing proof mapped | 10/10 |
| GC60 | [Singular limits and multiscale consistency](FORMAL_PROBLEMS.md#gc60-singular-limits-and-multiscale-consistency) | Candidate · formal | Related source links; scope unaudited | 10/10 |
| GC254 | [Degenerate band-edge envelope derivation](problems/11-physical-emergence-multiscale/GC254.md) · [Scope v1](scoped/GC254.md) | Candidate · scoped draft | Not yet reviewed | 9/10 |
| GC255 | [Discrete-to-continuum confinement persistence](problems/11-physical-emergence-multiscale/GC255.md) · [Scope v1](scoped/GC255.md) | Candidate · scoped draft | Not yet reviewed | 9/10 |
| GC256 | [Uniform modulation error over long times](problems/11-physical-emergence-multiscale/GC256.md) · [Scope v1](scoped/GC256.md) | Candidate · scoped draft | Not yet reviewed | 10/10 |
| GC257 | [Microscopic origin of cubic–quintic saturation](problems/11-physical-emergence-multiscale/GC257.md) · [Scope v1](scoped/GC257.md) | Candidate · scoped draft | Not yet reviewed | 9/10 |
| GC258 | [Scale separation near an avoided crossing](problems/11-physical-emergence-multiscale/GC258.md) · [Scope v1](scoped/GC258.md) | Candidate · scoped draft | Not yet reviewed | 9/10 |
| GC259 | [Effective geometric curvature from microstructure](problems/11-physical-emergence-multiscale/GC259.md) · [Scope v1](scoped/GC259.md) | Candidate · scoped draft | Not yet reviewed | 9/10 |
| GC260 | [Homogenization of periodically patterned media](problems/11-physical-emergence-multiscale/GC260.md) · [Scope v1](scoped/GC260.md) | Candidate · scoped draft | Not yet reviewed | 9/10 |
| GC261 | [Disorder-induced failure of effective equations](problems/11-physical-emergence-multiscale/GC261.md) · [Scope v1](scoped/GC261.md) | Candidate · scoped draft | Not yet reviewed | 9/10 |
| GC262 | [Boundary-layer corrections to wave confinement](problems/11-physical-emergence-multiscale/GC262.md) · [Scope v1](scoped/GC262.md) | Candidate · scoped draft | Not yet reviewed | 9/10 |
| GC263 | [Finite-size scaling of confinement thresholds](problems/11-physical-emergence-multiscale/GC263.md) · [Scope v1](scoped/GC263.md) | Candidate · scoped draft | Not yet reviewed | 9/10 |
| GC264 | [Conservation law transfer across model scales](problems/11-physical-emergence-multiscale/GC264.md) · [Scope v1](scoped/GC264.md) | Candidate · scoped draft | Not yet reviewed | 9/10 |
| GC265 | [Noncommuting continuum and long-time limits](problems/11-physical-emergence-multiscale/GC265.md) · [Scope v1](scoped/GC265.md) | Candidate · scoped draft | Not yet reviewed | 10/10 |
| GC266 | [Strong versus weak convergence of physical observables](problems/11-physical-emergence-multiscale/GC266.md) · [Scope v1](scoped/GC266.md) | Candidate · scoped draft | Not yet reviewed | 9/10 |
| GC267 | [Inverse calibration of effective coupling coefficients](problems/11-physical-emergence-multiscale/GC267.md) · [Scope v1](scoped/GC267.md) | Candidate · scoped draft | Not yet reviewed | 7/10 |
| GC268 | [Multiscale topological charge preservation](problems/11-physical-emergence-multiscale/GC268.md) · [Scope v1](scoped/GC268.md) | Candidate · scoped draft | Not yet reviewed | 9/10 |
| GC269 | [Error bounds for reduced three-dimensional models](problems/11-physical-emergence-multiscale/GC269.md) · [Scope v1](scoped/GC269.md) | Candidate · scoped draft | Not yet reviewed | 9/10 |
| GC270 | [Competing effective Hamiltonians from the same lattice](problems/11-physical-emergence-multiscale/GC270.md) · [Scope v1](scoped/GC270.md) | Candidate · scoped draft | Not yet reviewed | 9/10 |
| GC271 | [Emergent wave speed and stiffness constants](problems/11-physical-emergence-multiscale/GC271.md) · [Scope v1](scoped/GC271.md) | Candidate · scoped draft | Not yet reviewed | 9/10 |
| GC272 | [Breakdown of adiabatic mode elimination](problems/11-physical-emergence-multiscale/GC272.md) · [Scope v1](scoped/GC272.md) | Candidate · scoped draft | Not yet reviewed | 9/10 |
| GC273 | [Uniform regularity from microscopic energy bounds](problems/11-physical-emergence-multiscale/GC273.md) · [Scope v1](scoped/GC273.md) | Candidate · scoped draft | Not yet reviewed | 10/10 |
| GC274 | [Experimental falsification thresholds for envelope laws](problems/11-physical-emergence-multiscale/GC274.md) · [Scope v1](scoped/GC274.md) | Candidate · scoped draft | Not yet reviewed | 10/10 |
| GC275 | [Rigorous correspondence between lattice and optical phases](problems/11-physical-emergence-multiscale/GC275.md) · [Scope v1](scoped/GC275.md) | Candidate · scoped draft | Not yet reviewed | 9/10 |
| GC276 | [Long-wavelength stability versus microscopic instabilities](problems/11-physical-emergence-multiscale/GC276.md) · [Scope v1](scoped/GC276.md) | Candidate · scoped draft | Not yet reviewed | 9/10 |

## Photonic computation and physical information

[Subject overview](problems/12-photonic-wave-computing/README.md) · [Full roadmap and difficulty notes](ROADMAP_300.md#photonic-computation-and-physical-information)

| ID | Mathematical question | GC stage | Existing mathematical evidence | Difficulty |
|:--|:--|:--|:--|--:|
| GC63 | [Physical information and energy limits of wave computation](FORMAL_PROBLEMS.md#gc63-physical-information-and-energy-limits-of-wave-computation) | Candidate · formal | No existing proof mapped | 7/10 |
| GC277 | [Interference-based XOR robustness](problems/12-photonic-wave-computing/GC277.md) · [Scope v1](scoped/GC277.md) | Candidate · scoped draft | Not yet reviewed | 7/10 |
| GC278 | [Passive optical logic universality constraints](problems/12-photonic-wave-computing/GC278.md) · [Scope v1](scoped/GC278.md) | Candidate · scoped draft | Not yet reviewed | 7/10 |
| GC279 | [Cascadability of photonic logic gates](problems/12-photonic-wave-computing/GC279.md) · [Scope v1](scoped/GC279.md) | Candidate · scoped draft | Not yet reviewed | 7/10 |
| GC280 | [Optical phase memory retention](problems/12-photonic-wave-computing/GC280.md) · [Scope v1](scoped/GC280.md) | Candidate · scoped draft | Not yet reviewed | 7/10 |
| GC281 | [Photonic reversible gate synthesis](problems/12-photonic-wave-computing/GC281.md) · [Scope v1](scoped/GC281.md) | Candidate · scoped draft | Not yet reviewed | 7/10 |
| GC282 | [Wave-based arithmetic precision](problems/12-photonic-wave-computing/GC282.md) · [Scope v1](scoped/GC282.md) | Candidate · scoped draft | Not yet reviewed | 7/10 |
| GC283 | [Optical fan-out energy limits](problems/12-photonic-wave-computing/GC283.md) · [Scope v1](scoped/GC283.md) | Candidate · scoped draft | Not yet reviewed | 7/10 |
| GC284 | [Error accumulation in phase-coded circuits](problems/12-photonic-wave-computing/GC284.md) · [Scope v1](scoped/GC284.md) | Candidate · scoped draft | Not yet reviewed | 7/10 |
| GC285 | [Photonic neural operator stability](problems/12-photonic-wave-computing/GC285.md) · [Scope v1](scoped/GC285.md) | Candidate · scoped draft | Not yet reviewed | 7/10 |
| GC286 | [Optical versus electronic energy accounting](problems/12-photonic-wave-computing/GC286.md) · [Scope v1](scoped/GC286.md) | Candidate · scoped draft | Not yet reviewed | 6/10 |
| GC287 | [Integrated photonic wavelength selection](problems/12-photonic-wave-computing/GC287.md) · [Scope v1](scoped/GC287.md) | Candidate · scoped draft | Not yet reviewed | 7/10 |
| GC288 | [Thermal drift compensation in optical logic](problems/12-photonic-wave-computing/GC288.md) · [Scope v1](scoped/GC288.md) | Candidate · scoped draft | Not yet reviewed | 7/10 |
| GC289 | [Hybrid electro-optical feedback lower bounds](problems/12-photonic-wave-computing/GC289.md) · [Scope v1](scoped/GC289.md) | Candidate · scoped draft | Not yet reviewed | 8/10 |
| GC290 | [Multimode optical interference capacity](problems/12-photonic-wave-computing/GC290.md) · [Scope v1](scoped/GC290.md) | Candidate · scoped draft | Not yet reviewed | 7/10 |
| GC291 | [Optical routing with curvature-controlled media](problems/12-photonic-wave-computing/GC291.md) · [Scope v1](scoped/GC291.md) | Candidate · scoped draft | Not yet reviewed | 7/10 |
| GC292 | [Wavelet-inspired optical memory addressing](problems/12-photonic-wave-computing/GC292.md) · [Scope v1](scoped/GC292.md) | Candidate · scoped draft | Not yet reviewed | 7/10 |
| GC293 | [Pulse collision as a logic primitive](problems/12-photonic-wave-computing/GC293.md) · [Scope v1](scoped/GC293.md) | Candidate · scoped draft | Not yet reviewed | 7/10 |
| GC294 | [Optical error correction by redundancy](problems/12-photonic-wave-computing/GC294.md) · [Scope v1](scoped/GC294.md) | Candidate · scoped draft | Not yet reviewed | 7/10 |
| GC295 | [Photonic compiler correctness](problems/12-photonic-wave-computing/GC295.md) · [Scope v1](scoped/GC295.md) | Candidate · scoped draft | Not yet reviewed | 7/10 |
| GC296 | [Proof-carrying optical circuit calibration](problems/12-photonic-wave-computing/GC296.md) · [Scope v1](scoped/GC296.md) | Candidate · scoped draft | Not yet reviewed | 6/10 |
| GC297 | [Scaling of optical cross-talk in dense chips](problems/12-photonic-wave-computing/GC297.md) · [Scope v1](scoped/GC297.md) | Candidate · scoped draft | Not yet reviewed | 7/10 |
| GC298 | [Synchronization of independent optical clocks](problems/12-photonic-wave-computing/GC298.md) · [Scope v1](scoped/GC298.md) | Candidate · scoped draft | Not yet reviewed | 7/10 |
| GC299 | [Thermodynamic efficiency of optical state reset](problems/12-photonic-wave-computing/GC299.md) · [Scope v1](scoped/GC299.md) | Candidate · scoped draft | Not yet reviewed | 7/10 |
| GC300 | [Full-stack verified photonic arithmetic](problems/12-photonic-wave-computing/GC300.md) · [Scope v1](scoped/GC300.md) | Candidate · scoped draft | Not yet reviewed | 9/10 |

## What changes a research status?

A partial result, corrected hypothesis, prior-art match, or Lean-checked *subtheorem* is progress, but it does **not** silently close its parent GC question. For GC08, the explicit curvature-closure counterexample resolves a restricted uniqueness claim, not the full admissible-closure classification.

A formal resolution requires the precise quantifiers, a proof or admissible counterexample, comparison against prior literature, and a documented correspondence review. See [METHOD.md](METHOD.md), [the contribution guide](CONTRIBUTING.md), and [the completion records](completion_records.json). Numerical results and physical validation are assessed separately.

**Authoritative source:** [problem_registry.json](problem_registry.json). If an individual link or a displayed status becomes stale, reconcile it against the registry and the exact source theorem before editing this reader-facing summary.
