# Adoption inventory: existing Lean proofs, manuscripts, and GC questions

The Reyes Problem Repository is an **open invitation to contribute**, not a separate proof or publication pipeline. Its purpose is to track the mathematical questions motivated by the existing research program, invite human and AI-assisted contributors, and reuse the Lean files and papers **already present**.

## Complete initial cross-reference pass

The original **65 problems** now have an explicit machine-readable source mapping in [existing_work_links.json](existing_work_links.json), rendered for review in [GC65_ADOPTION.md](GC65_ADOPTION.md).

- **43/65** have at least one identified related existing Lean source or manuscript.
- **22/65** remain *not mapped in this initial conservative pass*. This is not evidence that no relevant artifact exists.
- The 43 comprise **11 direct but partial links**, **28 adjacent/different-scope connections**, **2 potentially close full-claim matches**, and **2 counterexample candidates**.
- **No GC-to-theorem correspondence has been certified by this mapping.** It is deliberately separate from the [Lean manuscript formalization manifest](../lean/formalization.yaml).
- **No GC statuses, original theorem statements, Lean modules, manuscripts, or existing issues have been changed** by this cross-reference exercise.

[Read all 65 links and limitations](GC65_ADOPTION.md) · [Machine adoption index](existing_work_links.json) · [GC workflow](WORKFLOW.md) · [All 300 candidate questions](ROADMAP_300.md)

## Initial problem-to-research anchors

| Question | Existing GC issue | Existing mathematical result or source | Why the issue is not automatically resolved |
|:--|:--|:--|:--|
| [GC01](problems/01-wave-dynamics/GC01.md) | [#54](https://github.com/rickyjreyes/math/issues/54) | [OrbitalStability.lean](../lean/MathProofs/OrbitalStability.lean), [paper](../papers/orbital-stability-fourth-order-cubic-quintic/main.tex) | Stability of the minimizing set is narrower than classification of all standing waves including excited states |
| [GC06](problems/02-confinement-curvature/GC06.md) | [#55](https://github.com/rickyjreyes/math/issues/55) | [WholeSpaceMinimizers.lean](../lean/MathProofs/WholeSpaceMinimizers.lean), [StrictBinding.lean](../lean/MathProofs/StrictBinding.lean), [paper](../papers/whole-space-fourth-order-cubic-quintic-minimizers/main.tex) | Sufficient mass ranges do not classify all parameter and mass regimes |
| [GC11](problems/03-spectral-scattering/GC11.md) | [#56](https://github.com/rickyjreyes/math/issues/56) | [DispersionMinimum.lean](../lean/MathProofs/DispersionMinimum.lean), [paper](../papers/exact-positive-wavenumber-minimum/main.tex) | Linear finite-wave-number minimization does not prove nonlinear wavelength selection |
| [GC36](problems/08-topology-multicomponent/GC36.md) | [#57](https://github.com/rickyjreyes/math/issues/57) | No exact source match yet identified | Need frozen Hopf-class dynamics and a coherent orbital stability question |
| [GC43](problems/09-computability-complexity/GC43.md) | [#58](https://github.com/rickyjreyes/math/issues/58) | No exact source match yet identified in this repository | Need a specific reversible wave-cell automaton and exact simulation target |
| [GC08](problems/02-confinement-curvature/GC08.md) | No dedicated GC issue | [M6BClosureTheorem.lean](../lean/MathProofs/M6BClosureTheorem.lean), [paper](../papers/m6b-nonlinear-curvature-nonuniqueness/main.tex), related [Lean issue #42](https://github.com/rickyjreyes/math/issues/42) | Verify whether its five-axiom closure family matches GC08's frozen admissibility requirements |

These are links to **real existing sources**, not new assertions of mathematical novelty or proof completeness.

## High-value correspondence reviews

The first full adoption reviews I would prioritize are:

1. **[GC15](problems/03-spectral-scattering/GC15.md):** The [finite Fourier-subspace noninvariance theorem](../papers/finite-fourier-coordinate-subspace-noninvariance/main.tex) may answer the exact GC classification. Check the domain, mode-set assumptions, and every quantified case against [FourierLeakage.lean](../lean/MathProofs/FourierLeakage.lean).
2. **[GC46](problems/10-lean-certified-analysis/GC46.md):** The [F01 whole-space global flow and conservation](../papers/orbital-stability-fourth-order-cubic-quintic/main.tex) may fulfill much of the intended Lean PDE theorem. Check that the full formal model, conservation, topology, continuity and no-new-axioms requirement match.
3. **[GC08](problems/02-confinement-curvature/GC08.md):** Compare the exact admissibility axioms with the existing M6B closure nonuniqueness counterexample.
4. **[GC13](problems/03-spectral-scattering/GC13.md):** Determine whether the existing Fourier-leakage theorem refutes the exact interband no-transfer quantifiers for an appropriate two-shell choice.

These are **review candidates**, not closed problems. If exact correspondence is established, use the existing Lean declarations by reference. Do not reprove or move the original work.

## GC66–GC300: staged activation

The **235 newer entries remain research sketches** and are preserved without rewriting. The [candidate activation guide](CANDIDATE_ACTIVATION.md) says how to transform one selected sketch into a frozen problem issue. Do not bulk-open issues or reclassify these as literature-verified open problems.

## Paper ↔ Lean, in either direction

- **Paper first:** An analytic proof or counterexample is developed and written. A separate Lean PR can formalize its exact mathematical statement. The paper's existing result remains valid or disputable on mathematical grounds while formalization is pending; only the verified label waits for the check.
- **Lean first:** A mathematically meaningful theorem is discovered or formalized in Lean. A paper may later explain its relevance, cite the exact formal declaration and commit, and distinguish any additional claims.
- **Both directions:** An error, missing assumption or counterexample discovered on either side is raised as an issue. Changes to a manuscript or proof are separate, reviewed contributions, and recorded rather than silently synchronized by changing meaning.

The [issue/PR/Lean/paper verification contract](WORKFLOW.md) governs **newly claimed formal GC issue resolutions**. It does not retroactively change the certified status, location, authorship, or scientific scope of existing manuscripts.

**Existing work is credit, not debt.** The research program continues even without outside contributions, and new contributors receive appropriate attribution.
