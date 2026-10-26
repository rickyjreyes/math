# Mathematical manuscripts and formal proof artifacts

**Richard J. Reyes · Independent Researcher**

A collection of **15 research manuscripts in 11 result families**, organized for independent mathematical inspection. Inspired in navigation by [openai/math](https://github.com/openai/math), with independent authorship and separate verification claims.

## Navigate

- [Overview PDF](overview.pdf) — concise guide to all result families.
- [Manuscript map](CONTENTS.md) — direct links to each **PDF**, LaTeX source, and notes.
- [Preprints](preprints/) — compiled manuscript PDFs.
- [Lean catalogue](lean/formalization.yaml) and [Lean project](lean/README.md) — exact status of every family.
- [History](history.md) — correction and release log.

## Featured results

| Family | Results | Scope |
| --- | --- | --- |
| **F01** | Strict binding, whole-space minimizer existence, orbital stability, negative trial energy | Combined focusing-cubic/defocusing-quintic fourth-order Hamiltonian on ℝ²; sufficient mass range |
| **F02** | High-frequency Sobolev obstruction, higher-derivative constraint count | Specified linear and regular fixed-background models |
| **F03** | Spectral–phase identity and 4/5 counterexample | Declared periodic spectral operator |
| **F04** | Instantaneous finite Fourier-mode leakage | Unprojected cubic–quintic torus dynamics |
| **F11** | E62 spectral energy concentration bound | Normalized Fourier energy in a measurable band; nonzero L² fields |
| **F11** | Band-pass negative gradient flow and exact dissipation | Periodic Swift–Hohenberg amplitude model with sufficiently regular solutions |

For F01, prior single-power work: Fernández, Jeanjean, Mandel and Mariş, *Journal of Differential Equations* **330** (2022), DOI [10.1016/j.jde.2022.04.037](https://doi.org/10.1016/j.jde.2022.04.037). An independent Hamiltonian model is **not** a derivation from a physically healthy parent, and D4 in this corpus is square symmetry in two spatial dimensions.

## Reproducibility

```bash
# Compile all 15 PDFs and overview.pdf
bash scripts/build_pdfs.sh

# Compile the explicit Lean supporting theorems
cd lean
lake update
lake exe cache get
lake build
```

[PDF workflow](.github/workflows/pdfs.yml) builds and publishes the actual PDFs to the repository on a successful main-branch run; [Lean workflow](.github/workflows/lean.yml) checks the included Lean code.

**Formalization status:** the Lean project includes kernel-checkable elementary theorems and substantive structural cores: the actual 11×31 matrix nullity bound, rank-two/positive-semidefinite scalar-gradient Gram obstruction, finite weighted variance and phase inequalities, 1D Fourier cutoff certificates, and null-support consequences. **The main nonlinear PDE and higher-derivative dynamics manuscripts remain unformalized.** A green Lean check does not certify all 15 PDFs. See [the per-family manifest](lean/formalization.yaml) and [the Lean guide](lean/README.md). Separate WCT Lean work: [wct-lean](https://github.com/rickyjreyes/wct-lean).

Every manuscript is a research draft, not independently peer-reviewed. Mathematical correctness, priority, physical interpretation and external replication are separate questions.

## Cite and review

Cite the specific manuscript and Git revision. [Citation metadata](CITATION.cff) · [Version history](history.md). Corrections, counterexamples and priority references are welcome through [issues](https://github.com/rickyjreyes/math/issues).
