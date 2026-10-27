# Mathematical manuscripts and formal proof artifacts

**Richard J. Reyes · Independent Researcher**

A growing collection of **research manuscripts organized by result family**, organized for independent mathematical inspection. Inspired in navigation by [openai/math](https://github.com/openai/math), with independent authorship and separate verification claims.

## Navigate

- [Overview PDF](overview.pdf) — concise guide to all result families.
- [Manuscript map](CONTENTS.md) — direct links to each **PDF**, LaTeX source, and notes.
- [E16: spectral concentration and argmax proof](papers/e16-linear-spectral-concentration/main.tex) — linear Fourier selection with explicit hypotheses.
- [E18: corrected WCT Lyapunov descent](papers/wct-e18-exact-gradient-lyapunov/main.tex) — complete proof under the exact negative-gradient-flow assumption.
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
| **F11** | E13/E14 negative-gradient-flow structure; E16 linear spectral concentration; E62 Fourier fraction | Periodic amplitude flow and continuum spectral selection under explicit initial-support assumptions |
| **F12** | E26: conditional historical curvature $L^2$ estimate | Additive-denominator version requires uniform separation; corrected M2/E17 operator is different |
| **M6B** | Regularized curvature closure and stationary inverse nonuniqueness | Explicit analytical counterexamples; no claim about M7 initial-value evolution |

For F01, prior single-power work: Fernández, Jeanjean, Mandel and Mariş, *Journal of Differential Equations* **330** (2022), DOI [10.1016/j.jde.2022.04.037](https://doi.org/10.1016/j.jde.2022.04.037). An independent Hamiltonian model is **not** a derivation from a physically healthy parent, and D4 in this corpus is square symmetry in two spatial dimensions.


**E68 addition:** [Localized-energy counterexamples and corrected theorem](papers/localized-gradient-energy-e68/main.tex) · [PDF](preprints/localized-gradient-energy-e68/paper.pdf) · [Notes](preprints/localized-gradient-energy-e68/README.md). Not Lean-formalized.

## Reproducibility

```bash
# Compile all manuscript PDFs and overview.pdf
bash scripts/build_pdfs.sh

# Compile the explicit Lean supporting theorems
cd lean
lake update
lake exe cache get
lake build
```

[PDF workflow](.github/workflows/pdfs.yml) builds and publishes the actual PDFs to the repository on a successful main-branch run; [Lean workflow](.github/workflows/lean.yml) checks the included Lean code.

**Formalization status:** the Lean project now formalizes, end to end on the stated function spaces, the strict-binding and negative-energy manuscripts (F01), ultraviolet Sobolev ill-posedness and the S004 constraint count (F02), the spectral–phase identity (F03), curvature nonattainment and strict spreading (F05), the dispersion minimum (F06) and continuous phase locking (F07), together with the earlier structural cores (11×31 matrix nullity, scalar-gradient Gram obstruction, Schwartz Fourier shell). **Still unformalized:** whole-space minimizer compactness and orbital stability (F01), local existence/uniqueness behind the F04 classification corollary, F09 numerical rank claims, the L² extension of F10, and F11/F12. A green Lean check certifies only the exported Lean statements. See [the per-manuscript manifest](lean/formalization.yaml) and [the Lean guide](lean/README.md). Separate WCT Lean work: [wct-lean](https://github.com/rickyjreyes/wct-lean).

Every manuscript is a research draft, not independently peer-reviewed. Mathematical correctness, priority, physical interpretation and external replication are separate questions.

## Cite and review

Cite the specific manuscript and Git revision. [Citation metadata](CITATION.cff) · [Version history](history.md). Corrections, counterexamples and priority references are welcome through [issues](https://github.com/rickyjreyes/math/issues).

## E61 — Continuum pattern-formation threshold

[LaTeX proof](papers/e61-pattern-formation-threshold/main.tex) · [PDF](preprints/e61-pattern-formation-threshold/paper.pdf) · [Notes](preprints/e61-pattern-formation-threshold/README.md). Exact threshold for the centered linear Swift--Hohenberg operator; no nonlinear localization claim.
