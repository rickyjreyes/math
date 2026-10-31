# Mathematical Manuscripts and Formal Proof Artifacts

**Richard J. Reyes** · Independent Researcher

This repository develops independently checkable mathematics relevant to the continuing **Wave Confinement Theory (WCT)** research program, investigating whether confinement, resonance, phase dynamics, curvature and nonlinear fields can support a consistent, experimentally testable physical framework. The mathematics also has independent value in fourth-order PDEs, spectral dynamics, variational analysis and geometric constraints.

Results are organized by mathematical subject so exact claims can be assessed without accepting a physical interpretation. **That separation is a verification strategy, not a retreat from WCT's foundational objectives.** Analytical proofs, Lean-checked statements, numerical evidence and physical hypotheses remain distinct levels of evidence.

**Open research invitation:** [The Reyes Problem Repository](reyes-problem-repository/README.md) organizes 300 proposed questions as a GitHub issue and pull-request research workflow. [Its proof contract](reyes-problem-repository/WORKFLOW.md) links, rather than replaces, the existing Lean declarations and papers. Researchers may contribute verified theorems or counterexamples with full attribution; ongoing work does not depend on outside participation.

**Explore:** [The Reyes Problem Repository](reyes-problem-repository/README.md) · [Complete manuscript catalogue](CONTENTS.md) · [Compiled PDFs](preprints/) · [Overview](overview.pdf) · [Lean formalization status](lean/formalization.yaml) · [Revision history](history.md)

## Research purpose and interpretation

The objective is to **advance and critically test WCT's foundational physics research**, while developing rigorous mathematics that stands independently. Engineering and control applications are complementary, not a compulsory replacement for this objective. Neither a mathematical success nor an obstruction settles WCT's physical validity without a corresponding physical derivation or experiment.

**Constructive scope rule:** an impossibility result excludes only its quantified model class. When a route fails, identify the exact assumption or formulation excluded, what wider hypotheses remain open, and the next meaningful proof, model construction or empirical test. Do not invent a successful alternative or conceal a genuine broad failure. See the [repository-wide research-direction policy](RESEARCH_DIRECTION.md) and [problem research workflow](reyes-problem-repository/WORKFLOW.md).

## Selected mathematical results

The table is a starting point, not an exhaustive list. Each link opens an individual compiled manuscript; the [catalogue](CONTENTS.md) links every manuscript to its PDF, LaTeX source, and notes.

| Area | Result and precise scope | Manuscript PDFs |
| :--- | :--- | :--- |
| **Fourth-order variational PDE** | Strict binding, minimizer existence, and orbital stability for a focusing-cubic/defocusing-quintic Hamiltonian on ℝ², within an explicit sufficient mass range. | [Strict binding](preprints/strict-subadditivity-fourth-order-cubic-quintic/paper.pdf) · [Existence](preprints/whole-space-fourth-order-cubic-quintic-minimizers/paper.pdf) · [Stability](preprints/orbital-stability-fourth-order-cubic-quintic/paper.pdf) |
| **Higher-derivative fields** | Constraint counting in a specified nonzero fixed-background complex-scalar sector; a separate linear homogeneous-sector ultraviolet Sobolev obstruction. | [Constraint analysis](preprints/s004-complex-scalar-constraint-count/paper.pdf) · [UV obstruction](preprints/uv-sobolev-ill-posedness-fourth-order-wave/paper.pdf) |
| **Scalar-gradient geometry (F08)** | A real-part scalar-gradient Gram tensor has rank at most two and is positive semidefinite; by itself, it cannot produce a Lorentzian metric. | [Rank and signature proof](preprints/scalar-gradient-lorentzian-no-go/paper.pdf) |
| **Spectral inverse problems (F09)** | Any 11 × 31 sensitivity matrix has nullity at least 20. This is a linearized local identifiability bound, not a global inverse theorem. | [Identifiability proof](preprints/sm-v18-local-identifiability-obstruction/paper.pdf) |
| **Fourier-band selection (E16)** | Exact linear modal-power evolution and conditional spectral concentration near the preferred shell, with additional hypotheses for dominant-wavenumber convergence. | [Spectral concentration proof](preprints/e16-linear-spectral-concentration/paper.pdf) |
| **Fourier projection (E59)** | A fixed sharp annulus mask defines an orthogonal L² projection satisfying P² = P, with exact energy decomposition and best approximation. | [Dominant-annulus projection](preprints/e59-dominant-annulus-projection/paper.pdf) |
| **Geometric phase locking (F07)** | Exact weighted closed-loop energy minimum at fixed winding and geometry, including its equality condition. | [Phase-locking proof](preprints/weighted-closed-loop-phase-locking/paper.pdf) |
| **Whole-space Fourier spectra (F10)** | An L² function supported in Fourier space on a measure-zero isolated frequency shell must vanish. | [Fourier-shell proof](preprints/isolated-fourier-shell-no-l2-bound-state/paper.pdf) |
| **Curvature energy and local estimates** | Whole-space nonattainment for a positive curvature energy; separate counterexamples and corrected hypotheses for localized-energy bounds. | [Nonattainment](preprints/positive-curvature-whole-space-nonattainment/paper.pdf) · [Localized estimates (E68)](preprints/localized-gradient-energy-e68/paper.pdf) |

The scalar-gradient tensor in the F08 result is, for a complex scalar field:

$$
T_{\mu\nu} = \mathrm{Re}\!\left( \partial_\mu \overline{\psi}\,\partial_\nu \psi \right).
$$

The rank and signature obstruction applies to this **specific positive-sign construction**, not to every possible metric built using scalar fields. Constructing a consistent alternative remains an open research task, not a presumed solution.

## Research map

| Family | Subject | Contents |
| --- | --- | --- |
| **F01** | Fourth-order variational PDE | Negative trial energy, strict binding, minimizers, orbital stability |
| **F02** | Higher-derivative fields | Canonical constraints and ultraviolet ill-posedness |
| **F03** | Spectral–phase geometry | Weighted curvature identity and counterexample |
| **F04** | Finite-mode dynamics | Failure of finite Fourier-subspace invariance under an unprojected nonlinear flow |
| **F05** | Curvature energy | Positive-energy whole-space nonattainment |
| **F06** | Dispersion | Exact positive-wavenumber minimum under stated parameter conditions |
| **F07** | Phase locking | Sharp closed-loop variational minimum |
| **F08** | Scalar-gradient tensors | Rank and Lorentzian-signature obstructions |
| **F09** | Spectral inverse problems | Structural matrix-nullity and local identifiability bounds |
| **F10** | Fourier localization | Nonexistence of nonzero L² states on an isolated spectral shell |
| **F11** | Fourier-band dynamics | E13/E14 gradient flow, E16 spectral selection, E59 fixed-annulus projection, E62 spectral fraction |
| **F12** | Curvature multipliers | Conditional E26 estimate for the historical additive denominator |

**Additional WCT operator results** include M2/E17 regularization, E18 Lyapunov descent, E58 resolvent bounds, E61 instability threshold, E69 curvature regularity, M3/E57 shell damping, M6B nonuniqueness, and E68 localized estimates. See the [complete catalogue](CONTENTS.md) for links and precise assumptions.

## Verification and reproducibility

Each manuscript has a separate proof and source. The [Lean project](lean/README.md) records which supporting statements have been formalized; **a successful Lean build does not certify every theorem in the PDFs**.

| Evidence | What it establishes |
| --- | --- |
| **Analytical manuscript** | A written mathematical argument under its specified definitions and assumptions; subject to independent mathematical review |
| **Lean formalization** | Kernel checking of the *exact declarations encoded in Lean*, which may be narrower than the corresponding manuscript |
| **Executable or numerical check** | A computational check of a stated instance or model; not a general analytic proof |
| **Physical interpretation** | An additional hypothesis or application, requiring its own mathematical and empirical justification |

**Formalization coverage:** the [per-family manifest](lean/formalization.yaml) marks **F01–F12** complete at the stated manuscript scope. These include strict binding, minimizer existence, global H² flow and orbital stability (F01); ultraviolet ill-posedness and specified S004 constraints (F02); spectral–phase identities (F03); nonlinear Fourier-mode leakage (F04); curvature-energy nonattainment (F05); dispersion minimization (F06); phase locking (F07); the global scalar-gradient tensor obstruction (F08); spectral parameter identifiability and local level-set geometry (F09); canonical whole-space L² Fourier-shell exclusion, including the manuscript's stated corollaries (F10); the E13/E14 gradient flow, E16 spectral concentration, E59 annulus projection and E62 spectral fraction (F11); and the conditional E26 estimate with its counterexample (F12). The F08/F10 integrations have corresponding merged, Lean-tested source PRs [#25](https://github.com/rickyjreyes/math/pull/25) and [#26](https://github.com/rickyjreyes/math/pull/26). These statements are formalized **only under their exact declared assumptions**.

**Verified inventory:** 173 project modules, 3,119 theorem/lemma source declarations (including private lemmas), and **14 of the 14 original manuscripts complete**. Beyond the original fourteen, all five F11/F12 manuscripts are complete, as are the supplementary M2/E17, E58, E61, M3/E57, M6B, E68, E69 and E18 manuscripts. The [fourteen-result review](docs/FORMALIZATION_REVIEW_2026-10-27.md) separates declaration counts from manuscript completeness and records the passing verification runs. The [analytic certification](docs/ANALYTIC_CERTIFICATION_2026-10-30.md) covers E62, E58, M2/E17, E26, M3/E57, E61, E16 and the F11 companions. It gives a correspondence table and an axiom audit for each manuscript. The [E68 mapping](docs/E68_LEAN_MANUSCRIPT_MAPPING.md) does the same for the localized gradient-energy manuscript, over `H¹(ℝⁿ)` and `H²(ℝⁿ)` defined by weak derivatives. The [E69 mapping](docs/E69_LEAN_MANUSCRIPT_MAPPING.md) does the same for the bounded-curvature manuscript, over the Fourier-defined `H^s(ℝⁿ)` of every real order. The [E18 mapping](docs/E18_LEAN_MANUSCRIPT_MAPPING.md) does the same for the Lyapunov-descent manuscript, over the Fourier space `H²(𝕋^d)`, `d ≤ 3`: the Fréchet derivative of the nonlinear energy, its `L²` representative on `H⁴`, and the exact dissipation identity, conditional on a given regular solution as in the manuscript.

**F09 completion:** [PR #51](https://github.com/rickyjreyes/math/pull/51) establishes the [actual middle determinant enclosure](lean/MathProofs/V18MiddleDeterminant.lean), the [complete Fréchet derivative](lean/MathProofs/V18Frechet.lean), and [rank 11 with nullity 20](lean/MathProofs/V18Rank.lean) for the original clipped 31-parameter observation map. Every entry of its selected 3+5+3 block is identified, including the cross-sector entries. [The completion theorem](lean/MathProofs/V18Identifiability.lean) provides a C¹ chart with C¹ inverse, identifies the local fiber with a twenty-dimensional slice, and proves nonlinear local non-identifiability. It uses the published exact-decimal coefficients, `alpha ∈ [5.172,5.173]`, and frozen `epsilon = 5`, in the open ambient parameter space. The [source-pinned external certificates](docs/SM_V18_ANALYTIC_RANK_CERTIFICATE.md) remain independent regression checks and supply no Lean assumptions. The full Lean build, focused F09 build, both certificate workflows, PDF build, and M6B regression workflow passed on the completion revision.

**Supplementary manuscripts:** all eight are complete in Lean. The last, E18 (exact Lyapunov descent along the specified negative-gradient flow), is conditional on an existing regular solution, exactly as stated in the manuscript; no existence or physical-dynamics claim is formalized or made.

To reproduce the PDF compilation (with a compatible LaTeX installation) and the Lean build:

```bash
git clone https://github.com/rickyjreyes/math.git
cd math

# Build manuscript PDFs and overview
bash scripts/build_pdfs.sh

# Check Lean declarations
cd lean
lake update
lake exe cache get
lake build
```

GitHub Actions also runs the [PDF compilation workflow](.github/workflows/pdfs.yml) and [Lean checking workflow](.github/workflows/lean.yml). The PDF workflow publishes compiled manuscripts under `preprints/` after a successful main-branch run.

## Scope and prior work

- **Model separation and research direction:** The F01 Hamiltonian is studied as an independent mathematical model. Its results do not establish a derivation from a ghost-free parent field theory. Establishing or ruling out a consistent parent construction remains a research target, not a declaration that the wider program is abandoned.
- **Dimensional notation:** “D4” in the corresponding variational analyses denotes **square symmetry in two spatial dimensions**; it is not a theorem about lifetimes in four spatial dimensions.
- **Operator versions:** E26 concerns a historical additive-denominator curvature operator under a uniform separation hypothesis. M2/E17 analyzes a different, corrected phase-covariant regularization.
- **Earlier literature:** For the related single-power fourth-order problem, see Fernández, Jeanjean, Mandel and Mariş, *Journal of Differential Equations* **330** (2022), [doi:10.1016/j.jde.2022.04.037](https://doi.org/10.1016/j.jde.2022.04.037). The combined cubic–quintic results should be read with this distinction in mind.

These are **research manuscripts, not peer-reviewed publications by virtue of appearing here**. Claims of mathematical validity, formal verification, novelty, and physical applicability require separate evaluation.

## Citation and review

Cite the **specific manuscript and Git revision**, rather than treating the entire repository as a single theorem or publication. See [citation metadata](CITATION.cff) and [version history](history.md). Corrections, counterexamples, reproduction reports, and priority references are welcome via [GitHub Issues](https://github.com/rickyjreyes/math/issues).
