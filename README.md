# Mathematical Manuscripts and Formal Proof Artifacts

**Richard J. Reyes** · Independent Researcher

A collection of mathematical manuscripts on **fourth-order partial differential equations, spectral dynamics, variational analysis, geometric constraints, and nonlinear operators**. The emphasis is on explicit hypotheses, self-contained arguments, counterexamples where claims fail, and reproducible source material.

Results are organized by mathematical subject rather than by a single overarching physical interpretation. **Analytical proofs, Lean-checked statements, and physical claims are distinct levels of evidence.**

**Explore:** [Complete manuscript catalogue](CONTENTS.md) · [Compiled PDFs](preprints/) · [Overview](overview.pdf) · [Lean formalization status](lean/formalization.yaml) · [Revision history](history.md)

## Selected mathematical results

The table is a starting point, not an exhaustive list. Each link opens an individual compiled manuscript; the [catalogue](CONTENTS.md) links every manuscript to its PDF, LaTeX source, and notes.

| Area | Result and precise scope | Proof |
| --- | --- | --- |
| **Fourth-order variational PDE** | Strict binding, minimizer existence, and orbital stability for a focusing-cubic/defocusing-quintic Hamiltonian on $\mathbb R^2$, within a stated sufficient mass range. | [Strict binding](preprints/strict-subadditivity-fourth-order-cubic-quintic/paper.pdf) · [Existence](preprints/whole-space-fourth-order-cubic-quintic-minimizers/paper.pdf) · [Stability](preprints/orbital-stability-fourth-order-cubic-quintic/paper.pdf) |
| **Higher-derivative fields** | Constraint counting for a specified nonzero fixed-background complex-scalar sector; a separate linear homogeneous-sector ultraviolet Sobolev obstruction. | [Constraint analysis](preprints/s004-complex-scalar-constraint-count/paper.pdf) · [UV obstruction](preprints/uv-sobolev-ill-posedness-fourth-order-wave/paper.pdf) |
| **Scalar-gradient geometry** | The tensor $T_{\mu\nu}=\operatorname{Re}(\partial_\mu\psi^*\partial_\nu\psi)$ has rank at most two and is positive semidefinite, so this construction alone cannot yield a Lorentzian metric. | [Rank and signature proof](preprints/scalar-gradient-lorentzian-no-go/paper.pdf) |
| **Spectral inverse problems** | An $11\times31$ sensitivity matrix has kernel dimension at least 20: a structural *linearized local* identifiability obstruction, not a global inverse theorem. | [Identifiability proof](preprints/sm-v18-local-identifiability-obstruction/paper.pdf) |
| **Fourier-band selection (E16)** | Exact linear modal-power evolution; normalized concentration near the preferred shell when that shell is present in the initial spectral support, with additional hypotheses for pointwise argmax convergence. | [Spectral concentration proof](preprints/e16-linear-spectral-concentration/paper.pdf) |
| **Fourier projection (E59)** | A fixed sharp annulus mask defines an orthogonal $L^2$ projection: $P^2=P$, with exact energy decomposition and best approximation. | [Dominant-annulus projection](preprints/e59-dominant-annulus-projection/paper.pdf) |
| **Geometric phase locking** | Exact weighted closed-loop energy minimum at fixed winding and geometry, including the equality condition. | [Phase-locking proof](preprints/weighted-closed-loop-phase-locking/paper.pdf) |
| **Whole-space Fourier spectra** | A nonzero $L^2$ function cannot have Fourier support confined to a measure-zero frequency shell. | [Fourier-shell proof](preprints/isolated-fourier-shell-no-l2-bound-state/paper.pdf) |
| **Curvature energy and local estimates** | Whole-space nonattainment for a positive curvature energy; separate counterexamples and corrected hypotheses for localized energy bounds. | [Nonattainment](preprints/positive-curvature-whole-space-nonattainment/paper.pdf) · [Localized estimates (E68)](preprints/localized-gradient-energy-e68/paper.pdf) |

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
| **F10** | Fourier localization | Nonexistence of nonzero $L^2$ states on an isolated spectral shell |
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

Lean-checked mathematical results include whole-space strict binding, negative energy, minimizer attainment and compactness modulo translations, global H² well-posedness of the flow and orbital stability of the full minimizing set (F01); ultraviolet Sobolev ill-posedness and S004 constraints (F02); continuous spectral–phase identities (F03); finite Fourier leakage with local classical torus well-posedness (F04); curvature nonattainment and spreading (F05); a positive-wavenumber dispersion minimum (F06); and weighted phase locking (F07). The original main-line supporting Lean modules and compendium are preserved. [An additional source-pinned interval certificate](docs/SM_V18_ANALYTIC_RANK_CERTIFICATE.md) verifies rank 11 and nullity 20 of the frozen model's analytic Jacobian; it is not a Lean-kernel proof. The global manifold scalar-tensor obstruction (F08) and complete F10 source are now in the maintained Lean build. F09's frozen 31-parameter Jacobian certificate remains outside Lean. F10's imported module requires CI on this combined revision. Refer to the [per-family manifest](lean/formalization.yaml) for precise coverage.

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

- **Model separation:** The F01 Hamiltonian is studied as an independent mathematical model. Its results do not establish a derivation from a ghost-free parent field theory.
- **Dimensional notation:** “D4” in the corresponding variational analyses denotes **square symmetry in two spatial dimensions**; it is not a theorem about lifetimes in four spatial dimensions.
- **Operator versions:** E26 concerns a historical additive-denominator curvature operator under a uniform separation hypothesis. M2/E17 analyzes a different, corrected phase-covariant regularization.
- **Earlier literature:** For the related single-power fourth-order problem, see Fernández, Jeanjean, Mandel and Mariş, *Journal of Differential Equations* **330** (2022), [doi:10.1016/j.jde.2022.04.037](https://doi.org/10.1016/j.jde.2022.04.037). The combined cubic–quintic results should be read with this distinction in mind.

These are **research manuscripts, not peer-reviewed publications by virtue of appearing here**. Claims of mathematical validity, formal verification, novelty, and physical applicability require separate evaluation.

## Citation and review

Cite the **specific manuscript and Git revision**, rather than treating the entire repository as a single theorem or publication. See [citation metadata](CITATION.cff) and [version history](history.md). Corrections, counterexamples, reproduction reports, and priority references are welcome via [GitHub Issues](https://github.com/rickyjreyes/math/issues).
