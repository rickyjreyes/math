# Lean 4 formalization status

This Mathlib v4.23.0 project integrates main-line supporting modules with newer full H² manuscript formalizations and conditional bridges. All declarations must pass Lean CI on the exact revision before being called kernel-checked. Manuscript-level status (which papers are formalized end to end) is in
[formalization.yaml](formalization.yaml).

The maintained import tree contains **154 project modules and 2,794 theorem/lemma declarations** (including private source lemmas). **14 of the 14 original manuscripts are complete** under the audit criterion. So are the five F11/F12 manuscripts and the supplementary M2/E17, E58, E61, M3/E57, M6B and E68 manuscripts. Declaration totals do not measure manuscript completeness. The [review and theorem table](../docs/FORMALIZATION_REVIEW_2026-10-27.md) records exact declarations, restrictions, and passing verification runs. The [analytic certification](../docs/ANALYTIC_CERTIFICATION_2026-10-30.md) does the same for E62, E58, M2/E17, E26, M3/E57, E61, E16, E59 and E13/E14.

### Manuscript formalizations

- [PhaseLockingContinuous](MathProofs/PhaseLockingContinuous.lean) — F07, complete:
  exact continuous weighted closed-loop phase-locking minimum for `H¹` phases.
- [DispersionMinimum](MathProofs/DispersionMinimum.lean) — F06, complete: existence,
  explicit formula and uniqueness of the positive-wavenumber dispersion minimum.
- [SpectralPhaseIdentity](MathProofs/SpectralPhaseIdentity.lean) — F03, complete:
  continuous spectral–phase identity, equality case and the 4/5 counterexample.
- [S004ConstraintCount](MathProofs/S004ConstraintCount.lean) — F02, complete: canonical
  Dirac analysis and `N_conf = 4` for the regular S004 scalar.
- [UVIllPosedness](MathProofs/UVIllPosedness.lean),
  [UVWholeSpace](MathProofs/UVWholeSpace.lean) — F02, complete: ultraviolet growth and
  Sobolev ill-posedness on `𝕋^d` and `ℝ^d`.
- [FourierLeakage](MathProofs/FourierLeakage.lean),
  [FourierLeakageWellPosed](MathProofs/FourierLeakageWellPosed.lean) — F04, complete:
  instantaneous leakage, local existence and uniqueness of classical solutions on `𝕋^d`, and
  the classification `E_S` invariant iff `|S| ≤ 1`.
- [SobolevH2](MathProofs/SobolevH2.lean) — `H²(ℝ^d; ℂ)` as the Schwartz closure of
  `(φ, ∇φ, Δφ)`, Parseval on `𝓢`, the 2D Fourier sup-norm estimate, dilations.
- [NegativeEnergy](MathProofs/NegativeEnergy.lean) — F01, complete: `I(m) < 0` at every
  positive mass on `H²(ℝ²)`.
- [StrictBinding](MathProofs/StrictBinding.lean) — F01, complete: explicit strict-binding
  range `0 < m ≤ m_B` and the frozen-parameter corollary.
- [WholeSpaceMinimizers](MathProofs/WholeSpaceMinimizers.lean) — F01, complete: for
  `0 < m ≤ m_B`, every minimizing sequence has a subsequence converging strongly in `H²(ℝ²)` after translations
  (concentration–compactness with a Fourier Hölder estimate, weak compactness, weak closedness
  of `H²` and the Brezis–Lieb lemma), so minimizers exist and `𝒢_m` is compact modulo
  translations.
- [FreeEvolution](MathProofs/FreeEvolution.lean), [H2Algebra](MathProofs/H2Algebra.lean),
  [CubicQuinticFlow](MathProofs/CubicQuinticFlow.lean),
  [OrbitalStability](MathProofs/OrbitalStability.lean) — F01, complete: the free group
  `e^{-it(Δ+k²)²}` on `𝓢`, `L²` and `H²`, the `H²(ℝ²)` algebra and the cubic–quintic
  nonlinearity, global `H²(ℝ²)` well-posedness with continuous dependence and conservation of
  mass and energy (interaction-picture Picard–Lindelöf), and orbital stability of the full
  minimizing set `𝒢_m` for `0 < m ≤ m_B`, including perturbations that change the mass.
- [FourierShellL2](MathProofs/FourierShellL2.lean) — F10, full manuscript formalization:
  Plancherel on `L²`, Fourier integral agreement, essential and distributional
  shell exclusion, Helmholtz and polynomial-multiplier corollaries, and
  fixed-carrier variable-envelope wave packets, checked in the full maintained build.
- [CurvatureNonattainment](MathProofs/CurvatureNonattainment.lean) — F05, complete:
  whole-space nonattainment in every dimension and strict spreading for `1 ≤ d ≤ 4`.

### Analytic manuscript certifications

The [certification report](../docs/ANALYTIC_CERTIFICATION_2026-10-30.md) maps every theorem, proposition, corollary and mathematical remark to these declarations. [AnalyticCertificationAudit.lean](AnalyticCertificationAudit.lean) prints the axioms of all 135 declarations cited there; all use only `propext`, `Classical.choice` and `Quot.sound`.

- [TorusFourier](MathProofs/TorusFourier.lean) — F11 (E59), complete: the Fourier Hilbert basis of `L²((ℝ/Lℤ)^d)`, bounded multipliers, the fixed-annulus orthogonal projection and the discrete E62 fraction.
- [SpectralConcentration](MathProofs/SpectralConcentration.lean), [E16TorusRemark](MathProofs/E16TorusRemark.lean) — F11 (E16), complete: the mild `L²` flow of `r − aΔ − bΔ²`, the exact modal power law, shell concentration, argmax convergence with its `t^{-1/2}` rate, the radial versions, the counterexample, and the flat-torus remark.
- [E62Certification](MathProofs/E62Certification.lean) with [E62LebesgueFraction](MathProofs/E62LebesgueFraction.lean) — F11 (E62), complete: the theorem with the manuscript's coefficient normalization, the projector form, Lebesgue-measurable continuous bands and all remarks.
- [BandPassFlow](MathProofs/BandPassFlow.lean) — F11 (E13/E14), complete: the negative gradient flow on `𝕋_L^d`, `d ≤ 3`, with exact dissipation, the centred Swift–Hohenberg form and the preferred shell.
- [RegularizedCurvatureL2](MathProofs/RegularizedCurvatureL2.lean), [E26Certification](MathProofs/E26Certification.lean), [E26QuotientDomain](MathProofs/E26QuotientDomain.lean) — F12 (E26), complete: `H²(Ω)` by weak derivatives, the conditional estimate on every open set, both corollaries, the counterexample, and the quotient on its a.e. domain. Sharpness of `1/δ` is proved in addition to the manuscript.
- [FourierMultiplierL2](MathProofs/FourierMultiplierL2.lean) — shared layer: Fourier multipliers on `L²(ℝ^d)`, `H^{2k}` by Fourier weights, unbounded realizations, resolvent and spectrum.
- [E58Certification](MathProofs/E58Certification.lean), [E58GreenFunction](MathProofs/E58GreenFunction.lean) — E58, complete: the sharp resolvent norm `1/r`, coercivity, band selectivity, the periodic box, and the one-dimensional sign-changing Green function.
- [SwiftHohenbergL2](MathProofs/SwiftHohenbergL2.lean), [E61Certification](MathProofs/E61Certification.lean) — E61, complete: `L_r` on `H⁴`, `σ(L_r) = (−∞, r]`, the semigroup and its exact generator, `‖e^{tL_r}‖ = e^{rt}`, the three regimes, the annulus, the periodic box and the parameter translation.
- [E57Certification](MathProofs/E57Certification.lean) — M3/E57, complete: `(Δ + k⋆²)²` self-adjoint on `H⁴`, the unique mild solution, off-shell damping, `‖S(t)‖ = 1`, the energy identities, the gradient-flow form, the torus gap and the sign-reversal scope.
- [E17Certification](MathProofs/E17Certification.lean) with [E17Canonical](MathProofs/E17Canonical.lean), [E17GlobalBound](MathProofs/E17GlobalBound.lean) — M2/E17, complete: the corrected regularizer's positivity, analyticity, global bound, reciprocal limits, uniform and `L²` convergence, fixed-ε control, phase invariance and the node/gauge remarks.

### E68 localized gradient-energy certification

The [E68 mapping](../docs/E68_LEAN_MANUSCRIPT_MAPPING.md) maps every assertion of the manuscript to a declaration. [E68CertificationAudit.lean](E68CertificationAudit.lean) prints the axioms of its 71 declarations; all use only `propext`, `Classical.choice` and `Quot.sound`.

- [E68Sobolev](MathProofs/E68Sobolev.lean), [E68H2](MathProofs/E68H2.lean) — `H¹(ℝⁿ)` and `H²(ℝⁿ)` by weak derivatives. The weak gradient is unique a.e. and the energies are invariant under a.e. changes. Smooth fields are included with classical = weak derivatives. Compatibility with `SobolevH2`, `E26.IsWeakDeriv` and `WeakH1Field` is proved.
- [E68Classification](MathProofs/E68Classification.lean) — `E68(n) ↔ n = 2` for every `n ≥ 1`, uniformly over centers, at the center `0`, and on `L²` classes.
- [E68Radial](MathProofs/E68Radial.lean), [E68Singular](MathProofs/E68Singular.lean) — polar integrals, and the fixed singular field `χ(|x|)|x|^{-a}`: in `H¹` (weak derivative across the origin), exact ball integrals, and blow-up at small radii.
- [E68Corrected](MathProofs/E68Corrected.lean) — E68′ with `ω_n^{1−2/n}R^{n−2}`, the admissible-class corollary, and the remark that `H¹` does not give the a priori bound.
- [E68SobolevEmbedding](MathProofs/E68SobolevEmbedding.lean) — `‖u‖_{p*} ≤ C_n‖∇u‖₂` for weak `H¹` (mollification, cutoff, Mathlib's GNS inequality, Fatou).
- [E68H2](MathProofs/E68H2.lean), [E68Certification](MathProofs/E68Certification.lean) — the `H²` estimate for `n = 3, 4` (embeddings and `L²–L⁶` interpolation) and its failure for `n > 4` with exact scaling integrals; the certification interface.

### Integrated additional proofs and diagnostics

- [IntrinsicScalarMetric](MathProofs/IntrinsicScalarMetric.lean): intrinsic positive-sign tensor and frame-covariance, but not a globally smooth cotangent tensor section.
- [MinimizerNonvanishing](MathProofs/MinimizerNonvanishing.lean): quantitative quartic nonvanishing for negative-energy near-minimizers.
- [OrbitalStabilityCriterion](MathProofs/OrbitalStabilityCriterion.lean): an abstract, conditional Cazenave–Lions orbital-stability reduction; the unconditional theorem for the cubic–quintic flow is [OrbitalStability](MathProofs/OrbitalStability.lean).
- [L2FourierShellBridge](MathProofs/L2FourierShellBridge.lean): infinite-dimensional L² shell exclusion under a supplied Plancherel equivalence; the canonical transform and the broader F10 corollaries are now encoded in [FourierShellL2](MathProofs/FourierShellL2.lean).
- [Source-pinned v18 analytic Jacobian rank certificate](../docs/SM_V18_ANALYTIC_RANK_CERTIFICATE.md): reproducible interval arithmetic, not Lean.
- Original main-line modules retained: CurvatureUniformBound, PhysicalDispersionMinimum, DispersionCriticalPoint, S004DiracBracket, GaussianTrialAlgebra, VariationalBinding, ContinuousPhaseIntegral, ContinuousPhaseOptimizer, ContinuousSpectralVariance, QuinticConvolution, UVGrowthBound, UVExponentialObstruction, DispersionBranchPositivity and DispersionRealDomain.
- [CurvatureLegacy](MathProofs/CurvatureLegacy.lean) preserves earlier abstract nonattainment and curvature-weight positivity support; full H² results are in CurvatureNonattainment.

- [ManifoldScalarMetric](MathProofs/ManifoldScalarMetric.lean) — full F08 global scalar-gradient manifold tensor and smooth tangent-bundle obstruction: actual mfderiv, bilinear form, positivity, nullity, det=0, covariance and nonnegative multiplets (CI passed).
- [L2Fourier](MathProofs/L2Fourier.lean) — canonical L² Fourier from Schwartz density and Plancherel, plus exact-shell exclusion (kernel-checked together with the F10 corollaries).
- [ExactSensitivityNullity](MathProofs/ExactSensitivityNullity.lean) — conditional exact-nullity-20 corollary for a full-row-rank 31-to-11 derivative (CI passed). The concrete frozen-v18 hypotheses are discharged by [V18Rank](MathProofs/V18Rank.lean).

### Frozen v18 F09 complete theorem chain

- [V18LightJacobian](MathProofs/V18LightJacobian.lean): exact nonzero source light 3×3 minor.
- [V18HeavyJacobian](MathProofs/V18HeavyJacobian.lean): positive heavy 3×3 minor with rational π bounds.
- [V18BlockJacobian](MathProofs/V18BlockJacobian.lean): generic lower-block-triangular determinant factorization.
- [V18MiddleDerivatives](MathProofs/V18MiddleDerivatives.lean): analytically derives all five selected derivatives of the frozen middle predictor, identifies their matrix entries.
- [V18MiddleJacobian](MathProofs/V18MiddleJacobian.lean): source-specific 5×5 real trigonometric matrix. [V18MiddleDeterminant](MathProofs/V18MiddleDeterminant.lean) proves `18000000 < middle.det < 24000000` using [V18MiddleEnclosures](MathProofs/V18MiddleEnclosures.lean) and [V18Interval](MathProofs/V18Interval.lean).
- [V18FullForward](MathProofs/V18FullForward.lean): all 31 real parameters, including both variable middle frequencies; its actual Jacobian and the model-specific structural nullity theorem.
- [V18MiddleFloor](MathProofs/V18MiddleFloor.lean), [V18MiddleClipped](MathProofs/V18MiddleClipped.lean): strict floor inactivity for all five frozen middle observations, and derivatives of the clipped outputs in all seven middle coordinate directions.

- [V18BranchBounds](MathProofs/V18BranchBounds.lean) and [V18Regularity](MathProofs/V18Regularity.lean): verified light/heavy clipping branches and C¹ neighborhood regularity of the original clipped map.
- [V18Frechet](MathProofs/V18Frechet.lean): explicit Fréchet derivative throughout a neighborhood, retaining all 31 parameter dependencies.
- [V18SelectedJacobian](MathProofs/V18SelectedJacobian.lean) and [V18Rank](MathProofs/V18Rank.lean): all 121 entries of the selected 3+5+3 restriction, its nonzero determinant, actual derivative rank 11, nullity 20, and surjectivity.
- [LocalLevelSet](MathProofs/LocalLevelSet.lean): the general conditional C¹ level-set theorem, a C¹ ambient chart with C¹ inverse, and exact local-fiber image.
- [V18Identifiability](MathProofs/V18Identifiability.lean): `ReyesMath.V18Forward.f09_completion` connects the complete proof chain for `alpha ∈ [5.172,5.173]` and frozen `epsilon = 5`. `observed_locally_nonidentifiable` supplies a distinct equal-output point in every ambient neighborhood.

All three F09 obligations are discharged for the actual exact-decimal real model. The geometry concerns an open ambient parameter domain; it does not classify distant fibers or identify the constrained optimizer box with a manifold. External certificates remain independent regression checks. The [signature and dependency audit](F09Audit.lean) prints the exported statements and their axioms; the audited declarations use only `propext`, `Classical.choice`, and `Quot.sound`.

### Supporting modules

- [Elementary](MathProofs/Elementary.lean) — original elementary algebra.
- [Structural](MathProofs/Structural.lean) — an **actual 11 × 31 matrix**
  kernel-dimension bound; n-dimensional scalar-gradient Gram rank ≤ 2
  and positive semidefiniteness; one-dimensional Fourier cutoff arithmetic;
  a finite weighted-variance identity and inequality.
- [PhaseLocking](MathProofs/PhaseLocking.lean) — finite-sum weighted
  Cauchy–Schwarz phase mismatch lower bound.
- [FourierSupport](MathProofs/FourierSupport.lean) — a.e. zero from
  support on a null set, including the 1D two-point Fourier shell.
- [PhaseMinimizer](MathProofs/PhaseMinimizer.lean) — exact discrete
  weighted phase remainder and sharp gap.
- [StructuralExtensions](MathProofs/StructuralExtensions.lean) — general
  rectangular nullity, arbitrary-carrier Gram rank and positivity,
  and coordinatewise multimode frequency escape in ℤ^d.
- [ModelAlgebra](MathProofs/ModelAlgebra.lean) — S004 acceleration Hessian
  determinant/nondegeneracy and exact dispersion discriminant identity.
- [DispersionMinimizer](MathProofs/DispersionMinimizer.lean) — conditional
  stationary-minimum uniqueness from a rigorous supporting-tangent identity.
- [UVDispersion](MathProofs/UVDispersion.lean) — both exact complex
  characteristic roots; no high-frequency Sobolev growth theorem.
- [LocalIdentifiability](MathProofs/LocalIdentifiability.lean) —
  local derivative-nullity obstruction for arbitrary differentiable
  maps from 31 to 11 real coordinates.
- [ComplexMetric](MathProofs/ComplexMetric.lean) — exact complex
  gradient tensor-to-Gram identity and 4D rank bound.
- [SphereNull](MathProofs/SphereNull.lean) — null Fourier shell and
  zero-a.e. Fourier representative in arbitrary positive Euclidean dimension.
- [ScalarGradientFields](MathProofs/ScalarGradientFields.lean) — rank and
  positive-sign quadratic obstruction using actual Fréchet derivatives of a complex scalar.
- [ChartedScalarMetric](MathProofs/ChartedScalarMetric.lean) — pointwise
  rank/signature obstruction for fields on arbitrary four-coordinate charted spaces.
- [MetricQuadratic](MathProofs/MetricQuadratic.lean) — explicit equality of
  matrix contraction with the directional-derivative sum of squares.
- [SchwartzShell](MathProofs/SchwartzShell.lean) — complete shell-exclusion
  proof for Schwartz-class fields using the actual invertible Fourier transform.

For precise statements and manuscript coverage, see
[formalization.yaml](formalization.yaml).
The build also rejects `sorry`, `admit`, and local `axiom`
declarations. A green check certifies the declarations in these files,
not conclusions from the PDF manuscripts that are not encoded.

## Build

```bash
cd lean
lake update
lake exe cache get
lake build

# Optional focused F09 build and exported-signature/dependency audit
lake build MathProofs.V18Identifiability
lake env lean F09Audit.lean

# Dependency audit of the analytic manuscript certifications
lake env lean AnalyticCertificationAudit.lean

# Dependency audit of the E68 certification
lake env lean E68CertificationAudit.lean
```

Lean and Mathlib release are pinned to v4.23.0. A dependency lockfile
is not yet committed.

## Gaps

All fourteen original manuscripts are complete under the manifest's criterion, and so are the additional families F11 and F12. Of the supplementary operator manuscripts, M2/E17, E58, E61, M3/E57, M6B and E68 are complete. E18 and E69 remain analytic only.

The F08 obstruction on a smooth four-manifold is fully formalized for an actual global complex scalar, including its covariant fiberwise tensor, nonnegativity, rank/nullity, determinant, pullback covariance, and continuous/C^m tangent-bundle evaluation. The F09 exact determinant, complete clipped derivative, rank, nullity, and C¹ local fiber are now proved together in Lean.

Separate research-grade Lean work lives in [wct-lean](https://github.com/rickyjreyes/wct-lean);
do not conflate its theorem count with this repository.

The canonical `L²` transform is in [L2Fourier](MathProofs/L2Fourier.lean). The complete F10 distributional Helmholtz, polynomial-dispersion and envelope-scale wavepacket statements are in [FourierShellL2](MathProofs/FourierShellL2.lean), checked in the maintained build.

## Completion criterion for each of the 14 tweets

The boolean `main_theorem_formalized` (per manuscript, and per family) stays false until the
**entire theorem as stated in its PDF** is a precise exported Lean declaration
with no `sorry`, `admit`, new axioms, unproved assumptions, or finite surrogate
used in place of the stated infinite-dimensional result. Supporting finite
models, algebraic identities, and theorems with stronger extra assumptions
never count as end-to-end certification of the manuscript.
