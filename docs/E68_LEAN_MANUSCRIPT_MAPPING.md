# E68: manuscript-to-Lean certification

**Issue:** [#41](https://github.com/rickyjreyes/math/issues/41) · **PR:** [#50](https://github.com/rickyjreyes/math/pull/50) · **Manuscript:** [`papers/localized-gradient-energy-e68/main.tex`](../papers/localized-gradient-energy-e68/main.tex) (unchanged).

Pinned versions: Lean 4.23.0, Mathlib v4.23.0. Entry point: [`lean/MathProofs/E68Certification.lean`](../lean/MathProofs/E68Certification.lean) (namespace `ReyesMath.E68Cert`). Dependency audit: [`lean/E68CertificationAudit.lean`](../lean/E68CertificationAudit.lean).

Every manuscript theorem, proposition, corollary and remark is a kernel-checked Lean declaration with the manuscript's quantifiers. There are no `sorry`, `admit`, new axioms or `native_decide`, and no finite-dimensional or numerical surrogate. No hypothesis is equivalent to the conclusion. All 71 audited declarations depend only on `propext`, `Classical.choice` and `Quot.sound`. No manuscript assertion was found to be false, so no correction is needed.

Reproduce:

```bash
cd lean
lake update && lake exe cache get
lake build MathProofs.E68Certification
lake env lean E68CertificationAudit.lean   # 71 lines, each: [propext, Classical.choice, Quot.sound]
lake build                                  # complete project
```

## The objects in the statements

| Manuscript object | Lean | Module |
|---|---|---|
| `ℝⁿ`, Lebesgue measure, `B_R(x₀) = {|x−x₀|<R}` | `EuclideanSpace ℝ (Fin n)`, `volume`, `Metric.ball x₀ R` | Mathlib |
| `ψ ∈ H¹(ℝⁿ)` with gradient `∇ψ` | `ReyesMath.E68.IsH1 ψ g`: `ψ ∈ L²(ℝⁿ;ℂ)`, `g ∈ L²(ℝⁿ;ℂⁿ)` and `∫ ψ ∂ᵢφ = −∫ gᵢ φ` for every coordinate `i` and every real `φ ∈ C_c^∞(ℝⁿ)` (genuine weak derivatives); `MemH1 ψ = ∃ g, IsH1 ψ g` | `E68Sobolev` |
| `‖ψ‖²_{H¹} = ‖ψ‖²₂ + ‖∇ψ‖²₂`, `|∇ψ|² = Σᵢ|∂ᵢψ|²` | `ReyesMath.E68.h1sq ψ g = ∫‖ψ‖² + ∫‖g‖²` (Euclidean norm on `ℂⁿ`) | `E68Sobolev` |
| `H¹` as equivalence classes | `ReyesMath.E68.H1 n : Set (Lp ℂ 2 volume)`, `h1Grad` (a.e.-unique weak gradient) | `E68Classification` |
| `ψ ∈ H²(ℝⁿ)`, `‖ψ‖²_{H²}` | `ReyesMath.E68.IsH2 ψ g H`: `IsH1 ψ g` and `IsH1 gᵢ (H i)` for each `i`, so `H i x j = ∂ⱼ∂ᵢψ` (all weak derivatives of order `≤ 2` in `L²`); `h2sq = ∫‖ψ‖² + ∫‖g‖² + Σᵢ ∫‖H i‖²` | `E68H2` |
| The estimate `(E68)` | `ReyesMath.E68.E68Holds n` (uniform over centers), `E68Holds0 n` (boxed form, center `0`), `E68L2Holds n` (on `L²` classes); exponent `R ^ ((n:ℤ) − 2)` | `E68Classification` |
| `ω_n = |B₁(0)|` | `volume.real (ball 0 1)` | Mathlib |
| `σ_{n−1} = |Sⁿ⁻¹|` | `ReyesMath.E68.Singular.surfaceArea n = volume.toSphere.real univ` (Mathlib's surface measure), `= n ω_n` (`surfaceArea_eq`) | `E68Singular`, `E68Radial` |

### The Sobolev bridge (`ReyesMath.E68Cert.bridge`)

| Requirement | Declaration | Module |
|---|---|---|
| Genuine weak derivatives against `C_c^∞` test functions | `IsH1.weak` (structure field) | `E68Sobolev` |
| Existence and a.e. uniqueness of the weak gradient | `IsH1.ae_eq_grad` (fundamental lemma `ae_eq_zero_of_integral_contDiff_smul_eq_zero`) | `E68Sobolev` |
| `L²` membership | `IsH1.memLp`, `IsH1.memLp_grad`, `IsH1.integrable_sq`, `IsH1.integrable_grad_sq` | `E68Sobolev` |
| Energies independent of representatives | `IsH1.congr_ae`, `h1sq_congr_ae`, `setIntegral_grad_congr_ae`; class form `e68L2_iff_e68` | `E68Sobolev`, `E68Classification` |
| Smooth inclusion, classical = weak gradient | `isH1_of_contDiff` (`C¹` compactly supported, by Mathlib integration by parts), `isH1_ofRealFn`, `norm_gradVec_ofRealFn`, `h1sq_ofRealFn`, `isH2_of_contDiff` | `E68Sobolev`, `E68H2` |
| Compatibility with `SobolevH2` | `isH1_of_H2` (every `Sobolev.H2` element is in `H¹` with its strong gradient) | `E68Sobolev` |
| Compatibility with `E26.IsWeakDeriv` | `isH1_iff_isWeakDeriv` (equivalence on `Ω = ℝⁿ`) | `E68Sobolev` |
| Compatibility with the earlier `WeakH1Field` | `WeakH1Field.isH1`, `IsH1.toWeakH1Field`, `memH1_iff_exists_weakH1Field` | `E68Sobolev` |
| Product rule with `C_c^∞` multipliers | `IsH1.smul_test` | `E68Sobolev` |

The bridge proves these facts; it does not assume them. Defining `IsH1` with a weak-gradient witness is not taken to establish any of them.

## Assertion-by-assertion mapping

All declarations are in `lean/MathProofs/`, imported by `lean/MathProofs.lean`, and checked by `.github/workflows/lean-e68.yml` (focused build, axiom audit, complete project) and `.github/workflows/lean.yml` (complete project). The verification evidence for each row is the CI listed under [Verification](#verification), and none of the rows has a remaining obstruction.

| # | Manuscript assertion | Fully qualified declaration | Hypotheses and quantifier order | Module (imports) |
|---|---|---|---|---|
| 1 | Thm 1.1: a uniform `C_n` exists iff `n = 2` (all centers) | `ReyesMath.E68Cert.classification` (`= ReyesMath.E68.e68_iff_two`) | `∀ n ≥ 1, (∃ C, ∀ ψ g, IsH1 ψ g → ∀ x₀ R, 0 < R → ∫_{B_R(x₀)}‖g‖² ≤ C R^{n−2}(∫‖ψ‖²+∫‖g‖²)) ↔ n = 2`. `C` precedes the field, center and radius. | `E68Certification` (`E68Classification`) |
| 1a | Boxed `(E68)` at center `0` | `ReyesMath.E68Cert.classification_center` (`= e68Holds0_iff_two`) | as row 1 with `x₀ = 0` | `E68Classification` |
| 1b | Same classification on genuine Sobolev classes | `ReyesMath.E68Cert.classification_L2` (`= e68L2_iff_two`) | `∀ n ≥ 1, E68L2Holds n ↔ n = 2` over `u ∈ H1 n ⊂ Lp ℂ 2` | `E68Classification` |
| 2 | `n = 2` with `C₂ = 1` | `ReyesMath.E68Cert.dimension_two`, `ReyesMath.E68.e68_two` | `∀ ψ g, IsH1 ψ g → ∀ x₀ R, ∫_{B_R(x₀)}‖g‖² ≤ 1·R⁰·h1sq ψ g` | `E68Classification` |
| 3 | `n = 1`: compact bump, `∫_{−R}^{R}|ψ'|² = A > 0` for `R ≥ 1`, no `C R⁻¹` bound | `ReyesMath.E68Cert.dimension_one`, `ReyesMath.E68.not_e68_one`, `not_e68_one_of_line` (the whole-line bump `compactOneDim`, lifted along the measure-preserving coordinate `lineEquiv`) | `0 < A`, `∀ R ≥ 1, ∫_{B_R} = A`, `¬ E68Holds0 1` | `E68Classification` (`E68OneDimEnergy`, `E68HigherDimEnergy`) |
| 4 | Singular field: cutoff `χ = 1` on `[0,1]`, `0` on `[2,∞)`, `C^∞`; `ψ = χ(|x|)|x|^{−a}` smooth off `0` | `ReyesMath.E68.Singular.chi_eq_one`, `chi_eq_zero`, `contDiff_chi`, `contDiffAt_psi`, `psi_of_le_one`, `psi_of_two_le` (packaged in `E68Cert.singular_field`) | `∀ n, ∀ a, 0 < a → a < (n−2)/2 → …`; `∀ x ≠ 0, ContDiffAt ℝ ∞ ψ x` | `E68Singular` |
| 5 | `∇ψ(x) = −a|x|^{−a−2}x` on `0 < |x| < 1` | `ReyesMath.E68.Singular.gradient_psi_of_lt_one`, `hasGradientAt_psi`, `gradC_eq_gradVec` | `∀ x, x ≠ 0 → ‖x‖ < 1 → gradient ψ x = (−a‖x‖^{−a−2}) • x`; Mathlib's `gradient` | `E68Singular` |
| 6 | `ψ, ∇ψ ∈ L²` | `ReyesMath.E68.Singular.memLp_psi`, `memLp_gradC` | majorants `|x|^{−a}1_{B̄₂}` and `(2K|x|^{1−a} + a|x|^{−a−1})1_{B̄₂}`, radial integrability (`E68Radial`) | `E68Singular` (`E68Radial`) |
| 7 | Classical derivatives are the weak derivatives across `0`; `ψ ∈ H¹` (value at `0` arbitrary) | `ReyesMath.E68.Singular.weak_deriv`, `isH1`, `isH1_update` | `∀ i φ, φ ∈ C_c^∞ → ∫ ψ∂ᵢφ = −∫ (∂ᵢψ)φ`, including `0 ∈ supp φ` | `E68Singular` |
| 8 | `∫_{B₁}|ψ|² = σ_{n−1}/(n−2a)` | `ReyesMath.E68.Singular.integral_sq_ball_one` (and `integral_sq_ball` for `0 < R ≤ 1`) | real Bochner integral; polar coordinates `setIntegral_ball_rpow` | `E68Singular` (`E68Radial`) |
| 9 | `∫_{B₁}|∇ψ|² = σ_{n−1}a²/(n−2−2a)` | `ReyesMath.E68.Singular.integral_grad_sq_ball_one` | as above | `E68Singular` |
| 10 | `∫_{B_R}|∇ψ|² = σ_{n−1}a²R^{n−2−2a}/(n−2−2a)`, `0 < R < 1` | `ReyesMath.E68.Singular.integral_grad_sq_ball_sphere` (and `integral_grad_sq_ball` for `R ≤ 1`) | `∀ R, 0 < R → R < 1 → …` | `E68Singular` |
| 11 | `R^{2−n}∫_{B_R}|∇ψ|² → +∞` as `R ↓ 0` | `ReyesMath.E68.Singular.blowup` | `Tendsto (fun R => R^{2−n} ∫_{B_R}‖∇ψ‖²) (𝓝[>] 0) atTop` | `E68Singular` |
| 12 | One fixed `H¹` field defeats every finite constant at arbitrarily small radii | `ReyesMath.E68.Singular.no_constant`, `defeats_every_constant`, `not_e68Holds0`, `not_e68` | the field is fixed first; `∀ C, ∀ ε > 0, ∃ R ∈ (0,ε), C R^{n−2}‖ψ‖²_{H¹} < ∫_{B_R}‖∇ψ‖²` | `E68Singular` |
| 13 | Prop 2.1: `∀ n > 2, ∀ C, ∃ ψ ∈ C_c^∞, R > 0` violating `(E68)` (`ψ_R = R^{1−n/2}φ(x/R)`) | `ReyesMath.E68Cert.smooth_concentration`, `ReyesMath.E68.no_uniform_E68_for_smooth_concentrations`, `smoothConcentration_gradient_energy_constant`, `smoothConcentration_mass_R_sq`, `smoothConcentration_ball_energy_eq_global` | each witness is also `IsH1` with its classical gradient | `E68Certification` (`E68SmoothCounterexample`, `E68ScaledGradient`) |
| 14 | Thm 3.1 (E68′): `n > 2`, `ψ ∈ H¹`, `∇ψ ∈ Lⁿ`: `∫_{B_R(x₀)}|∇ψ|² ≤ ω_n^{1−2/n}R^{n−2}‖∇ψ‖²_{Lⁿ}` | `ReyesMath.E68Cert.corrected` (`= ReyesMath.E68.e68_corrected`), `ball_energy_le`, `eLpNorm_ball_le` | `∀ n > 2, ∀ ψ g, IsH1 ψ g → MemLp g n → ∀ x₀ R, 0 < R → ∫_{B_R(x₀)}‖g‖² ≤ ω_n^{1−2/n} R^{n−2} (∫‖g‖ⁿ)^{2/n}`; Hölder with exponent `1/2 − 1/n` (`p = n/2`, `q = n/(n−2)` after squaring), `|B_R(x₀)| = ω_nRⁿ` (`euclidean_ball_volume_scaling`), `L²(B_R)` from `Lⁿ` on a finite ball, `2(1/2−1/n) = 1−2/n`, `n(1−2/n) = n−2` | `E68Corrected` (`E68CriticalGradient`) |
| 15 | Cor 3.2: admissible class with `‖∇ψ‖_{Lⁿ} ≤ K‖ψ‖_{H¹}` gives the constant `ω_n^{1−2/n}K²` | `ReyesMath.E68Cert.admissible` (`= e68_admissible`), `e68_apriori` | `𝒜` a set of (field, weak gradient) pairs; the bound is a hypothesis on `𝒜`, never derived from `H¹` | `E68Corrected` |
| 16 | Rem 3.3: the a priori bound does not follow from `H¹` | `ReyesMath.E68Cert.remark_3_3` (`= no_apriori_bound_on_H1`) | `∀ n > 2, ¬ ∃ K, ∀ ψ g, IsH1 ψ g → MemLp g n ∧ ‖g‖_{Lⁿ} ≤ K‖ψ‖_{H¹}`; such a `K` would give `E68(n)` | `E68Corrected` (`E68Singular`) |
| 17 | Cor 4.1: `n ∈ {3,4}`, `∀ ψ ∈ H²`: `∫_{B_R(x₀)}|∇ψ|² ≤ C_nR^{n−2}‖ψ‖²_{H²}` | `ReyesMath.E68Cert.h2_localized` (`= ReyesMath.E68.e68_H2`); `C₃ = ω₃^{1/3}·3C₃^{GNS}`, `C₄ = ω₄^{1/2}(4C₄^{GNS})²` | `∃ C, ∀ ψ g H, IsH2 ψ g H → ∀ x₀ R, 0 < R → …`; `C` precedes field, center, radius | `E68H2` |
| 17a | `n = 4`: `H¹ → L⁴` on the weak gradient | `ReyesMath.E68Cert.sobolev_four`, `ReyesMath.E68.grad_bound_four` | `‖ψ‖₄ ≤ C₄‖∇ψ‖₂` for every weak `H¹(ℝ⁴)` field; `‖∇ψ‖₄ ≤ 4C₄‖ψ‖_{H²}` | `E68SobolevEmbedding`, `E68H2` |
| 17b | `n = 3`: `H¹ → L⁶`, then `‖·‖₃ ≤ ‖·‖₂^{1/2}‖·‖₆^{1/2}` | `ReyesMath.E68Cert.sobolev_three`, `ReyesMath.E68.eLpNorm_three_le`, `grad_bound_three` | Hölder with `1/3 = 1/4 + 1/12`; `‖∇ψ‖₃ ≤ (3C₃)^{1/2}‖ψ‖_{H²}` | `E68SobolevEmbedding`, `E68H2` |
| 17c | The Sobolev embedding for weak `H¹` | `ReyesMath.E68.sobolev_H1`, `memLp_of_isH1` | `∀ n ≥ 1, 1/p* = 1/2 − 1/n → ∀ u G, IsH1 u G → ‖u‖_{p*} ≤ C_n‖G‖₂`, with `C_n` Mathlib's GNS constant | `E68SobolevEmbedding` |
| 18 | Prop 4.2: `n > 4`: no `C_n` for all `ψ ∈ C_c^∞`, all `R > 0`; `u_R = R^{2−n/2}φ(x/R)` with `‖u_R‖²₂ = R⁴‖φ‖²₂`, `‖∇u_R‖²₂ = R²‖∇φ‖²₂`, `‖D²u_R‖²₂ = ‖D²φ‖²₂` | `ReyesMath.E68Cert.h2_failure_smooth`, `h2_failure`, `h2_scaling`; `ReyesMath.E68.integral_dilateH2_sq`, `integral_gradVec_dilateH2_sq`, `integral_hess_dilateH2_sq`, connected to `high_dimensional_H2_scaling_obstruction` | actual functions and Lebesgue integrals; also refuted on all of `H²` | `E68H2` (`E68Scaling`) |
| 19 | Section 6, status and scope | rows 1–18 | editorial; no dynamical or physical claim is encoded | — |

## How the proofs go

* **Classification.** For `n = 2` the ball energy is at most the whole-space `H¹` energy. For `n = 1` the compact bump has constant ball energy for `R ≥ 1` while `C R⁻¹` tends to zero. For `n > 2`, either the smooth concentrations or the singular field gives the contradiction. All witnesses are genuine `IsH1` fields.
* **Singular field.** The field is written `ψ = F₀(|x|²)`, with `F_δ(s) = cut(s)(s + δ²)^{−a/2}` and `cut(s) = smoothTransition((4 − s)/3)`. For `δ ≠ 0` the regularizations `ψ_δ = F_δ(|x|²)` are `C^∞` with compact support, so integration by parts holds for them. Both sides of the identity converge as `δ_k = 1/(k+1) → 0` by dominated convergence, with majorants that do not depend on `δ`. The exact integrals come from Mathlib's polar decomposition `ℝⁿ∖{0} ≅ Sⁿ⁻¹ × (0,∞)` (`ReyesMath.E68.setIntegral_ball_rpow` in `E68Radial`). The manuscript's `ε`-ball boundary-term argument is replaced by this regularization argument; the proved statement is the same.
* **Sobolev embedding.** Mathlib's GNS inequality for `C¹_c` functions extends to weak `H¹` in three steps:
  1. Mollification: the classical gradient of `ρ ⋆ v` is `ρ ⋆ (weak gradient)`, from the weak identity tested against `t ↦ ρ(x − t)`. A pointwise Cauchy–Schwarz bound and `∫ ρ ⋆ h = ∫ h` give `‖∇(ρ⋆v)‖₂ ≤ ‖∇v‖₂`.
  2. Fatou's lemma along `ρ_k ⋆ v → v` a.e.
  3. Cutoffs `χ_R` with `|∇χ_R| ≤ 4K/R`, then Fatou's lemma again as `R → ∞`.

## Verification

* Local, pinned toolchain:
  * `lake build MathProofs.E68Certification`;
  * the complete project `lake build` (7370 jobs, exit 0, no warnings in E68 modules);
  * `lake env lean E68CertificationAudit.lean`, with 71 of 71 declarations on `[propext, Classical.choice, Quot.sound]`;
  * no `sorry`, `admit`, `axiom` or `native_decide` in any E68 module.
* Exact-head CI at `4d6f1fda30a2b9160deaab5c384aca7577cc8a3e`: [focused E68 workflow](https://github.com/rickyjreyes/math/actions/runs/41031962271) and [complete-project `lean.yml`](https://github.com/rickyjreyes/math/actions/runs/41031962266). Later revisions are recorded in [PR #50](https://github.com/rickyjreyes/math/pull/50) and in `lean/formalization.yaml` (`latest_fully_checked_revision`). The CI covers:
  * the focused E68 workflow (hole check, focused build, axiom audit, complete project);
  * the full `lean.yml` build;
  * the M6B, F09, analytic-cores and PDF workflows.

## Lean conventions that differ in form from the manuscript

* The singular field takes the value `0` at the origin (Lean's `0^{−a} = 0`); `isH1_update` shows that any value gives the same `H¹` field.
* `R^{n−2}` is the integer power `R ^ ((n:ℤ) − 2)`, which is `R^{−1}` for `n = 1`.
* The admissible class of Corollary 3.2 is a set of pairs (field, weak gradient), since the a priori bound is stated in terms of `∇ψ`.
* In Proposition 4.2 the manuscript takes `0 < R < 1`. The formal proof uses every `R > 0`, which is a stronger family of fields. The failure is proved at the single center `0`.

## History

Earlier checkpoints on this branch verified the components that the certificate now subsumes:
* the `n = 2` bound for `WeakH1Field` and for strong derivatives;
* the whole-line bump contradiction (`E68OneDimEnergy`);
* the smooth concentration counterexample (`E68SmoothCounterexample`, full-project CI at `087e05f8`);
* the extended-`Lp` Hölder step and the ball volume (`E68CriticalGradient`).
