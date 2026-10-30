# Analytic manuscript certification — 2026-10-30

This review certifies seven analytic manuscripts and the two F11 companions:

- **The seven:** E62, E58, M2/E17, E26, M3/E57, E61 and E16.
- **The companions:** E13/E14 and E59.

Each one is kernel-checked in Lean 4.23.0 / Mathlib 4.23.0. "Certified" means that every theorem, proposition, corollary and lemma in the manuscript is an exported Lean declaration. The same holds for every remark that makes a mathematical assertion. Each declaration is stated for the manuscript's actual objects:

- the unitary Fourier transform on `L²(ℝ^d)`;
- Sobolev spaces `H^{2k}` defined by Fourier weights, or by weak derivatives on open sets;
- unbounded operators with their natural domains;
- the Fourier basis of `L²` of the flat torus.

The declarations use the manuscript's hypotheses, with no finite-mode or numerical surrogate. They are proved without `sorry`, `admit`, `native_decide`, new axioms or unproved central assumptions.

A passing build proves the encoded propositions; the tables below record how each one matches the manuscript text. This document does not claim peer review, physical applicability or any statement the manuscripts themselves disclaim.

## Completion

The categories are:

- **Proved** — every statement holds as written, under the manuscript's hypotheses.
- **Corrected** — a statement was false as written and was replaced by the narrowest true version.
- **Refuted** — a statement is false and a counterexample is formalized.

| Manuscript | Issue | Proved | Corrected | Refuted | Unresolved |
| --- | --- | --- | --- | --- | --- |
| [E62 spectral energy fraction](../papers/spectral-energy-concentration-e62/main.tex) | [#34](https://github.com/rickyjreyes/math/issues/34) | Theorem, proposition, all four remarks | none | none | none |
| [E58 band-selective Green multiplier](../papers/band-selective-green-kernel-bound/main.tex) | [#38](https://github.com/rickyjreyes/math/issues/38) | Theorem, proposition, remark, Sections 4–7 | none | none | none |
| [M2/E17 corrected curvature regularizer](../papers/regularized-curvature-operator/main.tex) | [#36](https://github.com/rickyjreyes/math/issues/36) | Theorem (all five parts), both corollaries, proposition, all four remarks | none | none | none |
| [E26 conditional curvature L² bound](../papers/regularized-curvature-l2-bound/main.tex) | [#35](https://github.com/rickyjreyes/math/issues/35) | Theorem, both corollaries, remark, counterexample, corrected-multiplier section, scope statement | none | none | none |
| [M3/E57 Fourier-shell damping](../papers/swift-hohenberg-fourier-shell-damping/main.tex) | [#43](https://github.com/rickyjreyes/math/issues/43) | Theorem (i)–(iv), both corollaries, all three propositions, all three remarks | none | none | none |
| [E61 continuum spectral threshold](../papers/e61-pattern-formation-threshold/main.tex) | [#39](https://github.com/rickyjreyes/math/issues/39) | Theorem (all three cases), all three propositions, remark | none | none | none |
| [E16 linear spectral concentration](../papers/e16-linear-spectral-concentration/main.tex) | [#32](https://github.com/rickyjreyes/math/issues/32) | Two theorems, lemma, both corollaries, both propositions, both remarks | none | none | none |
| [E59 dominant-annulus projection](../papers/e59-dominant-annulus-projection/main.tex) (F11) | — | Theorem, both mathematical remarks | none | none | none (see the scope note below) |
| [E13/E14 band-pass gradient flow](../papers/band-pass-amplitude-negative-gradient-flow/main.tex) (F11) | — | E13 theorem, normalization, centred form, preferred shell, β > 0 corollary, E14 companion | none | none | none |

Several manuscripts contain their own counterexamples, all of which are formalized:

- E26's `x² − ε` example;
- E16's failure without spectral access;
- M2/E17's failure of the historical denominator;
- E58's sign-changing Green function.

These are statements made *by* the manuscripts, not refutations *of* them. No manuscript theorem was found to be false, so no manuscript text was changed.

**Scope note for E59.** The remark "Adaptive selections and nonlinear evolution" says that re-selecting the annulus from each input "need not be idempotent" and that a projection gives no PDE invariance. It names no selection rule, so it states no precise proposition and is not encoded. Every other mathematical assertion in E59 is encoded.

## Verification evidence

**Revision.** The Lean library content was verified at `a9a5c32f86c6d417c24fedd9863e2f9b0402d009` (pull request [#68](https://github.com/rickyjreyes/math/pull/68)). Every check on that commit passed:

| Workflow | Run | Result |
| --- | --- | --- |
| Full library build, all 136 modules (`lean.yml`) | [40994056837](https://github.com/rickyjreyes/math/actions/runs/40994056837) | success |
| Focused analytic cores (`lean-analytic-cores.yml`) | [40994057031](https://github.com/rickyjreyes/math/actions/runs/40994057031) | success |
| M6B regression (`lean-m6b.yml`) | [40994056871](https://github.com/rickyjreyes/math/actions/runs/40994056871) | success |
| F09 source verification (`f09-derivative-ci.yml`) | [40994056958](https://github.com/rickyjreyes/math/actions/runs/40994056958) | success |
| PDF build (`pdfs.yml`) | [40994057085](https://github.com/rickyjreyes/math/actions/runs/40994057085) | success |

The commit that adds this report also adds the audit below to the focused workflow, so the axiom check now runs on every pull request. `lean/formalization.yaml` records the latest fully checked revision and its runs.

**Axiom audit.** [`lean/AnalyticCertificationAudit.lean`](../lean/AnalyticCertificationAudit.lean) prints `#print axioms` for 103 exported main declarations, covering every row of the tables below. Each one depends only on `propext`, `Classical.choice` and `Quot.sound`. In particular:

- no declaration depends on `sorryAx`, so none uses `sorry` or `admit`;
- none depends on `Lean.ofReduceBool`, so none uses `native_decide`;
- none depends on a project axiom.

To reproduce, run this after building the imported modules:

```bash
cd lean
lake env lean AnalyticCertificationAudit.lean
```

**Source scan.** No file in `lean/MathProofs/` contains the words `sorry`, `admit`, `native_decide` or `sorryAx`, or an `axiom` declaration.

**Inventory.** The library now has 136 project modules and 2,522 theorem/lemma source declarations, including private lemmas. The count is `grep -cE '^(@\[[^]]*\] )?(private |protected )?(theorem|lemma) '` over `lean/MathProofs/*.lean`. It is an inventory, not a count of distinct results.

## Shared Lean objects

- **Fourier transform.** `Sobolev.FU` is the unitary transform `û(ξ) = (2π)^{-d/2} ∫ e^{-ix·ξ} u(x) dx` on `L²(ℝ^d) = Lp ℂ 2 volume` over `EuclideanSpace ℝ (Fin d)`. It is the Plancherel extension used by F10.
- **Sobolev scale.** `FMult.InH k u` means `(1 + |ξ|²)^k û ∈ L²`, so `InH k` is `H^{2k}(ℝ^d)`; `FMult.Hdom k` is the corresponding submodule.
- **Unbounded multipliers.** `FMult.pmulOp k m` is the maximal multiplication operator `𝓕⁻¹ M_m 𝓕` as a `LinearPMap` with domain `H^{2k}`. `FMult.fmul m` is the bounded multiplier.
- **Spectrum.** `FMult.uspectrum T` is the complement of the resolvent set. A point `z` is resolvent iff some bounded `R` satisfies `(z − T)R = I` on `L²` and `R(z − T) = I` on `D(T)`.
- **Swift–Hohenberg operators.** These are defined in `SH`:
  - `Aop = (Δ + k⋆²)²` and `Lr = r − a(Δ + k⋆²)²` on `H⁴`;
  - `Bop = Δ + k⋆²` on `H²`;
  - the semigroup `Sr t = 𝓕⁻¹ e^{tλ_r} 𝓕`;
  - `IsMildSH`, the `C([0,∞); L²)` mild solution, where `∫₀ᵗ u ∈ H⁴` and `L_r ∫₀ᵗ u = u(t) − u₀`.
- **Weak derivatives on open sets.** For E26 and M2/E17, `E26.MemH2 Ω ψ` uses weak derivatives of order at most 2 in `L²(Ω)`, tested against `C_c^∞(Ω)`. `E26.IsWeakLaplacian Ω ψ F` means `∫_Ω (Δφ)ψ = ∫_Ω φF` for every test function `φ`.
- **Flat torus.** `TorusL2` provides the Fourier Hilbert basis of `L²((ℝ/Lℤ)^d)`, its coefficients, Parseval, and bounded multipliers.

## Correspondence tables

All declarations are in namespace `ReyesMath`.

### E62 — `MathProofs/E62Certification.lean`

| Manuscript item | Lean declaration | Notes |
| --- | --- | --- |
| Theorem E62: η well defined, `0 ≤ η ≤ 1`, both equality cases | `E62Cert.theorem_e62` (also `TorusL2.e62`) | On `𝕋^d = (ℝ/2πℤ)^d` with `Â_k = (2π)^{-d}∫A e^{-ik·x} dx`. Includes Parseval in `L²(dx)`, `E_tot = E⋆ + E_out` and `0 < E_tot`, for an arbitrary `𝒜⋆ ⊆ ℤ^d`. |
| Remark (sharpness) | `E62Cert.sharpness`, `E62Cert.basis_eq_mode` | `e_p` is the function `x ↦ e^{ip·x}` as an element of `L²`. |
| Projector proof | `E62Cert.projector`, `E62Cert.projector_physical` | `P⋆` is the orthogonal projection onto its range, with `η = ‖P⋆A‖²/‖A‖²`, Pythagoras and both endpoint cases; the physical-norm version is included. |
| Proposition (continuous spectrum) | `E62Cert.continuous_spectrum`; `E62LebesgueFraction.fraction_bounds`, `fraction_zero_iff`, `fraction_one_iff` | For Lebesgue (null-)measurable `ℬ ⊆ ℝ^d`, with both a.e. equality conditions. |
| Remark (zero-width shell) | `E62Cert.zero_width_shell` | `d ≥ 1`, every `L²` field. |
| Remark (zero field) | `E62Cert.zero_field` | `E⋆ = E_tot = 0`. The value of `0/0` is Lean's convention only. |
| Remark (no monotonicity) | `E62Cert.no_monotonicity` | `η(t) = cos² t` with total energy 1; neither monotone nor antitone. |

### E58 — `MathProofs/E58Certification.lean`, `MathProofs/E58GreenFunction.lean`

| Manuscript item | Lean declaration | Notes |
| --- | --- | --- |
| Theorem E58 | `E58Cert.theorem_e58` | `d ≥ 1`, `r > 0`, `a ≥ 0`, `k⋆ ≥ 0`. Proves `0 < G ≤ 1/r`, equality iff `|k| = k⋆` when `a > 0`, `⨆ G = 1/r`, and `G ≡ 1/r` when `a = 0`. |
| Proposition (sharp continuum resolvent bound) | `E58Cert.resolvent`, `E58Cert.Solves`, `E58Cert.solves_iff` | Existence and uniqueness of `u ∈ L²` with `𝓛u = f` tested against every Schwartz function. Also `û = Gf̂`, `‖𝓛⁻¹‖ = 1/r`, and `u ∈ H⁴` when `a > 0`. |
| Near-shell construction (proof) | `E58Cert.near_shell` | Nonzero `f_ε` with Fourier support in `{||k|² − k⋆²| < ε}`. |
| Remark (norm attainment) | `E58Cert.not_attained`, `E58Cert.attained_of_a_zero` | For `a > 0` the norm is not attained; for `a = 0`, `𝓛⁻¹ = r⁻¹I`. |
| Section 4 (coercivity) | `E58Cert.coercivity` | `⟨u, 𝓛u⟩ = r‖u‖² + a‖(Δ + k⋆²)u‖²` on `D(𝓛) = H⁴`. |
| Section 5 (band selectivity) | `E58Cert.band_selectivity` | The derivative formula, strict decrease in the detuning, and `G ~ 1/(aδ²)`. |
| Section 5 (periodic box) | `E58Cert.periodic_box` | On `𝕋_L^d`: the coefficientwise solution, and the norm as the lattice maximum `≤ 1/r`. For `a > 0` the norm is `1/r` iff some lattice point lies on the shell, and strictly less otherwise. |
| Section 6 (physical Green function, `d = 1`, `k⋆ = 0`) | `E58Green.fourier_g`, `inversion`, `distrib`, `ode`, `sign_change`, `not_pointwise_bound` | `ĝ = 1/(r + ak⁴)`; Fourier inversion; `ag'''' + rg = δ₀` against Schwartz tests; the matching conditions. Also `g < 0` at `t = π`, and `g(0) > 1/r` for `r > 64a`. |
| Section 7 (scope) | `E58Cert.scope` | With `r = 0` the symbol vanishes on the shell; with `a < 0` it drops below `r` and has real zeros. |

### M2/E17 — `MathProofs/E17Certification.lean` (with `E17Canonical`, `E17GlobalBound`)

| Manuscript item | Lean declaration | Notes |
| --- | --- | --- |
| Theorem (1)–(5) | `E17Cert.main_theorem` | For every `ε > 0` and `α ∈ ℝ`: (1) `D_ε > 0` everywhere; (2) `ContDiff ℝ ⊤ R_ε` (real analytic, which implies `C^∞`), `R_ε(0) = 0`, globally bounded; (3) `R_ε(z) → 1/z`; (4) `sup_{|z|≥δ}` bound for `α ≥ 0`, and uniform convergence on compacts for every `α`; (5) the pointwise curvature limit. |
| Global bound at fixed ε | `E17Cert.global_bound` | `‖R_ε‖_∞ ≤ max{1/ρ, ρe^{2α₊ρ²}/ε²}` for every `ρ > 0`. |
| Error identity (proof) | `E17Cert.exact_difference`, `E17Cert.error_formula` | |
| Theorem (4) in detail | `E17Cert.uniform_bound`, `compact_bound`, `tendstoUniformlyOn_compact` | |
| Corollary (strong L² limit) | `E17Cert.l2_limit` | Open `Ω ⊆ ℝ^d`, `ψ ∈ H²(Ω)` by weak derivatives, `|ψ| ≥ δ` a.e., `α ≥ 0`. |
| Corollary (fixed-regularization control) | `E17Cert.fixed_eps_control` | Every `α ∈ ℝ`. |
| Remark (whole space) | `E17Cert.whole_space` | |
| Remark (no uniform convergence through a node) | `E17Cert.node_obstruction` | The exact formula at `z = ε`, the `1/(2ε)` asymptotics, and failure on every punctured ball. |
| Proposition (constant U(1) invariance) | `E17Cert.phase_invariance` | `C²` fields on `ℝ^d`. |
| Remark (local gauge) | `E17Cert.local_gauge` | Explicit position-dependent phase. |
| Historical denominator failure | `E17Cert.historical` | `ψ ≡ −ε` kills the additive denominator; the historical operator is not phase covariant. |

### E26 — `MathProofs/RegularizedCurvatureL2.lean`, `E26Certification.lean`, `E26QuotientDomain.lean`

| Manuscript item | Lean declaration | Notes |
| --- | --- | --- |
| Definitions `H²(Ω)`, `Δψ`, `D_ε`, `Θ_ε` | `E26.MemH2`, `E26.IsWeakLaplacian`, `E26.MemH2.exists_weakLaplacian`, `E26.IsWeakLaplacian.ae_eq`, `E26.Den`, `E26.Theta` | The weak Laplacian exists in `L²` and is unique a.e. |
| `Θ_ε` on the a.e. nonzero-denominator domain | `E26Domain.quotient_domain` | `{D ≠ 0}` is null-measurable with null complement, `Θ·D = −Δψ` on it, and `Θ` is the a.e.-unique solution. The value at zeros of `D` is therefore immaterial. |
| Theorem E26 | `E26.e26`, `E26.e26_Rd`, `E26Certification.main_theorem` | Every open `Ω` (any `d`, no boundary condition), every real `ε, α`. Also: `D ≠ 0` a.e., `‖1/D‖_∞ ≤ 1/δ`, and the squared-integral form. |
| Corollary (fields bounded away from zero) | `E26.cor_modulus`, `E26Certification.away_from_nodes_corollary` | `ε > 0`, `α ≥ 0` (the manuscript's standing assumptions). |
| Remark (whole space) | `E26.not_ae_norm_ge_of_memLp` | |
| Corollary (nonnegative real fields) | `E26.cor_nonneg`, `E26Certification.nonnegative_real_corollary` | `δ_ε = min{ε/2, εe^{−αε²/4}}`. |
| Counterexample (`ψ = x² − ε` on `(−1,1)`) | `E26.counterexample`, `E26Certification.smooth_counterexample` | `ψ ∈ H²`, `Δψ = 2`, `Θ = −2/x²`, `∫|Θ|² = ∞`, `‖Δψ‖² = 8`. No finite constant works and (H) fails. |
| Corrected multiplier (section) | `E26.corrected_bound` | `‖(Δψ)R_ε(ψ)‖ ≤ ε⁻¹ max{2, e^{αε²/2}/2}‖Δψ‖`. |
| Scope: δ cannot be replaced by ε | `E26.delta_not_replaceable`, `E26Certification.separation_is_not_regularization` | |
| Additional: the constant `1/δ` is sharp | `E26Domain.sharp_constant` | Not claimed by the manuscript. |

### M3/E57 — `MathProofs/E57Certification.lean` (with `SwiftHohenbergL2`)

| Manuscript item | Lean declaration | Notes |
| --- | --- | --- |
| Theorem: unique `L²` mild solution in `C([0,∞); L²)` | `E57Cert.main_theorem`, `SH.mild_iff` | `d ≥ 1`, `a > 0`, `k⋆ > 0`. |
| (i) Self-adjoint, nonnegative realization, domain `H⁴`, symbol | `E57Cert.part_i`, `SH.Aop_isSelfAdjoint`, `SH.inner_Aop`, `E57Cert.equivalence`, `E57Cert.symbol_schwartz` | The domain `{pû ∈ L²}` equals `H⁴`; Mathlib's `LinearPMap.adjoint` gives `𝒜* = 𝒜`; the form domain is `H²`. |
| (ii) `û(t) = e^{−atp}û₀` a.e. | `E57Cert.main_theorem` | |
| (iii) Off-shell bound with `P_δ` | `E57Cert.main_theorem`, `E57Cert.Pdelta_projection` | `P_δ` is idempotent and self-adjoint. |
| (iv) Strong decay, `‖S(t)‖ = 1`, no uniform exponential rate | `E57Cert.main_theorem` | |
| Semigroup and generator | `E57Cert.semigroup`, `E57Cert.e57_eq_Sr` | The generator is exactly `−a𝒜` on `H⁴`. |
| Remark (meaning of a Fourier mode) | `E57Cert.plane_wave_not_memLp` | |
| Corollary (preferred shell, near-shell expansion) | `E57Cert.shell_corollary` | |
| Corollary (no exact-shell `L²` state) | `E57Cert.no_shell_state` | |
| Proposition (monotone quadratic energy) | `E57Cert.energy_identities`, `E57Cert.smoothing`, `E57Cert.strong_ode` | Both identities for `t > 0`, the integrated identity for `t ≥ 0`, and the identities at `t = 0` for `H⁴` data. |
| Remark (gradient-flow convention) | `E57Cert.gradient` | The real gradient of `E` is `𝒜u`, uniquely. |
| Proposition (discrete shells on a flat torus) | `E57Cert.periodic` | `g_L > 0` attained, `Π₀ = 0` when the span is trivial. |
| Proposition (linear SH threshold) | `E57Cert.linear_threshold` | |
| Remark (scope: sign reversal) | `E57Cert.sign_reversal` | Unbounded amplification of band-limited data. |

### E61 — `MathProofs/E61Certification.lean` (with `SwiftHohenbergL2`)

| Manuscript item | Lean declaration | Notes |
| --- | --- | --- |
| Theorem: `D(L_r) = H⁴`, `σ(L_r) = (−∞, r]`, `‖e^{tL_r}‖ = e^{rt}`, `r_c = 0`, maximal rate exactly on the shell | `E61Cert.theorem_e61`, `SH.spectrum_Lr`, `SH.opNorm_Sr`, `SH.generator`, `SH.generator_domain` | `e^{tL_r}` is a semigroup whose generator is exactly `L_r` with domain `H⁴`. |
| (1) `r < 0` | `E61Cert.stable` | `‖u(t)‖ ≤ e^{rt}‖u₀‖` for every mild solution. |
| (2) `r = 0` | `E61Cert.critical` | Strong decay; `‖S(t)‖ = 1`; no uniform exponential bound; `0` is not an `L²` eigenvalue. |
| (3) `r > 0` | `E61Cert.unstable` | Nonzero data with `‖e^{tL_r}u₀‖ ≥ e^{rt/2}‖u₀‖`. |
| Proposition (unstable annulus) | `E61Cert.unstable_band` | |
| Remark (near-onset width) | `E61Cert.near_onset` | |
| Proposition (periodic-box threshold) | `E61Cert.periodic_box`, `E61Cert.rcL_tendsto` | |
| Proposition (control-parameter translation) | `E61Cert.translation` | The uncentred operator is the same weak generator. |
| Consistency with `E61ExactNorm` | `E61Cert.exactNorm_eq_Sr` | |

### E16 — `MathProofs/SpectralConcentration.lean`, `MathProofs/E16TorusRemark.lean`

| Manuscript item | Lean declaration | Notes |
| --- | --- | --- |
| Proposition (exact modal power law) | `SpectralConc.exact_modal_law` | Existence and uniqueness of the mild solution on `[0,∞)`. |
| Lemma (unique maximizing radius, strict gap) | `SpectralConc.gap_lemma` | |
| Theorem E16 (concentration) | `SpectralConc.concentration` | Under the spectral-access hypothesis (H). |
| Remark (normalized ≠ persistent) | `SpectralConc.decay_of_mu_zero` | |
| Theorem (argmax convergence) | `SpectralConc.argmax_convergence` | `C₀` representative of `|Â₀|²`. |
| Corollary (`t^{-1/2}` bound) | `SpectralConc.argmax_rate` | |
| Corollary (radial) | `SpectralConc.radial_law`, `SpectralConc.radial_corollary` | Mathlib's surface measure, polar integration. |
| Proposition (failure without spectral access) | `SpectralConc.counterexample` | Nonzero Schwartz datum. |
| Remark (flat tori) | `E16Torus.coef_flow`, `power_law`, `coef_ode`, `dominant_concentration`, `shell_missed` | |

### F11 companions

| Manuscript item | Lean declaration | Notes |
| --- | --- | --- |
| E59 Theorem | `TorusL2.e59` | Bounded, `P² = P`, `P* = P`, contraction, orthogonal projection onto `ℋ`, Pythagoras, unique best approximation, `‖P‖ = 1` / `P = 0`. |
| E59 spectral fraction, FFT identity, remarks | `TorusL2.e59_fraction`, `TorusL2.fft_projector`, `TorusL2.zero_mem_oneSided_not_mem_annulus`, `TorusL2.mult_idem_iff_mem` | |
| E13 Theorem and E14 companion | `BandPass.e13`, `balance_interval`, `real_gradient`, `half_gradient`, `half_flow`, `centred_operator`, `energySH_eq`, `centred_first_variation`, `preferred_shell`, `growing_band`, `energy_lower`, `finite_dissipation`, `periodic_stationary` | On `𝕋_L^d`, `d ≤ 3` (the manuscript's setting). |

## Conventions and differences in form

- **Division by zero.** Lean defines `x / 0 = 0`. This affects only `η` at the zero field, which E62's remark states is an added convention, and `Θ_ε` on a null set. For `Θ_ε`, `quotient_domain` proves the value there is immaterial.
- **Spectrum.** For unbounded operators, the spectrum is taken in the standard sense: the complement of the set of `z` for which `z − T` has a bounded two-sided inverse on `D(T)`.
- **Stronger than stated.** Several Lean statements are more general than the manuscript:
  - E26's theorem holds for every real `ε, α`;
  - M2/E17's fixed-regularization corollary holds for every real `α`;
  - M2/E17 part (5) holds for every field at a point where `ψ(x) ≠ 0`.
- **Normalizations.** The Fourier normalizations are those of the manuscripts:
  - unitary on `ℝ^d`;
  - `Â_k = (2π)^{-d}∫…` on `(ℝ/2πℤ)^d` for E62;
  - lattice frequencies `2πn/L` on `𝕋_L^d`.

## Not claimed

The manuscripts' own scope statements apply. Nothing here establishes:

- nonlinear pattern formation or persistence;
- localization or confinement;
- stability of nonlinear flows;
- well-posedness of any curvature-driven evolution;
- uniform-in-`ε` bounds;
- physical interpretation.
