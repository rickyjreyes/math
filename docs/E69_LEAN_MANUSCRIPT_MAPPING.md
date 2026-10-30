# E69: manuscript-to-Lean certification

**Issue:** [#40](https://github.com/rickyjreyes/math/issues/40) · **PR:** [#74](https://github.com/rickyjreyes/math/pull/74) · **Manuscript:** [`papers/high-regularity-bounded-curvature-e69/main.tex`](../papers/high-regularity-bounded-curvature-e69/main.tex) (unchanged).

Pinned versions: Lean 4.23.0, Mathlib v4.23.0. Entry point: [`lean/MathProofs/E69Certification.lean`](../lean/MathProofs/E69Certification.lean) (namespace `ReyesMath.E69Cert`). Dependency audit: [`lean/E69CertificationAudit.lean`](../lean/E69CertificationAudit.lean).

Theorem E69 and every assertion of its four remarks are kernel-checked Lean declarations with the manuscript's quantifiers:

* every dimension `n`, including every `n ≥ 1`;
* every `ε > 0`;
* every real `α`;
* every real Sobolev order `s > n/2 + 2`.

The setting is the actual Fourier-defined Sobolev spaces `H^s(ℝⁿ; ℂ)` and the essential-supremum norm. The Sobolev embedding `H^{s−2} ↪ L^∞` is proved, not assumed. Θ uses the corrected modulus-squared regularizer, not the older complex denominator, and no estimate uniform as `ε ↓ 0` is claimed; in fact one is refuted.

There are no `sorry`, `admit`, new axioms or `native_decide`, and no finite-dimensional or numerical surrogate. No hypothesis is equivalent to the conclusion. All 96 audited declarations depend only on `propext`, `Classical.choice` and `Quot.sound`. No manuscript assertion was found to be false, so no correction is needed.

Reproduce:

```bash
cd lean
lake update && lake exe cache get
lake build MathProofs.E69Certification
lake env lean E69CertificationAudit.lean   # 96 lines, each: [propext, Classical.choice, Quot.sound]
lake build                                  # complete project
```

## The objects in the statements

| Manuscript object | Lean | Module |
|---|---|---|
| `ℝⁿ`, Lebesgue measure, `L²(ℝⁿ; ℂ)` | `EuclideanSpace ℝ (Fin n)`, `volume`, `Sobolev.L2 n = Lp ℂ 2 volume` | Mathlib, `SobolevH2` |
| The unitary Fourier transform `û(ξ) = (2π)^{−n/2} ∫ u(x)e^{−ix·ξ}dx` | `Sobolev.FU : L2 n ≃ₗᵢ[ℂ] L2 n`, the Plancherel extension; `Sobolev.FU_ae_eq` identifies it with the integral `Sobolev.fourierU` on `L¹ ∩ L²` | `FourierShellL2` |
| `u ∈ H^s(ℝⁿ; ℂ)`, `s ∈ ℝ`, `‖u‖²_{H^s} = ∫(1+|ξ|²)^s|û(ξ)|²dξ` | `ReyesMath.E69.MemHs s u` (integrability of `(1+‖ξ‖²)^s ‖FU u ξ‖²`), `hsNorm s u` (its integral's square root), the subspace `Hs n s : Submodule ℂ (L2 n)` | `E69Sobolev` |
| `Δψ`, `(Δψ)^ = −|ξ|²ψ̂` | `ReyesMath.E69.lap ψ = FU⁻¹(−‖ξ‖² · FU ψ)` on `H²`; equal to the classical Laplacian (Mathlib's `Δ`) on Schwartz functions and to the weak Laplacian | `E69Sobolev` |
| `R_ε(z) = z̄/(|z|²+ε²e^{−2α|z|²})` | `ReyesMath.E26.Rε ε α z` (shared with M2/E17 and E26) | `RegularizedCurvatureL2` |
| `Θ_ε[ψ] = −(Δψ)R_ε(ψ)` | `ReyesMath.E69.Theta ε α ψ x = −(lap ψ x) · Rε ε α (ψ x)` on representatives; `Theta_congr_ae` shows independence of the representatives | `E69Curvature` |
| `‖·‖_{L^∞}` | `eLpNorm · ∞ volume` (essential supremum); `MemLp · ∞ volume` | Mathlib |
| `α₊`, `M_{ε,α} = max{1, e^{2α₊}/ε²}` | `max α 0`, `ReyesMath.E69.Mea ε α` | `E69Curvature` |
| `C_{n,s}` | `ReyesMath.E69.Cns n s = (2π)^{−n/2}(∫(1+|ξ|²)^{−(s−2)}dξ)^{1/2}` (a function of `n` and `s` only) | `E69Curvature` |
| The flat torus `𝕋_L^d`, `H^s(𝕋^d)`, periodic `Δ` | `TorusL2.Tor L d` with Haar probability `μ L d`; `ReyesMath.E69Torus.MemHsT s A` (`Σ_k (1+|ξ_k|²)^s|Â_k|² < ∞`), `hsNormT`; `BandPass.lap` (symbol `−|ξ_k|²`) | `E69Torus`, `TorusFourier`, `BandPassFlow` |

## Assertion-by-assertion mapping

All declarations are in `lean/MathProofs/`, imported by `lean/MathProofs.lean`. They are checked by:

* `.github/workflows/lean-e69.yml`: hole check, focused build, axiom audit and the complete project;
* `.github/workflows/lean.yml`: the complete project.

| # | Manuscript assertion | Fully qualified declaration | Hypotheses and quantifier order | Module |
|---|---|---|---|---|
| 1 | §1: `R_ε` with strictly positive denominator `D_ε(z) = |z|²+ε²e^{−2α|z|²}`, also at `z = 0` | `ReyesMath.E69Cert.reciprocal` (parts 1–2); `ReyesMath.E69.denom_pos`, `Rε_apply` (`= E17Cert.Deps_pos`) | `∀ ε > 0, ∀ α, ∀ z : ℂ` | `E69Curvature` |
| 2 | Proof, case `|z| ≤ 1`: `|R_ε(z)| ≤ e^{2α₊}/ε²`; case `|z| ≥ 1`: `|R_ε(z)| ≤ 1/|z| ≤ 1` | `ReyesMath.E69.norm_Rε_regimes` (in `E69Cert.reciprocal`) | `∀ ε > 0, ∀ α, ∀ z` | `E69Curvature` |
| 3 | (rec-bound) `sup_z |R_ε(z)| ≤ M_{ε,α} < ∞`; `R_ε(0) = 0` | `ReyesMath.E69.norm_Rε_le_Mea`, `Rε_zero` (in `E69Cert.reciprocal`) | `∀ ε > 0, ∀ α, ∀ z ∈ ℂ` | `E69Curvature` |
| 4 | `H^s(ℝⁿ; ℂ)` for real `s`, the norm `‖·‖_{H^s}` | `ReyesMath.E69Cert.sobolev_space`; `ReyesMath.E69.Hs`, `hsNorm_add_le`, `hsNorm_smul`, `hsNorm_eq_zero_iff`, `memHs_zero`, `hsNorm_zero` (Plancherel), `MemHs.mono`, `hsNorm_mono`, `memHs_toL2` (`𝓢 ⊂ H^s`) | `∀ n, ∀ s : ℝ` | `E69Sobolev` |
| 5 | `(Δψ)^ = −|ξ|²ψ̂` | `ReyesMath.E69.FU_lap` (in `E69Cert.laplacian`) | `∀ u ∈ H²(ℝⁿ)`, a.e. in `ξ` | `E69Sobolev` |
| 5a | `Δ` is the actual Laplacian | `ReyesMath.E69.lap_toL2`, `lap_toL2_ae` (classical `Δφ` for `φ ∈ 𝓢`); `inner_toL2_lap` (`⟨χ, Δu⟩ = ⟨Δχ, u⟩`); `isWeakLaplacian_lap` (`E26.IsWeakLaplacian univ`, real `C_c^∞` tests); `eq_lap_of_weak` (uniqueness) | `∀ u ∈ H², ∀ χ ∈ 𝓢` | `E69Sobolev` |
| 6 | (lap-hs) `‖Δψ‖_{H^{s−2}} ≤ ‖ψ‖_{H^s}` via `|ξ|⁴ ≤ (1+|ξ|²)²` | `ReyesMath.E69.memHs_lap`, `hsNorm_lap_le`, `lap_weight_le` (in `E69Cert.laplacian`) | `∀ s ≥ 2, ∀ ψ ∈ H^s` | `E69Sobolev` |
| 7 | Cauchy–Schwarz: `‖ŵ‖_{L¹} ≤ (∫(1+|ξ|²)^{−r})^{1/2}‖w‖_{H^r}`, the integral finite for `r > n/2` | `ReyesMath.E69.integrable_jw_neg` (Mathlib's `integrable_rpow_neg_one_add_norm_sq`), `integrable_FU`, `integral_norm_FU_le` (Hölder `p = q = 2`) | `∀ r > n/2, ∀ w ∈ H^r` | `E69Sobolev` |
| 8 | Fourier inversion `w(x) = (2π)^{−n/2}∫ŵ(ξ)e^{ix·ξ}dξ` | `ReyesMath.E69Cert.fourier_inversion`; `ReyesMath.E69.ae_eq_fourierUinv`, `FU_symm_ae_eq`, `fourierL2_symm_eq` (`𝓕⁻¹ = R∘𝓕` on `L²`), `fourier_dilF` (scaling law) | `∀ w ∈ L²` with `ŵ ∈ L¹`, a.e. in `x` | `E69Sobolev` |
| 9 | The embedding `H^{s−2} ↪ L^∞`, (lap-linf) `‖Δψ‖_∞ ≤ C_{n,s}‖Δψ‖_{H^{s−2}} ≤ C_{n,s}‖ψ‖_{H^s}` | `ReyesMath.E69Cert.embedding` (= `ReyesMath.E69.embedding`, with continuous representative); `ReyesMath.E69.lap_linf` | `∀ n, ∀ r > n/2` | `E69Sobolev`, `E69Curvature` |
| 10 | **Theorem E69**: `Θ_ε[ψ] ∈ L^∞` and `‖Θ_ε[ψ]‖_∞ ≤ C_{n,s}M_{ε,α}‖ψ‖_{H^s}`, `C_{n,s}` finite, positive, independent of `ψ, ε, α` | `ReyesMath.E69Cert.main_theorem`; `ReyesMath.E69.e69`, `Cns_pos`, `Cns_eq` | `∀ n, ∀ ε > 0, ∀ α ∈ ℝ, ∀ s > n/2+2, ∀ ψ ∈ H^s(ℝⁿ;ℂ)`; `C_{n,s}` is fixed before `ψ`, `ε`, `α` | `E69Curvature` |
| 11 | Remark (spatial dimensions): thresholds `5/2, 3, 7/2, 4, 9/2` | `ReyesMath.E69.thresholds` (in `E69Cert.remark_dimensions`) | `n = 1, …, 5` | `E69Remarks` |
| 12 | `H² ↪ L^∞` for `n ≤ 3` bounds `ψ` | `ReyesMath.E69.h2_linf` | `∀ n ≤ 3, ∀ ψ ∈ H²` | `E69Remarks` |
| 13 | … but not `Δψ`; `H²` regularity alone does not yield Theorem E69 | `ReyesMath.E69.h2_insufficient` | `∀ 1 ≤ n ≤ 3, ∃ ψ ∈ H²(ℝⁿ)`, bounded, with `Δψ ∉ L^∞` and `∀ ε > 0, ∀ α, Θ_ε[ψ] ∉ L^∞` | `E69Remarks` |
| 14 | Remark (other domains): flat torus with the periodic embedding | `ReyesMath.E69Torus.e69_torus`, `embeddingT`, `summable_wt_rpow_neg`, `hsNormT_lap_le` (in `E69Cert.remark_domains`) | `∀ L > 0, ∀ d ≥ 1, ∀ ε > 0, ∀ α, ∀ s > d/2+2, ∀ A ∈ H^s(𝕋_L^d)`; constant `(Σ_k(1+|ξ_k|²)^{−(s−2)})^{1/2}` | `E69Torus` |
| 15 | … bounded Lipschitz extension domain `Ω` when an embedding is available, constant depending on `Ω` | `ReyesMath.E69.theta_bound_of_linf` (in `E69Cert.remark_domains`) | any measure space `(Ω, μ)`; hypothesis: the available bound `‖F‖_{L^∞(Ω)} ≤ C_Ω N` for `F = Δψ`; conclusion `‖Θ‖_{L^∞(Ω)} ≤ C_Ω M_{ε,α} N` | `E69Remarks` |
| 16 | Remark (fixed regularization): no uniform estimate as `ε ↓ 0` | `ReyesMath.E69.no_uniform_in_eps` (`q = (|x|²−1)b ∈ ⋂_s H^s` with `‖Θ_ε[q]‖_∞ ≥ n/(ε(1+e^{2|α|}))`), `not_uniform_bound` (in `E69Cert.remark_fixed_regularization`) | `∀ n ≥ 1, ∀ α, ∀ s`: `¬ ∃ C, ∀ ε ∈ (0,1), ∀ ψ ∈ H^s, ‖Θ_ε[ψ]‖_∞ ≤ C‖ψ‖_{H^s}` | `E69Remarks` |
| 17 | … nor existence, uniqueness or stability of a PDE flow | — | editorial; no dynamical statement is encoded | — |
| 18 | Remark (choice of regularizer): the older denominator `ψ+εe^{−α|ψ|²}` can vanish | `ReyesMath.E69.oldDen_zero_alpha` (`z = −ε`, `α = 0`), `oldDen_vanishes` (`∀ α ≥ 0`, some `z = −t`, `0 < t ≤ ε`), `oldDen_inv_unbounded` (in `E69Cert.remark_regularizer`) | `∀ ε > 0, ∀ α ≥ 0` | `E69Remarks` |

## How the proofs go

* **The spaces.** `H^s(ℝⁿ)` is the set of `u ∈ L²` whose unitary transform is square-integrable against `(1+|ξ|²)^s`. The norm is the `L²` norm of `(1+|ξ|²)^{s/2}û` (`hsNorm_eq_norm_toLp`), which gives the triangle inequality.
* **The Laplacian.** It is the Fourier multiplier `−|ξ|²` on `H²`. On Schwartz functions it agrees with the classical Laplacian, because
  * `FU φ` is the Schwartz function `(2π)^{−n/2}𝓕φ(ξ/2π)` (`FUS`), and
  * Mathlib's `𝓕(Δφ) = −(2π)²|ξ|²𝓕φ` becomes `−|ξ|²` after the dilation (`FUS_lapS`).

  The weak identity `⟨χ, Δu⟩ = ⟨Δχ, u⟩` follows from unitarity of `FU`, because the multiplier is real.
* **Fourier inversion.** Five steps:
  1. On Schwartz functions, `𝓕⁻¹φ(x) = 𝓕φ(−x)`. By density this gives `𝓕⁻¹ = R ∘ 𝓕` on `L²`, where `R` is the reflection.
  2. With the `L¹ ∩ L²` identification of `fourierL2` and the scaling law `𝓕(g(λ·)) = λ^{−n}𝓕g(·/λ)`, this gives `FU⁻¹g(x) = ĝ(−x)` for `g ∈ L¹ ∩ L²`.
  3. Hence `u(x) = (2π)^{−n/2}∫û(ξ)e^{ix·ξ}dξ` a.e. when `û ∈ L¹`.
  4. The right side is continuous.
  5. It is bounded by `(2π)^{−n/2}‖û‖₁`.
* **The embedding.** Hölder with `(1+|ξ|²)^{−r/2}·(1+|ξ|²)^{r/2}|û|` gives `‖û‖₁ ≤ (∫(1+|ξ|²)^{−r})^{1/2}‖u‖_{H^r}`. The integral is finite for `2r > n` by Mathlib's `integrable_rpow_neg_one_add_norm_sq`. Fourier inversion then bounds `u`.
* **Theorem E69.** `‖Θ(x)‖ = ‖Δψ(x)‖‖R_ε(ψ(x))‖ ≤ (C_{n,s}‖ψ‖_{H^s})·M_{ε,α}` a.e. Measurability comes from continuity of `R_ε`.
* **`H²` is not enough.** The construction has four steps:
  1. Take `h = |x|^{−1/4}1_{|x|≤1} ∈ L²` (polar integrals, `E68.integrable_indicator_closedBall_rpow`), with `ψ₀ = (1−Δ)^{−1}h ∈ H²` and `Δψ₀ = ψ₀ − h`.
  2. For `n ≤ 3`, `ψ₀` has a bounded continuous representative.
  3. Adding a multiple of a bump makes `ψ(0) ≠ 0`, so `|R_ε(ψ)|` is bounded below near `0`.
  4. There `|Δψ| ≥ |h| − C` exceeds every level on a punctured ball of positive measure.
* **No uniform bound in `ε`.** Take `q = (|x|²−1)b` with `b = 1` on `B̄(0,2)`. On the annulus `1+ε/2 < |x|² < 1+ε`, `Δq = 2n` (from `M6B.squared_norm_laplacian_D`) and `q ∈ (ε/2, ε)`, so `|Θ_ε[q]| ≥ n/(ε(1+e^{2|α|}))` on an open set.
* **Torus.** The lattice sum `Σ_{ℤ^d}(1+|ξ_k|²)^{−r}` converges for `r > d/2` in every dimension, via `(1+Σk_j²)^{−r} ≤ Π_j(1+k_j²)^{−r/d}`. The Fourier series of `A ∈ H^r(𝕋^d)` then converges absolutely and uniformly to a continuous representative.

## Verification

* Local, pinned toolchain:
  * `lake build MathProofs.E69Certification`;
  * the complete project `lake build` (7375 jobs, exit 0, no warnings in E69 modules);
  * `lake env lean E69CertificationAudit.lean`, with 96 of 96 declarations on `[propext, Classical.choice, Quot.sound]`;
  * no `sorry`, `admit`, `axiom` or `native_decide` in any E69 module.
* Exact-head CI at `fb9e92829112d2598a6f3d72f87db8b3ec1bcc85`: [focused E69 workflow](https://github.com/rickyjreyes/math/actions/runs/41114874006) (also on [push](https://github.com/rickyjreyes/math/actions/runs/41114745328)) and [complete-project `lean.yml`](https://github.com/rickyjreyes/math/actions/runs/41114873524). Later revisions are recorded in [PR #74](https://github.com/rickyjreyes/math/pull/74) and in `lean/formalization.yaml` (`latest_fully_checked_revision`). The CI covers:
  * the focused E69 workflow (hole check, focused build, axiom audit, complete project);
  * the full `lean.yml` build;
  * the E68, M6B, F09, analytic-cores and PDF workflows.

## Lean conventions that differ in form from the manuscript

* `Θ_ε[ψ]` is defined pointwise from the `L²` representatives of `ψ` and `Δψ`. Changing representatives changes `Θ_ε[ψ]` only on a null set (`Theta_congr_ae`), so its `L^∞` class is well defined.
* `lap` is defined on all of `L²` and is `0` outside `H²`. Every statement about `lap ψ` assumes `ψ ∈ H²` or `ψ ∈ H^s` with `s ≥ 2`.
* The dimension is any `n : ℕ`; the manuscript's `n ≥ 1` is included. The remark constructions use `1 ≤ n`, and `1 ≤ n ≤ 3` for the `H²` counterexample, which is the range named in the remark.
* The torus statements use the Haar probability measure on `𝕋_L^d`. It has the same null sets as Lebesgue measure, so the `L^∞` norms agree, and the `H^s` norm is the Parseval-normalized one.
