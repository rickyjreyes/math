import MathProofs.E69Sobolev
import MathProofs.E69Curvature
import MathProofs.E69Remarks
import MathProofs.E69Torus

/-!
# E69 certification: the bounded corrected regularized curvature

The certification interface for the manuscript *E69: High-Regularity `L^∞` Bound for the
Corrected Regularized Curvature Operator* (`papers/high-regularity-bounded-curvature-e69`).
Each declaration states one assertion of the manuscript over the actual Fourier-defined Sobolev
spaces `H^s(ℝⁿ; ℂ)` of real order and the essential-supremum norm; the mapping is
`docs/E69_LEAN_MANUSCRIPT_MAPPING.md`.

* `reciprocal`: `D_ε(z) > 0`, the exact formula, `R_ε(0) = 0`, the two regimes and
  `|R_ε(z)| ≤ M_{ε,α}` for every `z ∈ ℂ`.
* `sobolev_space`: `H^s(ℝⁿ)` for real `s` is a normed subspace of `L²` with `H⁰ = L²`, monotone in
  `s`, containing the Schwartz space.
* `laplacian`: `(Δu)^ = −|ξ|² û`, the classical and the weak Laplacian, `Δ : H^s → H^{s−2}`
  with `‖Δψ‖_{H^{s−2}} ≤ ‖ψ‖_{H^s}`.
* `fourier_inversion`, `embedding`: `H^r(ℝⁿ) ↪ L^∞(ℝⁿ)` for `r > n/2` by Cauchy–Schwarz and Fourier
  inversion.
* `main_theorem`: **Theorem E69.**
* `remark_dimensions`, `remark_domains`, `remark_fixed_regularization`, `remark_regularizer`.
-/

open Filter Topology Complex InnerProductSpace MeasureTheory Set
open scoped ContDiff FourierTransform ENNReal

namespace ReyesMath

namespace E69Cert

open Sobolev E26 E69

variable {n : ℕ}

local notation "Rn" => EuclideanSpace ℝ (Fin n)

/-- **The regularized reciprocal** `R_ε(z) = z̄/(|z|² + ε²e^{−2α|z|²})`: the denominator is
strictly positive (also at `z = 0`), `R_ε(0) = 0`, `|R_ε(z)| ≤ e^{2α₊}/ε²` for `|z| ≤ 1`,
`|R_ε(z)| ≤ 1/|z| ≤ 1` for `|z| ≥ 1`, and `sup_z |R_ε(z)| ≤ M_{ε,α} = max{1, e^{2α₊}/ε²} < ∞`. -/
theorem reciprocal {ε : ℝ} (hε : 0 < ε) (α : ℝ) :
    (∀ z : ℂ, 0 < ‖z‖ ^ 2 + ε ^ 2 * Real.exp (-2 * α * ‖z‖ ^ 2)) ∧
    (∀ z : ℂ, Rε ε α z =
      (starRingEnd ℂ) z / ((‖z‖ ^ 2 + ε ^ 2 * Real.exp (-2 * α * ‖z‖ ^ 2) : ℝ) : ℂ)) ∧
    Rε ε α 0 = 0 ∧
    (∀ z : ℂ, ‖z‖ ≤ 1 → ‖Rε ε α z‖ ≤ Real.exp (2 * max α 0) / ε ^ 2) ∧
    (∀ z : ℂ, 1 ≤ ‖z‖ → ‖Rε ε α z‖ ≤ 1 / ‖z‖ ∧ 1 / ‖z‖ ≤ 1) ∧
    (∀ z : ℂ, ‖Rε ε α z‖ ≤ Mea ε α) ∧ Mea ε α = max 1 (Real.exp (2 * max α 0) / ε ^ 2) :=
  ⟨denom_pos hε α, Rε_apply ε α, Rε_zero ε α, fun z => (norm_Rε_regimes hε α z).1,
    fun z => (norm_Rε_regimes hε α z).2, norm_Rε_le_Mea hε α, rfl⟩

/-- **`H^s(ℝⁿ; ℂ)` for every real `s`**: the subspace `Hs n s` of `L²(ℝⁿ; ℂ)` defined by
`∫ (1 + |ξ|²)^s |û(ξ)|² dξ < ∞` with the unitary Fourier transform `û`, normed by
`‖u‖_{H^s}`: triangle inequality, homogeneity, definiteness; `‖u‖_{H⁰} = ‖u‖_{L²}`;
`H^s ⊂ H^t` with `‖u‖_{H^t} ≤ ‖u‖_{H^s}` for `t ≤ s`; `𝓢(ℝⁿ) ⊂ H^s`. -/
theorem sobolev_space (s : ℝ) :
    (∀ u : L2 n, u ∈ Hs n s ↔
      Integrable fun ξ => (1 + ‖ξ‖ ^ 2) ^ s * ‖(FU u : Rn → ℂ) ξ‖ ^ 2) ∧
    (∀ u : L2 n, hsNorm s u = Real.sqrt (∫ ξ, (1 + ‖ξ‖ ^ 2) ^ s * ‖(FU u : Rn → ℂ) ξ‖ ^ 2)) ∧
    (∀ u v : L2 n, MemHs s u → MemHs s v → hsNorm s (u + v) ≤ hsNorm s u + hsNorm s v) ∧
    (∀ (c : ℂ) (u : L2 n), hsNorm s (c • u) = ‖c‖ * hsNorm s u) ∧
    (∀ u : L2 n, MemHs s u → (hsNorm s u = 0 ↔ u = 0)) ∧
    (∀ u : L2 n, MemHs 0 u ∧ hsNorm 0 u = ‖u‖) ∧
    (∀ t : ℝ, t ≤ s → ∀ u : L2 n, MemHs s u → MemHs t u ∧ hsNorm t u ≤ hsNorm s u) ∧
    (∀ φ : SchwartzMap Rn ℂ, MemHs s (toL2 φ)) :=
  ⟨fun _ => Iff.rfl, fun _ => rfl, fun _ _ hu hv => hsNorm_add_le hu hv, hsNorm_smul s,
    fun _ hu => hsNorm_eq_zero_iff hu, fun u => ⟨memHs_zero u, hsNorm_zero u⟩,
    fun _ ht _ hu => ⟨hu.mono ht, hsNorm_mono hu ht⟩, memHs_toL2 s⟩

/-- **The Laplacian.** On `H²(ℝⁿ)`, `(Δu)^(ξ) = −|ξ|² û(ξ)`; on Schwartz functions `Δ` is the
classical Laplacian (Mathlib's `Δ`); `Δu` is the weak Laplacian of `u`, against Schwartz and
against real `C_c^∞` test functions (`E26.IsWeakLaplacian`), and it is the unique such
`L²` function; for `s ≥ 2`, `Δ : H^s → H^{s−2}` with `‖Δψ‖_{H^{s−2}} ≤ ‖ψ‖_{H^s}`. -/
theorem laplacian :
    (∀ u : L2 n, MemHs 2 u →
      (FU (lap u) : Rn → ℂ) =ᵐ[volume] fun ξ => -((‖ξ‖ ^ 2 : ℝ) : ℂ) * (FU u : Rn → ℂ) ξ) ∧
    (∀ φ : SchwartzMap Rn ℂ, (lap (toL2 φ) : Rn → ℂ) =ᵐ[volume] fun x => Δ (⇑φ) x) ∧
    (∀ u : L2 n, MemHs 2 u → ∀ χ : SchwartzMap Rn ℂ,
      inner ℂ (toL2 χ) (lap u) = inner ℂ (toL2 (lapS χ)) u) ∧
    (∀ u : L2 n, MemHs 2 u → E26.IsWeakLaplacian univ (u : Rn → ℂ) (lap u : Rn → ℂ)) ∧
    (∀ u v : L2 n, MemHs 2 u →
      (∀ χ : SchwartzMap Rn ℂ, inner ℂ (toL2 χ) v = inner ℂ (toL2 (lapS χ)) u) → v = lap u) ∧
    (∀ s : ℝ, 2 ≤ s → ∀ ψ : L2 n, MemHs s ψ →
      MemHs (s - 2) (lap ψ) ∧ hsNorm (s - 2) (lap ψ) ≤ hsNorm s ψ) :=
  ⟨fun _ hu => FU_lap hu, lap_toL2_ae, fun _ hu => inner_toL2_lap hu,
    fun _ hu => isWeakLaplacian_lap hu, fun _ _ hu h => eq_lap_of_weak hu h,
    fun _ hs _ hψ => ⟨memHs_lap hψ hs, hsNorm_lap_le hψ hs⟩⟩

/-- **Fourier inversion** on `L²(ℝⁿ)`: if `û ∈ L¹`, then
`u(x) = (2π)^{−n/2} ∫ û(ξ) e^{ix·ξ} dξ` for a.e. `x`, a continuous function bounded by
`(2π)^{−n/2}‖û‖_{L¹}`. -/
theorem fourier_inversion (u : L2 n) (hu : Integrable (FU u : Rn → ℂ)) :
    (u : Rn → ℂ) =ᵐ[volume] fourierUinv (FU u : Rn → ℂ) ∧
    Continuous (fourierUinv (FU u : Rn → ℂ)) ∧
    ∀ x, ‖fourierUinv (FU u : Rn → ℂ) x‖ ≤
      (2 * Real.pi) ^ (-((n : ℝ) / 2)) * ∫ ξ, ‖(FU u : Rn → ℂ) ξ‖ :=
  ⟨ae_eq_fourierUinv u hu, continuous_fourierUinv hu, norm_fourierUinv_le _⟩

/-- **The Sobolev embedding `H^r(ℝⁿ) ↪ L^∞(ℝⁿ)` for `r > n/2`**, every `n`: by Cauchy–Schwarz
`‖û‖_{L¹} ≤ (∫ (1 + |ξ|²)^{−r})^{1/2} ‖u‖_{H^r}` with a finite integral, and by Fourier inversion
`‖u‖_∞ ≤ C(n, r) ‖u‖_{H^r}`, `C(n, r) = (2π)^{−n/2}(∫ (1 + |ξ|²)^{−r} dξ)^{1/2} > 0`. -/
theorem embedding {r : ℝ} (hr : (n : ℝ) / 2 < r) :
    Integrable (fun ξ : Rn => (1 + ‖ξ‖ ^ 2) ^ (-r)) ∧ 0 < Cemb n r ∧
    ∀ u : L2 n, MemHs r u →
      Integrable (FU u : Rn → ℂ) ∧
      ∫ ξ, ‖(FU u : Rn → ℂ) ξ‖ ≤ Real.sqrt (∫ ξ : Rn, (1 + ‖ξ‖ ^ 2) ^ (-r)) * hsNorm r u ∧
      (∃ f : Rn → ℂ, Continuous f ∧ (u : Rn → ℂ) =ᵐ[volume] f ∧
        ∀ x, ‖f x‖ ≤ Cemb n r * hsNorm r u) ∧
      MemLp (u : Rn → ℂ) ∞ volume ∧
      eLpNorm (u : Rn → ℂ) ∞ volume ≤ ENNReal.ofReal (Cemb n r * hsNorm r u) :=
  ⟨integrable_jw_neg hr, Cemb_pos hr, fun _ hu =>
    ⟨integrable_FU hr hu, integral_norm_FU_le hr hu, (E69.embedding hr hu).1,
      (E69.embedding hr hu).2.2.1, (E69.embedding hr hu).2.2.2⟩⟩

/-- **Theorem E69 (bounded regularized curvature).** Let `n` be any dimension (in particular
every `n ≥ 1`), `ε > 0`, `α ∈ ℝ`, and `s > n/2 + 2`. If `ψ ∈ H^s(ℝⁿ; ℂ)`, then
`Θ_ε[ψ] = −(Δψ) R_ε(ψ) ∈ L^∞(ℝⁿ; ℂ)` and
`‖Θ_ε[ψ]‖_{L^∞} ≤ C_{n,s} M_{ε,α} ‖ψ‖_{H^s}`, with
`C_{n,s} = (2π)^{−n/2}(∫ (1 + |ξ|²)^{−(s−2)} dξ)^{1/2}` finite, positive, and independent of
`ψ`, `ε` and `α`. On the way: `‖Δψ‖_{L^∞} ≤ C_{n,s}‖Δψ‖_{H^{s−2}} ≤ C_{n,s}‖ψ‖_{H^s}`. -/
theorem main_theorem {ε : ℝ} (hε : 0 < ε) (α : ℝ) {s : ℝ} (hs : (n : ℝ) / 2 + 2 < s) :
    (Integrable (fun ξ : Rn => (1 + ‖ξ‖ ^ 2) ^ (-(s - 2))) ∧ 0 < Cns n s ∧
      Cns n s = (2 * Real.pi) ^ (-((n : ℝ) / 2)) *
        Real.sqrt (∫ ξ : Rn, (1 + ‖ξ‖ ^ 2) ^ (-(s - 2)))) ∧
    ∀ ψ : L2 n, MemHs s ψ →
      (∀ᵐ x ∂volume, ‖(lap ψ : Rn → ℂ) x‖ ≤ Cns n s * hsNorm s ψ) ∧
      MemLp (E69.Theta ε α ψ) ∞ volume ∧
      (∀ᵐ x ∂volume, ‖E69.Theta ε α ψ x‖ ≤ Cns n s * Mea ε α * hsNorm s ψ) ∧
      eLpNorm (E69.Theta ε α ψ) ∞ volume ≤ ENNReal.ofReal (Cns n s * Mea ε α * hsNorm s ψ) :=
  ⟨⟨(Cns_pos hs).1, (Cns_pos hs).2, Cns_eq n s⟩, fun _ hψ =>
    ⟨(lap_linf hs hψ).2.2.1, (e69 hε α hs hψ).1, (e69 hε α hs hψ).2.1, (e69 hε α hs hψ).2.2⟩⟩

/-- **Remark (spatial dimensions).** The threshold `n/2 + 2` is `5/2, 3, 7/2, 4, 9/2` for
`n = 1, …, 5`; for `n ≤ 3`, `H² ↪ L^∞` bounds `ψ`; but for every `1 ≤ n ≤ 3` some
`ψ ∈ H²(ℝⁿ)`, bounded, has `Δψ ∉ L^∞` and `Θ_ε[ψ] ∉ L^∞` for every `ε > 0` and `α`: `H²`
regularity alone does not yield Theorem E69. -/
theorem remark_dimensions :
    (((1 : ℕ) : ℝ) / 2 + 2 = 5 / 2 ∧ ((2 : ℕ) : ℝ) / 2 + 2 = 3 ∧ ((3 : ℕ) : ℝ) / 2 + 2 = 7 / 2 ∧
      ((4 : ℕ) : ℝ) / 2 + 2 = 4 ∧ ((5 : ℕ) : ℝ) / 2 + 2 = 9 / 2) ∧
    (n ≤ 3 → ∀ ψ : L2 n, MemHs 2 ψ → MemLp (ψ : Rn → ℂ) ∞ volume ∧
      eLpNorm (ψ : Rn → ℂ) ∞ volume ≤ ENNReal.ofReal (Cemb n 2 * hsNorm 2 ψ)) ∧
    (1 ≤ n → n ≤ 3 → ∃ ψ : L2 n, MemHs 2 ψ ∧ MemLp (ψ : Rn → ℂ) ∞ volume ∧
      ¬ MemLp (lap ψ : Rn → ℂ) ∞ volume ∧
      ∀ ε : ℝ, 0 < ε → ∀ α : ℝ, ¬ MemLp (E69.Theta ε α ψ) ∞ volume) :=
  ⟨thresholds, fun hn _ hψ => h2_linf hn hψ, fun h1 h3 => h2_insufficient h1 h3⟩

/-- **Remark (other domains).** On any domain or measure space, an available `L^∞` embedding
bound for `Δψ` with constant `C_Ω` gives `‖Θ_ε[ψ]‖_{L^∞(Ω)} ≤ C_Ω M_{ε,α} N`; on the flat torus
`𝕋_L^d` (every `d ≥ 1`, every real `s > d/2 + 2`) the periodic Sobolev embedding gives
Theorem E69 with the constant `C_{L,d,s} = (Σ_k (1 + |ξ_k|²)^{−(s−2)})^{1/2}`. -/
theorem remark_domains :
    (∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) {ε : ℝ}, 0 < ε → ∀ (α : ℝ) {ψ F : Ω → ℂ},
      AEStronglyMeasurable ψ μ → AEStronglyMeasurable F μ → ∀ {CΩ N : ℝ},
      (∀ᵐ x ∂μ, ‖F x‖ ≤ CΩ * N) →
      MemLp (fun x => -(F x) * Rε ε α (ψ x)) ∞ μ ∧
        eLpNorm (fun x => -(F x) * Rε ε α (ψ x)) ∞ μ ≤ ENNReal.ofReal (CΩ * Mea ε α * N)) ∧
    (∀ (L : ℝ) [Fact (0 < L)] {d : ℕ}, 1 ≤ d → ∀ {ε : ℝ}, 0 < ε → ∀ (α : ℝ) {s : ℝ},
      (d : ℝ) / 2 + 2 < s → ∀ A : TorusL2.L2 L d, E69Torus.MemHsT s A →
      Summable (fun k : Fin d → ℤ => BandPass.wt L k ^ (-(s - 2))) ∧
      MemLp (E69Torus.ThetaT ε α A) ∞ (TorusL2.μ L d) ∧
      eLpNorm (E69Torus.ThetaT ε α A) ∞ (TorusL2.μ L d) ≤
        ENNReal.ofReal (E69Torus.CembT L d (s - 2) * Mea ε α * E69Torus.hsNormT s A)) :=
  ⟨fun μ _ hε α _ _ hψ hF _ _ hemb =>
    ⟨(theta_bound_of_linf μ hε α hψ hF hemb).1, (theta_bound_of_linf μ hε α hψ hF hemb).2.2⟩,
    fun L _ _ hd _ hε α _ hs A hA =>
      ⟨E69Torus.summable_wt_rpow_neg hd (by linarith),
        (E69Torus.e69_torus hd hε α hs hA).1, (E69Torus.e69_torus hd hε α hs hA).2.2⟩⟩

/-- **Remark (fixed regularization).** The bound is for fixed `ε > 0`: for every `n ≥ 1` and `α`
the Schwartz field `q = (|x|² − 1) b` lies in every `H^s` with `‖Θ_ε[q]‖_∞ ≥ n/(ε(1 + e^{2|α|}))`
for `0 < ε < 1`, so no estimate `‖Θ_ε[ψ]‖_∞ ≤ C‖ψ‖_{H^s}` holds uniformly as `ε ↓ 0`. No PDE
existence, uniqueness or stability statement is made. -/
theorem remark_fixed_regularization (hn : 1 ≤ n) (α : ℝ) :
    ((∀ s, MemHs s (toL2 (E69.qS n))) ∧
      ∀ ε : ℝ, 0 < ε → ε < 1 →
        ENNReal.ofReal (n / (ε * (1 + Real.exp (2 * |α|)))) ≤
          eLpNorm (E69.Theta ε α (toL2 (E69.qS n))) ∞ volume) ∧
    ∀ s : ℝ, ¬ ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ ψ : L2 n, MemHs s ψ →
      eLpNorm (E69.Theta ε α ψ) ∞ volume ≤ ENNReal.ofReal (C * hsNorm s ψ) :=
  ⟨no_uniform_in_eps hn α, fun s => not_uniform_bound hn α s⟩

/-- **Remark (choice of regularizer).** The estimate uses the modulus-squared denominator, which
never vanishes; the older complex denominator `z + εe^{−α|z|²}` vanishes (at `z = −ε` for `α = 0`,
and at some `z = −t`, `0 < t ≤ ε`, for every `α ≥ 0`), and its reciprocal is unbounded. -/
theorem remark_regularizer {ε : ℝ} (hε : 0 < ε) :
    (∀ (α : ℝ) (z : ℂ), 0 < ‖z‖ ^ 2 + ε ^ 2 * Real.exp (-2 * α * ‖z‖ ^ 2)) ∧
    oldDen ε 0 (-(ε : ℂ)) = 0 ∧
    (∀ α : ℝ, 0 ≤ α → ∃ t : ℝ, 0 < t ∧ t ≤ ε ∧ oldDen ε α (-(t : ℂ)) = 0) ∧
    (∀ α : ℝ, 0 ≤ α → ∀ M : ℝ, ∃ z : ℂ, M < ‖(oldDen ε α z)⁻¹‖) :=
  ⟨fun α => denom_pos hε α, oldDen_zero_alpha ε, fun _ hα => oldDen_vanishes hε hα,
    fun _ hα => oldDen_inv_unbounded hε hα⟩

end E69Cert

end ReyesMath
