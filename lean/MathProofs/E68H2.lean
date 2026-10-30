import Mathlib
import MathProofs.E68Corrected
import MathProofs.E68SobolevEmbedding
import MathProofs.E68Scaling

/-!
# E68: the `H²` replacement (Corollary 4.1 and Proposition 4.2)

`IsH2 ψ g H` is the Sobolev space `H²(ℝⁿ; ℂ) = W^{2,2}(ℝⁿ)` by weak derivatives: `ψ ∈ H¹` with
weak gradient `g`, and every component `gᵢ = ∂ᵢψ` is in `H¹` with weak gradient `H i`, so that
`H i x j = ∂ⱼ∂ᵢψ(x)`. The norm is `‖ψ‖²_{H²} = ‖ψ‖²₂ + ‖∇ψ‖²₂ + Σᵢ ‖∇∂ᵢψ‖²₂` (`h2sq`).

* `eLpNorm_three_le`: the interpolation `‖f‖₃ ≤ ‖f‖₂^{1/2} ‖f‖₆^{1/2}` (Hölder with
  `1/3 = 1/4 + 1/12`).
* `grad_bound_four`, `grad_bound_three`: for `ψ ∈ H²(ℝ⁴)`, `‖∇ψ‖₄ ≤ 4 C₄ ‖ψ‖_{H²}` from the
  Sobolev embedding `H¹(ℝ⁴) ⊂ L⁴` applied to the weak gradient components. For
  `ψ ∈ H²(ℝ³)`, `‖∇ψ‖₃ ≤ (3 C₃)^{1/2} ‖ψ‖_{H²}` from `H¹(ℝ³) ⊂ L⁶` and the interpolation.
* `e68_H2` (Corollary 4.1): for `n ∈ {3, 4}` there is `C_n` with
  `∫_{B_R(x₀)} |∇ψ|² ≤ C_n R^{n-2} ‖ψ‖²_{H²}` for all `ψ ∈ H²`, `x₀` and `R > 0`. It is obtained
  by inserting these bounds into the corrected estimate `e68_corrected`.
* `not_e68_H2` (Proposition 4.2): for `n > 4` no such constant exists, already on
  `C_c^∞(ℝⁿ)`. The proof uses `u_R(x) = R^{2-n/2} φ(x/R)` and the exact identities
  `‖u_R‖²₂ = R⁴‖φ‖²₂`, `‖∇u_R‖²₂ = R²‖∇φ‖²₂`, `‖D²u_R‖²₂ = ‖D²φ‖²₂`, which feed
  `high_dimensional_H2_scaling_obstruction`.
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ContDiff ENNReal NNReal

namespace ReyesMath.E68

variable {n : ℕ}

local notation "Rn" => EuclideanSpace ℝ (Fin n)

/-! ### The Sobolev space `H²(ℝⁿ)` -/

/-- `ψ ∈ H²(ℝⁿ; ℂ)` with weak gradient `g` and weak second derivatives `H i = ∇(∂ᵢψ)`. -/
structure IsH2 (ψ : Rn → ℂ) (g : Rn → EuclideanSpace ℂ (Fin n))
    (H : Fin n → Rn → EuclideanSpace ℂ (Fin n)) : Prop where
  isH1 : IsH1 ψ g
  isH1_grad : ∀ i, IsH1 (fun x => g x i) (H i)

/-- `ψ ∈ H²(ℝⁿ; ℂ)`. -/
def MemH2 (ψ : Rn → ℂ) : Prop :=
  ∃ g H, IsH2 ψ g H

/-- `‖ψ‖²_{H²} = ‖ψ‖²_{L²} + ‖∇ψ‖²_{L²} + Σᵢ ‖∇∂ᵢψ‖²_{L²}`. -/
def h2sq (ψ : Rn → ℂ) (g : Rn → EuclideanSpace ℂ (Fin n))
    (H : Fin n → Rn → EuclideanSpace ℂ (Fin n)) : ℝ :=
  (∫ x, ‖ψ x‖ ^ 2) + (∫ x, ‖g x‖ ^ 2) + ∑ i, ∫ x, ‖H i x‖ ^ 2

theorem h2sq_nonneg (ψ : Rn → ℂ) (g : Rn → EuclideanSpace ℂ (Fin n))
    (H : Fin n → Rn → EuclideanSpace ℂ (Fin n)) : 0 ≤ h2sq ψ g H :=
  add_nonneg (add_nonneg (integral_nonneg fun _ => sq_nonneg _)
    (integral_nonneg fun _ => sq_nonneg _))
    (Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => sq_nonneg _)

theorem integral_grad_le_h2sq (ψ : Rn → ℂ) (g : Rn → EuclideanSpace ℂ (Fin n))
    (H : Fin n → Rn → EuclideanSpace ℂ (Fin n)) : (∫ x, ‖g x‖ ^ 2) ≤ h2sq ψ g H := by
  have h1 : 0 ≤ ∫ x, ‖ψ x‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have h2 : 0 ≤ ∑ i, ∫ x, ‖H i x‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => sq_nonneg _
  unfold h2sq
  linarith

theorem integral_hess_le_h2sq (ψ : Rn → ℂ) (g : Rn → EuclideanSpace ℂ (Fin n))
    (H : Fin n → Rn → EuclideanSpace ℂ (Fin n)) (i : Fin n) :
    (∫ x, ‖H i x‖ ^ 2) ≤ h2sq ψ g H := by
  have h1 : 0 ≤ ∫ x, ‖ψ x‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have h2 : 0 ≤ ∫ x, ‖g x‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have h3 : (∫ x, ‖H i x‖ ^ 2) ≤ ∑ j, ∫ x, ‖H j x‖ ^ 2 :=
    Finset.single_le_sum (f := fun j => ∫ x, ‖H j x‖ ^ 2)
      (fun _ _ => integral_nonneg fun _ => sq_nonneg _) (Finset.mem_univ i)
  unfold h2sq
  linarith

/-- The `H¹` energy is part of the `H²` energy. -/
theorem h1sq_le_h2sq (ψ : Rn → ℂ) (g : Rn → EuclideanSpace ℂ (Fin n))
    (H : Fin n → Rn → EuclideanSpace ℂ (Fin n)) : h1sq ψ g ≤ h2sq ψ g H := by
  have h3 : 0 ≤ ∑ i, ∫ x, ‖H i x‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => sq_nonneg _
  unfold h1sq h2sq
  linarith

/-- **Smooth inclusion.** A `C^∞` compactly supported field is in `H²`, with its classical
first and second derivatives. -/
theorem isH2_of_contDiff {f : Rn → ℂ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    IsH2 f (gradVec f) (fun i => gradVec (fun x => gradVec f x i)) where
  isH1 := isH1_of_contDiff (hf.of_le (by exact_mod_cast le_top)) hc
  isH1_grad i := by
    have h1 : ContDiff ℝ ∞ (fun x => gradVec f x i) :=
      (hf.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const
    exact isH1_of_contDiff (h1.of_le (by exact_mod_cast le_top))
      ((hc.fderiv ℝ).comp_left (g := fun L : Rn →L[ℝ] ℂ => L (ev i)) (by simp))

/-! ### `L^p` bounds -/

theorem eLpNorm_two_eq_sqrt {F : Type*} [NormedAddCommGroup F] {f : Rn → F}
    (hf : MemLp f 2 volume) :
    eLpNorm f 2 volume = ENNReal.ofReal (Real.sqrt (∫ x, ‖f x‖ ^ 2)) := by
  rw [hf.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top, Real.sqrt_eq_rpow]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  norm_num

theorem eLpNorm_hess_le {ψ : Rn → ℂ} {g : Rn → EuclideanSpace ℂ (Fin n)}
    {H : Fin n → Rn → EuclideanSpace ℂ (Fin n)} (h : IsH2 ψ g H) (i : Fin n) :
    eLpNorm (H i) 2 volume ≤ ENNReal.ofReal (Real.sqrt (h2sq ψ g H)) := by
  rw [eLpNorm_two_eq_sqrt (h.isH1_grad i).memLp_grad]
  exact ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt (integral_hess_le_h2sq ψ g H i))

theorem eLpNorm_grad_le {ψ : Rn → ℂ} {g : Rn → EuclideanSpace ℂ (Fin n)}
    {H : Fin n → Rn → EuclideanSpace ℂ (Fin n)} (h : IsH2 ψ g H) :
    eLpNorm g 2 volume ≤ ENNReal.ofReal (Real.sqrt (h2sq ψ g H)) := by
  rw [eLpNorm_two_eq_sqrt h.isH1.memLp_grad]
  exact ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt (integral_grad_le_h2sq ψ g H))

theorem norm_le_sum_norm_apply (v : EuclideanSpace ℂ (Fin n)) : ‖v‖ ≤ ∑ i, ‖v i‖ := by
  have h1 : ‖v‖ ^ 2 ≤ (∑ i, ‖v i‖) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    exact Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => norm_nonneg _
  exact (pow_le_pow_iff_left₀ (norm_nonneg _)
    (Finset.sum_nonneg fun i _ => norm_nonneg _) two_ne_zero).1 h1

/-- `‖g‖_{Lᵖ} ≤ Σᵢ ‖gᵢ‖_{Lᵖ}` for a vector field. -/
theorem eLpNorm_le_sum_apply {p : ℝ≥0∞} (hp : 1 ≤ p) {g : Rn → EuclideanSpace ℂ (Fin n)}
    (hg : AEStronglyMeasurable g volume) :
    eLpNorm g p volume ≤ ∑ i, eLpNorm (fun x => g x i) p volume := by
  have hmeas : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      AEStronglyMeasurable (fun x => ‖g x i‖) volume := fun i _ =>
    ((EuclideanSpace.proj (𝕜 := ℂ) i).continuous.comp_aestronglyMeasurable hg).norm
  calc eLpNorm g p volume ≤ eLpNorm (fun x => ∑ i, ‖g x i‖) p volume :=
        eLpNorm_mono fun x => by
          rw [Real.norm_of_nonneg (Finset.sum_nonneg fun i _ => norm_nonneg _)]
          exact norm_le_sum_norm_apply _
    _ = eLpNorm (∑ i, fun x => ‖g x i‖) p volume := by
        congr 1
        funext x
        simp [Finset.sum_apply]
    _ ≤ ∑ i, eLpNorm (fun x => ‖g x i‖) p volume := eLpNorm_sum_le hmeas hp
    _ = ∑ i, eLpNorm (fun x => g x i) p volume := by simp_rw [eLpNorm_norm]

instance holderTriple_four_twelve_three : ENNReal.HolderTriple 4 12 3 := ⟨by
  rw [← ENNReal.toReal_eq_toReal_iff' (by simp) (by simp)]
  rw [ENNReal.toReal_add (by simp) (by simp)]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_ofNat]
  norm_num⟩

/-- **Interpolation between `L²` and `L⁶`:** `‖f‖₃ ≤ ‖f‖₂^{1/2} ‖f‖₆^{1/2}`. -/
theorem eLpNorm_three_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {F : Type*}
    [NormedAddCommGroup F] {f : α → F} (hf : AEStronglyMeasurable f μ) :
    eLpNorm f 3 μ ≤ eLpNorm f 2 μ ^ (1 / 2 : ℝ) * eLpNorm f 6 μ ^ (1 / 2 : ℝ) := by
  have hs : AEStronglyMeasurable (fun x => ‖f x‖ ^ (1 / 2 : ℝ)) μ :=
    (hf.norm.aemeasurable.pow_const _).aestronglyMeasurable
  have h := eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm (p := 4) (q := 12) (r := 3) hs hs
    (fun a b : ℝ => a * b) 1 (Eventually.of_forall fun x => by simp [norm_mul])
  have e1 : (fun x => ‖f x‖ ^ (1 / 2 : ℝ) * ‖f x‖ ^ (1 / 2 : ℝ)) = fun x => ‖f x‖ := by
    funext x
    rw [← Real.rpow_add' (norm_nonneg _) (by norm_num)]
    norm_num
  have e2 : (4 : ℝ≥0∞) * ENNReal.ofReal (1 / 2) = 2 := by
    rw [← ENNReal.ofReal_ofNat 4, ← ENNReal.ofReal_mul (by norm_num)]
    norm_num
  have e3 : (12 : ℝ≥0∞) * ENNReal.ofReal (1 / 2) = 6 := by
    rw [← ENNReal.ofReal_ofNat 12, ← ENNReal.ofReal_mul (by norm_num)]
    norm_num
  simp only at h
  rw [e1, eLpNorm_norm, eLpNorm_norm_rpow f (by norm_num : (0 : ℝ) < 1 / 2),
    eLpNorm_norm_rpow f (by norm_num : (0 : ℝ) < 1 / 2), e2, e3] at h
  simpa using h

/-- Converting an `Lⁿ` bound into the real form used by `e68_corrected`. -/
theorem rpow_integral_le_of_eLpNorm_le {F : Type*} [NormedAddCommGroup F] {p : ℕ} (hp : 0 < p)
    {g : Rn → F} (hg : MemLp g p volume) {c h : ℝ} (hc : 0 ≤ c) (hh : 0 ≤ h)
    (hle : eLpNorm g p volume ≤ ENNReal.ofReal (c * Real.sqrt h)) :
    (∫ x, ‖g x‖ ^ p) ^ (2 / (p : ℝ)) ≤ c ^ 2 * h := by
  rw [hg.eLpNorm_eq_integral_rpow_norm (by exact_mod_cast hp.ne') (ENNReal.natCast_ne_top p)]
    at hle
  simp only [ENNReal.toReal_natCast, Real.rpow_natCast] at hle
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at hle
  have hI : 0 ≤ ∫ x, ‖g x‖ ^ p := integral_nonneg fun x => by positivity
  have h2 := pow_le_pow_left₀ (Real.rpow_nonneg hI _) hle 2
  rw [← Real.rpow_mul_natCast hI, mul_pow, Real.sq_sqrt hh] at h2
  have hp' : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  convert h2 using 2
  push_cast
  field_simp

/-- **From an `Lⁿ` bound on `∇ψ` to the localized `H²` estimate.** -/
theorem ball_energy_le_of_grad_bound (hn : 2 < n) {c : ℝ} (hc : 0 ≤ c) {ψ : Rn → ℂ}
    {g : Rn → EuclideanSpace ℂ (Fin n)} {H : Fin n → Rn → EuclideanSpace ℂ (Fin n)}
    (h : IsH2 ψ g H) (hgn : MemLp g n volume)
    (hb : eLpNorm g n volume ≤ ENNReal.ofReal (c * Real.sqrt (h2sq ψ g H)))
    (x₀ : Rn) {R : ℝ} (hR : 0 < R) :
    (∫ x in ball x₀ R, ‖g x‖ ^ 2) ≤
      (volume.real (ball (0 : Rn) 1) ^ (1 - 2 / (n : ℝ)) * c ^ 2) * R ^ ((n : ℤ) - 2) *
        h2sq ψ g H := by
  have h1 := e68_corrected hn h.isH1 hgn x₀ hR
  have h2 := rpow_integral_le_of_eLpNorm_le (by omega) hgn hc (h2sq_nonneg ψ g H) hb
  have h3 : 0 ≤ volume.real (ball (0 : Rn) 1) ^ (1 - 2 / (n : ℝ)) * R ^ ((n : ℤ) - 2) :=
    mul_nonneg (Real.rpow_nonneg measureReal_nonneg _) (zpow_nonneg hR.le _)
  calc (∫ x in ball x₀ R, ‖g x‖ ^ 2) ≤
      volume.real (ball (0 : Rn) 1) ^ (1 - 2 / (n : ℝ)) * R ^ ((n : ℤ) - 2) *
        (∫ x, ‖g x‖ ^ n) ^ (2 / (n : ℝ)) := h1
    _ ≤ volume.real (ball (0 : Rn) 1) ^ (1 - 2 / (n : ℝ)) * R ^ ((n : ℤ) - 2) *
        (c ^ 2 * h2sq ψ g H) := mul_le_mul_of_nonneg_left h2 h3
    _ = _ := by ring

/-- The Sobolev embedding applied to each component of the weak gradient: for
`ψ ∈ H²(ℝⁿ)` and `1/p* = 1/2 - 1/n`, `‖∇ψ‖_{L^{p*}} ≤ n C_n ‖ψ‖_{H²}`. -/
theorem eLpNorm_grad_sobolev_le (hn : 0 < n) {p' : ℝ≥0} (hp' : (p' : ℝ)⁻¹ = 2⁻¹ - (n : ℝ)⁻¹)
    {ψ : Rn → ℂ} {g : Rn → EuclideanSpace ℂ (Fin n)}
    {H : Fin n → Rn → EuclideanSpace ℂ (Fin n)} (h : IsH2 ψ g H) (hp1 : 1 ≤ (p' : ℝ≥0∞)) :
    eLpNorm g p' volume ≤
      ENNReal.ofReal (n * sobolevConst n * Real.sqrt (h2sq ψ g H)) := by
  calc eLpNorm g p' volume ≤ ∑ i, eLpNorm (fun x => g x i) p' volume :=
        eLpNorm_le_sum_apply hp1 h.isH1.memLp_grad.1
    _ ≤ ∑ _i : Fin n, (sobolevConst n : ℝ≥0∞) * ENNReal.ofReal (Real.sqrt (h2sq ψ g H)) :=
        Finset.sum_le_sum fun i _ => (sobolev_H1 hn hp' (h.isH1_grad i)).trans
          (mul_le_mul_left' (eLpNorm_hess_le h i) _)
    _ = ENNReal.ofReal (n * sobolevConst n * Real.sqrt (h2sq ψ g H)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity), mul_assoc]

/-- **`n = 4`:** `‖∇ψ‖_{L⁴} ≤ 4 C₄ ‖ψ‖_{H²}`, from `H¹(ℝ⁴) ⊂ L⁴`. -/
theorem grad_bound_four {ψ : EuclideanSpace ℝ (Fin 4) → ℂ}
    {g : EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℂ (Fin 4)}
    {H : Fin 4 → EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℂ (Fin 4)} (h : IsH2 ψ g H) :
    MemLp g 4 volume ∧
      eLpNorm g 4 volume ≤ ENNReal.ofReal (4 * sobolevConst 4 * Real.sqrt (h2sq ψ g H)) := by
  have hb := eLpNorm_grad_sobolev_le (n := 4) (p' := 4) (by norm_num) (by norm_num) h
    (by norm_num)
  have e : ((4 : ℝ≥0) : ℝ≥0∞) = 4 := by norm_num
  rw [e] at hb
  exact ⟨⟨h.isH1.memLp_grad.1, hb.trans_lt ENNReal.ofReal_lt_top⟩, by exact_mod_cast hb⟩

/-- **`n = 3`:** `‖∇ψ‖_{L³} ≤ (3 C₃)^{1/2} ‖ψ‖_{H²}`, from `H¹(ℝ³) ⊂ L⁶` and the
interpolation `‖f‖₃ ≤ ‖f‖₂^{1/2} ‖f‖₆^{1/2}`. -/
theorem grad_bound_three {ψ : EuclideanSpace ℝ (Fin 3) → ℂ}
    {g : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℂ (Fin 3)}
    {H : Fin 3 → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℂ (Fin 3)} (h : IsH2 ψ g H) :
    MemLp g 3 volume ∧ eLpNorm g 3 volume ≤
      ENNReal.ofReal (Real.sqrt (3 * sobolevConst 3) * Real.sqrt (h2sq ψ g H)) := by
  set s := Real.sqrt (h2sq ψ g H) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have h6 := eLpNorm_grad_sobolev_le (n := 3) (p' := 6) (by norm_num) (by norm_num) h
    (by norm_num)
  have e : ((6 : ℝ≥0) : ℝ≥0∞) = 6 := by norm_num
  rw [e] at h6
  have h2 := eLpNorm_grad_le h
  have hb : eLpNorm g 3 volume ≤ ENNReal.ofReal (Real.sqrt (3 * sobolevConst 3) * s) := by
    refine (eLpNorm_three_le h.isH1.memLp_grad.1).trans ?_
    have hc0 : (0 : ℝ) ≤ 3 * sobolevConst 3 := by positivity
    calc eLpNorm g 2 volume ^ (1 / 2 : ℝ) * eLpNorm g 6 volume ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal s ^ (1 / 2 : ℝ) *
          ENNReal.ofReal ((3 : ℕ) * sobolevConst 3 * s) ^ (1 / 2 : ℝ) := by
          gcongr
      _ = ENNReal.ofReal (Real.sqrt (3 * sobolevConst 3) * s) := by
          rw [ENNReal.ofReal_rpow_of_nonneg hs0 (by norm_num),
            ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
            ← ENNReal.ofReal_mul (Real.rpow_nonneg hs0 _), ← Real.sqrt_eq_rpow,
            ← Real.sqrt_eq_rpow, ← Real.sqrt_mul hs0]
          congr 1
          push_cast
          rw [show s * (3 * (sobolevConst 3 : ℝ) * s) = (3 * sobolevConst 3) * s ^ 2 by ring,
            Real.sqrt_mul hc0, Real.sqrt_sq hs0]
  exact ⟨⟨h.isH1.memLp_grad.1, hb.trans_lt ENNReal.ofReal_lt_top⟩, hb⟩

/-- **Corollary 4.1 (`H²` localized estimate, `n ∈ {3, 4}`).** There is a constant `C_n`,
independent of `ψ`, `x₀` and `R`, such that `∫_{B_R(x₀)} |∇ψ|² ≤ C_n R^{n-2} ‖ψ‖²_{H²}` for
every `ψ ∈ H²(ℝⁿ)`. -/
theorem e68_H2 (hn : n = 3 ∨ n = 4) :
    ∃ C : ℝ, ∀ (ψ : Rn → ℂ) (g : Rn → EuclideanSpace ℂ (Fin n))
      (H : Fin n → Rn → EuclideanSpace ℂ (Fin n)), IsH2 ψ g H →
        ∀ (x₀ : Rn) (R : ℝ), 0 < R →
          (∫ x in ball x₀ R, ‖g x‖ ^ 2) ≤ C * R ^ ((n : ℤ) - 2) * h2sq ψ g H := by
  rcases hn with rfl | rfl
  · refine ⟨volume.real (ball (0 : EuclideanSpace ℝ (Fin 3)) 1) ^ (1 - 2 / ((3 : ℕ) : ℝ)) *
      Real.sqrt (3 * sobolevConst 3) ^ 2, fun ψ g H h x₀ R hR => ?_⟩
    obtain ⟨hm, hb⟩ := grad_bound_three h
    exact ball_energy_le_of_grad_bound (by norm_num) (Real.sqrt_nonneg _) h
      (by exact_mod_cast hm) (by exact_mod_cast hb) x₀ hR
  · refine ⟨volume.real (ball (0 : EuclideanSpace ℝ (Fin 4)) 1) ^ (1 - 2 / ((4 : ℕ) : ℝ)) *
      (4 * sobolevConst 4) ^ 2, fun ψ g H h x₀ R hR => ?_⟩
    obtain ⟨hm, hb⟩ := grad_bound_four h
    exact ball_energy_le_of_grad_bound (by norm_num) (by positivity) h
      (by exact_mod_cast hm) (by exact_mod_cast hb) x₀ hR

/-! ### Proposition 4.2: failure above dimension four -/

/-- The classical gradient of a dilated field: `∇(a φ(·/R))(x) = (a/R) ∇φ(x/R)`. -/
theorem gradVec_dilate {f : Rn → ℂ} (hf : Differentiable ℝ f) (a R : ℝ) (x : Rn) :
    gradVec (fun y => a • f (R⁻¹ • y)) x = (a * R⁻¹) • gradVec f (R⁻¹ • x) := by
  have hd : DifferentiableAt ℝ (fun y => f (R⁻¹ • y)) x :=
    (hf (R⁻¹ • x)).comp x (differentiableAt_id.const_smul R⁻¹)
  show coordVec (fderiv ℝ (a • fun y => f (R⁻¹ • y)) x) = _
  rw [fderiv_const_smul hd, fderiv_comp_smul, smul_smul, map_smul]
  rfl

/-- `u_R(x) = R^{2-n/2} φ(x/R)`. -/
def dilateH2 (R : ℝ) (φ : Rn → ℂ) (x : Rn) : ℂ := (R ^ (2 - (n : ℝ) / 2)) • φ (R⁻¹ • x)

theorem amp_sq_mul {R : ℝ} (hR : 0 < R) : (R ^ (2 - (n : ℝ) / 2)) ^ 2 * R ^ n = R ^ 4 := by
  rw [← Real.rpow_natCast R n, ← Real.rpow_mul_natCast hR.le, ← Real.rpow_add hR,
    show (2 - (n : ℝ) / 2) * ((2 : ℕ) : ℝ) + n = ((4 : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_natCast]

/-- `‖u_R‖²_{L²} = R⁴ ‖φ‖²_{L²}`. -/
theorem integral_dilateH2_sq {R : ℝ} (hR : 0 < R) (φ : Rn → ℂ) :
    (∫ x, ‖dilateH2 R φ x‖ ^ 2) = R ^ 4 * ∫ x, ‖φ x‖ ^ 2 := by
  have e : ∀ x, ‖dilateH2 R φ x‖ ^ 2 = (R ^ (2 - (n : ℝ) / 2)) ^ 2 * ‖φ (R⁻¹ • x)‖ ^ 2 := by
    intro x
    rw [dilateH2, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  simp_rw [e]
  rw [integral_const_mul, integral_inverse_smul_exact n R hR (fun y => ‖φ y‖ ^ 2), ← mul_assoc,
    amp_sq_mul hR]

/-- `‖∇u_R‖²_{L²} = R² ‖∇φ‖²_{L²}`. -/
theorem integral_gradVec_dilateH2_sq {R : ℝ} (hR : 0 < R) {φ : Rn → ℂ}
    (hφ : Differentiable ℝ φ) :
    (∫ x, ‖gradVec (dilateH2 R φ) x‖ ^ 2) = R ^ 2 * ∫ x, ‖gradVec φ x‖ ^ 2 := by
  have e : ∀ x, ‖gradVec (dilateH2 R φ) x‖ ^ 2 =
      (R ^ (2 - (n : ℝ) / 2) * R⁻¹) ^ 2 * ‖gradVec φ (R⁻¹ • x)‖ ^ 2 := by
    intro x
    rw [show dilateH2 R φ = fun y => (R ^ (2 - (n : ℝ) / 2)) • φ (R⁻¹ • y) from rfl,
      gradVec_dilate hφ, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  simp_rw [e]
  rw [integral_const_mul, integral_inverse_smul_exact n R hR (fun y => ‖gradVec φ y‖ ^ 2),
    ← mul_assoc]
  congr 1
  have h := amp_sq_mul (n := n) hR
  set a := R ^ (2 - (n : ℝ) / 2)
  calc (a * R⁻¹) ^ 2 * R ^ n = (a ^ 2 * R ^ n) * (R⁻¹) ^ 2 := by ring
    _ = R ^ 2 := by rw [h]; field_simp

/-- `‖∇∂ᵢu_R‖²_{L²} = ‖∇∂ᵢφ‖²_{L²}`: the second-derivative energy is scale invariant. -/
theorem integral_hess_dilateH2_sq {R : ℝ} (hR : 0 < R) {φ : Rn → ℂ}
    (hφ : ContDiff ℝ 2 φ) (i : Fin n) :
    (∫ x, ‖gradVec (fun y => gradVec (dilateH2 R φ) y i) x‖ ^ 2) =
      ∫ x, ‖gradVec (fun y => gradVec φ y i) x‖ ^ 2 := by
  have hd : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hdi : Differentiable ℝ (fun z => gradVec φ z i) :=
    ((hφ.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).differentiable
      (by simp)
  have e1 : (fun y => gradVec (dilateH2 R φ) y i) =
      fun y => (R ^ (2 - (n : ℝ) / 2) * R⁻¹) • (fun z => gradVec φ z i) (R⁻¹ • y) := by
    funext y
    rw [show dilateH2 R φ = fun y => (R ^ (2 - (n : ℝ) / 2)) • φ (R⁻¹ • y) from rfl,
      gradVec_dilate hd]
    rfl
  have e : ∀ x, ‖gradVec (fun y => gradVec (dilateH2 R φ) y i) x‖ ^ 2 =
      (R ^ (2 - (n : ℝ) / 2) * R⁻¹ * R⁻¹) ^ 2 *
        ‖gradVec (fun y => gradVec φ y i) (R⁻¹ • x)‖ ^ 2 := by
    intro x
    rw [e1, gradVec_dilate hdi, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  simp_rw [e]
  rw [integral_const_mul, integral_inverse_smul_exact n R hR
    (fun y => ‖gradVec (fun y => gradVec φ y i) y‖ ^ 2), ← mul_assoc]
  have h := amp_sq_mul (n := n) hR
  have hR4 : (R ^ (2 - (n : ℝ) / 2) * R⁻¹ * R⁻¹) ^ 2 * R ^ n = 1 := by
    set a := R ^ (2 - (n : ℝ) / 2)
    calc (a * R⁻¹ * R⁻¹) ^ 2 * R ^ n = (a ^ 2 * R ^ n) * (R⁻¹) ^ 4 := by ring
      _ = 1 := by rw [h]; field_simp
  rw [hR4, one_mul]

theorem gradVec_eq_zero_of_notMem_tsupport {f : Rn → ℂ} {y : Rn} (hy : y ∉ tsupport f) :
    gradVec f y = 0 := by
  have : fderiv ℝ f y = 0 := by
    by_contra h
    exact hy (support_fderiv_subset ℝ h)
  rw [gradVec, this, map_zero]

/-- The complexified compact profile, supported in `B̄(0, 1/2)`. -/
def h2Profile (n : ℕ) : EuclideanSpace ℝ (Fin n) → ℂ :=
  ofRealFn (fun y => compactProfile n y)

theorem contDiff_h2Profile : ContDiff ℝ ∞ (h2Profile n) :=
  Complex.ofRealCLM.contDiff.comp (compactProfile_smooth n)

theorem h2Profile_eq_zero {y : Rn} (hy : 1 / 2 ≤ ‖y‖) : h2Profile n y = 0 := by
  rw [h2Profile, ofRealFn, (compactProfile n).zero_of_le_dist (by simpa [compactProfile] using hy),
    Complex.ofReal_zero]

theorem gradVec_h2Profile_eq_zero {y : Rn} (hy : 1 / 2 < ‖y‖) : gradVec (h2Profile n) y = 0 := by
  apply gradVec_eq_zero_of_notMem_tsupport
  intro hmem
  have hsub : tsupport (h2Profile n) ⊆ closedBall (0 : Rn) (1 / 2) := by
    apply closure_minimal _ isClosed_closedBall
    intro z hz
    by_contra hz'
    exact hz (h2Profile_eq_zero (by simpa [mem_closedBall, dist_zero_right, le_of_lt] using
      (lt_of_not_ge (fun h => hz' (mem_closedBall_zero_iff.2 h))).le))
  have := mem_closedBall_zero_iff.1 (hsub hmem)
  linarith

theorem contDiff_dilateH2 (R : ℝ) {φ : Rn → ℂ} (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (dilateH2 R φ) :=
  (hφ.comp (contDiff_id.const_smul R⁻¹)).const_smul _

theorem hasCompactSupport_dilateH2 {R : ℝ} (hR : 0 < R) {φ : Rn → ℂ}
    (hφc : HasCompactSupport φ) : HasCompactSupport (dilateH2 R φ) :=
  (hφc.comp_smul (inv_ne_zero hR.ne')).smul_left (f := fun _ => R ^ (2 - (n : ℝ) / 2))

/-- The gradient of `u_R` vanishes outside `B_R`, so its ball energy is its total energy. -/
theorem ball_energy_dilateH2 {R : ℝ} (hR : 0 < R) :
    (∫ x in ball (0 : Rn) R, ‖gradVec (dilateH2 R (h2Profile n)) x‖ ^ 2) =
      ∫ x, ‖gradVec (dilateH2 R (h2Profile n)) x‖ ^ 2 := by
  have hd : Differentiable ℝ (h2Profile n : Rn → ℂ) :=
    contDiff_h2Profile.differentiable (by simp)
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  have hx' : R ≤ ‖x‖ := by simpa [mem_ball, dist_zero_right] using hx
  have hy : 1 / 2 < ‖R⁻¹ • x‖ := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hR.le), inv_mul_eq_div,
      lt_div_iff₀ hR]
    linarith
  rw [show dilateH2 R (h2Profile n) =
      fun y => (R ^ (2 - (n : ℝ) / 2)) • h2Profile n (R⁻¹ • y) from rfl,
    gradVec_dilate hd, gradVec_h2Profile_eq_zero hy, smul_zero, norm_zero]
  norm_num

/-- **Proposition 4.2.** For `n > 4` there is no constant `C` for which
`∫_{B_R} |∇ψ|² ≤ C R^{n-2} ‖ψ‖²_{H²}` holds for all `ψ ∈ C_c^∞(ℝⁿ)` and all `R > 0`. The
fields `u_R(x) = R^{2-n/2} φ(x/R)` have `∫_{B_R} |∇u_R|² = R² ‖∇φ‖²₂` and
`‖u_R‖²_{H²} = R⁴‖φ‖²₂ + R²‖∇φ‖²₂ + ‖D²φ‖²₂`. -/
theorem not_e68_H2_smooth (hn : 4 < n) :
    ¬ ∃ C : ℝ, ∀ ψ : Rn → ℂ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → ∀ R : ℝ, 0 < R →
      (∫ x in ball (0 : Rn) R, ‖gradVec ψ x‖ ^ 2) ≤
        C * R ^ ((n : ℤ) - 2) *
          h2sq ψ (gradVec ψ) (fun i => gradVec (fun x => gradVec ψ x i)) := by
  rintro ⟨C, hC⟩
  have hφ : ContDiff ℝ ∞ (h2Profile n) := contDiff_h2Profile
  have hφ2 : ContDiff ℝ 2 (h2Profile n) := hφ.of_le (WithTop.coe_le_coe.2 le_top)
  have hφd : Differentiable ℝ (h2Profile n) := hφ.differentiable (by simp)
  have hφc : HasCompactSupport (h2Profile n) :=
    (compactProfile_hasCompactSupport n).comp_left Complex.ofReal_zero
  set A := ∫ x, ‖h2Profile n x‖ ^ 2
  set B := ∫ x, ‖gradVec (h2Profile n) x‖ ^ 2 with hBdef
  set D := ∑ i, ∫ x, ‖gradVec (fun y => gradVec (h2Profile n) y i) x‖ ^ 2
  have hB : 0 < B := by
    have hdr : Differentiable ℝ (fun y : Rn => compactProfile n y) :=
      (compactProfile_smooth n).differentiable (by simp)
    have := compactProfile_gradient_energy_positive n (by omega)
    rw [hBdef]
    simp_rw [h2Profile, norm_gradVec_ofRealFn (hdr _)]
    exact this
  apply high_dimensional_H2_scaling_obstruction n hn B A B D hB
  refine ⟨C, fun R hR => ?_⟩
  have h := hC (dilateH2 R (h2Profile n)) (contDiff_dilateH2 R hφ)
    (hasCompactSupport_dilateH2 hR hφc) R hR
  have hz : R ^ ((n : ℤ) - 2) = R ^ (n - 2) := by
    rw [show (n : ℤ) - 2 = ((n - 2 : ℕ) : ℤ) by omega, zpow_natCast]
  rw [ball_energy_dilateH2 hR, integral_gradVec_dilateH2_sq hR hφd, hz] at h
  unfold h2sq at h
  rw [integral_dilateH2_sq hR, integral_gradVec_dilateH2_sq hR hφd] at h
  simp_rw [integral_hess_dilateH2_sq hR hφ2] at h
  exact h

/-- **Proposition 4.2 on `H²`.** For `n > 4` the localized `H²` estimate fails on
`H²(ℝⁿ)`, even for the single center `0`. -/
theorem not_e68_H2 (hn : 4 < n) :
    ¬ ∃ C : ℝ, ∀ (ψ : Rn → ℂ) (g : Rn → EuclideanSpace ℂ (Fin n))
      (H : Fin n → Rn → EuclideanSpace ℂ (Fin n)), IsH2 ψ g H →
        ∀ (x₀ : Rn) (R : ℝ), 0 < R →
          (∫ x in ball x₀ R, ‖g x‖ ^ 2) ≤ C * R ^ ((n : ℤ) - 2) * h2sq ψ g H := by
  rintro ⟨C, hC⟩
  exact not_e68_H2_smooth hn
    ⟨C, fun ψ hψ hψc R hR => hC _ _ _ (isH2_of_contDiff hψ hψc) 0 R hR⟩

end ReyesMath.E68
