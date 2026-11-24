import MathProofs.StrictBinding
import MathProofs.FourierShellL2

/-! Shifted-shell Fourier estimates in the exact repository H² space.
Candidate implementation, to be checked against the pinned Mathlib version. -/

open Filter Topology Complex InnerProductSpace MeasureTheory Set
open scoped ContDiff FourierTransform

namespace ReyesMath
namespace Sobolev

local notation "R2" => EuclideanSpace ℝ (Fin 2)

theorem integrable_inv_shell (k : ℝ) {η : ℝ} (hη : 0 < η) :
    Integrable fun ξ : R2 => 1 / ((qS ξ - k ^ 2) ^ 2 + η) := by
  let C : ℝ := 2 + 2 * k ^ 4 / η
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ((integrable_inv_quartic hη).const_mul C).mono' ?_ ?_
  · exact Continuous.aestronglyMeasurable (continuous_const.div
      (by unfold qS; fun_prop) (fun ξ => by positivity))
  · filter_upwards [] with ξ
    let q := qS ξ
    let w := (q - k ^ 2) ^ 2 + η
    have hw : 0 < w := by dsimp [w]; positivity
    have hq : 0 < q ^ 2 + η := by positivity
    change ‖1 / w‖ ≤ C * (1 / (q ^ 2 + η))
    rw [Real.norm_of_nonneg (by positivity)]
    have hh : q ^ 2 + η ≤ C * w := by
      have he : C * w = 2 * (q - k ^ 2) ^ 2 + 2 * η + 2 * k ^ 4 +
          (2 * k ^ 4 / η) * (q - k ^ 2) ^ 2 := by
        dsimp [C, w]
        field_simp
        <;> ring
      rw [he]
      nlinarith [sq_nonneg (q - 2 * k ^ 2),
        mul_nonneg (show 0 ≤ 2 * k ^ 4 / η by positivity) (sq_nonneg (q - k ^ 2))]
    calc
      1 / w ≤ C / (q ^ 2 + η) := (div_le_div_iff₀ hw hq).2 (by simpa using hh)
      _ = _ := by ring

/-- Bound the shifted quadratic integral on the positive half-line by its full-line value. -/
theorem integral_halfline_shell_le (k : ℝ) {c η : ℝ} (hc : 0 < c) (hη : 0 < η) :
    (∫ u in Ioi (0 : ℝ), 1 / ((c * u - k ^ 2) ^ 2 + η)) ≤
      Real.pi / (c * Real.sqrt η) := by
  let b := c / Real.sqrt η
  have hs := Real.sqrt_pos.2 hη
  have hb : 0 < b := div_pos hc hs
  have he (u : ℝ) : 1 / ((c * u - k ^ 2) ^ 2 + η) =
      η⁻¹ * (1 + (b * (u - k ^ 2 / c)) ^ 2)⁻¹ := by
    dsimp [b]
    field_simp [hc.ne', hs.ne', hη.ne']
    rw [Real.sq_sqrt hη.le]
    <;> ring
  have hint : Integrable (fun u : ℝ => 1 / ((c * u - k ^ 2) ^ 2 + η)) := by
    simp_rw [he]
    exact ((integrable_inv_one_add_mul_sq hb.ne').comp_sub_right (k ^ 2 / c)).const_mul _
  calc
    (∫ u in Ioi (0 : ℝ), 1 / ((c * u - k ^ 2) ^ 2 + η)) ≤
        ∫ u : ℝ, 1 / ((c * u - k ^ 2) ^ 2 + η) :=
      setIntegral_le_integral hint (Eventually.of_forall fun _ => by positivity)
    _ = Real.pi / (c * Real.sqrt η) := by
      simp_rw [he]
      rw [integral_const_mul, integral_sub_right_eq_self,
        integral_univ_inv_one_add_mul_sq, abs_of_pos hb]
      dsimp [b]
      field_simp
      rw [Real.sq_sqrt hη.le]

/-- In dimension two the inverse shifted-symbol weight is bounded uniformly in k. -/
theorem integral_inv_shell_le (k : ℝ) {η : ℝ} (hη : 0 < η) :
    (∫ ξ : R2, 1 / ((qS ξ - k ^ 2) ^ 2 + η)) ≤ 1 / (4 * Real.sqrt η) := by
  have hπ : 0 < Real.pi := Real.pi_pos
  unfold qS
  have hrad := integral_fun_norm_addHaar (volume : Measure R2)
    (fun r : ℝ => 1 / (((2 * Real.pi) ^ 2 * r ^ 2 - k ^ 2) ^ 2 + η))
  simp only at hrad
  rw [hrad, finrank_euclideanSpace_fin]
  have hball : (volume : Measure R2).real (Metric.ball 0 1) = Real.pi := by
    rw [Measure.real, EuclideanSpace.volume_ball_fin_two]
    simp [ENNReal.toReal_ofReal hπ.le]
  rw [hball]
  have hinner : ∫ y in Ioi (0 : ℝ), y ^ (2 - 1) •
      (1 / (((2 * Real.pi) ^ 2 * y ^ 2 - k ^ 2) ^ 2 + η)) =
      1 / 2 * ∫ u in Ioi (0 : ℝ), 1 / (((2 * Real.pi) ^ 2 * u - k ^ 2) ^ 2 + η) := by
    have hsub := integral_comp_rpow_Ioi_of_pos
      (g := fun u : ℝ => 1 / (((2 * Real.pi) ^ 2 * u - k ^ 2) ^ 2 + η))
      (p := 2) two_pos
    rw [← hsub, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
    simp only [smul_eq_mul]
    rw [show ((2 : ℝ) - 1) = 1 by norm_num, Real.rpow_one, Real.rpow_two]
    norm_num
    ring
  rw [hinner]
  simp only [nsmul_eq_mul, smul_eq_mul, Nat.cast_ofNat]
  have h := integral_halfline_shell_le k (c := (2 * Real.pi) ^ 2) (by positivity) hη
  calc
    _ ≤ 2 * Real.pi * (1 / 2 * (Real.pi / ((2 * Real.pi) ^ 2 * Real.sqrt η))) := by gcongr
    _ = _ := by field_simp; ring

private theorem norm_shift_fourier (φ : SchwartzMap R2 ℂ) (k : ℝ) (ξ : R2) :
    ‖𝓕 (⇑(lapS φ + ((k ^ 2 : ℝ) : ℂ) • φ)) ξ‖ ^ 2 =
      (qS ξ - k ^ 2) ^ 2 * ‖𝓕 (⇑φ) ξ‖ ^ 2 := by
  rw [← coe_fS, fS_add, fS_smul, SchwartzMap.add_apply, SchwartzMap.smul_apply,
    coe_fS, coe_fS, fourier_lapS, smul_eq_mul]
  rw [← add_mul]
  rw [show -(qS ξ : ℂ) + ((k ^ 2 : ℝ) : ℂ) = -((qS ξ - k ^ 2 : ℝ) : ℂ) by push_cast; ring]
  rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]

theorem integrable_weight_shell (φ : SchwartzMap R2 ℂ) (k η : ℝ) :
    Integrable fun ξ : R2 => ((qS ξ - k ^ 2) ^ 2 + η) * ‖𝓕 (⇑φ) ξ‖ ^ 2 := by
  have h1 : Integrable fun ξ : R2 => (qS ξ - k ^ 2) ^ 2 * ‖𝓕 (⇑φ) ξ‖ ^ 2 := by
    refine (integrable_normSq (fS (lapS φ + ((k ^ 2 : ℝ) : ℂ) • φ))).congr
      (Eventually.of_forall fun ξ => ?_)
    rw [coe_fS, norm_shift_fourier]
  have h2 : Integrable fun ξ : R2 => ‖𝓕 (⇑φ) ξ‖ ^ 2 := by
    rw [← coe_fS]
    exact integrable_normSq (fS φ)
  simp_rw [add_mul]
  exact h1.add (h2.const_mul η)

theorem integral_weight_shell (φ : SchwartzMap R2 ℂ) (k η : ℝ) :
    ∫ ξ, ((qS ξ - k ^ 2) ^ 2 + η) * ‖𝓕 (⇑φ) ξ‖ ^ 2 =
      ‖toL2 (lapS φ) + ((k ^ 2 : ℝ) : ℂ) • toL2 φ‖ ^ 2 + η * ‖toL2 φ‖ ^ 2 := by
  have h1 : Integrable fun ξ : R2 => (qS ξ - k ^ 2) ^ 2 * ‖𝓕 (⇑φ) ξ‖ ^ 2 := by
    refine (integrable_normSq (fS (lapS φ + ((k ^ 2 : ℝ) : ℂ) • φ))).congr
      (Eventually.of_forall fun ξ => ?_)
    rw [coe_fS, norm_shift_fourier]
  have h2 : Integrable fun ξ : R2 => ‖𝓕 (⇑φ) ξ‖ ^ 2 := by
    rw [← coe_fS]
    exact integrable_normSq (fS φ)
  simp_rw [add_mul]
  rw [integral_add h1 (h2.const_mul η), integral_const_mul, ← norm_toL2_sq_fourier]
  simp_rw [← norm_shift_fourier φ k]
  rw [← norm_toL2_sq_fourier, map_add, map_smul]

theorem sup_bound_shell_schwartz (φ : SchwartzMap R2 ℂ) (k : ℝ) {η : ℝ} (hη : 0 < η) (x : R2) :
    ‖φ x‖ ^ 2 ≤ (‖toL2 (lapS φ) + ((k ^ 2 : ℝ) : ℂ) • toL2 φ‖ ^ 2 + η * ‖toL2 φ‖ ^ 2) / (4 * Real.sqrt η) := by
  set A : ℝ := 1 / (4 * Real.sqrt η) with hA
  set B : ℝ := ‖toL2 (lapS φ) + ((k ^ 2 : ℝ) : ℂ) • toL2 φ‖ ^ 2 + η * ‖toL2 φ‖ ^ 2 with hB
  have hsη := Real.sqrt_pos.2 hη
  have hApos : 0 < A := by positivity
  have hB0 : 0 ≤ B := by positivity
  have hFφ : Integrable (𝓕 (⇑φ)) := by rw [← coe_fS]; exact (fS φ).integrable
  have hinv : 𝓕⁻ (𝓕 (⇑φ)) = ⇑φ := Continuous.fourier_inversion φ.continuous φ.integrable hFφ
  -- `|φ(x)| ≤ ∫ |𝓕φ|`
  have h1 : ‖φ x‖ ≤ ∫ ξ, ‖𝓕 (⇑φ) ξ‖ := by
    conv_lhs => rw [← hinv, Real.fourierIntegralInv_eq]
    refine le_trans (norm_integral_le_integral_norm _) (le_of_eq ?_)
    congr 1
    funext ξ
    simp [Circle.smul_def]
  -- AM–GM against the weight
  have h2 : ∀ t : ℝ, 0 < t → ∫ ξ, ‖𝓕 (⇑φ) ξ‖ ≤ (t * A + B / t) / 2 := by
    intro t ht
    have hw : ∀ ξ : R2, 0 < (qS ξ - k ^ 2) ^ 2 + η := fun ξ => by positivity
    have hmono : ∀ ξ : R2, ‖𝓕 (⇑φ) ξ‖ ≤
        (t * (1 / ((qS ξ - k ^ 2) ^ 2 + η)) + ((qS ξ - k ^ 2) ^ 2 + η) * ‖𝓕 (⇑φ) ξ‖ ^ 2 / t) / 2 := by
      intro ξ
      have hwξ := hw ξ
      set a := ‖𝓕 (⇑φ) ξ‖
      set w := (qS ξ - k ^ 2) ^ 2 + η
      rw [le_div_iff₀ two_pos]
      have hid : t * (1 / w) + w * a ^ 2 / t - a * 2 = (t - w * a) ^ 2 / (w * t) := by
        field_simp
        ring
      have : 0 ≤ (t - w * a) ^ 2 / (w * t) := by positivity
      linarith
    have hint : Integrable fun ξ : R2 =>
        (t * (1 / ((qS ξ - k ^ 2) ^ 2 + η)) + ((qS ξ - k ^ 2) ^ 2 + η) * ‖𝓕 (⇑φ) ξ‖ ^ 2 / t) / 2 := by
      have hW := integrable_weight_shell φ k η
      exact (((integrable_inv_shell k hη).const_mul t).add (hW.div_const t)).div_const 2
    calc ∫ ξ, ‖𝓕 (⇑φ) ξ‖
        ≤ ∫ ξ, (t * (1 / ((qS ξ - k ^ 2) ^ 2 + η)) + ((qS ξ - k ^ 2) ^ 2 + η) * ‖𝓕 (⇑φ) ξ‖ ^ 2 / t) / 2 :=
          integral_mono (integrable_fourier_norm φ) hint hmono
      _ ≤ (t * A + B / t) / 2 := by
          have hW := integrable_weight_shell φ k η
          rw [integral_div, integral_add ((integrable_inv_shell k hη).const_mul t)
            (hW.div_const t), integral_const_mul, integral_div, integral_weight_shell]
          have hI := mul_le_mul_of_nonneg_left (integral_inv_shell_le k hη) ht.le
          rw [hA, hB]
          linarith
  -- optimize
  have hnn : 0 ≤ ‖φ x‖ := norm_nonneg _
  have key : ‖φ x‖ ^ 2 ≤ A * B := by
    rcases hB0.lt_or_eq with hBpos | hB0'
    · set t := Real.sqrt (B / A) with ht
      have htpos : 0 < t := Real.sqrt_pos.2 (div_pos hBpos hApos)
      have h3 := le_trans h1 (h2 t htpos)
      have ht2 : t ^ 2 = B / A := Real.sq_sqrt (div_pos hBpos hApos).le
      have h4 : (t * A + B / t) / 2 = t * A := by
        field_simp
        rw [ht2]
        field_simp
        ring
      rw [h4] at h3
      have h5 : (t * A) ^ 2 = A * B := by
        rw [mul_pow, ht2]
        field_simp
      calc ‖φ x‖ ^ 2 ≤ (t * A) ^ 2 := pow_le_pow_left₀ hnn h3 2
        _ = A * B := h5
    · have h3 : ∀ t : ℝ, 0 < t → ‖φ x‖ ≤ t * A / 2 := fun t ht => by
        have := le_trans h1 (h2 t ht)
        rw [← hB0', zero_div, add_zero] at this
        exact this
      have h4 : ‖φ x‖ ≤ 0 := by
        by_contra hcon
        push_neg at hcon
        have := h3 (‖φ x‖ / A) (div_pos hcon hApos)
        field_simp at this
        linarith
      have : ‖φ x‖ = 0 := le_antisymm h4 hnn
      rw [this, ← hB0']
      simp
  calc ‖φ x‖ ^ 2 ≤ A * B := key
    _ = B / (4 * Real.sqrt η) := by rw [hA]; ring


namespace H2

theorem ae_sup_bound_shell (U : H2 2) (k : ℝ) {η : ℝ} (hη : 0 < η) :
    ∀ᵐ x ∂(volume : Measure R2), ‖U.val x‖ ^ 2 ≤ (T k U + η * M U) / (4 * Real.sqrt η) := by
  obtain ⟨φ, h0, -, h2⟩ := U.approx
  obtain ⟨ns, hmono, hns⟩ := (tendstoInMeasure_of_tendsto_Lp h0).exists_seq_tendsto_ae
  have hcoe : ∀ᵐ x ∂(volume : Measure R2), ∀ n, (toL2 (φ n) : R2 → ℂ) x = φ n x :=
    ae_all_iff.2 fun n => coeFn_toL2 (φ n)
  have hs : Tendsto ns atTop atTop := hmono.tendsto_atTop
  filter_upwards [hns, hcoe] with x hx hc
  have hlim1 : Tendsto (fun i => ‖φ (ns i) x‖ ^ 2) atTop (𝓝 (‖U.val x‖ ^ 2)) := by
    have := (hx.norm).pow 2
    simpa only [hc] using this
  have hlim2 : Tendsto (fun i => (‖toL2 (lapS (φ (ns i))) + ((k ^ 2 : ℝ) : ℂ) • toL2 (φ (ns i))‖ ^ 2 + η * ‖toL2 (φ (ns i))‖ ^ 2) /
      (4 * Real.sqrt η)) atTop (𝓝 ((T k U + η * M U) / (4 * Real.sqrt η))) := by
    have hA := (((h2.comp hs).add ((h0.comp hs).const_smul ((k ^ 2 : ℝ) : ℂ))).norm).pow 2
    have hB := (((h0.comp hs).norm).pow 2).const_mul η
    exact (hA.add hB).div_const _
  exact le_of_tendsto_of_tendsto' hlim1 hlim2 fun i => sup_bound_shell_schwartz (φ (ns i)) k hη x

end H2
end Sobolev
end ReyesMath

#print axioms ReyesMath.Sobolev.H2.ae_sup_bound_shell
