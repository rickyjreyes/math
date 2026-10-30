import MathProofs.V18MiddleFloor

/-!
# Strict clipping and floor bounds at the frozen observation vector

These estimates apply to the actual real-valued forward model. The
logarithmic and exponential estimates are kernel-checked; no numerical
certificate is used as a hypothesis.
-/

noncomputable section
namespace ReyesMath.V18Forward

private theorem log_three_lt : Real.log (3 : ℝ) < 1.1 := by
  apply (Real.log_lt_iff_lt_exp (by norm_num)).2
  have h := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 1.1 by norm_num) 6
  norm_num [Finset.sum_range_succ] at h
  linarith

private theorem log_four_lt : Real.log (4 : ℝ) < 1.387 := by
  have h : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    calc
      Real.log (4 : ℝ) = Real.log ((2 : ℝ)^2) := by norm_num
      _ = 2 * Real.log 2 := Real.log_pow _ _
  rw [h]
  linarith [Real.log_two_lt_d9]

private theorem exp_light_one_lt : Real.exp (-6.1744 : ℝ) < 0.01 := by
  have h := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 6.1744 by norm_num) 7
  norm_num [Finset.sum_range_succ] at h
  have he : (100 : ℝ) < Real.exp 6.1744 := by linarith
  have hi := one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 100) he
  convert hi using 1 <;> norm_num [Real.exp_neg]

private theorem exp_light_two_lt : Real.exp (-12.3488 : ℝ) < 0.01 :=
  lt_of_le_of_lt (Real.exp_le_exp.mpr (by norm_num)) exp_light_one_lt

private theorem exp_light_three_lt : Real.exp (-18.5232 : ℝ) < 0.001 := by
  have h := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 18.5232 by norm_num) 4
  norm_num [Finset.sum_range_succ] at h
  have he : (1000 : ℝ) < Real.exp 18.5232 := by linarith
  have hi := one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 1000) he
  convert hi using 1 <;> norm_num [Real.exp_neg]

/-- The frozen light numerator, retaining the source clipping operation. -/
def frozenLightBase (n : ℕ) : ℝ :=
  (0.3877 : ℝ) * (if n = 0 then 0 else (n : ℝ) / (n + 1)) +
    (-2.3676) * topo n + (-8.2963) * Real.log (1 + (n : ℝ)) +
    6.8830 * (n : ℝ)^2 + (-1.7948) * (n : ℝ)^3 +
    (-8.6415) * Real.exp (clip (-50) 50 ((-6.1744) * (n : ℝ))) +
    0.9981 / (if n = 0 then 1 else (n : ℝ)^2)

theorem frozen_lightRaw_eq (alpha : ℝ) (n : ℕ) :
    lightRaw (frozen alpha 5) n = frozenLightBase n *
      (1 + Real.exp (alpha * ((n : ℝ) - 5)))⁻¹ *
      (if n = 3 then (0.0048 : ℝ) else 1) := by
  simp only [lightRaw, frozen, frozenLightBase, Matrix.cons_val]
  split_ifs <;> simp_all

private theorem frozenLightBase_one : (0.4 : ℝ) < frozenLightBase 1 := by
  norm_num [frozenLightBase, topo, clip]
  have hl : Real.log (2 : ℝ) < 0.694 := lt_trans Real.log_two_lt_d9 (by norm_num)
  have he := exp_light_one_lt
  norm_num only at hl he
  linarith

private theorem frozenLightBase_two : (2 : ℝ) < frozenLightBase 2 := by
  norm_num [frozenLightBase, topo, clip]
  have hl := log_three_lt
  have he := exp_light_two_lt
  norm_num only at hl he
  linarith

private theorem frozenLightBase_three : (0.005 : ℝ) < frozenLightBase 3 := by
  norm_num [frozenLightBase, topo, clip]
  have hl := log_four_lt
  have he := exp_light_three_lt
  norm_num only at hl he
  linarith

private theorem suppression_ge_half {alpha x : ℝ} (ha : 0 ≤ alpha) (hx : x ≤ 5) :
    (1 / 2 : ℝ) ≤ (1 + Real.exp (alpha * (x - 5)))⁻¹ := by
  have he : Real.exp (alpha * (x - 5)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos ha (sub_nonpos.mpr hx))
  simpa only [one_div] using
    one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 1 + Real.exp (alpha * (x - 5)))
      (show 1 + Real.exp (alpha * (x - 5)) ≤ 2 by linarith)

/-- All three observed light floors are strictly inactive. The estimate
holds for every nonnegative alpha, including the manuscript interval. -/
theorem frozen_light_floor_lt (alpha : ℝ) (ha : 0 ≤ alpha) (i : Fin 3) :
    (1e-12 : ℝ) < lightRaw (frozen alpha 5) (i.val + 1) := by
  rw [frozen_lightRaw_eq]
  fin_cases i
  · norm_num only [Fin.val_zero, zero_add, Nat.reduceEqDiff, ↓reduceIte]
    have hs := suppression_ge_half ha (by norm_num : (1 : ℝ) ≤ 5)
    have hp := mul_lt_mul_of_pos_right frozenLightBase_one
      (by positivity : (0 : ℝ) < (1 + Real.exp (alpha * (1 - 5)))⁻¹)
    norm_num at hs hp ⊢
    nlinarith only [hs, hp]
  · norm_num only [Fin.val_one, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
    have hs := suppression_ge_half ha (by norm_num : (2 : ℝ) ≤ 5)
    have hp := mul_lt_mul_of_pos_right frozenLightBase_two
      (by positivity : (0 : ℝ) < (1 + Real.exp (alpha * (2 - 5)))⁻¹)
    norm_num at hs hp ⊢
    nlinarith only [hs, hp]
  · norm_num only [Fin.reduceFinMk, Nat.reduceAdd, ↓reduceIte, Nat.cast_ofNat]
    have hs := suppression_ge_half ha (by norm_num : (3 : ℝ) ≤ 5)
    have hp := mul_lt_mul_of_pos_right frozenLightBase_three
      (by positivity : (0 : ℝ) < (1 + Real.exp (alpha * (3 - 5)))⁻¹)
    norm_num at hs hp ⊢
    nlinarith only [hs, hp]

/-- The three heavy observation indices, in output order. -/
def heavyN : Fin 3 → ℕ := ![95, 96, 123]

theorem frozen_light_exp_clip (alpha : ℝ) (i : Fin 3) :
    -50 < frozen alpha 5 6 * (i.val + 1 : ℕ) ∧
      frozen alpha 5 6 * (i.val + 1 : ℕ) < 50 := by
  change -50 < (-6.1744 : ℝ) * (i.val + 1 : ℕ) ∧
    (-6.1744 : ℝ) * (i.val + 1 : ℕ) < 50
  fin_cases i <;> norm_num

theorem frozen_heavy_exp_clip (alpha : ℝ) (i : Fin 3) :
    frozen alpha 5 6 * (heavyN i : ℝ) < -50 := by
  change (-6.1744 : ℝ) * (heavyN i : ℝ) < -50
  fin_cases i <;> norm_num [heavyN, Matrix.cons_val]

theorem frozen_boson_power_clip (alpha : ℝ) :
    -10 < frozen alpha 5 19 ∧ frozen alpha 5 19 < 10 := by
  change (-10 : ℝ) < 9.039 ∧ (9.039 : ℝ) < 10
  norm_num

theorem heavy_ratio_clip (i : Fin 3) :
    (1e-6 : ℝ) < (heavyN i : ℝ) / 100 ∧
      (heavyN i : ℝ) / 100 < (1e6 : ℝ) := by
  fin_cases i <;> norm_num [heavyN, Matrix.cons_val]

private theorem frozenLightBase_heavy_neg (i : Fin 3) :
    frozenLightBase (heavyN i) < 0 := by
  have he := Real.exp_pos (-50 : ℝ)
  fin_cases i
  · have hl := Real.log_nonneg (show (1 : ℝ) ≤ 96 by norm_num)
    norm_num [heavyN, frozenLightBase, topo, clip, Matrix.cons_val]
    nlinarith
  · have hl := Real.log_nonneg (show (1 : ℝ) ≤ 97 by norm_num)
    norm_num [heavyN, frozenLightBase, topo, clip, Matrix.cons_val]
    nlinarith
  · have hl := Real.log_nonneg (show (1 : ℝ) ≤ 124 by norm_num)
    norm_num [heavyN, frozenLightBase, topo, clip, Matrix.cons_val]
    nlinarith

/-- The inner light floor is strictly active at all three heavy outputs.
This is independent of alpha; it removes the apparent light/heavy coupling
locally once continuity is used. -/
theorem frozen_heavy_light_floor (alpha : ℝ) (i : Fin 3) :
    lightRaw (frozen alpha 5) (heavyN i) < (1e-12 : ℝ) := by
  rw [frozen_lightRaw_eq]
  have hn : heavyN i ≠ 3 := by fin_cases i <;> decide
  simp only [if_neg hn, mul_one]
  exact lt_trans
    (mul_neg_of_neg_of_pos (frozenLightBase_heavy_neg i) (by positivity)) (by norm_num)

theorem frozen_heavyCorrection_pos (alpha : ℝ) (i : Fin 3) :
    0 < heavyCorrection (frozen alpha 5) (heavyN i) := by
  fin_cases i
  · have hb := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 0.95) (9.039 : ℝ)
    have hs := Real.one_le_rpow_of_pos_of_le_one_of_nonpos
      (by norm_num : (0 : ℝ) < 0.95) (by norm_num : (0.95 : ℝ) ≤ 1)
      (by norm_num : (-1.189 : ℝ) ≤ 0)
    have ht := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 0.95) (5.615 : ℝ)
    have hw := Real.neg_one_le_sin ((-1.264 : ℝ) * 95 + 4.685)
    change 0 < 12795 * (clip (1e-6) (1e6) ((95 : ℝ) / 100)) ^ (clip (-10) 10 (9.039 : ℝ)) +
      61635 * (clip (1e-6) (1e6) ((95 : ℝ) / 100)) ^ (-1.189 : ℝ) +
      17770 * (clip (1e-6) (1e6) ((95 : ℝ) / 100)) ^ (5.615 : ℝ) +
      8624 * Real.sin ((-1.264 : ℝ) * 95 + 4.685) + 0
    norm_num [clip]
    norm_num at hb hs ht hw
    nlinarith
  · have hb := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 0.96) (9.039 : ℝ)
    have hs := Real.one_le_rpow_of_pos_of_le_one_of_nonpos
      (by norm_num : (0 : ℝ) < 0.96) (by norm_num : (0.96 : ℝ) ≤ 1)
      (by norm_num : (-1.189 : ℝ) ≤ 0)
    have ht := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 0.96) (5.615 : ℝ)
    have hw := Real.neg_one_le_sin ((-1.264 : ℝ) * 96 + 4.685)
    change 0 < 12795 * (clip (1e-6) (1e6) ((96 : ℝ) / 100)) ^ (clip (-10) 10 (9.039 : ℝ)) +
      61635 * (clip (1e-6) (1e6) ((96 : ℝ) / 100)) ^ (-1.189 : ℝ) +
      17770 * (clip (1e-6) (1e6) ((96 : ℝ) / 100)) ^ (5.615 : ℝ) +
      8624 * Real.sin ((-1.264 : ℝ) * 96 + 4.685) + 0
    norm_num [clip]
    norm_num at hb hs ht hw
    nlinarith
  · have hb : (6 : ℝ) < (1.23 : ℝ) ^ (9.039 : ℝ) := by
      calc
        (6 : ℝ) < (1.23 : ℝ) ^ (9 : ℝ) := by norm_num
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    have hs := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 1.23) (-1.189 : ℝ)
    have ht := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 1.23) (5.615 : ℝ)
    change 0 < 12795 * (clip (1e-6) (1e6) ((123 : ℝ) / 100)) ^ (clip (-10) 10 (9.039 : ℝ)) +
      61635 * (clip (1e-6) (1e6) ((123 : ℝ) / 100)) ^ (-1.189 : ℝ) +
      17770 * (clip (1e-6) (1e6) ((123 : ℝ) / 100)) ^ (5.615 : ℝ) +
      0 + (896077 * ((123 : ℝ) / (123 + 1)) + (-952363))
    norm_num [clip]
    norm_num only at hb hs ht
    nlinarith

/-- The outer heavy floors are strictly inactive. -/
theorem frozen_heavy_floor_lt (alpha : ℝ) (i : Fin 3) :
    (1e-12 : ℝ) < light (frozen alpha 5) (heavyN i) +
      heavyCorrection (frozen alpha 5) (heavyN i) := by
  have h := frozen_heavy_light_floor alpha i
  rw [light, max_eq_right h.le]
  exact lt_add_of_pos_right _ (frozen_heavyCorrection_pos alpha i)

end ReyesMath.V18Forward
