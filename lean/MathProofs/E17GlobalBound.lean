import MathProofs.RegularizedCurvatureL2
import MathProofs.E17Canonical

/-!
# E17: global fixed-ε multiplier bound for arbitrary real α

The previous corrected-regularizer bound imposed α ≥ 0. The actual
M2/E17 manuscript asserts global fixed-ε boundedness for all α ∈ ℝ.
The following explicit estimate closes that parameter gap.

For |z| ≤ 1, the denominator is bounded below by
  ε² exp(-2|α|).
For |z| > 1, the |z|² term alone bounds |Rε| by 1.
The resulting constant is finite for each fixed ε > 0; nothing
here asserts uniform boundedness as ε tends to zero.
-/

open Real

noncomputable section

namespace ReyesMath
namespace E17GlobalBound

/-- An explicit finite global bound valid even for α < 0. -/
theorem arbitrary_alpha_bound {ε : ℝ} (hε : 0 < ε) (α : ℝ) (z : ℂ) :
    ‖E26.Rε ε α z‖ ≤
      max 1 (Real.exp (2 * |α|) / ε ^ 2) := by
  rw [E26.norm_Rε hε]
  by_cases hz : ‖z‖ ≤ 1
  · have hz2 : ‖z‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg z]
    have he : -2 * |α| ≤ -2 * α * ‖z‖ ^ 2 := by
      rcases le_total 0 α with ha | ha
      · rw [abs_of_nonneg ha]
        nlinarith [mul_nonneg ha (sub_nonneg.mpr hz2)]
      · rw [abs_of_nonpos ha]
        nlinarith [mul_nonneg (neg_nonneg.mpr ha) (sq_nonneg ‖z‖)]
    have hExp : Real.exp (-2 * |α|) ≤
        Real.exp (-2 * α * ‖z‖ ^ 2) := Real.exp_le_exp.mpr he
    have hLow : ε ^ 2 * Real.exp (-2 * |α|) ≤
        ‖z‖ ^ 2 + ε ^ 2 * Real.exp (-2 * α * ‖z‖ ^ 2) := by
      nlinarith [mul_le_mul_of_nonneg_left hExp (sq_nonneg ε), sq_nonneg ‖z‖]
    have hPos : 0 < ε ^ 2 * Real.exp (-2 * |α|) := by positivity
    have hA : ‖z‖ /
        (‖z‖ ^ 2 + ε ^ 2 * Real.exp (-2 * α * ‖z‖ ^ 2)) ≤
        ‖z‖ / (ε ^ 2 * Real.exp (-2 * |α|)) :=
      div_le_div_of_nonneg_left (norm_nonneg z) hPos hLow
    have hB : ‖z‖ / (ε ^ 2 * Real.exp (-2 * |α|)) ≤
        1 / (ε ^ 2 * Real.exp (-2 * |α|)) :=
      div_le_div_of_nonneg_right hz hPos.le
    have hEq : 1 / (ε ^ 2 * Real.exp (-2 * |α|)) =
        Real.exp (2 * |α|) / ε ^ 2 := by
      rw [show -2 * |α| = -(2 * |α|) by ring, Real.exp_neg]
      field_simp
    exact (hA.trans hB).trans (by rw [hEq]; exact le_max_right _ _)
  · have hz1 : 1 < ‖z‖ := lt_of_not_ge hz
    have hz0 : 0 < ‖z‖ := lt_trans one_pos hz1
    have hLower : ‖z‖ ^ 2 ≤
        ‖z‖ ^ 2 + ε ^ 2 * Real.exp (-2 * α * ‖z‖ ^ 2) :=
      le_add_of_nonneg_right (by positivity)
    have hA : ‖z‖ /
        (‖z‖ ^ 2 + ε ^ 2 * Real.exp (-2 * α * ‖z‖ ^ 2)) ≤
        ‖z‖ / ‖z‖ ^ 2 :=
      div_le_div_of_nonneg_left (norm_nonneg z) (by positivity) hLower
    have hEq : ‖z‖ / ‖z‖ ^ 2 = (‖z‖)⁻¹ := by
      field_simp [ne_of_gt hz0]
    have hB : (‖z‖)⁻¹ ≤ 1 := by
      simpa only [one_div, inv_one] using
        (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hz1.le)
    exact (hA.trans (by rw [hEq]; exact hB)).trans (le_max_left _ _)

end E17GlobalBound
end ReyesMath
