import MathProofs.E62Projector

/-!
# E62: the manuscript's exact trigonometric two-mode example

For two orthogonal spectral modes with amplitudes cos t and sin t,
the selected fraction equals cos²t. Although it is always in [0,1],
it is neither monotone nor antitone. These are exact real-analytic
identities, not numerical time samples or an assumed evolution PDE.
-/

namespace ReyesMath
namespace E62TrigonometricScope

open RemainingCores

noncomputable def twoModeFraction (t : ℝ) : ℝ :=
  energyFraction (Real.cos t ^ 2)
    (Real.cos t ^ 2 + Real.sin t ^ 2)

theorem fraction_eq_cos_sq (t : ℝ) :
    twoModeFraction t = Real.cos t ^ 2 := by
  unfold twoModeFraction energyFraction
  rw [Real.cos_sq_add_sin_sq]
  simp

theorem fraction_at_zero : twoModeFraction 0 = 1 := by
  rw [fraction_eq_cos_sq]
  norm_num

theorem fraction_at_pi_div_two :
    twoModeFraction (Real.pi / 2) = 0 := by
  rw [fraction_eq_cos_sq]
  simp

theorem fraction_at_pi : twoModeFraction Real.pi = 1 := by
  rw [fraction_eq_cos_sq]
  simp

theorem fraction_not_monotone : ¬ Monotone twoModeFraction := by
  intro hm
  have h := hm (show (0 : ℝ) ≤ Real.pi / 2 by positivity)
  rw [fraction_at_zero, fraction_at_pi_div_two] at h
  norm_num at h

theorem fraction_not_antitone : ¬ Antitone twoModeFraction := by
  intro hm
  have h := hm (show Real.pi / 2 ≤ Real.pi by
    have hp := Real.pi_pos
    linarith)
  rw [fraction_at_pi_div_two, fraction_at_pi] at h
  norm_num at h

end E62TrigonometricScope
end ReyesMath
