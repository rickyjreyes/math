import Mathlib
import MathProofs.E68SmoothProfiles

/-!
# E68: a genuine positive derivative-energy integral in dimension one

The profile is Mathlib's nonconstant, compactly supported C-infinity
bump in (-1,1). This file proves positivity of its actual whole-line
Lebesgue integral of the squared classical derivative. It is not an
abstract "positive energy" parameter substituted into a scaling law.

The full E68 one-dimensional contradiction additionally requires the
comparison of this integral to the exact radius-dependent right side.
-/

noncomputable section
open scoped ContDiff
open MeasureTheory

namespace ReyesMath.E68

private def bump1 : ℝ → ℝ := fun x => compactOneDim x

private theorem bump1_smooth : ContDiff ℝ ∞ bump1 :=
  compactOneDim_smooth

private theorem bump1_compact : HasCompactSupport bump1 :=
  compactOneDim_hasCompactSupport

/-- The derivative of the actual smooth compact bump cannot vanish
identically because its values at 0 and 1 are distinct. -/
theorem compactOneDim_deriv_nonzero :
    ∃ x : ℝ, deriv bump1 x ≠ 0 := by
  by_contra hnone
  push_neg at hnone
  have hconst : bump1 0 = bump1 1 :=
    is_const_of_deriv_eq_zero
      (bump1_smooth.differentiable (by simp)) hnone 0 1
  exact compactOneDim_nonconstant hconst

/-- The real-valued derivative has compact support, so its squared
derivative is integrable over actual Lebesgue measure on R. -/
theorem compactOneDim_deriv_energy_integrable :
    Integrable (fun x : ℝ => (deriv bump1 x) ^ 2) := by
  have hc : Continuous (fun x : ℝ => (deriv bump1 x) ^ 2) :=
    (bump1_smooth.continuous_deriv (by simp)).pow 2
  have hs : HasCompactSupport (fun x : ℝ => (deriv bump1 x) ^ 2) := by
    simpa [bump1, pow_two, Pi.mul_apply] using
      (bump1_compact.deriv.mul_right
        (f' := fun x : ℝ => deriv bump1 x))
  exact hc.integrable_of_hasCompactSupport hs

/-- Strictly positive real continuum gradient energy:
integral over the whole real line of |f'(x)|^2 is nonzero. -/
theorem compactOneDim_deriv_energy_positive :
    0 < ∫ x : ℝ, (deriv bump1 x) ^ 2 := by
  obtain ⟨x, hx⟩ := compactOneDim_deriv_nonzero
  have hc : Continuous (fun y : ℝ => (deriv bump1 y) ^ 2) :=
    (bump1_smooth.continuous_deriv (by simp)).pow 2
  have hs : HasCompactSupport (fun y : ℝ => (deriv bump1 y) ^ 2) := by
    simpa [bump1, pow_two, Pi.mul_apply] using
      (bump1_compact.deriv.mul_right
        (f' := fun y : ℝ => deriv bump1 y))
  have hnonneg : 0 ≤ (fun y : ℝ => (deriv bump1 y) ^ 2) := by
    intro y
    exact sq_nonneg _
  have hne : (deriv bump1 x) ^ 2 ≠ 0 := pow_ne_zero 2 hx
  exact hc.integral_pos_of_hasCompactSupport_nonneg_nonzero hs hnonneg hne

end ReyesMath.E68
