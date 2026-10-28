import Mathlib
import MathProofs.M6BStationary

/-!
# Exact Lebesgue integrals for the two sine factors in M6B

The interval integrals here are the genuine interval Lebesgue integrals
used by the square's area integral, not numerical approximations.
-/

noncomputable section
open Real
namespace ReyesMath.M6B

theorem sin_sq_one_integral :
    (∫ x in (0 : ℝ)..Real.pi, Real.sin x ^ 2) = Real.pi / 2 := by
  rw [integral_sin_sq]
  simp

theorem sin_sq_two_integral :
    (∫ x in (0 : ℝ)..Real.pi, Real.sin (2 * x) ^ 2) = Real.pi / 2 := by
  have hscale :
      (2 : ℝ) * (∫ x in (0 : ℝ)..Real.pi, Real.sin (2 * x) ^ 2) =
      ∫ x in (0 : ℝ)..2 * Real.pi, Real.sin x ^ 2 := by
    simpa only [mul_zero, zero_mul] using
      (intervalIntegral.mul_integral_comp_mul_left
        (f := fun x : ℝ => Real.sin x ^ 2) (a := 0) (b := Real.pi) (c := 2))
  have hdouble :
      (∫ x in (0 : ℝ)..2 * Real.pi, Real.sin x ^ 2) = Real.pi := by
    rw [integral_sin_sq]
    simp
  rw [hdouble] at hscale
  linarith

/-- Exact pointwise squared amplitude, shared by both M6B fields. -/
theorem square_normSq_formula (c x y : ℝ) :
    Complex.normSq (squarePlus c x y) =
      c ^ 2 * (Real.sin x ^ 2 * Real.sin (2 * y) ^ 2 +
        Real.sin (2 * x) ^ 2 * Real.sin y ^ 2) := by
  simp [squarePlus, squareModeF, squareModeG, Complex.normSq_apply]
  ring

/-- Same pointwise mass density for the opposite-phase field. -/
theorem squareMinus_normSq_formula (c x y : ℝ) :
    Complex.normSq (squareMinus c x y) =
      c ^ 2 * (Real.sin x ^ 2 * Real.sin (2 * y) ^ 2 +
        Real.sin (2 * x) ^ 2 * Real.sin y ^ 2) := by
  rw [← square_intensity_eq]
  exact square_normSq_formula c x y

end ReyesMath.M6B
