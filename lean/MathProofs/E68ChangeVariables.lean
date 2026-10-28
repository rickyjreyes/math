import Mathlib
import MathProofs.E68HigherDimEnergy

/-!
# E68: exact whole-space Lebesgue-integral dilation identity

This is an actual Haar/Lebesgue change-of-variables theorem for the
Euclidean continuum. It is not the formal symbolic scaling equality
previously used as a surrogate. The derivative chain rule for the
concentrating field and the local ball-energy estimate remain separate.
-/

noncomputable section
open MeasureTheory

namespace ReyesMath.E68

/-- In dimension n, a positive dilation of the domain by the
inverse radius R⁻¹ has the exact Jacobian multiplier Rⁿ in the
whole-space Lebesgue integral, for any real measurable or
non-integrable test function (the standard Bochner integral
convention returns zero for non-integrable cases). -/
theorem integral_inverse_smul_exact
    (n : ℕ) (R : ℝ) (hR : 0 < R)
    (g : EuclideanSpace ℝ (Fin n) → ℝ) :
    (∫ x : EuclideanSpace ℝ (Fin n), g ((R⁻¹ : ℝ) • x)) =
      R ^ n * (∫ x : EuclideanSpace ℝ (Fin n), g x) := by
  let E := EuclideanSpace ℝ (Fin n)
  have h := MeasureTheory.integral_comp_smul
    (μ := (volume : Measure E)) g (R⁻¹)
  simpa [E, finrank_euclideanSpace, inv_pow, smul_eq_mul,
    abs_of_pos (pow_pos hR n)] using h

end ReyesMath.E68
