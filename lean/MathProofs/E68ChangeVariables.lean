import Mathlib
import MathProofs.E68HigherDimEnergy

/-!
# E68: exact whole-space Lebesgue-integral dilation identity

The identity is obtained from Mathlib's Haar-measure inverse-dilation
change-of-variables theorem, not an algebraic scaling surrogate.
For a non-integrable function the Bochner integral convention is zero.
The derivative chain rule and local-ball energy estimate remain separate.
-/

noncomputable section
open MeasureTheory

namespace ReyesMath.E68

/-- In n-dimensional Euclidean space, positive dilation by inverse radius
has the exact Lebesgue Jacobian R^n, with no grid approximation. -/
theorem integral_inverse_smul_exact
    (n : ℕ) (R : ℝ) (hR : 0 < R)
    (g : EuclideanSpace ℝ (Fin n) → ℝ) :
    (∫ x : EuclideanSpace ℝ (Fin n), g ((R⁻¹ : ℝ) • x)) =
      R ^ n * (∫ x : EuclideanSpace ℝ (Fin n), g x) := by
  have h := MeasureTheory.Measure.integral_comp_inv_smul_of_nonneg
    (volume : Measure (EuclideanSpace ℝ (Fin n))) g hR.le
  simpa only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul] using h

end ReyesMath.E68
