import Mathlib
import MathProofs.Structural

/-!
# The complex scalar gradient tensor as an actual real Gram matrix

This links the complex-valued formula in the manuscript to the real
positive-semidefinite two-column Gram construction. The pointwise algebra
is formalized in dimension four; no spacetime metric field is constructed.
-/

namespace ReyesMath

/-- The complex-gradient product has precisely the real Gram entry. -/
theorem complex_gradient_real_identity (a b c d : ℝ) :
    (star (Complex.mk a b) * Complex.mk c d).re =
      a * c + b * d := by
  simp [Complex.mul_re]
  ring

private def pointwiseComplexGradientTensor
    (da db : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => (star (Complex.mk (da i) (db i)) *
      Complex.mk (da j) (db j)).re

/-- The physical-looking Re(conjugate-gradient times gradient) 4×4 tensor
equals the two-column carrier Gram matrix, entry by entry. -/
theorem complex_gradient_tensor_eq_gram
    (da db : Fin 4 → ℝ) :
    pointwiseComplexGradientTensor da db =
      (scalarGradientCarrier da db) *
        (scalarGradientCarrier da db).transpose := by
  ext i j
  rw [scalarGradientCarrier_gram_entry]
  exact complex_gradient_real_identity (da i) (db i) (da j) (db j)

/-- The actual complex formula has rank at most two in four dimensions. -/
theorem complex_gradient_tensor_rank_le_two
    (da db : Fin 4 → ℝ) :
    (pointwiseComplexGradientTensor da db).rank ≤ 2 := by
  rw [complex_gradient_tensor_eq_gram]
  exact scalarGradientCarrier_rank_le_two da db

end ReyesMath
