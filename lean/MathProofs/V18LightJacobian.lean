import Mathlib

/-!
# Frozen v18 Jacobian: exact analytic light-block certificate

The v18 model has three nonzero light-sector observations n=1,2,3.
Their derivatives with respect to (m0, theta, gamma), with the
historical branching and all other parameters fixed, are the rows
D_n * eps_n * (n/(n+1), n², n³), where
D_n = 1/(1+exp(alpha*(n-epsilon))) > 0,
eps_1=eps_2=1, eps_3=0.0048.

The rational 3x3 base determinant is exactly 9; hence the light-sector
Jacobian block has strictly positive determinant for *every* real
alpha and epsilon, not just the historically optimized fitted values.

This certifies one diagonal block. The middle and heavy determinants
are proved nonzero in V18MiddleDeterminant and V18HeavyJacobian, and
V18SelectedJacobian identifies all three as blocks of the actual derivative.
-/

noncomputable section
namespace ReyesMath.V18LightJacobian

/-- The three analytic light partial derivative rows before suppression. -/
def base : Matrix (Fin 3) (Fin 3) ℝ :=
  !![(1 / 2 : ℝ), 1, 1; (2 / 3 : ℝ), 4, 8; (3 / 4 : ℝ), 9, 27]

theorem base_det : base.det = 9 := by
  rw [Matrix.det_fin_three]
  simp only [
    show base 0 0 = (1 / 2 : ℝ) from rfl,
    show base 0 1 = (1 : ℝ) from rfl,
    show base 0 2 = (1 : ℝ) from rfl,
    show base 1 0 = (2 / 3 : ℝ) from rfl,
    show base 1 1 = (4 : ℝ) from rfl,
    show base 1 2 = (8 : ℝ) from rfl,
    show base 2 0 = (3 / 4 : ℝ) from rfl,
    show base 2 1 = (9 : ℝ) from rfl,
    show base 2 2 = (27 : ℝ) from rfl]
  norm_num

/-- Historically frozen epsilon_3=0.0048 and the logistic suppression. -/
def rowScale (alpha epsilon : ℝ) (i : Fin 3) : ℝ :=
  (if i = 2 then (0.0048 : ℝ) else 1) /
    (1 + Real.exp (alpha * (((i.val + 1 : ℕ) : ℝ) - epsilon)))

theorem rowScale_pos (alpha epsilon : ℝ) (i : Fin 3) :
    0 < rowScale alpha epsilon i := by
  unfold rowScale
  by_cases hi : i = 2
  · simp only [hi, ite_true]
    positivity
  · simp only [hi, ite_false]
    positivity

def minor (alpha epsilon : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.diagonal (rowScale alpha epsilon) * base

theorem minor_det (alpha epsilon : ℝ) :
    (minor alpha epsilon).det =
      (∏ i : Fin 3, rowScale alpha epsilon i) * 9 := by
  simp only [minor, Matrix.det_mul, Matrix.det_diagonal, base_det]

/-- No floating-point rank threshold: this block is exactly invertible. -/
theorem minor_det_pos (alpha epsilon : ℝ) :
    0 < (minor alpha epsilon).det := by
  rw [minor_det]
  exact mul_pos (Finset.prod_pos fun i _ => rowScale_pos alpha epsilon i) (by norm_num)

theorem minor_det_ne_zero (alpha epsilon : ℝ) :
    (minor alpha epsilon).det ≠ 0 := ne_of_gt (minor_det_pos alpha epsilon)

end ReyesMath.V18LightJacobian
