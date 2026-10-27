import MathProofs.V18LightJacobian

/-!
# Exact 11-by-11 v18 sensitivity minor block factorization

The selected frozen v18 Jacobian columns are:
 - light: (m0, theta, gamma), dimensions 3
 - middle: (offset, quad, amp, phase, harmonic), dimensions 5
 - heavy: (boson_nonlin1_scale, wz_break_scale, higgs_offset), dimensions 3

The observations are ordered 3 light, 5 middle, 3 heavy. There is no
dependence of the light observations on middle/heavy coefficients, and
no dependence of middle observations on heavy coefficients. The selected
11-by-11 derivative minor is therefore block lower triangular.

The full determinant factorizes exactly into its three diagonal block
determinants. This Lean statement does not yet certify the nonzero
real-trigonometric middle and heavy block determinants. Those still
have a reproducible external outward-rounded interval certificate.
-/

/- The nested Sum index for 3+5+3 determinant synthesis needs more
kernel recursion than the small default, not an admitted theorem. -/
set_option maxRecDepth 8192

noncomputable section
namespace ReyesMath.V18BlockJacobian

/-- Eleven observable rows with 3+5+3 selected coefficient columns. -/
def minor
    (L : Matrix (Fin 3) (Fin 3) ℝ)
    (M : Matrix (Fin 5) (Fin 5) ℝ)
    (H : Matrix (Fin 3) (Fin 3) ℝ)
    (A : Matrix ((Fin 5) ⊕ (Fin 3)) (Fin 3) ℝ)
    (B : Matrix (Fin 3) (Fin 5) ℝ) :
    Matrix (Fin 3 ⊕ (Fin 5 ⊕ Fin 3)) (Fin 3 ⊕ (Fin 5 ⊕ Fin 3)) ℝ :=
  Matrix.fromBlocks L 0 A (Matrix.fromBlocks M 0 B H)

/-- Determinant of an arbitrary lower-block-triangular three-sector
matrix. Proof is entirely generic; it avoids forcing the kernel to
expand permutations of the concrete eleven-coordinate index type. -/
theorem det_three_blocks
    {I J K : Type*}
    [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J]
    [Fintype K] [DecidableEq K]
    (L : Matrix I I ℝ)
    (M : Matrix J J ℝ)
    (H : Matrix K K ℝ)
    (A : Matrix (J ⊕ K) I ℝ)
    (B : Matrix K J ℝ) :
    (Matrix.fromBlocks L 0 A (Matrix.fromBlocks M 0 B H)).det =
      L.det * M.det * H.det := by
  calc
    (Matrix.fromBlocks L 0 A (Matrix.fromBlocks M 0 B H)).det =
        L.det * (Matrix.fromBlocks M 0 B H).det :=
      Matrix.det_fromBlocks_zero₁₂ _ _ _
    _ = L.det * (M.det * H.det) := by
      rw [Matrix.det_fromBlocks_zero₁₂]
    _ = L.det * M.det * H.det := by ring

/-- Specialized source-visible 3+5+3 analytic minor identity.
This is a direct application of the generic proven determinant theorem. -/
theorem minor_det
    (L : Matrix (Fin 3) (Fin 3) ℝ)
    (M : Matrix (Fin 5) (Fin 5) ℝ)
    (H : Matrix (Fin 3) (Fin 3) ℝ)
    (A : Matrix ((Fin 5) ⊕ (Fin 3)) (Fin 3) ℝ)
    (B : Matrix (Fin 3) (Fin 5) ℝ) :
    (minor L M H A B).det = L.det * M.det * H.det :=
  det_three_blocks L M H A B

/-- The exact light block is positive for all suppression parameters.
Thus certification of nonzero middle and heavy block determinants
suffices for full-row-rank of the selected eleven-column minor. -/
theorem v18_minor_ne_zero_of_middle_heavy
    (alpha epsilon : ℝ)
    (M : Matrix (Fin 5) (Fin 5) ℝ)
    (H : Matrix (Fin 3) (Fin 3) ℝ)
    (A : Matrix ((Fin 5) ⊕ (Fin 3)) (Fin 3) ℝ)
    (B : Matrix (Fin 3) (Fin 5) ℝ)
    (hM : M.det ≠ 0) (hH : H.det ≠ 0) :
    (minor (V18LightJacobian.minor alpha epsilon) M H A B).det ≠ 0 := by
  rw [minor_det]
  exact mul_ne_zero
    (mul_ne_zero (V18LightJacobian.minor_det_ne_zero alpha epsilon) hM) hH

end ReyesMath.V18BlockJacobian
