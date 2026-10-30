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
determinants. V18SelectedJacobian proves the concrete restriction of the
actual derivative has this form, with both lower off-diagonal blocks zero
on the verified frozen branch. V18Rank packages the generic determinant
argument as invertibility before concrete instantiation.
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

/-!
The universal theorem `det_three_blocks` is the formal
determinant factorization for *every* finite three-sector block system.
Direct rewriting of a concrete determinant can force normalization of its
large permutation enumeration on the pinned build. V18Rank avoids that
expansion by first proving generic block invertibility, then instantiating
it and exporting the actual selected determinant's nonvanishing.
-/

end ReyesMath.V18BlockJacobian
