import MathProofs.V18Frechet
import MathProofs.V18MiddleDeterminant
import MathProofs.V18BlockJacobian

/-!
# The selected minor of the actual Fréchet derivative

The index equivalence records the manuscript's 3+5+3 ordering. Each entry
below is evaluated on a coordinate vector of the full 31-dimensional space.
In particular, all six off-diagonal blocks are checked. The heavy/light
block vanishes because the inner light floor is locally constant, as proved
in `V18Regularity`; this is already part of the full derivative formula.
-/

noncomputable section
namespace ReyesMath.V18Forward
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

abbrev Sector := Fin 3 ⊕ (Fin 5 ⊕ Fin 3)

def sectorEquiv : Sector ≃ Fin 11 :=
  (Equiv.sumCongr (Equiv.refl (Fin 3))
    (finSumFinEquiv : Fin 5 ⊕ Fin 3 ≃ Fin 8)).trans finSumFinEquiv

/-- Restriction of the actual Fréchet derivative to the eleven selected
parameter directions, in the specified observation order. -/
def selectedMinor (p : Params) : Matrix Sector Sector ℝ :=
  fun i j => jacobian p (Pi.single (selectedColumn (sectorEquiv j)) 1) (sectorEquiv i)

private theorem observedD_light (p v : Params) (i : Fin 3) :
    observedD p v (sectorEquiv (Sum.inl i)) = lightD p (i.val + 1) v := by
  fin_cases i <;> rfl

private theorem observedD_middle (p v : Params) (i : Fin 5) :
    observedD p v (sectorEquiv (Sum.inr (Sum.inl i))) = middleD p (middleN i) v := by
  fin_cases i <;> rfl

private theorem observedD_heavy (p v : Params) (i : Fin 3) :
    observedD p v (sectorEquiv (Sum.inr (Sum.inr i))) = heavyD p (heavyN i) v := by
  fin_cases i <;> rfl

private theorem selected_block_00 (alpha : ℝ) (i : Fin 3) (j : Fin 3) :
    observedD (frozen alpha 5) (Pi.single (selectedColumn (sectorEquiv (Sum.inl j))) 1)
      (sectorEquiv (Sum.inl i)) = V18LightJacobian.minor alpha 5 i j := by
  have hp8 : frozen alpha 5 8 = (0.0048 : ℝ) := rfl
  have hp9 : frozen alpha 5 9 = (2241.1 : ℝ) := rfl
  have hp10 : frozen alpha 5 10 = (5.0632 : ℝ) := rfl
  have hp11 : frozen alpha 5 11 = (9.4062 : ℝ) := rfl
  have hp12 : frozen alpha 5 12 = (1.6469 : ℝ) := rfl
  have hp21 : frozen alpha 5 21 = (-1.189 : ℝ) := rfl
  have hp25 : frozen alpha 5 25 = (-1.264 : ℝ) := rfl
  have hp26 : frozen alpha 5 26 = (4.685 : ℝ) := rfl
  have hp29 : frozen alpha 5 29 = (alpha : ℝ) := rfl
  have hp30 : frozen alpha 5 30 = (5 : ℝ) := rfl
  rw [observedD_light]
  simp only [V18LightJacobian.minor, Matrix.diagonal_mul]
  fin_cases i <;> fin_cases j
  · change lightD (frozen alpha 5) 1 (Pi.single 0 1) = V18LightJacobian.rowScale alpha 5 0 * (1 / 2)
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change lightD (frozen alpha 5) 1 (Pi.single 3 1) = V18LightJacobian.rowScale alpha 5 0 * 1
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change lightD (frozen alpha 5) 1 (Pi.single 4 1) = V18LightJacobian.rowScale alpha 5 0 * 1
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change lightD (frozen alpha 5) 2 (Pi.single 0 1) = V18LightJacobian.rowScale alpha 5 1 * (2 / 3)
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change lightD (frozen alpha 5) 2 (Pi.single 3 1) = V18LightJacobian.rowScale alpha 5 1 * 4
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change lightD (frozen alpha 5) 2 (Pi.single 4 1) = V18LightJacobian.rowScale alpha 5 1 * 8
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change lightD (frozen alpha 5) 3 (Pi.single 0 1) = V18LightJacobian.rowScale alpha 5 2 * (3 / 4)
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
    ring
  · change lightD (frozen alpha 5) 3 (Pi.single 3 1) = V18LightJacobian.rowScale alpha 5 2 * 9
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
    ring
  · change lightD (frozen alpha 5) 3 (Pi.single 4 1) = V18LightJacobian.rowScale alpha 5 2 * 27
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
    ring

private theorem selected_block_01 (alpha : ℝ) (i : Fin 3) (j : Fin 5) :
    observedD (frozen alpha 5) (Pi.single (selectedColumn (sectorEquiv (Sum.inr (Sum.inl j)))) 1)
      (sectorEquiv (Sum.inl i)) = 0 := by
  have hp8 : frozen alpha 5 8 = (0.0048 : ℝ) := rfl
  have hp9 : frozen alpha 5 9 = (2241.1 : ℝ) := rfl
  have hp10 : frozen alpha 5 10 = (5.0632 : ℝ) := rfl
  have hp11 : frozen alpha 5 11 = (9.4062 : ℝ) := rfl
  have hp12 : frozen alpha 5 12 = (1.6469 : ℝ) := rfl
  have hp21 : frozen alpha 5 21 = (-1.189 : ℝ) := rfl
  have hp25 : frozen alpha 5 25 = (-1.264 : ℝ) := rfl
  have hp26 : frozen alpha 5 26 = (4.685 : ℝ) := rfl
  have hp29 : frozen alpha 5 29 = (alpha : ℝ) := rfl
  have hp30 : frozen alpha 5 30 = (5 : ℝ) := rfl
  rw [observedD_light]
  fin_cases i <;> fin_cases j
  · change lightD (frozen alpha 5) 1 (Pi.single 14 1) = 0
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change lightD (frozen alpha 5) 1 (Pi.single 15 1) = 0
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change lightD (frozen alpha 5) 1 (Pi.single 9 1) = 0
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change lightD (frozen alpha 5) 1 (Pi.single 12 1) = 0
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change lightD (frozen alpha 5) 1 (Pi.single 13 1) = 0
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change lightD (frozen alpha 5) 2 (Pi.single 14 1) = 0
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change lightD (frozen alpha 5) 2 (Pi.single 15 1) = 0
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change lightD (frozen alpha 5) 2 (Pi.single 9 1) = 0
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change lightD (frozen alpha 5) 2 (Pi.single 12 1) = 0
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change lightD (frozen alpha 5) 2 (Pi.single 13 1) = 0
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change lightD (frozen alpha 5) 3 (Pi.single 14 1) = 0
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change lightD (frozen alpha 5) 3 (Pi.single 15 1) = 0
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change lightD (frozen alpha 5) 3 (Pi.single 9 1) = 0
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change lightD (frozen alpha 5) 3 (Pi.single 12 1) = 0
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change lightD (frozen alpha 5) 3 (Pi.single 13 1) = 0
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]

private theorem selected_block_02 (alpha : ℝ) (i : Fin 3) (j : Fin 3) :
    observedD (frozen alpha 5) (Pi.single (selectedColumn (sectorEquiv (Sum.inr (Sum.inr j)))) 1)
      (sectorEquiv (Sum.inl i)) = 0 := by
  have hp8 : frozen alpha 5 8 = (0.0048 : ℝ) := rfl
  have hp9 : frozen alpha 5 9 = (2241.1 : ℝ) := rfl
  have hp10 : frozen alpha 5 10 = (5.0632 : ℝ) := rfl
  have hp11 : frozen alpha 5 11 = (9.4062 : ℝ) := rfl
  have hp12 : frozen alpha 5 12 = (1.6469 : ℝ) := rfl
  have hp21 : frozen alpha 5 21 = (-1.189 : ℝ) := rfl
  have hp25 : frozen alpha 5 25 = (-1.264 : ℝ) := rfl
  have hp26 : frozen alpha 5 26 = (4.685 : ℝ) := rfl
  have hp29 : frozen alpha 5 29 = (alpha : ℝ) := rfl
  have hp30 : frozen alpha 5 30 = (5 : ℝ) := rfl
  rw [observedD_light]
  fin_cases i <;> fin_cases j
  · change lightD (frozen alpha 5) 1 (Pi.single 20 1) = 0
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change lightD (frozen alpha 5) 1 (Pi.single 24 1) = 0
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change lightD (frozen alpha 5) 1 (Pi.single 28 1) = 0
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change lightD (frozen alpha 5) 2 (Pi.single 20 1) = 0
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change lightD (frozen alpha 5) 2 (Pi.single 24 1) = 0
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change lightD (frozen alpha 5) 2 (Pi.single 28 1) = 0
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change lightD (frozen alpha 5) 3 (Pi.single 20 1) = 0
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change lightD (frozen alpha 5) 3 (Pi.single 24 1) = 0
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change lightD (frozen alpha 5) 3 (Pi.single 28 1) = 0
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]

private theorem selected_block_10 (alpha : ℝ) (i : Fin 5) (j : Fin 3) :
    observedD (frozen alpha 5) (Pi.single (selectedColumn (sectorEquiv (Sum.inl j))) 1)
      (sectorEquiv (Sum.inr (Sum.inl i))) = 0 := by
  have hp8 : frozen alpha 5 8 = (0.0048 : ℝ) := rfl
  have hp9 : frozen alpha 5 9 = (2241.1 : ℝ) := rfl
  have hp10 : frozen alpha 5 10 = (5.0632 : ℝ) := rfl
  have hp11 : frozen alpha 5 11 = (9.4062 : ℝ) := rfl
  have hp12 : frozen alpha 5 12 = (1.6469 : ℝ) := rfl
  have hp21 : frozen alpha 5 21 = (-1.189 : ℝ) := rfl
  have hp25 : frozen alpha 5 25 = (-1.264 : ℝ) := rfl
  have hp26 : frozen alpha 5 26 = (4.685 : ℝ) := rfl
  have hp29 : frozen alpha 5 29 = (alpha : ℝ) := rfl
  have hp30 : frozen alpha 5 30 = (5 : ℝ) := rfl
  rw [observedD_middle]
  fin_cases i <;> fin_cases j
  · change middleD (frozen alpha 5) 12 (Pi.single 0 1) = 0
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change middleD (frozen alpha 5) 12 (Pi.single 3 1) = 0
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change middleD (frozen alpha 5) 12 (Pi.single 4 1) = 0
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change middleD (frozen alpha 5) 19 (Pi.single 0 1) = 0
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change middleD (frozen alpha 5) 19 (Pi.single 3 1) = 0
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change middleD (frozen alpha 5) 19 (Pi.single 4 1) = 0
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change middleD (frozen alpha 5) 53 (Pi.single 0 1) = 0
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change middleD (frozen alpha 5) 53 (Pi.single 3 1) = 0
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change middleD (frozen alpha 5) 53 (Pi.single 4 1) = 0
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change middleD (frozen alpha 5) 73 (Pi.single 0 1) = 0
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change middleD (frozen alpha 5) 73 (Pi.single 3 1) = 0
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change middleD (frozen alpha 5) 73 (Pi.single 4 1) = 0
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change middleD (frozen alpha 5) 91 (Pi.single 0 1) = 0
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change middleD (frozen alpha 5) 91 (Pi.single 3 1) = 0
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change middleD (frozen alpha 5) 91 (Pi.single 4 1) = 0
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]

private theorem selected_block_11 (alpha : ℝ) (i : Fin 5) (j : Fin 5) :
    observedD (frozen alpha 5) (Pi.single (selectedColumn (sectorEquiv (Sum.inr (Sum.inl j)))) 1)
      (sectorEquiv (Sum.inr (Sum.inl i))) = V18MiddleJacobian.middle i j := by
  have hp8 : frozen alpha 5 8 = (0.0048 : ℝ) := rfl
  have hp9 : frozen alpha 5 9 = (2241.1 : ℝ) := rfl
  have hp10 : frozen alpha 5 10 = (5.0632 : ℝ) := rfl
  have hp11 : frozen alpha 5 11 = (9.4062 : ℝ) := rfl
  have hp12 : frozen alpha 5 12 = (1.6469 : ℝ) := rfl
  have hp21 : frozen alpha 5 21 = (-1.189 : ℝ) := rfl
  have hp25 : frozen alpha 5 25 = (-1.264 : ℝ) := rfl
  have hp26 : frozen alpha 5 26 = (4.685 : ℝ) := rfl
  have hp29 : frozen alpha 5 29 = (alpha : ℝ) := rfl
  have hp30 : frozen alpha 5 30 = (5 : ℝ) := rfl
  rw [observedD_middle]
  fin_cases i <;> fin_cases j
  · change middleD (frozen alpha 5) 12 (Pi.single 14 1) = 1
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change middleD (frozen alpha 5) 12 (Pi.single 15 1) = 144
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change middleD (frozen alpha 5) 12 (Pi.single 9 1) = Real.sin ((5.0632 : ℝ) * 12 + 1.6469)
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change middleD (frozen alpha 5) 12 (Pi.single 12 1) = (2241.1 : ℝ) * Real.cos ((5.0632 : ℝ) * 12 + 1.6469)
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change middleD (frozen alpha 5) 12 (Pi.single 13 1) = Real.sin ((9.4062 : ℝ) * 12)
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change middleD (frozen alpha 5) 19 (Pi.single 14 1) = 1
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change middleD (frozen alpha 5) 19 (Pi.single 15 1) = 361
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change middleD (frozen alpha 5) 19 (Pi.single 9 1) = Real.sin ((5.0632 : ℝ) * 19 + 1.6469)
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change middleD (frozen alpha 5) 19 (Pi.single 12 1) = (2241.1 : ℝ) * Real.cos ((5.0632 : ℝ) * 19 + 1.6469)
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change middleD (frozen alpha 5) 19 (Pi.single 13 1) = Real.sin ((9.4062 : ℝ) * 19)
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change middleD (frozen alpha 5) 53 (Pi.single 14 1) = 1
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change middleD (frozen alpha 5) 53 (Pi.single 15 1) = 2809
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change middleD (frozen alpha 5) 53 (Pi.single 9 1) = Real.sin ((5.0632 : ℝ) * 53 + 1.6469)
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change middleD (frozen alpha 5) 53 (Pi.single 12 1) = (2241.1 : ℝ) * Real.cos ((5.0632 : ℝ) * 53 + 1.6469)
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change middleD (frozen alpha 5) 53 (Pi.single 13 1) = Real.sin ((9.4062 : ℝ) * 53)
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change middleD (frozen alpha 5) 73 (Pi.single 14 1) = 1
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change middleD (frozen alpha 5) 73 (Pi.single 15 1) = 5329
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change middleD (frozen alpha 5) 73 (Pi.single 9 1) = Real.sin ((5.0632 : ℝ) * 73 + 1.6469)
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change middleD (frozen alpha 5) 73 (Pi.single 12 1) = (2241.1 : ℝ) * Real.cos ((5.0632 : ℝ) * 73 + 1.6469)
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change middleD (frozen alpha 5) 73 (Pi.single 13 1) = Real.sin ((9.4062 : ℝ) * 73)
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change middleD (frozen alpha 5) 91 (Pi.single 14 1) = 1
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change middleD (frozen alpha 5) 91 (Pi.single 15 1) = 8281
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change middleD (frozen alpha 5) 91 (Pi.single 9 1) = Real.sin ((5.0632 : ℝ) * 91 + 1.6469)
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change middleD (frozen alpha 5) 91 (Pi.single 12 1) = (2241.1 : ℝ) * Real.cos ((5.0632 : ℝ) * 91 + 1.6469)
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change middleD (frozen alpha 5) 91 (Pi.single 13 1) = Real.sin ((9.4062 : ℝ) * 91)
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]

private theorem selected_block_12 (alpha : ℝ) (i : Fin 5) (j : Fin 3) :
    observedD (frozen alpha 5) (Pi.single (selectedColumn (sectorEquiv (Sum.inr (Sum.inr j)))) 1)
      (sectorEquiv (Sum.inr (Sum.inl i))) = 0 := by
  have hp8 : frozen alpha 5 8 = (0.0048 : ℝ) := rfl
  have hp9 : frozen alpha 5 9 = (2241.1 : ℝ) := rfl
  have hp10 : frozen alpha 5 10 = (5.0632 : ℝ) := rfl
  have hp11 : frozen alpha 5 11 = (9.4062 : ℝ) := rfl
  have hp12 : frozen alpha 5 12 = (1.6469 : ℝ) := rfl
  have hp21 : frozen alpha 5 21 = (-1.189 : ℝ) := rfl
  have hp25 : frozen alpha 5 25 = (-1.264 : ℝ) := rfl
  have hp26 : frozen alpha 5 26 = (4.685 : ℝ) := rfl
  have hp29 : frozen alpha 5 29 = (alpha : ℝ) := rfl
  have hp30 : frozen alpha 5 30 = (5 : ℝ) := rfl
  rw [observedD_middle]
  fin_cases i <;> fin_cases j
  · change middleD (frozen alpha 5) 12 (Pi.single 20 1) = 0
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change middleD (frozen alpha 5) 12 (Pi.single 24 1) = 0
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change middleD (frozen alpha 5) 12 (Pi.single 28 1) = 0
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change middleD (frozen alpha 5) 19 (Pi.single 20 1) = 0
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change middleD (frozen alpha 5) 19 (Pi.single 24 1) = 0
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change middleD (frozen alpha 5) 19 (Pi.single 28 1) = 0
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change middleD (frozen alpha 5) 53 (Pi.single 20 1) = 0
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change middleD (frozen alpha 5) 53 (Pi.single 24 1) = 0
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change middleD (frozen alpha 5) 53 (Pi.single 28 1) = 0
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change middleD (frozen alpha 5) 73 (Pi.single 20 1) = 0
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change middleD (frozen alpha 5) 73 (Pi.single 24 1) = 0
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change middleD (frozen alpha 5) 73 (Pi.single 28 1) = 0
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change middleD (frozen alpha 5) 91 (Pi.single 20 1) = 0
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change middleD (frozen alpha 5) 91 (Pi.single 24 1) = 0
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change middleD (frozen alpha 5) 91 (Pi.single 28 1) = 0
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]

private theorem selected_block_20 (alpha : ℝ) (i : Fin 3) (j : Fin 3) :
    observedD (frozen alpha 5) (Pi.single (selectedColumn (sectorEquiv (Sum.inl j))) 1)
      (sectorEquiv (Sum.inr (Sum.inr i))) = 0 := by
  have hp8 : frozen alpha 5 8 = (0.0048 : ℝ) := rfl
  have hp9 : frozen alpha 5 9 = (2241.1 : ℝ) := rfl
  have hp10 : frozen alpha 5 10 = (5.0632 : ℝ) := rfl
  have hp11 : frozen alpha 5 11 = (9.4062 : ℝ) := rfl
  have hp12 : frozen alpha 5 12 = (1.6469 : ℝ) := rfl
  have hp21 : frozen alpha 5 21 = (-1.189 : ℝ) := rfl
  have hp25 : frozen alpha 5 25 = (-1.264 : ℝ) := rfl
  have hp26 : frozen alpha 5 26 = (4.685 : ℝ) := rfl
  have hp29 : frozen alpha 5 29 = (alpha : ℝ) := rfl
  have hp30 : frozen alpha 5 30 = (5 : ℝ) := rfl
  rw [observedD_heavy]
  fin_cases i <;> fin_cases j
  · change heavyD (frozen alpha 5) 95 (Pi.single 0 1) = 0
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change heavyD (frozen alpha 5) 95 (Pi.single 3 1) = 0
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change heavyD (frozen alpha 5) 95 (Pi.single 4 1) = 0
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change heavyD (frozen alpha 5) 96 (Pi.single 0 1) = 0
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change heavyD (frozen alpha 5) 96 (Pi.single 3 1) = 0
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change heavyD (frozen alpha 5) 96 (Pi.single 4 1) = 0
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change heavyD (frozen alpha 5) 123 (Pi.single 0 1) = 0
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change heavyD (frozen alpha 5) 123 (Pi.single 3 1) = 0
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change heavyD (frozen alpha 5) 123 (Pi.single 4 1) = 0
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]

private theorem selected_block_21 (alpha : ℝ) (i : Fin 3) (j : Fin 5) :
    observedD (frozen alpha 5) (Pi.single (selectedColumn (sectorEquiv (Sum.inr (Sum.inl j)))) 1)
      (sectorEquiv (Sum.inr (Sum.inr i))) = 0 := by
  have hp8 : frozen alpha 5 8 = (0.0048 : ℝ) := rfl
  have hp9 : frozen alpha 5 9 = (2241.1 : ℝ) := rfl
  have hp10 : frozen alpha 5 10 = (5.0632 : ℝ) := rfl
  have hp11 : frozen alpha 5 11 = (9.4062 : ℝ) := rfl
  have hp12 : frozen alpha 5 12 = (1.6469 : ℝ) := rfl
  have hp21 : frozen alpha 5 21 = (-1.189 : ℝ) := rfl
  have hp25 : frozen alpha 5 25 = (-1.264 : ℝ) := rfl
  have hp26 : frozen alpha 5 26 = (4.685 : ℝ) := rfl
  have hp29 : frozen alpha 5 29 = (alpha : ℝ) := rfl
  have hp30 : frozen alpha 5 30 = (5 : ℝ) := rfl
  rw [observedD_heavy]
  fin_cases i <;> fin_cases j
  · change heavyD (frozen alpha 5) 95 (Pi.single 14 1) = 0
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change heavyD (frozen alpha 5) 95 (Pi.single 15 1) = 0
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change heavyD (frozen alpha 5) 95 (Pi.single 9 1) = 0
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change heavyD (frozen alpha 5) 95 (Pi.single 12 1) = 0
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change heavyD (frozen alpha 5) 95 (Pi.single 13 1) = 0
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change heavyD (frozen alpha 5) 96 (Pi.single 14 1) = 0
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change heavyD (frozen alpha 5) 96 (Pi.single 15 1) = 0
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change heavyD (frozen alpha 5) 96 (Pi.single 9 1) = 0
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change heavyD (frozen alpha 5) 96 (Pi.single 12 1) = 0
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change heavyD (frozen alpha 5) 96 (Pi.single 13 1) = 0
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change heavyD (frozen alpha 5) 123 (Pi.single 14 1) = 0
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change heavyD (frozen alpha 5) 123 (Pi.single 15 1) = 0
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change heavyD (frozen alpha 5) 123 (Pi.single 9 1) = 0
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change heavyD (frozen alpha 5) 123 (Pi.single 12 1) = 0
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change heavyD (frozen alpha 5) 123 (Pi.single 13 1) = 0
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]

private theorem selected_block_22 (alpha : ℝ) (i : Fin 3) (j : Fin 3) :
    observedD (frozen alpha 5) (Pi.single (selectedColumn (sectorEquiv (Sum.inr (Sum.inr j)))) 1)
      (sectorEquiv (Sum.inr (Sum.inr i))) = V18HeavyJacobian.heavy i j := by
  have hp8 : frozen alpha 5 8 = (0.0048 : ℝ) := rfl
  have hp9 : frozen alpha 5 9 = (2241.1 : ℝ) := rfl
  have hp10 : frozen alpha 5 10 = (5.0632 : ℝ) := rfl
  have hp11 : frozen alpha 5 11 = (9.4062 : ℝ) := rfl
  have hp12 : frozen alpha 5 12 = (1.6469 : ℝ) := rfl
  have hp21 : frozen alpha 5 21 = (-1.189 : ℝ) := rfl
  have hp25 : frozen alpha 5 25 = (-1.264 : ℝ) := rfl
  have hp26 : frozen alpha 5 26 = (4.685 : ℝ) := rfl
  have hp29 : frozen alpha 5 29 = (alpha : ℝ) := rfl
  have hp30 : frozen alpha 5 30 = (5 : ℝ) := rfl
  rw [observedD_heavy]
  fin_cases i <;> fin_cases j
  · change heavyD (frozen alpha 5) 95 (Pi.single 20 1) = (0.95 : ℝ) ^ (-1.189 : ℝ)
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change heavyD (frozen alpha 5) 95 (Pi.single 24 1) = Real.sin (-115.395 : ℝ)
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change heavyD (frozen alpha 5) 95 (Pi.single 28 1) = 0
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change heavyD (frozen alpha 5) 96 (Pi.single 20 1) = (0.96 : ℝ) ^ (-1.189 : ℝ)
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change heavyD (frozen alpha 5) 96 (Pi.single 24 1) = Real.sin (-116.659 : ℝ)
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change heavyD (frozen alpha 5) 96 (Pi.single 28 1) = 0
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change heavyD (frozen alpha 5) 123 (Pi.single 20 1) = (1.23 : ℝ) ^ (-1.189 : ℝ)
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change heavyD (frozen alpha 5) 123 (Pi.single 24 1) = 0
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]
  · change heavyD (frozen alpha 5) 123 (Pi.single 28 1) = 1
    norm_num [lightD, lightBaseD, lightSuppressionD, lightSuppression,
      middleD, heavyD, wzD, higgsD, coord, Pi.single_apply, Fin.ext_iff,
      V18LightJacobian.rowScale, hp8, hp9, hp10, hp11, hp12, hp21, hp25, hp26, hp29, hp30]

/-- Exact identification of all 121 entries of the selected Jacobian. -/
theorem selectedMinor_frozen_eq (alpha : ℝ) (ha : 0 ≤ alpha) :
    selectedMinor (frozen alpha 5) =
      V18BlockJacobian.minor (V18LightJacobian.minor alpha 5)
        V18MiddleJacobian.middle V18HeavyJacobian.heavy 0 0 := by
  ext i j
  simp only [selectedMinor, jacobian_frozen_eq alpha ha]
  rcases i with i | (i | i) <;> rcases j with j | (j | j)
  all_goals simp only [V18BlockJacobian.minor,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply]
  · exact selected_block_00 alpha i j
  · exact selected_block_01 alpha i j
  · exact selected_block_02 alpha i j
  · exact selected_block_10 alpha i j
  · exact selected_block_11 alpha i j
  · exact selected_block_12 alpha i j
  · exact selected_block_20 alpha i j
  · exact selected_block_21 alpha i j
  · exact selected_block_22 alpha i j

end ReyesMath.V18Forward
