import MathProofs.V18SelectedJacobian

/-!
# Exact rank and nullity of the full clipped observation derivative

The invertible matrix is the actual derivative restricted to the selected
coordinate directions. Rank monotonicity under restriction therefore gives
a lower bound for that full derivative, not for an auxiliary sensitivity map.
-/

noncomputable section
namespace ReyesMath.V18Forward
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

private theorem blocks_isUnit
    {I J K : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]
    (L : Matrix I I ℝ) (M : Matrix J J ℝ) (H : Matrix K K ℝ)
    (hL : L.det ≠ 0) (hM : M.det ≠ 0) (hH : H.det ≠ 0) :
    IsUnit (Matrix.fromBlocks L 0 0 (Matrix.fromBlocks M 0 0 H)) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  rw [V18BlockJacobian.det_three_blocks]
  exact isUnit_iff_ne_zero.mpr (mul_ne_zero (mul_ne_zero hL hM) hH)

private theorem det_ne_zero_of_isUnit {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℝ) (h : IsUnit A) : A.det ≠ 0 :=
  isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det A).mp h)

theorem selectedMinor_isUnit (alpha : ℝ) (ha : 0 ≤ alpha) :
    IsUnit (selectedMinor (frozen alpha 5)) := by
  rw [selectedMinor_frozen_eq alpha ha]
  exact blocks_isUnit _ _ _ (V18LightJacobian.minor_det_ne_zero alpha 5)
    V18MiddleJacobian.middle_det_ne_zero V18HeavyJacobian.heavy_det_ne_zero

theorem selectedMinor_det_ne_zero (alpha : ℝ) (ha : 0 ≤ alpha) :
    (selectedMinor (frozen alpha 5)).det ≠ 0 :=
  det_ne_zero_of_isUnit _ (selectedMinor_isUnit alpha ha)

theorem selectedMinor_rank (alpha : ℝ) (ha : 0 ≤ alpha) :
    (selectedMinor (frozen alpha 5)).rank = 11 := by
  simpa [Sector] using Matrix.rank_of_isUnit _ (selectedMinor_isUnit alpha ha)

/-- The full derivative matrix before any columns are selected. -/
def jacobianMatrix (p : Params) : Matrix (Fin 11) (Fin 31) ℝ :=
  LinearMap.toMatrix' (jacobian p).toLinearMap

theorem selectedMinor_eq_submatrix (p : Params) :
    selectedMinor p =
      (jacobianMatrix p).submatrix sectorEquiv (fun j => selectedColumn (sectorEquiv j)) := by
  ext i j
  simp only [selectedMinor, jacobianMatrix, Matrix.submatrix_apply, LinearMap.toMatrix'_apply,
    ContinuousLinearMap.coe_coe]
  have hb : (Pi.single (selectedColumn (sectorEquiv j)) 1 : Params) =
      (fun k : Fin 31 => if k = selectedColumn (sectorEquiv j) then 1 else 0) := by
    funext k
    simp only [Pi.single_apply]
  rw [hb]

theorem jacobianMatrix_rank (alpha : ℝ) (ha : 0 ≤ alpha) :
    (jacobianMatrix (frozen alpha 5)).rank = 11 := by
  have hr := Matrix.rank_submatrix_le
    (fun j : Sector => selectedColumn (sectorEquiv j)) sectorEquiv
    (jacobianMatrix (frozen alpha 5)).transpose
  have he :
      (jacobianMatrix (frozen alpha 5)).transpose.submatrix
          (fun j : Sector => selectedColumn (sectorEquiv j)) sectorEquiv =
        (selectedMinor (frozen alpha 5)).transpose := by
    rw [selectedMinor_eq_submatrix]
    rfl
  rw [he, Matrix.rank_transpose, Matrix.rank_transpose, selectedMinor_rank alpha ha] at hr
  exact le_antisymm
    (by simpa using (Matrix.rank_le_card_height (jacobianMatrix (frozen alpha 5)))) hr

/-- Exact rank of the Fréchet derivative of `observed` at the frozen vector. -/
theorem jacobian_rank (alpha : ℝ) (ha : 0 ≤ alpha) :
    Module.finrank ℝ (LinearMap.range (jacobian (frozen alpha 5)).toLinearMap) = 11 := by
  have h := jacobianMatrix_rank alpha ha
  change Module.finrank ℝ (LinearMap.range
    (LinearMap.toMatrix' (jacobian (frozen alpha 5)).toLinearMap).mulVecLin) = 11 at h
  rw [← Matrix.toLin'_apply', Matrix.toLin'_toMatrix'] at h
  exact h

theorem jacobian_nullity (alpha : ℝ) (ha : 0 ≤ alpha) :
    Module.finrank ℝ (LinearMap.ker (jacobian (frozen alpha 5)).toLinearMap) = 20 := by
  have hsum := LinearMap.finrank_range_add_finrank_ker (jacobian (frozen alpha 5)).toLinearMap
  have hd : Module.finrank ℝ Params = 31 := by simp [Params]
  have hr := jacobian_rank alpha ha
  omega

theorem jacobian_surjective (alpha : ℝ) (ha : 0 ≤ alpha) :
    Function.Surjective (jacobian (frozen alpha 5)) := by
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq
  simpa using jacobian_rank alpha ha

/-- The manuscript interval is included without assuming an exact value of
the historically optimized suppression parameter. -/
theorem rank_nullity_on_alpha_interval (alpha : ℝ) (ha : alpha ∈ Set.Icc 5.172 5.173) :
    Module.finrank ℝ (LinearMap.range (jacobian (frozen alpha 5)).toLinearMap) = 11 ∧
    Module.finrank ℝ (LinearMap.ker (jacobian (frozen alpha 5)).toLinearMap) = 20 := by
  have h : 0 ≤ alpha := by linarith [ha.1]
  exact ⟨jacobian_rank alpha h, jacobian_nullity alpha h⟩

end ReyesMath.V18Forward
