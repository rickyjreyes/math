import Mathlib

/-!
# Frozen v18 heavy-sector exact nonzero 3×3 Jacobian minor

The frozen heavy observable indices are n=95,96,123, with selected
parameters (boson_nonlin1_scale, wz_break_scale, higgs_offset).
The resulting block is

  [ (95/100)^(-1.189)  sin(-1.264*95+4.685)   0 ]
  [ (96/100)^(-1.189)  sin(-1.264*96+4.685)   0 ]
  [ (123/100)^(-1.189)           0            1 ].

The determinant is strictly positive *symbolically*:
the first base is positive, sin(-116.659)>0,
the second base is positive, and sin(-115.395)<0.
The sine signs are proved by exact period reduction and certified
rational bounds 3.14 < π < 3.15, not floating-point approximations.

This certifies the exact frozen heavy analytic block, conditional only
on the independently stated branch selection in the v18 model.
-/

noncomputable section
namespace ReyesMath.V18HeavyJacobian

private theorem pi_bounds : (3.14 : ℝ) < Real.pi ∧ Real.pi < 3.15 :=
  ⟨Real.pi_gt_d2, Real.pi_lt_d2⟩

theorem sin_96_pos : 0 < Real.sin (-116.659 : ℝ) := by
  have hx : 0 < (-116.659 : ℝ) + 38 * Real.pi := by
    nlinarith [pi_bounds.1]
  have hy : (-116.659 : ℝ) + 38 * Real.pi < Real.pi := by
    nlinarith [pi_bounds.2]
  have hs := Real.sin_pos_of_pos_of_lt_pi hx hy
  have hper : Real.sin ((-116.659 : ℝ) + 38 * Real.pi) =
      Real.sin (-116.659 : ℝ) := by
    convert Real.sin_add_nat_mul_two_pi (-116.659 : ℝ) 19 using 1 <;> ring
  rw [hper] at hs
  exact hs

theorem sin_95_neg : Real.sin (-115.395 : ℝ) < 0 := by
  have hx : 0 < (-115.395 : ℝ) + 37 * Real.pi := by
    nlinarith [pi_bounds.1]
  have hy : (-115.395 : ℝ) + 37 * Real.pi < Real.pi := by
    nlinarith [pi_bounds.2]
  have hs := Real.sin_pos_of_pos_of_lt_pi hx hy
  have hshift : Real.sin ((-115.395 : ℝ) + 38 * Real.pi) =
      -Real.sin ((-115.395 : ℝ) + 37 * Real.pi) := by
    convert Real.sin_add_pi ((-115.395 : ℝ) + 37 * Real.pi) using 1 <;> ring
  have hper : Real.sin ((-115.395 : ℝ) + 38 * Real.pi) =
      Real.sin (-115.395 : ℝ) := by
    convert Real.sin_add_nat_mul_two_pi (-115.395 : ℝ) 19 using 1 <;> ring
  rw [hper] at hshift
  linarith

private def a95 : ℝ := (0.95 : ℝ) ^ (-1.189 : ℝ)
private def a96 : ℝ := (0.96 : ℝ) ^ (-1.189 : ℝ)
private def a123 : ℝ := (1.23 : ℝ) ^ (-1.189 : ℝ)

private theorem a95_pos : 0 < a95 := Real.rpow_pos_of_pos (by norm_num) _
private theorem a96_pos : 0 < a96 := Real.rpow_pos_of_pos (by norm_num) _

/-- Exact analytic heavy minor at the historical coefficients. -/
def heavy : Matrix (Fin 3) (Fin 3) ℝ :=
  !![a95, Real.sin (-115.395), 0;
     a96, Real.sin (-116.659), 0;
     a123, 0, 1]

theorem heavy_det_eq :
    heavy.det =
      a95 * Real.sin (-116.659) - Real.sin (-115.395) * a96 := by
  rw [Matrix.det_fin_three]
  simp only [
    show heavy 0 0 = a95 from rfl,
    show heavy 0 1 = Real.sin (-115.395) from rfl,
    show heavy 0 2 = (0 : ℝ) from rfl,
    show heavy 1 0 = a96 from rfl,
    show heavy 1 1 = Real.sin (-116.659) from rfl,
    show heavy 1 2 = (0 : ℝ) from rfl,
    show heavy 2 0 = a123 from rfl,
    show heavy 2 1 = (0 : ℝ) from rfl,
    show heavy 2 2 = (1 : ℝ) from rfl]
  ring

/-- Exact symbolic positivity of the analytic heavy block, hence rank three.
The stronger numerical lower bound >1.2 remains a separate interval result. -/
theorem heavy_det_pos : 0 < heavy.det := by
  rw [heavy_det_eq]
  have h1 : 0 < a95 * Real.sin (-116.659) :=
    mul_pos a95_pos sin_96_pos
  have h2 : Real.sin (-115.395) * a96 < 0 :=
    mul_neg_of_neg_of_pos sin_95_neg a96_pos
  linarith

theorem heavy_det_ne_zero : heavy.det ≠ 0 :=
  ne_of_gt heavy_det_pos

end ReyesMath.V18HeavyJacobian
