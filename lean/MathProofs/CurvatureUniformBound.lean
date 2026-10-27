import Mathlib
import MathProofs.CurvatureLegacy

/-!
# Global uniform bound on the *actual* curvature weight F

With ε>0, α≥0 and s≥0,
  F(s) = s / (s + ε² exp(-2αs))²
satisfies F(s) ≤ 1 + (ε² exp(-2α))⁻².
This closes a genuine analytic ingredient of whole-space
nonattainment: the missing work is the H² field dilation, including
exact energy scaling and mass preservation.
-/

namespace ReyesMath

/-- A finite, parameter-dependent bound valid at every density
including the zero-field and large-field regimes. -/
theorem positive_curvature_weight_uniform_bound
    (ε α s : ℝ) (hε : 0 < ε) (hα : 0 ≤ α) (hs : 0 ≤ s) :
    positiveCurvatureWeight ε α s ≤
      1 + (ε ^ 2 * Real.exp (-2 * α))⁻¹ ^ 2 := by
  let E : ℝ := ε ^ 2 * Real.exp (-2 * α)
  let A : ℝ := ε ^ 2 * Real.exp (-2 * α * s)
  have hE : 0 < E := by
    dsimp [E]
    positivity
  have hA : 0 < A := by
    dsimp [A]
    positivity
  have hden : 0 < s + A := by linarith
  have hboundE : 0 ≤ E⁻¹ ^ 2 := sq_nonneg _
  unfold positiveCurvatureWeight
  change s / (s + A) ^ 2 ≤ 1 + E⁻¹ ^ 2
  by_cases hsmall : s ≤ 1
  · have hexp : Real.exp (-2 * α) ≤ Real.exp (-2 * α * s) := by
      apply Real.exp_le_exp.mpr
      have hprod : 0 ≤ α * (1 - s) :=
        mul_nonneg hα (by linarith)
      nlinarith
    have hAle : E ≤ A := by
      dsimp [E, A]
      exact mul_le_mul_of_nonneg_left hexp (sq_nonneg ε)
    have hdenE : E ≤ s + A := by linarith
    have hsq : E ^ 2 ≤ (s + A) ^ 2 := by nlinarith
    have hweight : s * E ^ 2 ≤ (s + A) ^ 2 := by
      have hm : s * E ^ 2 ≤ 1 * E ^ 2 :=
        mul_le_mul_of_nonneg_right hsmall (sq_nonneg E)
      nlinarith
    have hfrac : s / (s + A) ^ 2 ≤ 1 / E ^ 2 :=
      (div_le_div_iff₀ (pow_pos hden _) (pow_pos hE _)).2 (by nlinarith)
    have hrep : 1 / E ^ 2 = E⁻¹ ^ 2 := by
      field_simp [ne_of_gt hE]
    rw [hrep] at hfrac
    linarith
  · have hlarge : 1 ≤ s := le_of_not_ge hsmall
    have hsum : 1 ≤ s + A := by linarith
    have hsum2 : 0 ≤ (s + A) * ((s + A) - 1) :=
      mul_nonneg (le_of_lt hden) (by linarith)
    have hsq : s ≤ (s + A) ^ 2 := by nlinarith
    have hfrac : s / (s + A) ^ 2 ≤ 1 :=
      (div_le_iff₀ (pow_pos hden _)).2 (by nlinarith)
    linarith

end ReyesMath
