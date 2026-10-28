import Mathlib
import MathProofs.E68SmoothProfiles
import MathProofs.E68Scaling

/-!
# E68: a genuine positive derivative-energy integral in dimension one

The profile is Mathlib's nonconstant, compactly supported C-infinity
bump in (-1,1). This file proves positivity of its actual whole-line
Lebesgue integral of the squared classical derivative. It is not an
abstract "positive energy" parameter substituted into a scaling law.

The full E68 one-dimensional contradiction additionally requires the
comparison of this integral to the exact radius-dependent right side.
-/

noncomputable section
open scoped ContDiff
open MeasureTheory
open Function

namespace ReyesMath.E68

private def bump1 : ℝ → ℝ := fun x => compactOneDim x

private theorem bump1_smooth : ContDiff ℝ ∞ bump1 :=
  compactOneDim_smooth

private theorem bump1_compact : HasCompactSupport bump1 :=
  compactOneDim_hasCompactSupport

/-- The derivative of the actual smooth compact bump cannot vanish
identically because its values at 0 and 1 are distinct. -/
theorem compactOneDim_deriv_nonzero :
    ∃ x : ℝ, deriv bump1 x ≠ 0 := by
  by_contra hnone
  push_neg at hnone
  have hconst : bump1 0 = bump1 1 :=
    is_const_of_deriv_eq_zero
      (bump1_smooth.differentiable (by simp)) hnone 0 1
  exact compactOneDim_nonconstant hconst

/-- The real-valued derivative has compact support, so its squared
derivative is integrable over actual Lebesgue measure on R. -/
theorem compactOneDim_deriv_energy_integrable :
    Integrable (fun x : ℝ => (deriv bump1 x) ^ 2) := by
  have hc : Continuous (fun x : ℝ => (deriv bump1 x) ^ 2) :=
    (bump1_smooth.continuous_deriv (by simp)).pow 2
  have hs : HasCompactSupport (fun x : ℝ => (deriv bump1 x) ^ 2) := by
    simpa [bump1, pow_two, Pi.mul_apply] using
      (bump1_compact.deriv.mul_right
        (f' := fun x : ℝ => deriv bump1 x))
  exact hc.integrable_of_hasCompactSupport hs

/-- Strictly positive real continuum gradient energy:
integral over the whole real line of |f'(x)|^2 is nonzero. -/
theorem compactOneDim_deriv_energy_positive :
    0 < ∫ x : ℝ, (deriv bump1 x) ^ 2 := by
  obtain ⟨x, hx⟩ := compactOneDim_deriv_nonzero
  have hc : Continuous (fun y : ℝ => (deriv bump1 y) ^ 2) :=
    (bump1_smooth.continuous_deriv (by simp)).pow 2
  have hs : HasCompactSupport (fun y : ℝ => (deriv bump1 y) ^ 2) := by
    simpa [bump1, pow_two, Pi.mul_apply] using
      (bump1_compact.deriv.mul_right
        (f' := fun y : ℝ => deriv bump1 y))
  have hnonneg : 0 ≤ (fun y : ℝ => (deriv bump1 y) ^ 2) := by
    intro y
    exact sq_nonneg _
  have hne : (deriv bump1 x) ^ 2 ≠ 0 := pow_ne_zero 2 hx
  exact hc.integral_pos_of_hasCompactSupport_nonneg_nonzero hs hnonneg hne


/-- Every point with nonzero squared derivative belongs to the open
ball of radius R>=1: the original bump has radius 1/2 and the support
of its derivative lies inside the original closed support. -/
theorem compactOneDim_deriv_energy_support_ball
    (R : ℝ) (hR : 1 ≤ R) :
    Function.support (fun x : ℝ => (deriv bump1 x) ^ 2) ⊆
      Metric.ball (0 : ℝ) R := by
  intro x hx
  have hd : x ∈ Function.support (deriv bump1) := by
    intro he
    apply hx
    simp [he]
  have hts : x ∈ tsupport bump1 := support_deriv_subset hd
  change x ∈ tsupport (compactOneDim : ℝ → ℝ) at hts
  rw [compactOneDim.tsupport_eq] at hts
  have hdist : dist x (0 : ℝ) ≤ (1 / 2 : ℝ) := by
    simpa [Metric.mem_closedBall, compactOneDim] using hts
  exact Metric.mem_ball.mpr (lt_of_le_of_lt hdist (by linarith))

/-- Actual ball derivative energy equals the whole-line Lebesgue
integral once the ball contains the compact support. -/
theorem compactOneDim_deriv_ball_energy_eq_global
    (R : ℝ) (hR : 1 ≤ R) :
    (∫ x in Metric.ball (0 : ℝ) R, (deriv bump1 x) ^ 2) =
      (∫ x : ℝ, (deriv bump1 x) ^ 2) := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  by_contra he
  have hs : x ∈ Function.support
      (fun y : ℝ => (deriv bump1 y) ^ 2) := he
  exact hx (compactOneDim_deriv_energy_support_ball R hR hs)

/-- Genuine one-dimensional counterexample to an R^-1-uniform
local-gradient/H1-energy estimate. Both energies here are literal
continuum integrals of a single explicit C-infinity compact bump.
No abstract substitute for positive gradient energy is used. -/
theorem compactOneDim_forbids_uniform_inverse_radius_energy :
    ¬ ∃ C : ℝ, ∀ R : ℝ, 1 ≤ R →
      (∫ x in Metric.ball (0 : ℝ) R, (deriv bump1 x) ^ 2) ≤
      C * ((∫ x : ℝ, (bump1 x) ^ 2) +
           (∫ x : ℝ, (deriv bump1 x) ^ 2)) / R := by
  rintro ⟨C, hall⟩
  apply (large_radius_one_dimensional_obstruction
    (∫ x : ℝ, (deriv bump1 x) ^ 2)
    ((∫ x : ℝ, (bump1 x) ^ 2) +
     (∫ x : ℝ, (deriv bump1 x) ^ 2))
    compactOneDim_deriv_energy_positive)
  refine ⟨C, ?_⟩
  intro R hR
  simpa only [compactOneDim_deriv_ball_energy_eq_global R hR] using hall R hR

end ReyesMath.E68
