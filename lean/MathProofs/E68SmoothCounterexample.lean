import Mathlib
import MathProofs.E68ScaledGradient

/-!
# E68: continuum smooth concentration obstruction in dimensions n > 2

This file finishes the missing bridge from actual compactly supported
smooth functions, their genuine Fréchet derivatives, and whole-space
Lebesgue integrals to the smooth E68 counterexample.

In particular, a single uniform constant cannot bound the local
gradient energy of *all* scaled smooth compact bump fields at all
positive radii if n > 2. This is distinct from the fixed singular
H¹ counterexample, the corrected E68' theorem, and H² embedding claims.
-/

noncomputable section

open MeasureTheory

namespace ReyesMath.E68

/-- The actual normalized radial bump is supported inside the ball
of radius R, rather than only being abstractly compactly supported. -/
theorem smoothConcentration_tsupport_inside_ball
    (n : ℕ) (R : ℝ) (hR : 0 < R) :
    tsupport (smoothConcentration n R) ⊆
      Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R := by
  intro x hx
  have hs : x ∈ tsupport
      (fun y : EuclideanSpace ℝ (Fin n) =>
        compactProfile n ((R⁻¹ : ℝ) • y)) := by
    exact (tsupport_mul_subset_right
      (f := fun _ : EuclideanSpace ℝ (Fin n) =>
        R ^ (1 - (n : ℝ) / 2))
      (g := fun y : EuclideanSpace ℝ (Fin n) =>
        compactProfile n ((R⁻¹ : ℝ) • y))) (by
          simpa only [smoothConcentration] using hx)
  have hp : (R⁻¹ : ℝ) • x ∈
      tsupport (fun y : EuclideanSpace ℝ (Fin n) =>
        compactProfile n y) :=
    tsupport_comp_subset_preimage
      (f := fun y : EuclideanSpace ℝ (Fin n) => (R⁻¹ : ℝ) • y)
      (fun y : EuclideanSpace ℝ (Fin n) => compactProfile n y)
      (by fun_prop) hs
  rw [(compactProfile n).tsupport_eq] at hp
  have hnorm : ‖(R⁻¹ : ℝ) • x‖ ≤ (1 / 2 : ℝ) := by
    simpa [Metric.mem_closedBall, dist_zero, compactProfile] using hp
  have hnorm' : R⁻¹ * ‖x‖ ≤ (1 / 2 : ℝ) := by
    simpa [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)] using hnorm
  have hrunit : R * R⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hR)
  have hsmall : ‖x‖ ≤ R / 2 := by
    calc
      ‖x‖ = R * (R⁻¹ * ‖x‖) := by rw [← mul_assoc, hrunit, one_mul]
      _ ≤ R * (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left hnorm' hR.le
      _ = R / 2 := by ring
  apply Metric.mem_ball.mpr
  have : R / 2 < R := by linarith
  simpa [dist_zero] using lt_of_le_of_lt hsmall this

/-- Every nonzero squared Fréchet derivative lies in the actual
physical ball B_R, using the smooth field's closed topological support. -/
theorem smoothConcentration_gradient_support_inside_ball
    (n : ℕ) (R : ℝ) (hR : 0 < R) :
    Function.support (fun x : EuclideanSpace ℝ (Fin n) =>
      ‖fderiv ℝ (smoothConcentration n R) x‖ ^ 2) ⊆
        Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R := by
  intro x hx
  have hd : x ∈ Function.support
      (fderiv ℝ (smoothConcentration n R)) := by
    intro hz
    exact hx (by simp [hz])
  exact smoothConcentration_tsupport_inside_ball n R hR
    ((support_fderiv_subset ℝ) hd)

/-- A genuine ball integral equals the whole-space gradient energy
of the actual normalized smooth field at every positive radius. -/
theorem smoothConcentration_ball_energy_eq_global
    (n : ℕ) (R : ℝ) (hR : 0 < R) :
    (∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R,
      ‖fderiv ℝ (smoothConcentration n R) x‖ ^ 2) =
    (∫ x : EuclideanSpace ℝ (Fin n),
      ‖fderiv ℝ (smoothConcentration n R) x‖ ^ 2) := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  by_contra he
  exact hx (smoothConcentration_gradient_support_inside_ball n R hR he)

/-- For n>2, no universal E68 constant works even on the explicit
smooth compactly supported concentration family. Both sides are
literal continuum integral quantities of the actual scaled fields. -/
theorem no_uniform_E68_for_smooth_concentrations
    (n : ℕ) (hn : 2 < n) :
    ¬ ∃ C : ℝ, ∀ R : ℝ, 0 < R →
      (∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R,
        ‖fderiv ℝ (smoothConcentration n R) x‖ ^ 2) ≤
      C * R ^ (n - 2) *
        ((∫ x : EuclideanSpace ℝ (Fin n),
          (smoothConcentration n R x) ^ 2) +
         (∫ x : EuclideanSpace ℝ (Fin n),
          ‖fderiv ℝ (smoothConcentration n R) x‖ ^ 2)) := by
  let A : ℝ := ∫ x : EuclideanSpace ℝ (Fin n),
    ‖fderiv ℝ (fun y => compactProfile n y) x‖ ^ 2
  let B : ℝ := ∫ x : EuclideanSpace ℝ (Fin n),
    (compactProfile n x) ^ 2
  have hA : 0 < A := by
    exact compactProfile_gradient_energy_positive n (by omega)
  apply (smooth_concentration_scaling_obstruction n hn A B hA)
  rintro ⟨C, hC⟩
  refine ⟨C, ?_⟩
  intro R hR
  have hh := hC R hR
  rw [smoothConcentration_ball_energy_eq_global n R hR,
    smoothConcentration_gradient_energy_constant n (by omega) R hR,
    smoothConcentration_mass_R_sq n (by omega) R hR] at hh
  simpa only [A, B, add_comm] using hh

end ReyesMath.E68
