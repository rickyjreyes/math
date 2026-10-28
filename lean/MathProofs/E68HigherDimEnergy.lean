import Mathlib
import MathProofs.E68SmoothProfiles

/-!
# E68 n>2: genuine nonzero continuum gradient-energy witnesses

For any positive Euclidean dimension, the C-infinity compact bump
is nonconstant. Its actual Fréchet derivative has finite, strictly
positive squared L2 Lebesgue energy. These facts provide the required
nonzero numerator for a concentrating-field scaling contradiction.

This does NOT prove the change-of-variables formula for the scaled
family, the singular H1 counterexample, or the full E68 iff theorem.
-/

noncomputable section
open scoped ContDiff
open MeasureTheory

namespace ReyesMath.E68

private def bumpD (n : ℕ) :
    EuclideanSpace ℝ (Fin n) → ℝ :=
  fun x => compactProfile n x

private theorem bumpD_smooth (n : ℕ) :
    ContDiff ℝ ∞ (bumpD n) := compactProfile_smooth n

private theorem bumpD_compact (n : ℕ) :
    HasCompactSupport (bumpD n) := compactProfile_hasCompactSupport n

/-- The actual n-dimensional bump has a nonzero Fréchet derivative
somewhere, since it equals one at the origin and vanishes at a
standard unit coordinate vector. -/
theorem compactProfile_fderiv_nonzero
    (n : ℕ) (hn : 0 < n) :
    ∃ x : EuclideanSpace ℝ (Fin n), fderiv ℝ (bumpD n) x ≠ 0 := by
  let i : Fin n := ⟨0, by omega⟩
  let e : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single i (1 : ℝ)
  have h0 : bumpD n 0 = 1 := by
    apply (compactProfile n).one_of_mem_closedBall
    simp [bumpD, Metric.mem_closedBall]
  have he : bumpD n e = 0 := by
    apply (compactProfile n).zero_of_le_dist
    simp [bumpD, e, compactProfile, dist_zero]
  by_contra hnone
  push_neg at hnone
  have heq : bumpD n (0 : EuclideanSpace ℝ (Fin n)) =
      bumpD n e :=
    is_const_of_fderiv_eq_zero
      ((bumpD_smooth n).differentiable (by simp)) hnone 0 e
  rw [h0, he] at heq
  norm_num at heq

/-- Squared actual derivative norm of the smooth radial bump is
Lebesgue-integrable on full R^n, without a grid approximation. -/
theorem compactProfile_gradient_energy_integrable
    (n : ℕ) :
    Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
      ‖fderiv ℝ (bumpD n) x‖ ^ 2) := by
  have hc : Continuous (fun x : EuclideanSpace ℝ (Fin n) =>
      ‖fderiv ℝ (bumpD n) x‖ ^ 2) :=
    ((bumpD_smooth n).continuous_fderiv (by simp)).norm.pow 2
  have hs : HasCompactSupport
      (fun x : EuclideanSpace ℝ (Fin n) =>
        ‖fderiv ℝ (bumpD n) x‖ ^ 2) := by
    have hh : HasCompactSupport
        (fun x : EuclideanSpace ℝ (Fin n) =>
          ‖fderiv ℝ (bumpD n) x‖) :=
      ((bumpD_compact n).fderiv ℝ).norm
    simpa [pow_two, Pi.mul_apply] using
      hh.mul_right (f' := fun x : EuclideanSpace ℝ (Fin n) =>
        ‖fderiv ℝ (bumpD n) x‖)
  exact hc.integrable_of_hasCompactSupport hs

/-- Strictly positive whole-space L2 derivative energy for a genuine
nonconstant smooth compact bump in every positive dimension. -/
theorem compactProfile_gradient_energy_positive
    (n : ℕ) (hn : 0 < n) :
    0 < (∫ x : EuclideanSpace ℝ (Fin n),
      ‖fderiv ℝ (bumpD n) x‖ ^ 2) := by
  obtain ⟨x, hx⟩ := compactProfile_fderiv_nonzero n hn
  have hc : Continuous (fun y : EuclideanSpace ℝ (Fin n) =>
      ‖fderiv ℝ (bumpD n) y‖ ^ 2) :=
    ((bumpD_smooth n).continuous_fderiv (by simp)).norm.pow 2
  have hs : HasCompactSupport
      (fun y : EuclideanSpace ℝ (Fin n) =>
        ‖fderiv ℝ (bumpD n) y‖ ^ 2) := by
    have hh : HasCompactSupport
        (fun y : EuclideanSpace ℝ (Fin n) =>
          ‖fderiv ℝ (bumpD n) y‖) :=
      ((bumpD_compact n).fderiv ℝ).norm
    simpa [pow_two, Pi.mul_apply] using
      hh.mul_right (f' := fun y : EuclideanSpace ℝ (Fin n) =>
        ‖fderiv ℝ (bumpD n) y‖)
  have hnonneg : 0 ≤ (fun y : EuclideanSpace ℝ (Fin n) =>
      ‖fderiv ℝ (bumpD n) y‖ ^ 2) := by
    intro y
    exact sq_nonneg _
  have hnorm : ‖fderiv ℝ (bumpD n) x‖ ≠ 0 := by
    intro hz
    exact hx (norm_eq_zero.mp hz)
  have hsq : ‖fderiv ℝ (bumpD n) x‖ ^ 2 ≠ 0 :=
    pow_ne_zero 2 hnorm
  exact hc.integral_pos_of_hasCompactSupport_nonneg_nonzero hs hnonneg hsq

end ReyesMath.E68
