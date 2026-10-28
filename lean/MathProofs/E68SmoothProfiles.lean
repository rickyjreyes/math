import Mathlib

/-!
# E68: actual C-infinity compactly supported functions

Unlike a purely symbolic scaling contradiction, these are genuine
real-space functions on EuclideanSpace ℝ (Fin n), constructed from
Mathlib's smooth bump-function infrastructure.  The missing step for
the complete E68 classification is to prove the exact whole-space L²
derivative integral scaling and positive gradient energy of these
specific profiles.
-/

noncomputable section
open scoped ContDiff

namespace ReyesMath.E68

/-- Explicit C∞ bump of inner radius 1/4 and outer radius 1/2. -/
def compactProfile (n : ℕ) :
    ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) :=
  ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

theorem compactProfile_smooth (n : ℕ) :
    ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin n) =>
      compactProfile n x) :=
  (compactProfile n).contDiff (n := ⊤)

theorem compactProfile_hasCompactSupport (n : ℕ) :
    HasCompactSupport (fun x : EuclideanSpace ℝ (Fin n) =>
      compactProfile n x) :=
  (compactProfile n).hasCompactSupport

/-- Actual pointwise Euclidean rescaling in the E68 concentration
argument. This does *not* replace its measure and Sobolev estimates. -/
def smoothConcentration (n : ℕ) (R : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (R ^ (1 - (n : ℝ) / 2)) *
    compactProfile n ((R⁻¹ : ℝ) • x)

/-- The scaled concentration function is genuinely C∞ in every
dimension, not a formal scaling symbol. -/
theorem smoothConcentration_smooth (n : ℕ) (R : ℝ) :
    ContDiff ℝ ∞ (smoothConcentration n R) := by
  have hlin : ContDiff ℝ ∞
      (fun x : EuclideanSpace ℝ (Fin n) => (R⁻¹ : ℝ) • x) :=
    contDiff_const_smul _
  have hb : ContDiff ℝ ∞
      (fun x : EuclideanSpace ℝ (Fin n) =>
        compactProfile n ((R⁻¹ : ℝ) • x)) :=
    (compactProfile_smooth n).comp hlin
  unfold smoothConcentration
  exact contDiff_const.mul hb

/-- A concrete nonconstant smooth compactly supported real function
whose support is in (-1,1), for the dimension-one case. -/
def compactOneDim : ContDiffBump (0 : ℝ) :=
  ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

theorem compactOneDim_smooth : ContDiff ℝ ∞ (fun x : ℝ => compactOneDim x) :=
  compactOneDim.contDiff (n := ⊤)

theorem compactOneDim_hasCompactSupport :
    HasCompactSupport (fun x : ℝ => compactOneDim x) :=
  compactOneDim.hasCompactSupport

theorem compactOneDim_at_zero : compactOneDim 0 = 1 := by
  apply compactOneDim.one_of_mem_closedBall
  simp [Metric.mem_closedBall, compactOneDim]

theorem compactOneDim_at_one : compactOneDim 1 = 0 := by
  apply compactOneDim.zero_of_le_dist
  norm_num [compactOneDim, Real.dist_eq]

theorem compactOneDim_nonconstant : compactOneDim 0 ≠ compactOneDim 1 := by
  rw [compactOneDim_at_zero, compactOneDim_at_one]
  norm_num

/-- Every positive-radius concentration is an actual compactly
supported smooth field, not a formal rescaling symbol. -/
theorem smoothConcentration_hasCompactSupport (n : ℕ) (R : ℝ)
    (hR : 0 < R) :
    HasCompactSupport (smoothConcentration n R) := by
  have hcomp : HasCompactSupport
      (fun x : EuclideanSpace ℝ (Fin n) =>
        compactProfile n ((R⁻¹ : ℝ) • x)) :=
    (compactProfile_hasCompactSupport n).comp_smul
      (inv_ne_zero (ne_of_gt hR))
  change HasCompactSupport
    ((fun _ : EuclideanSpace ℝ (Fin n) =>
        R ^ (1 - (n : ℝ) / 2)) *
      (fun x : EuclideanSpace ℝ (Fin n) =>
        compactProfile n ((R⁻¹ : ℝ) • x)))
  exact hcomp.mul_left

/-- The chosen one-dimensional bump has support *inside* (-1,1),
exactly as required for the large-radius E68 counterexample. -/
theorem compactOneDim_support_in_unit_interval :
    Function.support (fun x : ℝ => compactOneDim x) ⊆
      Set.Ioo (-1 : ℝ) 1 := by
  intro x hx
  have hball : x ∈ Metric.ball (0 : ℝ) compactOneDim.rOut := by
    rw [← compactOneDim.support_eq]
    exact hx
  have hnorm : |x| < (1 / 2 : ℝ) := by
    simpa [Metric.mem_ball, Real.dist_eq, compactOneDim] using hball
  exact ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩

end ReyesMath.E68
