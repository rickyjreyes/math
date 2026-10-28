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

namespace ReyesMath.E68

/-- Explicit C∞ bump of inner radius 1/4 and outer radius 1/2. -/
def compactProfile (n : ℕ) :
    ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) :=
  ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

theorem compactProfile_smooth (n : ℕ) :
    ContDiff ℝ ⊤ (fun x : EuclideanSpace ℝ (Fin n) =>
      compactProfile n x) :=
  (compactProfile n).contDiff

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
    ContDiff ℝ ⊤ (smoothConcentration n R) := by
  have hlin : ContDiff ℝ ⊤
      (fun x : EuclideanSpace ℝ (Fin n) => (R⁻¹ : ℝ) • x) :=
    contDiff_const_smul _
  have hb : ContDiff ℝ ⊤
      (fun x : EuclideanSpace ℝ (Fin n) =>
        compactProfile n ((R⁻¹ : ℝ) • x)) :=
    (compactProfile_smooth n).comp hlin
  unfold smoothConcentration
  exact contDiff_const.mul hb

/-- A concrete nonconstant smooth compactly supported real function
whose support is in (-1,1), for the dimension-one case. -/
def compactOneDim : ContDiffBump (0 : ℝ) :=
  ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

theorem compactOneDim_smooth : ContDiff ℝ ⊤ (fun x : ℝ => compactOneDim x) :=
  compactOneDim.contDiff

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

end ReyesMath.E68
