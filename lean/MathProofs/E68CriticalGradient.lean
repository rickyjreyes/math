import Mathlib

/-!
# E68: genuine whole-space critical Lⁿ gradient control on Euclidean balls

This is the exact Hölder exponent step of the corrected E68' theorem.
The statements use the *actual* Lebesgue volume measure, actual open
Euclidean balls, and actual Lᵖ seminorms (no finite model).
-/

noncomputable section
open MeasureTheory

namespace ReyesMath.E68

/-- For dimension n>2, actual L² gradient seminorm on any ball is
controlled by the global Lⁿ seminorm and the exact volume factor.
The vector field g can be the weak gradient of an H¹ function.
No H¹->Lⁿ regularity is assumed or inferred. -/
theorem local_critical_gradient_norm
    (n : ℕ) (hn : 2 < n)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg : AEStronglyMeasurable g (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (center : EuclideanSpace ℝ (Fin n)) (R : ℝ) :
    eLpNorm g 2 (volume.restrict (Metric.ball center R)) ≤
      eLpNorm g (n : ℝ≥0∞) volume *
        ((volume.restrict (Metric.ball center R)) Set.univ) ^
          (1 / (2 : ℝ≥0∞).toReal - 1 / (n : ℝ≥0∞).toReal) := by
  have hpq : (2 : ℝ≥0∞) ≤ (n : ℝ≥0∞) := by
    exact_mod_cast Nat.le_of_lt hn
  have hcomp := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (f := g) (μ := volume.restrict (Metric.ball center R))
    hpq hg.restrict
  calc
    eLpNorm g 2 (volume.restrict (Metric.ball center R)) ≤
        eLpNorm g (n : ℝ≥0∞) (volume.restrict (Metric.ball center R)) *
          ((volume.restrict (Metric.ball center R)) Set.univ) ^
            (1 / (2 : ℝ≥0∞).toReal - 1 / (n : ℝ≥0∞).toReal) := hcomp
    _ ≤ eLpNorm g (n : ℝ≥0∞) volume *
          ((volume.restrict (Metric.ball center R)) Set.univ) ^
            (1 / (2 : ℝ≥0∞).toReal - 1 / (n : ℝ≥0∞).toReal) := by
      gcongr
      exact eLpNorm_restrict_le g (n : ℝ≥0∞) volume (Metric.ball center R)

/-- Exact radius dependence of Lebesgue volume for every n>2 and R>0.
This is the geometric origin of the R^(n-2) energy exponent. -/
theorem euclidean_ball_volume_scaling
    (n : ℕ) (hn : 2 < n)
    (center : EuclideanSpace ℝ (Fin n)) (R : ℝ) (hR : 0 < R) :
    volume (Metric.ball center R) =
      ENNReal.ofReal (R ^ n) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
  rw [Measure.addHaar_ball (volume : Measure (EuclideanSpace ℝ (Fin n))) center hR.le]
  simp [finrank_euclideanSpace]

end ReyesMath.E68
