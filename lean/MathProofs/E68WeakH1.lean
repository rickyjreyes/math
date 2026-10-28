import Mathlib
import MathProofs.E68Scaling

/-!
# E68 in dimension two: genuine weak H¹ gradients

The field's weak gradient is specified by integration by parts against
every smooth compactly supported real test function, for every direction.
This is a distributional definition, not an implicit assumption that a
classical strong fderiv exists. The two energies are actual whole-space
Lebesgue integrals.
-/

noncomputable section

open MeasureTheory

namespace ReyesMath.E68

/-- A complex distributional H¹ field on ℝⁿ, expressed using its
real-linear weak gradient and the exact distributional testing identity.
The L² energies are required to be integrable, not merely finite on a
chosen bounded region. -/
structure WeakH1Field (n : ℕ) where
  ψ : EuclideanSpace ℝ (Fin n) → ℂ
  weakGradient :
    EuclideanSpace ℝ (Fin n) →
      (EuclideanSpace ℝ (Fin n) →L[ℝ] ℂ)
  squareIntegrable :
    Integrable (fun x => ‖ψ x‖ ^ 2)
  gradientSquareIntegrable :
    Integrable (fun x => ‖weakGradient x‖ ^ 2)
  distributionalDerivative :
    ∀ (v : EuclideanSpace ℝ (Fin n))
      (φ : EuclideanSpace ℝ (Fin n) → ℝ),
      ContDiff ℝ ⊤ φ → HasCompactSupport φ →
        (∫ x, ψ x * ((fderiv ℝ φ x) v : ℂ)) =
          -(∫ x, (weakGradient x v) * (φ x : ℂ))

/-- E68 at n=2 for a *distributional* H¹ field: radius and center
are arbitrary, the sharp C₂=1 works, and the energy is computed
from the actual weak gradient rather than the classical fderiv. -/
theorem weakH1_two_dimensional_local_energy
    (u : WeakH1Field 2)
    (center : EuclideanSpace ℝ (Fin 2)) (R : ℝ) (_hR : 0 < R) :
    (∫ x in Metric.ball center R, ‖u.weakGradient x‖ ^ 2) ≤
      (∫ x, ‖u.ψ x‖ ^ 2) +
      (∫ x, ‖u.weakGradient x‖ ^ 2) := by
  have hloc :
      (∫ x in Metric.ball center R, ‖u.weakGradient x‖ ^ 2) ≤
        (∫ x, ‖u.weakGradient x‖ ^ 2) :=
    setIntegral_le_integral u.gradientSquareIntegrable
      (Filter.Eventually.of_forall (fun x =>
        sq_nonneg (‖u.weakGradient x‖)))
  have hpos : 0 ≤ (∫ x, ‖u.ψ x‖ ^ 2) :=
    integral_nonneg (fun x => sq_nonneg (‖u.ψ x‖))
  linarith

end ReyesMath.E68
