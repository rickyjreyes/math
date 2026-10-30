import MathProofs.RemainingCores

/-!
# E26: conditional continuum L² curvature-quotient bound

The denominator lower bound is an *almost-everywhere* separation
assumption on the actual complex-valued fields, not a pointwise
condition artificially imposed at every representative. The result
uses the genuine continuum extended L² norm (eLpNorm at exponent 2).

This does not by itself prove the manuscript's independent
counterexample or its full curvature-operator regularity.
-/

namespace ReyesMath
namespace E26L2

open MeasureTheory RemainingCores

/-- Genuine continuum extended L² norm bound for a separated
complex denominator. The almost-everywhere denominator hypothesis
is exactly the one required for the quotient estimate. -/
theorem quotient_eLpNorm_le_scaled
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (numerator denominator : α → ℂ) (δ : ℝ)
    (hδ : 0 < δ)
    (hsep : ∀ᵐ x ∂μ, δ ≤ ‖denominator x‖) :
    eLpNorm (fun x => numerator x / denominator x) 2 μ ≤
      eLpNorm (fun x => (1 / δ : ℝ) • numerator x) 2 μ := by
  apply eLpNorm_mono_ae
  filter_upwards [hsep] with x hx
  calc
    ‖numerator x / denominator x‖ ≤
        (1 / δ) * ‖numerator x‖ :=
      conditionalCurvature_pointwise (numerator x) (denominator x) δ hδ hx
    _ = ‖(1 / δ : ℝ) • numerator x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos (by norm_num) hδ)]

end E26L2
end ReyesMath
