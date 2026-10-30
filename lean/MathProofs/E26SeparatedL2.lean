import MathProofs.E26L2

/-!
# E26: genuine L² integrability and norm estimate under denominator separation

This is the Hilbert-space formulation of the historical E26 conditional
quotient result. It proves that every L² numerator divided by a
measurable, almost-everywhere uniformly separated complex denominator
remains in L², with the sharp general comparison factor 1/δ.

For the exact E26 PDE statement one must additionally identify the
numerator with the weak Laplacian of an H² field and the denominator
with the historical additive regularization. Those field-level
identifications are not assumed proved here.
-/

namespace ReyesMath
namespace E26SeparatedL2

open MeasureTheory RemainingCores

variable {α : Type*} [MeasurableSpace α]

/-- Uniform separation is sufficient for the quotient of a genuine
L² numerator to belong to the same L² space. -/
theorem quotient_memLp (μ : Measure α)
    (numerator denominator : α → ℂ) (δ : ℝ)
    (hδ : 0 < δ)
    (hn : MemLp numerator 2 μ)
    (hq : AEStronglyMeasurable
      (fun x => numerator x / denominator x) μ)
    (hsep : ∀ᵐ x ∂μ, δ ≤ ‖denominator x‖) :
    MemLp (fun x => numerator x / denominator x) 2 μ := by
  apply MemLp.of_le_mul hn hq
  filter_upwards [hsep] with x hx
  exact conditionalCurvature_pointwise (numerator x)
    (denominator x) δ hδ hx

/-- The conditional estimate is an inequality of the actual L²
equivalence-class norms, not just an extended seminorm of raw functions. -/
theorem quotient_L2_norm_le (μ : Measure α)
    (numerator denominator : α → ℂ) (δ : ℝ)
    (hδ : 0 < δ)
    (hn : MemLp numerator 2 μ)
    (hq : AEStronglyMeasurable
      (fun x => numerator x / denominator x) μ)
    (hsep : ∀ᵐ x ∂μ, δ ≤ ‖denominator x‖) :
    ‖(quotient_memLp μ numerator denominator δ hδ hn hq hsep).toLp
      (fun x => numerator x / denominator x)‖ ≤
        (1 / δ) * ‖hn.toLp numerator‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards
    [MemLp.coeFn_toLp
      (quotient_memLp μ numerator denominator δ hδ hn hq hsep),
     MemLp.coeFn_toLp hn, hsep] with x hx hy hz
  rw [hx, hy]
  exact conditionalCurvature_pointwise (numerator x)
    (denominator x) δ hδ hz

end E26SeparatedL2
end ReyesMath
