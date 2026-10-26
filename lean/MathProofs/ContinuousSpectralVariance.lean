import Mathlib

/-!
# Continuous weighted variance identity

Unlike the old finite-sum variance statement, this is the exact Bochner
integral weighted-variance identity on an arbitrary measure space.
The full spectral-phase identity also requires the periodic eigenfunction,
polar decomposition, and integration-by-parts links, which remain open.
-/

namespace ReyesMath

open MeasureTheory

/-- The variance of an integrable observable with a normalized weight
equals weighted mean-square minus squared weighted mean. -/
theorem continuous_normalized_weighted_variance
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (w σ : α → ℝ)
    (hw : Integrable w μ)
    (hws : Integrable (fun x => w x * σ x) μ)
    (hwsq : Integrable (fun x => w x * (σ x) ^ 2) μ)
    (hwnorm : (∫ x, w x ∂μ) = 1) :
    (∫ x, w x * (σ x - (∫ y, w y * σ y ∂μ)) ^ 2 ∂μ) =
      (∫ x, w x * σ x ^ 2 ∂μ) -
        (∫ x, w x * σ x ∂μ) ^ 2 := by
  let c : ℝ := ∫ x, w x * σ x ∂μ
  have hexact :
      (fun x => w x * (σ x - c) ^ 2) =
      (fun x => (w x * σ x ^ 2 - (2 * c) * (w x * σ x)) +
        c ^ 2 * w x) := by
    funext x
    ring
  have hint1 : Integrable (fun x => w x * σ x ^ 2 -
      (2 * c) * (w x * σ x)) μ :=
    hwsq.sub (hws.const_mul _)
  have hint2 : Integrable (fun x => c ^ 2 * w x) μ :=
    hw.const_mul _
  change (∫ x, w x * (σ x - c) ^ 2 ∂μ) =
    (∫ x, w x * σ x ^ 2 ∂μ) - c ^ 2
  rw [hexact]
  calc
    (∫ x, (w x * σ x ^ 2 - (2 * c) * (w x * σ x)) +
      c ^ 2 * w x ∂μ) =
      (∫ x, w x * σ x ^ 2 - (2 * c) * (w x * σ x) ∂μ) +
        (∫ x, c ^ 2 * w x ∂μ) := integral_add hint1 hint2
    _ = (∫ x, w x * σ x ^ 2 ∂μ) -
        (2 * c) * (∫ x, w x * σ x ∂μ) +
        c ^ 2 * (∫ x, w x ∂μ) := by
      rw [integral_sub hwsq (hws.const_mul _),
        integral_const_mul, integral_const_mul]
    _ = (∫ x, w x * σ x ^ 2 ∂μ) - c ^ 2 := by
      rw [hwnorm]
      dsimp [c]
      ring

end ReyesMath
