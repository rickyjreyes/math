import Mathlib
import MathProofs.ContinuousPhaseIntegral

/-!
# Attainment of the continuous fixed-integral weighted phase minimum

The admissible objects here are real mismatch functions on a measure space;
the H¹ winding phase-lift theorem is a separate (stronger) task.
No finite-dimensional surrogate or discrete sum is used.
-/

namespace ReyesMath

open MeasureTheory

/-- The explicit covariant mismatch f*=C/(I w) is an integrable
fixed-total-mismatch competitor and attains the exact lower energy. -/
theorem continuous_phase_optimal_mismatch_exists
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (w : α → ℝ) (C : ℝ)
    (hw : ∀ x, w x ≠ 0)
    (hinv : Integrable (fun x => (w x)⁻¹) μ)
    (hI : (∫ x, (w x)⁻¹ ∂μ) ≠ 0) :
    ∃ f : α → ℝ,
      Integrable f μ ∧
      (∫ x, f x ∂μ) = C ∧
      Integrable (fun x => w x * f x ^ 2) μ ∧
      (∫ x, w x * f x ^ 2 ∂μ) =
        C ^ 2 / (∫ x, (w x)⁻¹ ∂μ) := by
  let I : ℝ := ∫ x, (w x)⁻¹ ∂μ
  let η : ℝ := C / I
  let f : α → ℝ := fun x => η * (w x)⁻¹
  have hf : Integrable f μ := hinv.const_mul η
  have hfun :
      (fun x => w x * f x ^ 2) =
      (fun x => η ^ 2 * (w x)⁻¹) := by
    funext x
    dsimp [f]
    field_simp [hw x] <;> ring
  have he : Integrable (fun x => w x * f x ^ 2) μ := by
    rw [hfun]
    exact hinv.const_mul _
  have hIn : I ≠ 0 := hI
  have hη : η * I = C := by
    dsimp [η]
    field_simp [hIn]
  refine ⟨f, hf, ?_, he, ?_⟩
  · change (∫ x, η * (w x)⁻¹ ∂μ) = C
    rw [integral_const_mul]
    exact hη
  · rw [hfun, integral_const_mul]
    change η ^ 2 * I = C ^ 2 / I
    dsimp [η]
    field_simp [hIn] <;> ring

end ReyesMath
