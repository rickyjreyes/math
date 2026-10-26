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

/-- Equality in the continuous weighted bound fixes the minimizing
mismatch almost everywhere. In the H¹ phase setting this is the uniqueness
statement for the covariant phase gradient; lifting to a phase and proving
uniqueness up to constants is the remaining separate Sobolev step. -/
theorem continuous_phase_minimizer_ae_unique
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (w f : α → ℝ) (C : ℝ)
    (hw : ∀ x, 0 < w x)
    (hf : Integrable f μ)
    (hinv : Integrable (fun x => (w x)⁻¹) μ)
    (hI : (∫ x, (w x)⁻¹ ∂μ) ≠ 0)
    (hC : (∫ x, f x ∂μ) = C)
    (hres : Integrable (fun x =>
      w x * (f x -
        (C / (∫ y, (w y)⁻¹ ∂μ)) * (w x)⁻¹) ^ 2) μ)
    (henergy : (∫ x, w x * f x ^ 2 ∂μ) =
      C ^ 2 / (∫ x, (w x)⁻¹ ∂μ)) :
    f =ᵐ[μ] (fun x =>
      (C / (∫ y, (w y)⁻¹ ∂μ)) * (w x)⁻¹) := by
  have hgap := continuous_phase_exact_gap μ w f C
    (fun x => ne_of_gt (hw x)) hf hinv hI hC hres
  have hz :
      (∫ x, w x * (f x -
        (C / (∫ y, (w y)⁻¹ ∂μ)) * (w x)⁻¹) ^ 2 ∂μ) = 0 := by
    linarith
  have hnonneg :
      0 ≤ (fun x : α =>
        w x * (f x - (C / (∫ y, (w y)⁻¹ ∂μ)) *
          (w x)⁻¹) ^ 2) := by
    intro x
    exact mul_nonneg (le_of_lt (hw x)) (sq_nonneg _)
  have hzero := (integral_eq_zero_iff_of_nonneg hnonneg hres).mp hz
  filter_upwards [hzero] with x hx
  have hsquare :
      (f x - (C / (∫ y, (w y)⁻¹ ∂μ)) * (w x)⁻¹) ^ 2 = 0 :=
    (mul_eq_zero.mp hx).resolve_left (ne_of_gt (hw x))
  nlinarith [hsquare]


end ReyesMath
