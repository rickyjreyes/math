import Mathlib

/-!
# Continuous weighted phase mismatch: exact integral square completion

This module addresses the **continuous integral**, not a finite-sum surrogate.
For a positive measurable weight on a measure space, the sharp fixed-integral
lower bound and the unique algebraic candidate are obtained by integrating an
exact pointwise square-completion identity. The H¹ endpoint/winding-lift
construction and a.e. equality uniqueness will be handled separately.
-/

namespace ReyesMath

open MeasureTheory

/-- A pointwise identity that holds for *any* nonzero real weight. -/
theorem continuous_phase_square_pointwise
    (w f η : ℝ) (hw : w ≠ 0) :
    w * f ^ 2 =
      w * (f - η * w⁻¹) ^ 2 + 2 * η * f - η ^ 2 * w⁻¹ := by
  field_simp [hw] <;> ring

/-- Exact integral-level completion of the square. Every term is a
genuine Bochner integral on the specified measure space. -/
theorem continuous_phase_square_integral
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (w f : α → ℝ) (η : ℝ)
    (hw : ∀ x, w x ≠ 0)
    (hf : Integrable f μ)
    (hinv : Integrable (fun x => (w x)⁻¹) μ)
    (hres : Integrable (fun x => w x * (f x - η * (w x)⁻¹) ^ 2) μ) :
    (∫ x, w x * f x ^ 2 ∂μ) =
      (∫ x, w x * (f x - η * (w x)⁻¹) ^ 2 ∂μ) +
        2 * η * (∫ x, f x ∂μ) -
        η ^ 2 * (∫ x, (w x)⁻¹ ∂μ) := by
  have hpoint :
      (fun x => w x * f x ^ 2) =
      (fun x =>
        (w x * (f x - η * (w x)⁻¹) ^ 2 + 2 * η * f x) -
          η ^ 2 * (w x)⁻¹) := by
    funext x
    exact continuous_phase_square_pointwise (w x) (f x) η (hw x)
  rw [hpoint]
  change
    (∫ x, ((fun y => w y * (f y - η * (w y)⁻¹) ^ 2) +
      (fun y => 2 * η * f y) -
      (fun y => η ^ 2 * (w y)⁻¹)) x ∂μ) =
      (∫ x, w x * (f x - η * (w x)⁻¹) ^ 2 ∂μ) +
        2 * η * (∫ x, f x ∂μ) -
        η ^ 2 * (∫ x, (w x)⁻¹ ∂μ)
  rw [integral_sub (hres.add (hf.const_mul _)) (hinv.const_mul _)]
  rw [integral_add hres (hf.const_mul _)]
  rw [integral_const_mul, integral_const_mul]

/-- The continuous fixed-integral phase-energy identity. The only
variable is f; C and the weight are fixed. -/
theorem continuous_phase_exact_gap
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (w f : α → ℝ) (C : ℝ)
    (hw : ∀ x, w x ≠ 0)
    (hf : Integrable f μ)
    (hinv : Integrable (fun x => (w x)⁻¹) μ)
    (hI : (∫ x, (w x)⁻¹ ∂μ) ≠ 0)
    (hC : (∫ x, f x ∂μ) = C)
    (hres : Integrable (fun x =>
      w x * (f x -
        (C / (∫ y, (w y)⁻¹ ∂μ)) * (w x)⁻¹) ^ 2) μ) :
    (∫ x, w x * f x ^ 2 ∂μ) =
      C ^ 2 / (∫ x, (w x)⁻¹ ∂μ) +
        (∫ x, w x * (f x -
          (C / (∫ y, (w y)⁻¹ ∂μ)) * (w x)⁻¹) ^ 2 ∂μ) := by
  let I : ℝ := ∫ x, (w x)⁻¹ ∂μ
  let η : ℝ := C / I
  have hid := continuous_phase_square_integral μ w f η hw hf hinv hres
  rw [hC] at hid
  have hc : 2 * η * C - η ^ 2 * I = C ^ 2 / I := by
    dsimp [η]
    field_simp [hI]
    ring
  change (∫ x, w x * f x ^ 2 ∂μ) =
    C ^ 2 / I +
      (∫ x, w x * (f x - η * (w x)⁻¹) ^ 2 ∂μ)
  calc
    _ = (∫ x, w x * (f x - η * (w x)⁻¹) ^ 2 ∂μ) +
        2 * η * C - η ^ 2 * I := hid
    _ = C ^ 2 / I +
       (∫ x, w x * (f x - η * (w x)⁻¹) ^ 2 ∂μ) := by
        rw [show
          (∫ x, w x * (f x - η * (w x)⁻¹) ^ 2 ∂μ) +
            2 * η * C - η ^ 2 * I =
          (∫ x, w x * (f x - η * (w x)⁻¹) ^ 2 ∂μ) +
            (2 * η * C - η ^ 2 * I) from by ring]
        rw [hc]
        ring

/-- The sharp continuous bound follows immediately from the exact
nonnegative residual integral. -/
theorem continuous_phase_lower_bound
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (w f : α → ℝ) (C : ℝ)
    (hw : ∀ x, 0 < w x)
    (hf : Integrable f μ)
    (hinv : Integrable (fun x => (w x)⁻¹) μ)
    (hI : (∫ x, (w x)⁻¹ ∂μ) ≠ 0)
    (hC : (∫ x, f x ∂μ) = C)
    (hres : Integrable (fun x =>
      w x * (f x -
        (C / (∫ y, (w y)⁻¹ ∂μ)) * (w x)⁻¹) ^ 2) μ) :
    C ^ 2 / (∫ x, (w x)⁻¹ ∂μ) ≤
      (∫ x, w x * f x ^ 2 ∂μ) := by
  rw [continuous_phase_exact_gap μ w f C
    (fun x => ne_of_gt (hw x)) hf hinv hI hC hres]
  have hnonneg :
      0 ≤ (∫ x, w x * (f x -
          (C / (∫ y, (w y)⁻¹ ∂μ)) * (w x)⁻¹) ^ 2 ∂μ) :=
    integral_nonneg (fun x => mul_nonneg (le_of_lt (hw x)) (sq_nonneg _))
  linarith

end ReyesMath
