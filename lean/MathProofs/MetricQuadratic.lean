import Mathlib
import MathProofs.ScalarGradientFields

/-!
# Actual tensor contraction, not just a separately defined sum of squares

The 4×4 metric tensor arising from a differentiable complex scalar is
contracted against an arbitrary real tangent-coordinate vector. Its value
is proved equal to the sum of squared directional derivatives, and is
therefore nonnegative.
-/

namespace ReyesMath

open scoped BigOperators

/-- The Gram matrix contraction equals the square of each of the two
scalar-gradient directional derivatives, for arbitrary finite dimension. -/
theorem gradient_gram_matrix_quadratic
    {n : ℕ} (a b v : Fin n → ℝ) :
    (∑ i, ∑ j,
      ((scalarGradientCarrier a b *
        (scalarGradientCarrier a b).transpose) i j) * v i * v j) =
      scalarGradientGram a b v v := by
  have hprod (g : Fin n → ℝ) :
      (∑ i, ∑ j, g i * g j) = (∑ i, g i) ^ 2 := by
    calc
      (∑ i, ∑ j, g i * g j) =
          ∑ i, g i * (∑ j, g j) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.mul_sum]
      _ = (∑ i, g i) * (∑ j, g j) := by
            rw [Finset.sum_mul]
      _ = (∑ i, g i) ^ 2 := by ring
  simp_rw [scalarGradientCarrier_gram_entry]
  change (∑ i, ∑ j, (a i * a j + b i * b j) * v i * v j) =
    (∑ i, a i * v i) * (∑ i, a i * v i) +
      (∑ i, b i * v i) * (∑ i, b i * v i)
  calc
    (∑ i, ∑ j, (a i * a j + b i * b j) * v i * v j) =
      ∑ i, ∑ j,
        ((a i * v i) * (a j * v j) +
          (b i * v i) * (b j * v j)) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
    _ = (∑ i, ∑ j, (a i * v i) * (a j * v j)) +
        (∑ i, ∑ j, (b i * v i) * (b j * v j)) := by
          simp only [Finset.sum_add_distrib]
    _ = (∑ i, a i * v i) * (∑ i, a i * v i) +
        (∑ i, b i * v i) * (∑ i, b i * v i) := by
          rw [hprod (fun i => a i * v i), hprod (fun i => b i * v i)]
          ring

/-- The exact 4×4 complex-field metric matrix has nonnegative quadratic
evaluation in every real tangent direction. -/
theorem complex_field_matrix_psd
    (ψ : (Fin 4 → ℝ) → ℂ) (x v : Fin 4 → ℝ)
    (hψ : DifferentiableAt ℝ ψ x) :
    0 ≤ ∑ i, ∑ j, (complexFieldMetric ψ x) i j * v i * v j := by
  rw [complex_field_metric_is_gram ψ x hψ]
  rw [gradient_gram_matrix_quadratic]
  exact scalarGradientGram_psd _ _ _

/-- Therefore the actual complex-field tensor cannot have a negative
Lorentzian timelike direction in any chart coordinate system. -/
theorem complex_field_matrix_no_timelike
    (ψ : (Fin 4 → ℝ) → ℂ) (x v : Fin 4 → ℝ)
    (hψ : DifferentiableAt ℝ ψ x) :
    ¬ (∑ i, ∑ j, (complexFieldMetric ψ x) i j * v i * v j) < 0 := by
  exact not_lt.mpr (complex_field_matrix_psd ψ x v hψ)

end ReyesMath
