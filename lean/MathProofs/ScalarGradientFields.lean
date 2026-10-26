import Mathlib
import MathProofs.ComplexMetric
import MathProofs.Structural

/-!
# Metric obstruction for an actual differentiable complex scalar field

This is the coordinate-chart (four real coordinates) formulation of the
pointwise rank/signature obstruction. The real and imaginary gradient entries
are extracted from the Fréchet derivatives of a single complex scalar field,
rather than provided as arbitrary unrelated vectors.

Any smooth four-manifold has four-coordinate charts; translating this chart
statement into the full bundled-manifold formulation is still a separate
formalization obligation.
-/

namespace ReyesMath

/-- The coordinate covector of the real component of a complex field. -/
noncomputable def realFieldGradient
    (ψ : (Fin 4 → ℝ) → ℂ) (x : Fin 4 → ℝ) : Fin 4 → ℝ :=
  fun i => fderiv ℝ (fun y => (ψ y).re) x (Pi.single i (1 : ℝ))

/-- The coordinate covector of its imaginary component. -/
noncomputable def imagFieldGradient
    (ψ : (Fin 4 → ℝ) → ℂ) (x : Fin 4 → ℝ) : Fin 4 → ℝ :=
  fun i => fderiv ℝ (fun y => (ψ y).im) x (Pi.single i (1 : ℝ))

/-- The actual real 4×4 tensor formed from the complex gradient product. -/
noncomputable def complexFieldMetric
    (ψ : (Fin 4 → ℝ) → ℂ) (x : Fin 4 → ℝ) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j =>
    (star (Complex.mk (realFieldGradient ψ x i) (imagFieldGradient ψ x i)) *
      Complex.mk (realFieldGradient ψ x j) (imagFieldGradient ψ x j)).re

/-- An honest scalar field produces the two-column positive-sign Gram tensor,
entry by entry, not merely an abstract two-gradient form. -/
theorem complex_field_metric_is_gram
    (ψ : (Fin 4 → ℝ) → ℂ) (x : Fin 4 → ℝ)
    (_hψ : DifferentiableAt ℝ ψ x) :
    complexFieldMetric ψ x =
      scalarGradientCarrier (realFieldGradient ψ x) (imagFieldGradient ψ x) *
        (scalarGradientCarrier (realFieldGradient ψ x)
          (imagFieldGradient ψ x)).transpose := by
  ext i j
  change (star (Complex.mk (realFieldGradient ψ x i) (imagFieldGradient ψ x i)) *
    Complex.mk (realFieldGradient ψ x j) (imagFieldGradient ψ x j)).re =
      (scalarGradientCarrier (realFieldGradient ψ x)
        (imagFieldGradient ψ x) *
          (scalarGradientCarrier (realFieldGradient ψ x)
            (imagFieldGradient ψ x)).transpose) i j
  rw [scalarGradientCarrier_gram_entry]
  exact complex_gradient_real_identity
    (realFieldGradient ψ x i) (imagFieldGradient ψ x i)
    (realFieldGradient ψ x j) (imagFieldGradient ψ x j)

/-- The complex scalar field, evaluated at any differentiability point,
cannot produce a rank-four Lorentzian tensor by this construction. -/
theorem complex_field_metric_rank_le_two
    (ψ : (Fin 4 → ℝ) → ℂ) (x : Fin 4 → ℝ)
    (hψ : DifferentiableAt ℝ ψ x) :
    (complexFieldMetric ψ x).rank ≤ 2 := by
  rw [complex_field_metric_is_gram ψ x hψ]
  exact scalarGradientCarrier_rank_le_two
    (realFieldGradient ψ x) (imagFieldGradient ψ x)

/-- For each tangent coordinate direction, the quadratic form is nonnegative. -/
theorem complex_field_metric_quadratic_nonnegative
    (ψ : (Fin 4 → ℝ) → ℂ) (x v : Fin 4 → ℝ)
    (_hψ : DifferentiableAt ℝ ψ x) :
    0 ≤ scalarGradientGram (realFieldGradient ψ x)
      (imagFieldGradient ψ x) v v := by
  exact scalarGradientGram_psd _ _ _

/-- In particular this tensor has no negative timelike directions. -/
theorem complex_field_metric_no_timelike
    (ψ : (Fin 4 → ℝ) → ℂ) (x v : Fin 4 → ℝ)
    (hψ : DifferentiableAt ℝ ψ x) :
    ¬ scalarGradientGram (realFieldGradient ψ x)
      (imagFieldGradient ψ x) v v < 0 :=
  not_lt.mpr (complex_field_metric_quadratic_nonnegative ψ x v hψ)

end ReyesMath
