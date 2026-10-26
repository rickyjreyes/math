import Mathlib.Geometry.Manifold.MFDeriv.Basic
import MathProofs.ScalarGradientFields
import MathProofs.MetricQuadratic

/-!
# Pointwise rank/signature obstruction in arbitrary four-chart spaces

A complex field on a charted four-dimensional space is pulled back by its
preferred local chart. The actual derivatives of this pullback feed the
complex-gradient tensor. For every chartwise differentiability point, this
tensor has rank at most two and no timelike coordinate direction.

No independent Lorentzian background metric, global tensor bundle,
or gauge constraint is assumed or constructed.
-/

namespace ReyesMath

open ChartedSpace

/-- The complex field expressed in the preferred chart at a manifold point. -/
noncomputable def complexScalarInChart
    {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin 4 → ℝ) M]
    (ψ : M → ℂ) (p : M) : (Fin 4 → ℝ) → ℂ :=
  fun y => ψ ((chartAt (Fin 4 → ℝ) p).symm y)

/-- The coordinate tensor derived from one scalar on a four-dimensional
charted space cannot have full rank at any chartwise differentiability point. -/
theorem charted_complex_metric_rank_le_two
    {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin 4 → ℝ) M]
    (ψ : M → ℂ) (p : M)
    (hψ : DifferentiableAt ℝ (complexScalarInChart ψ p)
      (chartAt (Fin 4 → ℝ) p p)) :
    (complexFieldMetric (complexScalarInChart ψ p)
      (chartAt (Fin 4 → ℝ) p p)).rank ≤ 2 := by
  exact complex_field_metric_rank_le_two _ _ hψ

/-- Every chart tangent-coordinate quadratic evaluation is nonnegative. -/
theorem charted_complex_metric_no_timelike
    {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin 4 → ℝ) M]
    (ψ : M → ℂ) (p : M) (v : Fin 4 → ℝ)
    (hψ : DifferentiableAt ℝ (complexScalarInChart ψ p)
      (chartAt (Fin 4 → ℝ) p p)) :
    ¬ scalarGradientGram
        (realFieldGradient (complexScalarInChart ψ p) (chartAt (Fin 4 → ℝ) p p))
        (imagFieldGradient (complexScalarInChart ψ p) (chartAt (Fin 4 → ℝ) p p))
        v v < 0 := by
  exact complex_field_metric_no_timelike _ _ v hψ

/-- Simultaneously at every point on any 4-chart space on which the scalar
is differentiable in its preferred coordinate chart. -/
theorem charted_complex_metric_everywhere_obstruction
    {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin 4 → ℝ) M]
    (ψ : M → ℂ)
    (hψ : ∀ p : M, DifferentiableAt ℝ
      (complexScalarInChart ψ p) (chartAt (Fin 4 → ℝ) p p)) :
    ∀ p : M,
      (complexFieldMetric (complexScalarInChart ψ p)
          (chartAt (Fin 4 → ℝ) p p)).rank ≤ 2 ∧
      ∀ v : Fin 4 → ℝ,
        ¬ scalarGradientGram
            (realFieldGradient (complexScalarInChart ψ p)
              (chartAt (Fin 4 → ℝ) p p))
            (imagFieldGradient (complexScalarInChart ψ p)
              (chartAt (Fin 4 → ℝ) p p)) v v < 0 := by
  intro p
  exact ⟨charted_complex_metric_rank_le_two ψ p (hψ p),
    fun v => charted_complex_metric_no_timelike ψ p v (hψ p)⟩

/-- The actual chartwise tensor-matrix contraction is nonnegative
for every tangent-coordinate vector, not merely a separately defined Gram
quadratic. -/
theorem charted_complex_metric_matrix_psd
    {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin 4 → ℝ) M]
    (ψ : M → ℂ) (p : M) (v : Fin 4 → ℝ)
    (hψ : DifferentiableAt ℝ (complexScalarInChart ψ p)
      (chartAt (Fin 4 → ℝ) p p)) :
    0 ≤ ∑ i, ∑ j,
      (complexFieldMetric (complexScalarInChart ψ p)
        (chartAt (Fin 4 → ℝ) p p)) i j * v i * v j := by
  exact complex_field_matrix_psd _ _ v hψ

/-- A single complex scalar never supplies a Lorentzian four-metric via
the positive-sign derivative-product tensor on any four-coordinate charted
space: rank is at most two and there is no negative quadratic direction. -/
theorem charted_complex_metric_full_pointwise_obstruction
    {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin 4 → ℝ) M]
    (ψ : M → ℂ)
    (hψ : ∀ p : M, DifferentiableAt ℝ
      (complexScalarInChart ψ p) (chartAt (Fin 4 → ℝ) p p)) :
    ∀ p : M,
      (complexFieldMetric (complexScalarInChart ψ p)
        (chartAt (Fin 4 → ℝ) p p)).rank ≤ 2 ∧
      ∀ v : Fin 4 → ℝ, 0 ≤ ∑ i, ∑ j,
        (complexFieldMetric (complexScalarInChart ψ p)
          (chartAt (Fin 4 → ℝ) p p)) i j * v i * v j := by
  intro p
  exact ⟨charted_complex_metric_rank_le_two ψ p (hψ p),
    fun v => charted_complex_metric_matrix_psd ψ p v (hψ p)⟩


end ReyesMath
