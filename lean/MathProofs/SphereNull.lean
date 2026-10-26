import Mathlib
import MathProofs.FourierSupport

/-!
# Arbitrary-dimensional Fourier-shell exclusion: measure-theoretic core

Using the Haar-measure null-sphere theorem from Mathlib, this proves that
any complex Fourier representative supported on a single Euclidean frequency
sphere is zero almost everywhere, in every positive finite dimension.
The separate L² Plancherel/inverse-Fourier identification of the *original*
physical field is not yet established in the pinned Mathlib v4.23 project.
-/

namespace ReyesMath

open MeasureTheory

/-- Every positive-dimensional Euclidean Fourier shell has Lebesgue measure
zero, including radius zero. -/
theorem euclidean_frequency_shell_measure_zero
    (d : ℕ) (k : ℝ) :
    (volume : Measure (EuclideanSpace ℝ (Fin (d + 1))))
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) k) = 0 := by
  exact Measure.addHaar_sphere (volume : Measure
    (EuclideanSpace ℝ (Fin (d + 1)))) 0 k

/-- A complex Fourier representative with pointwise support on one shell
vanishes almost everywhere in arbitrary positive dimension. -/
theorem euclidean_frequency_shell_ae_zero
    (d : ℕ) (k : ℝ)
    (f : EuclideanSpace ℝ (Fin (d + 1)) → ℂ)
    (hf : ∀ ξ, ξ ∉ Metric.sphere
      (0 : EuclideanSpace ℝ (Fin (d + 1))) k → f ξ = 0) :
    f =ᵐ[volume] (fun _ => 0) := by
  exact zero_ae_of_null_support volume
    (Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) k)
    (euclidean_frequency_shell_measure_zero d k) f hf

end ReyesMath
