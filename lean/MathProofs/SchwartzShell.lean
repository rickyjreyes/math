import Mathlib.Analysis.Distribution.FourierSchwartz
import MathProofs.SphereNull

/-!
# Isolated Fourier shells: full transform-inversion proof for Schwartz fields

Unlike a bare null-support lemma, this theorem uses Mathlib's actual
continuous linear Fourier equivalence on Schwartz space, proves the Fourier
transform vanishes from shell support, and pulls zero back by Fourier
invertibility. It holds on Euclidean spaces of every positive finite dimension.

Extending this from Schwartz space to all L² wavefunctions requires the
Plancherel L² Fourier equivalence and is a distinct remaining obligation.
-/

namespace ReyesMath

open MeasureTheory Metric
open scoped SchwartzMap

/-- A Schwartz-class state whose *actual Fourier transform* is supported on
a single frequency sphere vanishes identically. No extra nonzero or decay
assumption is imposed beyond the definition of Schwartz space. -/
theorem schwartz_fourier_shell_no_bound_state
    (d : ℕ) (k : ℝ)
    (u : 𝓢(EuclideanSpace ℝ (Fin (d + 1)), ℂ))
    (hcarrier : ∀ ξ : EuclideanSpace ℝ (Fin (d + 1)),
        ξ ∉ sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) k →
          (SchwartzMap.fourierTransformCLE ℂ u : EuclideanSpace ℝ (Fin (d + 1)) → ℂ) ξ = 0) :
    u = 0 := by
  let v : 𝓢(EuclideanSpace ℝ (Fin (d + 1)), ℂ) :=
    SchwartzMap.fourierTransformCLE ℂ u
  have hv_ae : (v : EuclideanSpace ℝ (Fin (d + 1)) → ℂ) =ᵐ[volume]
      (fun _ => 0) := by
    exact euclidean_frequency_shell_ae_zero d k v hcarrier
  have hv_everywhere : (v : EuclideanSpace ℝ (Fin (d + 1)) → ℂ) =
      (fun _ => 0) :=
    MeasureTheory.Measure.eq_of_ae_eq hv_ae v.continuous continuous_const
  have hv_zero : v = 0 := by
    ext ξ
    exact congrFun hv_everywhere ξ
  apply (SchwartzMap.fourierTransformCLE ℂ).injective
  simpa only [map_zero] using hv_zero

end ReyesMath
