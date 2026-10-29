import MathProofs.FourierShellL2

/-!
# E62: measurable masks on the genuine continuum L² Fourier transform

These results use the actual Plancherel operator previously built in
MathProofs.FourierShellL2, rather than an assumed Fourier isometry.
They give the general measurable spectral mask contraction and the
zero-width frequency-shell exclusion.

The full ratio, orthogonal projection construction and both general
a.e. equality characterizations remain separate obligations.
-/

namespace ReyesMath
namespace E62Continuous

open MeasureTheory

/-- Indicator masking is norm-contractive on arbitrary measurable
continuous spectra, even before specializing to Fourier transforms. -/
theorem spectral_mask_eLpNorm_le
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f : α → ℂ) (S : Set α) (hS : MeasurableSet S) :
    eLpNorm (S.indicator f) 2 μ ≤ eLpNorm f 2 μ := by
  exact eLpNorm_indicator_le f hS.nullMeasurableSet

/-- The Fourier mask on an arbitrary measurable subset of R^d has
no more L² energy than the original Plancherel representative. -/
theorem actual_fourier_mask_eLpNorm_le {d : ℕ}
    (u : Sobolev.L2 d)
    (S : Set (EuclideanSpace ℝ (Fin d))) (hS : MeasurableSet S) :
    eLpNorm (S.indicator
      (Sobolev.fourierL2 u : EuclideanSpace ℝ (Fin d) → ℂ)) 2 volume ≤
    eLpNorm
      (Sobolev.fourierL2 u : EuclideanSpace ℝ (Fin d) → ℂ) 2 volume := by
  exact spectral_mask_eLpNorm_le volume _ S hS

/-- For positive spatial dimension, selecting only the exact Fourier
sphere produces the zero representative almost everywhere. -/
theorem exact_shell_mask_ae_zero
    (d : ℕ) (k : ℝ) (u : Sobolev.L2 (d + 1)) :
    (Metric.sphere
      (0 : EuclideanSpace ℝ (Fin (d + 1))) k).indicator
      (Sobolev.fourierL2 u :
        EuclideanSpace ℝ (Fin (d + 1)) → ℂ) =ᵐ[volume]
      (fun _ => (0 : ℂ)) := by
  apply zero_ae_of_null_support volume
    (Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) k)
    (euclidean_frequency_shell_measure_zero d k)
  intro ξ hξ
  exact Set.indicator_of_not_mem hξ _

end E62Continuous
end ReyesMath
