import Mathlib.Analysis.Fourier.AddCircle
import MathProofs.E62Discrete

/-!
# E62: actual one-dimensional torus Fourier/Parseval bridge

Uses Mathlib's existing Fourier Hilbert basis for L² on the additive circle.
Unlike the abstract mode-family model, the coefficients here are the actual
Fourier coefficients of an L² equivalence class. Parseval identifies their
full squared-modulus tsum with the physical L² energy.

This is the genuine 1D torus case. Extension to products of circles
and a physical-space orthogonal spectral projector is still open.
-/

namespace ReyesMath
namespace E62Torus1D

open MeasureTheory AddCircle
open E62Discrete

variable {T : ℝ} [Fact (0 < T)]

/-- Actual Fourier coefficients of an L² field on the period-T circle,
with probability-normalized Haar measure. -/
noncomputable def coefficients
    (f : Lp ℂ 2 (AddCircle.haarAddCircle (T := T))) (n : ℤ) : ℂ :=
  fourierCoeff (f : AddCircle T → ℂ) n

/-- Mathlib's Fourier Hilbert basis gives square-summability of the
actual coefficients, not just a stipulated summable sequence. -/
theorem coefficients_summable
    (f : Lp ℂ 2 (AddCircle.haarAddCircle (T := T))) :
    Summable (fun n : ℤ => ‖coefficients f n‖ ^ 2) := by
  exact (hasSum_sq_fourierCoeff f).summable

/-- Parseval: the infinite coefficient energy of a genuine L² field
equals its physical L² integral in the normalized torus convention. -/
theorem totalEnergy_eq_L2_integral
    (f : Lp ℂ 2 (AddCircle.haarAddCircle (T := T))) :
    totalEnergy (coefficients f) =
      ∫ x : AddCircle T, ‖(f : AddCircle T → ℂ) x‖ ^ 2 ∂
        (AddCircle.haarAddCircle (T := T)) := by
  simpa only [totalEnergy, coefficients] using
    (tsum_sq_fourierCoeff f)

/-- Bounds for a genuinely Fourier-defined nonzero mode family on T¹.
The explicit nonzero-mode premise avoids an unproved coefficient
injectivity equivalence in this supporting statement. -/
theorem actual_fourier_fraction_bounds
    (f : Lp ℂ 2 (AddCircle.haarAddCircle (T := T)))
    (S : Set ℤ) (hne : ∃ n, coefficients f n ≠ 0) :
    0 ≤ fraction (coefficients f) S ∧ fraction (coefficients f) S ≤ 1 :=
  fraction_bounds (coefficients f) S (coefficients_summable f) hne

/-- The zero-fraction characterization is about the actual
torus Fourier coefficients, not an abstract surrogate sequence. -/
theorem actual_fourier_fraction_zero_iff
    (f : Lp ℂ 2 (AddCircle.haarAddCircle (T := T)))
    (S : Set ℤ) (hne : ∃ n, coefficients f n ≠ 0) :
    fraction (coefficients f) S = 0 ↔
      ∀ n ∈ S, coefficients f n = 0 :=
  fraction_zero_iff (coefficients f) S (coefficients_summable f) hne

/-- Similarly the fraction is one exactly for Fourier support
inside the chosen band. -/
theorem actual_fourier_fraction_one_iff
    (f : Lp ℂ 2 (AddCircle.haarAddCircle (T := T)))
    (S : Set ℤ) (hne : ∃ n, coefficients f n ≠ 0) :
    fraction (coefficients f) S = 1 ↔
      ∀ n ∉ S, coefficients f n = 0 :=
  fraction_one_iff (coefficients f) S (coefficients_summable f) hne

end E62Torus1D
end ReyesMath
