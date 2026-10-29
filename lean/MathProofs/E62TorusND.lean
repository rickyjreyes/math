import Mathlib.Analysis.Fourier.AddCircleMulti
import MathProofs.E62Discrete

/-!
# E62: genuine arbitrary finite-dimensional torus Fourier energy fraction

This module closes the missing passage from *abstract* coefficient
families to the actual Fourier series of every L² function on the
unit d-torus. We use Mathlib's proved complete multivariable Hilbert
basis and Parseval theorems, not an assumed Fourier equivalence.

The independent physical-space orthogonal projector, full whole-space
continuous-spectrum equality cases, and time evolution are separate.
-/

namespace ReyesMath
namespace E62TorusND

open MeasureTheory E62Discrete UnitAddTorus

variable {d : Type*} [Fintype d]

/-- The actual multivariate Fourier coefficients of an L²-class on T^d. -/
noncomputable def coefficients
    (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) (n : d → ℤ) : ℂ :=
  UnitAddTorus.mFourierCoeff f n

/-- The infinite Fourier-mode energy is summable in every finite dimension. -/
theorem coefficients_summable
    (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) :
    Summable (fun n : d → ℤ => ‖coefficients f n‖ ^ 2) := by
  simpa only [coefficients] using
    (UnitAddTorus.hasSum_sq_mFourierCoeff f).summable

/-- Exact Parseval identity for the actual multivariate Fourier coefficients. -/
theorem parseval
    (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) :
    totalEnergy (coefficients f) =
      ∫ x : UnitAddTorus d, ‖(f : UnitAddTorus d → ℂ) x‖ ^ 2 := by
  simpa only [totalEnergy, coefficients] using
    (UnitAddTorus.hasSum_sq_mFourierCoeff f).tsum_eq

/-- Fourier completeness: every nonzero L² class has a nonzero coefficient. -/
theorem coefficients_nontrivial_of_nonzero
    (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) (hf : f ≠ 0) :
    ∃ n : d → ℤ, coefficients f n ≠ 0 := by
  classical
  by_contra h
  push_neg at h
  have hz : ∀ n : d → ℤ, UnitAddTorus.mFourierCoeff f n = 0 := by
    intro n
    exact h n
  have hterm :
      (fun n : d → ℤ =>
        UnitAddTorus.mFourierCoeff f n • UnitAddTorus.mFourierLp 2 n) =
      (fun _ => (0 : Lp ℂ 2 (volume : Measure (UnitAddTorus d)))) := by
    funext n
    simp [hz n]
  have hs := UnitAddTorus.hasSum_mFourier_series_L2 f
  rw [hterm] at hs
  exact hf (hs.unique hasSum_zero)

/-- Physical L² energy splits into selected and complementary regions. -/
theorem physical_energy_split
    (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d)))
    (S : Set (d → ℤ)) :
    (∫ x : UnitAddTorus d, ‖(f : UnitAddTorus d → ℂ) x‖ ^ 2) =
      selectedEnergy (coefficients f) S +
        selectedEnergy (coefficients f) Sᶜ := by
  calc
    _ = totalEnergy (coefficients f) := (parseval f).symm
    _ = selectedEnergy (coefficients f) S +
          selectedEnergy (coefficients f) Sᶜ :=
      totalEnergy_split (coefficients f) S (coefficients_summable f)

/-- The denominator is positive for every nonzero physical L² field. -/
theorem physical_energy_pos
    (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d)))
    (hf : f ≠ 0) :
    0 < (∫ x : UnitAddTorus d, ‖(f : UnitAddTorus d → ℂ) x‖ ^ 2) := by
  rw [← parseval f]
  exact totalEnergy_pos (coefficients f) (coefficients_summable f)
    (coefficients_nontrivial_of_nonzero f hf)

/-- The manuscript's 0 ≤ η ≤ 1 conclusion for all nonzero L² fields on T^d. -/
theorem actual_fraction_bounds
    (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d)))
    (S : Set (d → ℤ)) (hf : f ≠ 0) :
    0 ≤ fraction (coefficients f) S ∧
      fraction (coefficients f) S ≤ 1 :=
  fraction_bounds (coefficients f) S (coefficients_summable f)
    (coefficients_nontrivial_of_nonzero f hf)

/-- Zero fraction iff all selected actual Fourier coefficients vanish. -/
theorem actual_fraction_zero_iff
    (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d)))
    (S : Set (d → ℤ)) (hf : f ≠ 0) :
    fraction (coefficients f) S = 0 ↔
      ∀ n ∈ S, coefficients f n = 0 :=
  fraction_zero_iff (coefficients f) S (coefficients_summable f)
    (coefficients_nontrivial_of_nonzero f hf)

/-- Full fraction iff all unselected actual Fourier coefficients vanish. -/
theorem actual_fraction_one_iff
    (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d)))
    (S : Set (d → ℤ)) (hf : f ≠ 0) :
    fraction (coefficients f) S = 1 ↔
      ∀ n ∉ S, coefficients f n = 0 :=
  fraction_one_iff (coefficients f) S (coefficients_summable f)
    (coefficients_nontrivial_of_nonzero f hf)

end E62TorusND
end ReyesMath
