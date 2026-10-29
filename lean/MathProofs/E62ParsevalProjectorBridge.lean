import MathProofs.E62TorusND
import MathProofs.E62Projector

/-!
# E62: exact Fourier-projector/Parseval representation of the torus ratio

This bridge identifies the actual d-torus L² Fourier energy fraction
with the energy of the selected Fourier coefficient projector divided
by the physical L² integral. It is not an unproved "FFT surrogate":
the coefficients come from Mathlib's complete multivariate Fourier
Hilbert basis and the denominator is the genuine Parseval integral.
-/

noncomputable section
open MeasureTheory
attribute [local instance] Real.fact_zero_lt_one
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace ReyesMath
namespace E62ParsevalProjectorBridge

open MeasureTheory E62Discrete E62Projector UnitAddTorus

variable {d : Type*} [Fintype d]

/-- The normalized spectral-energy fraction is exactly the
orthogonal coefficient-mask energy divided by physical L² energy
for every nonzero d-dimensional torus field. -/
theorem actual_torus_fraction_eq_projected_energy_ratio
    (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d)))
    (S : Set (d → ℤ)) (hf : f ≠ 0) :
    E62Discrete.fraction (E62TorusND.coefficients f) S =
      E62Discrete.totalEnergy
        (selectModes S (E62TorusND.coefficients f)) /
        (∫ x : UnitAddTorus d, ‖(f : UnitAddTorus d → ℂ) x‖ ^ 2) := by
  change E62Discrete.selectedEnergy (E62TorusND.coefficients f) S /
        E62Discrete.totalEnergy (E62TorusND.coefficients f) = _
  rw [← masked_energy_eq_selected S (E62TorusND.coefficients f),
      E62TorusND.parseval f]

/-- The projector ratio is well-defined for every nonzero torus L² field:
its denominator is strictly positive, with no zero-field convention. -/
theorem actual_torus_projector_denominator_pos
    (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) (hf : f ≠ 0) :
    0 < (∫ x : UnitAddTorus d, ‖(f : UnitAddTorus d → ℂ) x‖ ^ 2) :=
  E62TorusND.physical_energy_pos f hf

end E62ParsevalProjectorBridge
end ReyesMath
