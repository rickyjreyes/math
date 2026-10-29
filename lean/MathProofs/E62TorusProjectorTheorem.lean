import MathProofs.E62TorusPhysicalProjector

/-!
# E62 final torus orthogonal Fourier projection theorem

The physical projector is a genuine bounded complex-linear operator
on L²(Tᵈ), transported from the Hilbert ℓ² coefficient mask by
Mathlib's complete multivariate Fourier basis. It is self-adjoint,
idempotent, and complementary; Parseval yields the exact normalized
energy ratio and physical-space Pythagorean decomposition.

No finite Fourier cutoffs or assumed Fourier isometries are used.
-/

noncomputable section
open MeasureTheory
attribute [local instance] Real.fact_zero_lt_one
local instance e62TorusProjectorTheoremMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance e62TorusProjectorTheoremIsAddHaar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance e62TorusProjectorTheoremIsProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace ReyesMath
namespace E62TorusProjectorTheorem

open MeasureTheory UnitAddTorus E62TorusPhysicalProjector E62Discrete
attribute [local instance] Classical.propDecidable

variable {d : Type*} [Fintype d]

private abbrev CoeffSpace (d : Type*) := lp (fun _ : d → ℤ => ℂ) 2
private abbrev TorusL2 (d : Type*) [Fintype d] :=
  Lp ℂ 2 (volume : Measure (UnitAddTorus d))

/-- The characteristic-function mask is self-adjoint on Hilbert ℓ²,
for arbitrary (including infinite) selected index sets. -/
theorem selectedCoefficients_inner (S : Set (d → ℤ))
    (f g : CoeffSpace d) :
    inner ℂ (selectedCoefficients S f) g =
      inner ℂ f (selectedCoefficients S g) := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro k
  by_cases hk : k ∈ S <;> simp [selectedCoefficients, hk]

/-- The genuine physical torus Fourier projector is self-adjoint. -/
theorem torusProjection_self_adjoint (S : Set (d → ℤ))
    (f g : TorusL2 d) :
    inner ℂ (torusProjection S f) g =
      inner ℂ f (torusProjection S g) := by
  let e := (UnitAddTorus.mFourierBasis (d := d)).repr
  have hf : e (torusProjection S f) = selectedCoefficients S (e f) := by
    change e (e.symm (selectedCoefficients S (e f))) = _
    exact e.apply_symm_apply _
  have hg : e (torusProjection S g) = selectedCoefficients S (e g) := by
    change e (e.symm (selectedCoefficients S (e g))) = _
    exact e.apply_symm_apply _
  calc
    inner ℂ (torusProjection S f) g =
        inner ℂ (e (torusProjection S f)) (e g) :=
      (e.inner_map_map _ _).symm
    _ = inner ℂ (selectedCoefficients S (e f)) (e g) := by rw [hf]
    _ = inner ℂ (e f) (selectedCoefficients S (e g)) :=
      selectedCoefficients_inner S (e f) (e g)
    _ = inner ℂ (e f) (e (torusProjection S g)) := by rw [hg]
    _ = inner ℂ f (torusProjection S g) := e.inner_map_map _ _

/-- The selected and rejected ℓ² coefficient masks reconstruct the
original vector exactly. -/
theorem selectedCoefficients_add_complement (S : Set (d → ℤ))
    (f : CoeffSpace d) :
    selectedCoefficients S f + selectedCoefficients Sᶜ f = f := by
  apply Subtype.ext
  funext k
  rw [lp.coeFn_add, Pi.add_apply]
  by_cases hk : k ∈ S <;> simp [selectedCoefficients, hk]

/-- The selected physical Fourier projector and its complementary
projector add to the identity on the complete Hilbert L² torus. -/
theorem torusProjection_add_complement (S : Set (d → ℤ))
    (f : TorusL2 d) :
    torusProjection S f + torusProjection Sᶜ f = f := by
  let e := (UnitAddTorus.mFourierBasis (d := d)).repr
  change e.symm (selectedCoefficients S (e f)) +
    e.symm (selectedCoefficients Sᶜ (e f)) = f
  calc
    e.symm (selectedCoefficients S (e f)) +
        e.symm (selectedCoefficients Sᶜ (e f)) =
      e.symm (selectedCoefficients S (e f) +
        selectedCoefficients Sᶜ (e f)) :=
      (e.symm.map_add _ _).symm
    _ = e.symm (e f) := by rw [selectedCoefficients_add_complement]
    _ = f := e.symm_apply_apply f

/-- Actual total Fourier coefficient energy equals the physical
Hilbert-space norm squared by the complete multivariate basis. -/
theorem physical_totalEnergy_eq_norm_sq (f : TorusL2 d) :
    E62Discrete.totalEnergy (E62TorusND.coefficients f) = ‖f‖ ^ 2 := by
  let e := (UnitAddTorus.mFourierBasis (d := d)).repr
  have hc : E62TorusND.coefficients f =
      (e f : (d → ℤ) → ℂ) := by
    funext k
    exact (UnitAddTorus.mFourierBasis_repr f k).symm
  rw [hc]
  have hn := coefficient_norm_sq (e f)
  simpa only [e, (UnitAddTorus.mFourierBasis (d := d)).repr.norm_map] using hn.symm

/-- Exact physical-space Pythagoras for the two complementary
orthogonal torus spectral projections. -/
theorem torusProjection_pythagoras (S : Set (d → ℤ))
    (f : TorusL2 d) :
    ‖f‖ ^ 2 = ‖torusProjection S f‖ ^ 2 +
      ‖torusProjection Sᶜ f‖ ^ 2 := by
  calc
    ‖f‖ ^ 2 = E62Discrete.totalEnergy (E62TorusND.coefficients f) :=
      (physical_totalEnergy_eq_norm_sq f).symm
    _ = E62Discrete.selectedEnergy (E62TorusND.coefficients f) S +
          E62Discrete.selectedEnergy (E62TorusND.coefficients f) Sᶜ :=
      E62Discrete.totalEnergy_split _ S (E62TorusND.coefficients_summable f)
    _ = ‖torusProjection S f‖ ^ 2 +
          ‖torusProjection Sᶜ f‖ ^ 2 := by
      rw [torusProjection_norm_sq, torusProjection_norm_sq]

/-- The spectral concentration fraction in the E62 manuscript
is exactly the orthogonal Fourier projector's physical L² energy
ratio for every nonzero physical field. -/
theorem torus_fraction_eq_projector_norm_ratio (S : Set (d → ℤ))
    (f : TorusL2 d) (hf : f ≠ 0) :
    E62Discrete.fraction (E62TorusND.coefficients f) S =
      ‖torusProjection S f‖ ^ 2 / ‖f‖ ^ 2 := by
  change E62Discrete.selectedEnergy (E62TorusND.coefficients f) S /
      E62Discrete.totalEnergy (E62TorusND.coefficients f) = _
  rw [torusProjection_norm_sq, physical_totalEnergy_eq_norm_sq]

end E62TorusProjectorTheorem
end ReyesMath
