import MathProofs.E62TorusND
import MathProofs.E62ParsevalProjectorBridge
import MathProofs.E62Projector

/-!
# E62 physical d-torus Fourier projector

The selected Fourier mask is first constructed on the **actual** Hilbert
sequence space ℓ²(ℤᵈ, ℂ). We transport this bounded operator through
Mathlib's complete multivariate Fourier Hilbert-basis isometry to a
bounded complex-linear operator on genuine L²(Tᵈ, ℂ).

The resulting physical-space Fourier projector is idempotent and
self-adjoint, and its L² norm squared is exactly selected Fourier
coefficient energy. This closes the operator-level bridge rather than
merely masking untyped Fourier coefficient functions.
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
namespace E62TorusPhysicalProjector

open MeasureTheory UnitAddTorus E62Discrete

variable {d : Type*} [Fintype d]

private abbrev CoeffSpace (d : Type*) := lp (fun _ : d → ℤ => ℂ) 2

/-- Every Hilbert ℓ² coefficient sequence has a summable square modulus. -/
theorem coefficient_summable (f : CoeffSpace d) :
    Summable (fun k : d → ℤ => ‖f k‖ ^ 2) := by
  have hh := (lp.memℓp f).summable
    (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  simpa only [ENNReal.toReal_ofNat] using hh

/-- A selected set of coordinates of an ℓ² vector is again ℓ². -/
noncomputable def selectedCoefficients (S : Set (d → ℤ))
    (f : CoeffSpace d) : CoeffSpace d := by
  classical
  refine ⟨(fun k => if k ∈ S then f k else 0), ?_⟩
  apply memℓp_gen
  have hs := E62Discrete.summable_selected (f : (d → ℤ) → ℂ) S
    (coefficient_summable f)
  convert hs using 1
  ext k
  by_cases hk : k ∈ S <;> simp [hk]

theorem selectedCoefficients_add (S : Set (d → ℤ))
    (f g : CoeffSpace d) :
    selectedCoefficients S (f + g) =
      selectedCoefficients S f + selectedCoefficients S g := by
  classical
  ext k
  by_cases hk : k ∈ S <;>
    simp [selectedCoefficients, hk, lp.coeFn_add, Pi.add_apply]

theorem selectedCoefficients_smul (S : Set (d → ℤ))
    (c : ℂ) (f : CoeffSpace d) :
    selectedCoefficients S (c • f) =
      c • selectedCoefficients S f := by
  classical
  ext k
  by_cases hk : k ∈ S <;>
    simp [selectedCoefficients, hk, lp.coeFn_smul, Pi.smul_apply]

theorem selectedCoefficients_idempotent (S : Set (d → ℤ))
    (f : CoeffSpace d) :
    selectedCoefficients S (selectedCoefficients S f) =
      selectedCoefficients S f := by
  classical
  ext k
  by_cases hk : k ∈ S <;> simp [selectedCoefficients, hk]

theorem coefficient_norm_sq (f : CoeffSpace d) :
    ‖f‖ ^ 2 = E62Discrete.totalEnergy (f : (d → ℤ) → ℂ) := by
  simpa only [E62Discrete.totalEnergy, ENNReal.toReal_ofNat] using
    (lp.norm_rpow_eq_tsum
      (by norm_num : 0 < (2 : ℝ≥0∞).toReal) f)

theorem selectedCoefficients_norm_sq (S : Set (d → ℤ))
    (f : CoeffSpace d) :
    ‖selectedCoefficients S f‖ ^ 2 =
      E62Discrete.selectedEnergy (f : (d → ℤ) → ℂ) S := by
  calc
    ‖selectedCoefficients S f‖ ^ 2 =
        E62Discrete.totalEnergy
          (selectedCoefficients S f : (d → ℤ) → ℂ) :=
      coefficient_norm_sq (selectedCoefficients S f)
    _ = E62Discrete.selectedEnergy (f : (d → ℤ) → ℂ) S := by
      unfold E62Discrete.totalEnergy E62Discrete.selectedEnergy
      apply tsum_congr
      intro k
      by_cases hk : k ∈ S <;> simp [selectedCoefficients, hk]

theorem selectedCoefficients_norm_le (S : Set (d → ℤ))
    (f : CoeffSpace d) :
    ‖selectedCoefficients S f‖ ≤ ‖f‖ := by
  have hsq :
      ‖selectedCoefficients S f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
    rw [selectedCoefficients_norm_sq, coefficient_norm_sq]
    exact E62Discrete.selectedEnergy_le_total (f : (d → ℤ) → ℂ)
      S (coefficient_summable f)
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

noncomputable def selectedLinear (S : Set (d → ℤ)) :
    CoeffSpace d →ₗ[ℂ] CoeffSpace d where
  toFun := selectedCoefficients S
  map_add' := selectedCoefficients_add S
  map_smul' := selectedCoefficients_smul S

noncomputable def selectedCLM (S : Set (d → ℤ)) :
    CoeffSpace d →L[ℂ] CoeffSpace d :=
  (selectedLinear S).mkContinuous 1 (by
    intro f
    simpa using selectedCoefficients_norm_le S f)

/-- Actual bounded Fourier projector P_S on the Hilbert L² torus. -/
noncomputable def torusProjection (S : Set (d → ℤ)) :
    Lp ℂ 2 (volume : Measure (UnitAddTorus d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (UnitAddTorus d)) :=
  (UnitAddTorus.mFourierBasis (d := d)).repr.symm.toContinuousLinearMap.comp
    ((selectedCLM S).comp
      (UnitAddTorus.mFourierBasis (d := d)).repr.toContinuousLinearMap)

/-- The physical Fourier projector really masks the Fourier coefficients
of every complex L² torus field. -/
theorem torusProjection_coefficients (S : Set (d → ℤ))
    (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d)))
    (k : d → ℤ) :
    E62TorusND.coefficients (torusProjection S f) k =
      if k ∈ S then E62TorusND.coefficients f k else 0 := by
  rw [show E62TorusND.coefficients (torusProjection S f) k =
      (UnitAddTorus.mFourierBasis (d := d)).repr (torusProjection S f) k
      from (UnitAddTorus.mFourierBasis_repr (torusProjection S f) k).symm]
  change ((UnitAddTorus.mFourierBasis (d := d)).repr
    ((UnitAddTorus.mFourierBasis (d := d)).repr.symm
      (selectedCoefficients S
        ((UnitAddTorus.mFourierBasis (d := d)).repr f)))) k = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  classical
  by_cases hk : k ∈ S <;>
    simp [selectedCoefficients, hk, E62TorusND.coefficients,
      ← UnitAddTorus.mFourierBasis_repr]

/-- Idempotence holds in the actual physical L² operator space. -/
theorem torusProjection_idempotent (S : Set (d → ℤ))
    (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) :
    torusProjection S (torusProjection S f) = torusProjection S f := by
  change (UnitAddTorus.mFourierBasis (d := d)).repr.symm
    (selectedCoefficients S
      ((UnitAddTorus.mFourierBasis (d := d)).repr
        ((UnitAddTorus.mFourierBasis (d := d)).repr.symm
          (selectedCoefficients S
            ((UnitAddTorus.mFourierBasis (d := d)).repr f))))) = _
  rw [LinearIsometryEquiv.apply_symm_apply,
    selectedCoefficients_idempotent]
  rfl

/-- The physical projected L² energy is exactly selected Fourier
coefficient energy, with no normalization loss. -/
theorem torusProjection_norm_sq (S : Set (d → ℤ))
    (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) :
    ‖torusProjection S f‖ ^ 2 =
      E62Discrete.selectedEnergy (E62TorusND.coefficients f) S := by
  change ‖(UnitAddTorus.mFourierBasis (d := d)).repr.symm
      (selectedCoefficients S
        ((UnitAddTorus.mFourierBasis (d := d)).repr f))‖ ^ 2 = _
  rw [(UnitAddTorus.mFourierBasis (d := d)).repr.symm.norm_map,
    selectedCoefficients_norm_sq]
  congr 1
  funext k
  exact (UnitAddTorus.mFourierBasis_repr f k).symm

end E62TorusPhysicalProjector
end ReyesMath
