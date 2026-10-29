import MathProofs.E62TorusND
import MathProofs.E62ParsevalProjectorBridge

/-!
# E62: sharp 0/1 energy fractions are realized by actual torus Fourier modes

These are not abstract coefficient countermodels. The witnesses are
Mathlib's normalized Fourier monomials in the genuine multivariate
complex Hilbert L² space. Their coefficients follow from completeness
and orthonormality of Mathlib's Fourier Hilbert basis.
-/

noncomputable section
open MeasureTheory
attribute [local instance] Real.fact_zero_lt_one
local instance e62TorusSharpnessMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance e62TorusSharpnessIsAddHaar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance e62TorusSharpnessIsProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace ReyesMath
namespace E62TorusSharpness

open MeasureTheory UnitAddTorus E62TorusND E62Discrete

variable {d : Type*} [Fintype d]

/-- The actual torus Fourier monomial e^(i k·x) has exactly one
nonzero Fourier coefficient. -/
theorem pure_mode_coefficients (p q : d → ℤ) :
    E62TorusND.coefficients (UnitAddTorus.mFourierLp 2 p) q =
      if q = p then (1 : ℂ) else 0 := by
  change UnitAddTorus.mFourierCoeff (UnitAddTorus.mFourierLp 2 p) q = _
  rw [← UnitAddTorus.mFourierBasis_repr,
    HilbertBasis.repr_apply_apply, UnitAddTorus.coe_mFourierBasis]
  by_cases h : q = p
  · subst q
    rw [if_pos rfl, inner_self_eq_norm_sq_to_K,
      (UnitAddTorus.orthonormal_mFourier).1 p]
    norm_num
  · rw [if_neg h]
    exact (UnitAddTorus.orthonormal_mFourier).2 h

/-- The normalized Fourier monomial is a genuine nonzero L² field. -/
theorem pure_mode_nonzero (p : d → ℤ) :
    (UnitAddTorus.mFourierLp 2 p :
      Lp ℂ 2 (volume : Measure (UnitAddTorus d))) ≠ 0 := by
  intro hz
  have hn := (UnitAddTorus.orthonormal_mFourier).1 p
  rw [hz, norm_zero] at hn
  norm_num at hn

/-- Every selected nonempty band attains the sharp upper endpoint
η = 1 via an actual nonzero torus Fourier field. -/
theorem exists_actual_fraction_one (S : Set (d → ℤ))
    (hS : S.Nonempty) :
    ∃ f : Lp ℂ 2 (volume : Measure (UnitAddTorus d)),
      f ≠ 0 ∧ E62Discrete.fraction (E62TorusND.coefficients f) S = 1 := by
  obtain ⟨p, hp⟩ := hS
  refine ⟨UnitAddTorus.mFourierLp 2 p, pure_mode_nonzero p, ?_⟩
  rw [E62TorusND.actual_fraction_one_iff _ S (pure_mode_nonzero p)]
  intro q hq
  rw [pure_mode_coefficients, if_neg]
  exact fun he => hq (he ▸ hp)

/-- Every band with nonempty complement attains the sharp lower
endpoint η = 0 using an actual nonzero torus Fourier monomial. -/
theorem exists_actual_fraction_zero (S : Set (d → ℤ))
    (hS : Sᶜ.Nonempty) :
    ∃ f : Lp ℂ 2 (volume : Measure (UnitAddTorus d)),
      f ≠ 0 ∧ E62Discrete.fraction (E62TorusND.coefficients f) S = 0 := by
  obtain ⟨p, hp⟩ := hS
  refine ⟨UnitAddTorus.mFourierLp 2 p, pure_mode_nonzero p, ?_⟩
  rw [E62TorusND.actual_fraction_zero_iff _ S (pure_mode_nonzero p)]
  intro q hq
  rw [pure_mode_coefficients, if_neg]
  exact fun he => hp (he ▸ hq)

end E62TorusSharpness
end ReyesMath
