import MathProofs.E62ProjectorL2

/-!
# E62 continuum spectral projection as an actual bounded self-adjoint operator

The map f ↦ 1_S f is a genuine continuous complex-linear operator on
L²(μ).  It is idempotent and self-adjoint, so its Plancherel conjugate
is the orthogonal Fourier projector stated in the E62 manuscript.
Every claim is on L² equivalence classes, not arbitrary representatives.
-/

namespace ReyesMath
namespace E62ProjectionOperator

open MeasureTheory E62ContinuumL2 E62ProjectorL2

variable {α : Type*} [MeasurableSpace α]

theorem maskedL2_add (μ : Measure α) (S : Set α) (hS : MeasurableSet S)
    (f g : Lp ℂ 2 μ) :
    maskedL2 μ (f + g) S hS =
      maskedL2 μ f S hS + maskedL2 μ g S hS := by
  apply Lp.ext_iff.mpr
  filter_upwards
    [maskedL2_ae μ (f + g) S hS,
     maskedL2_ae μ f S hS,
     maskedL2_ae μ g S hS,
     Lp.coeFn_add f g,
     Lp.coeFn_add (maskedL2 μ f S hS) (maskedL2 μ g S hS)]
    with x hfg hf hg hsum hmask
  rw [hfg, hmask]
  simp only [Pi.add_apply]
  rw [hf, hg]
  by_cases hx : x ∈ S <;> simp [hx, hsum]

theorem maskedL2_smul (μ : Measure α) (S : Set α) (hS : MeasurableSet S)
    (c : ℂ) (f : Lp ℂ 2 μ) :
    maskedL2 μ (c • f) S hS = c • maskedL2 μ f S hS := by
  apply Lp.ext_iff.mpr
  filter_upwards
    [maskedL2_ae μ (c • f) S hS,
     maskedL2_ae μ f S hS,
     Lp.coeFn_smul c f,
     Lp.coeFn_smul c (maskedL2 μ f S hS)]
    with x hcf hf hsmul hmask
  rw [hcf, hmask]
  simp only [Pi.smul_apply]
  rw [hf]
  by_cases hx : x ∈ S <;> simp [hx, hsmul]

/-- Complex-linear characteristic-function multiplication on true L² classes. -/
noncomputable def maskLinear (μ : Measure α) (S : Set α)
    (hS : MeasurableSet S) : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ where
  toFun := fun f => maskedL2 μ f S hS
  map_add' := maskedL2_add μ S hS
  map_smul' := maskedL2_smul μ S hS

/-- Bounded Fourier mask operator on an arbitrary measure space. -/
noncomputable def maskCLM (μ : Measure α) (S : Set α)
    (hS : MeasurableSet S) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (maskLinear μ S hS).mkContinuous 1 (by
    intro f
    simpa using maskedL2_norm_le μ f S hS)

/-- The mask operator is idempotent. -/
theorem maskCLM_idempotent (μ : Measure α) (S : Set α)
    (hS : MeasurableSet S) (f : Lp ℂ 2 μ) :
    maskCLM μ S hS (maskCLM μ S hS f) = maskCLM μ S hS f := by
  change maskedL2 μ (maskedL2 μ f S hS) S hS = maskedL2 μ f S hS
  apply Lp.ext_iff.mpr
  filter_upwards
    [maskedL2_ae μ (maskedL2 μ f S hS) S hS,
     maskedL2_ae μ f S hS] with x hh hf
  rw [hh]
  by_cases hx : x ∈ S <;> simp [hx, hf]

/-- Self-adjointness follows by integration of the pointwise mask identity. -/
theorem maskCLM_self_adjoint (μ : Measure α) (S : Set α)
    (hS : MeasurableSet S) (f g : Lp ℂ 2 μ) :
    inner ℂ (maskCLM μ S hS f) g =
      inner ℂ f (maskCLM μ S hS g) := by
  change inner ℂ (maskedL2 μ f S hS) g =
    inner ℂ f (maskedL2 μ g S hS)
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [maskedL2_ae μ f S hS,
    maskedL2_ae μ g S hS] with x hf hg
  rw [hf, hg]
  by_cases hx : x ∈ S <;> simp [hx]

end E62ProjectionOperator
end ReyesMath
