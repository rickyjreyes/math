import MathProofs.E62ContinuumL2

/-!
# E62: actual continuum L² orthogonal spectral decomposition

Unlike a coordinate-only finite surrogate, this proof uses masked
representatives of genuine L² equivalence classes on arbitrary
measure spaces, and the complex Hilbert L² inner product.
The selected mask and its complement add to the original field and
are orthogonal. Pythagoras yields exact energy splitting and the
η=1 almost-everywhere Fourier-support characterization.
-/

namespace ReyesMath
namespace E62ProjectorL2

open MeasureTheory E62ContinuumL2 RemainingCores

variable {α : Type*} [MeasurableSpace α]

/-- Every L² field decomposes exactly into the selected and complementary
measurable spectral masks, as an equality of L² equivalence classes. -/
theorem mask_add_complement (μ : Measure α) (f : Lp ℂ 2 μ)
    (S : Set α) (hS : MeasurableSet S) :
    maskedL2 μ f S hS + maskedL2 μ f Sᶜ hS.compl = f := by
  apply Lp.ext_iff.mpr
  filter_upwards [Lp.coeFn_add (maskedL2 μ f S hS)
    (maskedL2 μ f Sᶜ hS.compl),
    maskedL2_ae μ f S hS, maskedL2_ae μ f Sᶜ hS.compl] with x hsum hs hc
  rw [hsum, hs, hc]
  by_cases hx : x ∈ S <;> simp [hx]

/-- The two Fourier masks are orthogonal in the *actual* L² Hilbert space. -/
theorem mask_orthogonal_complement (μ : Measure α) (f : Lp ℂ 2 μ)
    (S : Set α) (hS : MeasurableSet S) :
    inner ℂ (maskedL2 μ f S hS) (maskedL2 μ f Sᶜ hS.compl) = 0 := by
  rw [L2.inner_def]
  apply integral_eq_zero_of_ae
  filter_upwards [maskedL2_ae μ f S hS,
    maskedL2_ae μ f Sᶜ hS.compl] with x hs hc
  rw [hs, hc]
  by_cases hx : x ∈ S <;> simp [hx]

/-- Exact Pythagoras for the true continuous-spectrum L² energy split. -/
theorem norm_sq_eq_selected_add_complement (μ : Measure α) (f : Lp ℂ 2 μ)
    (S : Set α) (hS : MeasurableSet S) :
    ‖f‖ ^ 2 =
      ‖maskedL2 μ f S hS‖ ^ 2 +
        ‖maskedL2 μ f Sᶜ hS.compl‖ ^ 2 := by
  have h := norm_add_sq
    (maskedL2 μ f S hS) (maskedL2 μ f Sᶜ hS.compl)
  rw [mask_orthogonal_complement μ f S hS] at h
  simpa [mask_add_complement μ f S hS] using h

/-- Actual physical-space Plancherel Pythagoras in arbitrary dimension:
the Fourier energy of u splits exactly into the two measurable bands. -/
theorem actual_fourier_pythagoras {d : ℕ}
    (u : Sobolev.L2 d)
    (S : Set (EuclideanSpace ℝ (Fin d))) (hS : MeasurableSet S) :
    ‖u‖ ^ 2 =
      ‖maskedL2 volume (Sobolev.fourierL2 u) S hS‖ ^ 2 +
        ‖maskedL2 volume (Sobolev.fourierL2 u) Sᶜ hS.compl‖ ^ 2 := by
  have h := norm_sq_eq_selected_add_complement
    volume (Sobolev.fourierL2 u) S hS
  rw [(Sobolev.fourierL2).norm_map] at h
  exact h

/-- E62 continuum η=1 iff the actual Fourier transform has no mass
outside the selected measurable band. -/
theorem actual_fourier_fraction_one_iff {d : ℕ}
    (u : Sobolev.L2 d)
    (S : Set (EuclideanSpace ℝ (Fin d))) (hS : MeasurableSet S)
    (hu : u ≠ 0) :
    E62ContinuumL2.fraction u S hS = 1 ↔
      ∀ᵐ ξ ∂volume, ξ ∉ S →
        (Sobolev.fourierL2 u : EuclideanSpace ℝ (Fin d) → ℂ) ξ = 0 := by
  unfold E62ContinuumL2.fraction
  rw [energyFraction_one_iff _ _ (sq_pos_of_pos (norm_pos_iff.mpr hu))]
  have hp := actual_fourier_pythagoras u S hS
  have hc := maskedL2_eq_zero_iff volume
    (Sobolev.fourierL2 u) Sᶜ hS.compl
  constructor
  · intro h
    have hsq : ‖maskedL2 volume
        (Sobolev.fourierL2 u) Sᶜ hS.compl‖ ^ 2 = 0 := by
      linarith
    have hz : maskedL2 volume (Sobolev.fourierL2 u) Sᶜ hS.compl = 0 :=
      norm_eq_zero.mp (pow_eq_zero hsq)
    exact hc.mp hz
  · intro h
    have hz : maskedL2 volume (Sobolev.fourierL2 u) Sᶜ hS.compl = 0 :=
      hc.mpr h
    rw [hz] at hp
    simp only [norm_zero, zero_pow (by norm_num), add_zero] at hp
    exact hp.symm

end E62ProjectorL2
end ReyesMath
