import MathProofs.E62ProjectorL2

/-!
# E62: arbitrary Lebesgue-measurable continuous Fourier bands

The main E62 manuscript allows *Lebesgue*-measurable spectral regions,
not merely Borel-measurable subsets of ℝᵈ. In Mathlib this is expressed
as NullMeasurableSet S volume, since the ambient measurable structure
on Euclidean space is Borel. This module proves the genuine L² bound,
both equality cases, and orthogonal Pythagoras in that stronger scope.

No assumptions of Borel measurability or finite Fourier support appear.
-/

namespace ReyesMath
namespace E62LebesgueFraction

open MeasureTheory RemainingCores

variable {α : Type*} [MeasurableSpace α]

/-- Indicator masks of arbitrary μ-Lebesgue-measurable sets define
actual L² equivalence classes, not just pointwise symbolic functions. -/
/-- An explicit membership witness avoids ambiguous elaboration of the
Lebesgue-measurable indicator during L² quotient construction. -/
private theorem maskedNull_memLp (μ : Measure α)
    (f : Lp ℂ 2 μ) (S : Set α)
    (hS : NullMeasurableSet S μ) :
    MemLp (S.indicator (f : α → ℂ)) 2 μ := by
  exact MemLp.indicator hS (Lp.memLp f)

noncomputable def maskedNull (μ : Measure α)
    (f : Lp ℂ 2 μ) (S : Set α)
    (hS : NullMeasurableSet S μ) : Lp ℂ 2 μ :=
  MemLp.toLp (S.indicator (f : α → ℂ))
    (maskedNull_memLp μ f S hS)

theorem maskedNull_ae (μ : Measure α)
    (f : Lp ℂ 2 μ) (S : Set α) (hS : NullMeasurableSet S μ) :
    (maskedNull μ f S hS : α → ℂ) =ᵐ[μ] S.indicator (f : α → ℂ) := by
  unfold maskedNull
  exact MemLp.coeFn_toLp (maskedNull_memLp μ f S hS)

theorem maskedNull_norm_le (μ : Measure α)
    (f : Lp ℂ 2 μ) (S : Set α) (hS : NullMeasurableSet S μ) :
    ‖maskedNull μ f S hS‖ ≤ ‖f‖ := by
  have hle : eLpNorm (S.indicator (f : α → ℂ)) 2 μ ≤
      eLpNorm (f : α → ℂ) 2 μ := eLpNorm_indicator_le _
  have ht : (eLpNorm (S.indicator (f : α → ℂ)) 2 μ).toReal ≤
      (eLpNorm (f : α → ℂ) 2 μ).toReal :=
    ENNReal.toReal_mono (Lp.eLpNorm_ne_top f) hle
  calc
    ‖maskedNull μ f S hS‖ =
        (eLpNorm (S.indicator (f : α → ℂ)) 2 μ).toReal := by
      unfold maskedNull
      exact Lp.norm_toLp (S.indicator (f : α → ℂ))
        (maskedNull_memLp μ f S hS)
    _ ≤ (eLpNorm (f : α → ℂ) 2 μ).toReal := ht
    _ = ‖f‖ := (Lp.norm_def f).symm

theorem maskedNull_eq_zero_iff (μ : Measure α)
    (f : Lp ℂ 2 μ) (S : Set α) (hS : NullMeasurableSet S μ) :
    maskedNull μ f S hS = 0 ↔
      ∀ᵐ x ∂μ, x ∈ S → (f : α → ℂ) x = 0 := by
  rw [Lp.eq_zero_iff_ae_eq_zero]
  constructor
  · intro h
    have he : S.indicator (f : α → ℂ) =ᵐ[μ] (0 : α → ℂ) :=
      (maskedNull_ae μ f S hS).symm.trans h
    filter_upwards [he] with x hx hm
    simpa [Set.indicator_of_mem hm] using hx
  · intro h
    have he : S.indicator (f : α → ℂ) =ᵐ[μ] (0 : α → ℂ) := by
      filter_upwards [h] with x hx
      by_cases hm : x ∈ S
      · simpa [Set.indicator_of_mem hm] using hx hm
      · simp [Set.indicator_of_notMem hm]
    exact (maskedNull_ae μ f S hS).trans he

theorem maskedNull_add_complement (μ : Measure α)
    (f : Lp ℂ 2 μ) (S : Set α) (hS : NullMeasurableSet S μ) :
    maskedNull μ f S hS + maskedNull μ f Sᶜ hS.compl = f := by
  apply Lp.ext_iff.mpr
  filter_upwards [Lp.coeFn_add (maskedNull μ f S hS)
    (maskedNull μ f Sᶜ hS.compl),
    maskedNull_ae μ f S hS, maskedNull_ae μ f Sᶜ hS.compl]
    with x hsum hs hc
  rw [hsum]
  simp only [Pi.add_apply]
  rw [hs, hc]
  by_cases hx : x ∈ S <;> simp [hx]

theorem maskedNull_orthogonal (μ : Measure α)
    (f : Lp ℂ 2 μ) (S : Set α) (hS : NullMeasurableSet S μ) :
    inner ℂ (maskedNull μ f S hS) (maskedNull μ f Sᶜ hS.compl) = 0 := by
  rw [L2.inner_def]
  apply integral_eq_zero_of_ae
  filter_upwards [maskedNull_ae μ f S hS,
    maskedNull_ae μ f Sᶜ hS.compl] with x hs hc
  rw [hs, hc]
  by_cases hx : x ∈ S <;> simp [hx]

theorem maskedNull_pythagoras (μ : Measure α)
    (f : Lp ℂ 2 μ) (S : Set α) (hS : NullMeasurableSet S μ) :
    ‖f‖ ^ 2 =
      ‖maskedNull μ f S hS‖ ^ 2 +
      ‖maskedNull μ f Sᶜ hS.compl‖ ^ 2 := by
  have h := norm_add_sq (𝕜 := ℂ)
    (maskedNull μ f S hS) (maskedNull μ f Sᶜ hS.compl)
  rw [maskedNull_orthogonal μ f S hS] at h
  simpa [maskedNull_add_complement μ f S hS] using h

/-- The Fourier mask norm does not exceed the actual physical L² norm,
for any Lebesgue-measurable set, including non-Borel representatives. -/
theorem actual_fourier_mask_norm_le {d : ℕ} (u : Sobolev.L2 d)
    (S : Set (EuclideanSpace ℝ (Fin d)))
    (hS : NullMeasurableSet S volume) :
    ‖maskedNull volume (Sobolev.fourierL2 u) S hS‖ ≤ ‖u‖ := by
  calc
    ‖maskedNull volume (Sobolev.fourierL2 u) S hS‖ ≤
      ‖Sobolev.fourierL2 u‖ :=
      maskedNull_norm_le volume (Sobolev.fourierL2 u) S hS
    _ = ‖u‖ := (Sobolev.fourierL2).norm_map u

/-- The exact E62 fraction for an arbitrary Lebesgue-measurable
spectral band S on whole-space Fourier L²(ℝᵈ). -/
noncomputable def fraction {d : ℕ} (u : Sobolev.L2 d)
    (S : Set (EuclideanSpace ℝ (Fin d)))
    (hS : NullMeasurableSet S volume) : ℝ :=
  energyFraction
    (‖maskedNull volume (Sobolev.fourierL2 u) S hS‖ ^ 2)
    (‖u‖ ^ 2)

theorem fraction_bounds {d : ℕ} (u : Sobolev.L2 d)
    (S : Set (EuclideanSpace ℝ (Fin d)))
    (hS : NullMeasurableSet S volume) (hu : u ≠ 0) :
    0 ≤ fraction u S hS ∧ fraction u S hS ≤ 1 := by
  apply energyFraction_bounds
  · exact sq_nonneg _
  · nlinarith [actual_fourier_mask_norm_le u S hS,
      norm_nonneg u,
      norm_nonneg (maskedNull volume (Sobolev.fourierL2 u) S hS)]
  · exact sq_pos_of_pos (norm_pos_iff.mpr hu)

theorem fraction_zero_iff {d : ℕ} (u : Sobolev.L2 d)
    (S : Set (EuclideanSpace ℝ (Fin d)))
    (hS : NullMeasurableSet S volume) (hu : u ≠ 0) :
    fraction u S hS = 0 ↔
      ∀ᵐ ξ ∂volume, ξ ∈ S →
        (Sobolev.fourierL2 u : EuclideanSpace ℝ (Fin d) → ℂ) ξ = 0 := by
  unfold fraction
  rw [energyFraction_zero_iff _ _ (sq_pos_of_pos (norm_pos_iff.mpr hu))]
  rw [sq_eq_zero_iff, norm_eq_zero]
  exact maskedNull_eq_zero_iff volume _ S hS

theorem fraction_one_iff {d : ℕ} (u : Sobolev.L2 d)
    (S : Set (EuclideanSpace ℝ (Fin d)))
    (hS : NullMeasurableSet S volume) (hu : u ≠ 0) :
    fraction u S hS = 1 ↔
      ∀ᵐ ξ ∂volume, ξ ∉ S →
        (Sobolev.fourierL2 u : EuclideanSpace ℝ (Fin d) → ℂ) ξ = 0 := by
  unfold fraction
  rw [energyFraction_one_iff _ _ (sq_pos_of_pos (norm_pos_iff.mpr hu))]
  have hp := maskedNull_pythagoras volume (Sobolev.fourierL2 u) S hS
  rw [(Sobolev.fourierL2).norm_map] at hp
  have hc := maskedNull_eq_zero_iff volume (Sobolev.fourierL2 u) Sᶜ hS.compl
  constructor
  · intro h
    have hsq : ‖maskedNull volume (Sobolev.fourierL2 u) Sᶜ hS.compl‖ ^ 2 = 0 := by
      linarith
    have hz : maskedNull volume (Sobolev.fourierL2 u) Sᶜ hS.compl = 0 :=
      norm_eq_zero.mp (pow_eq_zero hsq)
    exact hc.mp hz
  · intro h
    have hz : maskedNull volume (Sobolev.fourierL2 u) Sᶜ hS.compl = 0 :=
      hc.mpr h
    rw [hz] at hp
    simpa using hp.symm

end E62LebesgueFraction
end ReyesMath
