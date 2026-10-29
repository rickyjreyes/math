import MathProofs.E62Continuous
import MathProofs.RemainingCores

/-!
# E62: continuum L² spectral projection by measurable Fourier mask

We construct a genuine L²-class from the masked representative, prove
its contraction, and characterize its zero set by almost-everywhere
vanishing on the selected region. This is not merely the inequality
for abstract arrays or a finite FFT.

The operator-valued orthogonal-projector and full Pythagorean equality
characterization are left separate from these first analytic bridges.
-/

namespace ReyesMath
namespace E62ContinuumL2

open MeasureTheory RemainingCores

variable {α : Type*} [MeasurableSpace α]

/-- Selected Fourier data as a genuine L² equivalence class. -/
noncomputable def maskedL2 (μ : Measure α)
    (f : Lp ℂ 2 μ) (S : Set α) (hS : MeasurableSet S) : Lp ℂ 2 μ :=
  (MemLp.indicator hS (Lp.memLp f)).toLp (S.indicator (f : α → ℂ))

/-- The masked L² class has exactly the expected almost-everywhere representative. -/
theorem maskedL2_ae (μ : Measure α)
    (f : Lp ℂ 2 μ) (S : Set α) (hS : MeasurableSet S) :
    (maskedL2 μ f S hS : α → ℂ) =ᵐ[μ] S.indicator (f : α → ℂ) := by
  exact MemLp.coeFn_toLp _

/-- The multiplier by a measurable characteristic function is L² contractive. -/
theorem maskedL2_norm_le (μ : Measure α)
    (f : Lp ℂ 2 μ) (S : Set α) (hS : MeasurableSet S) :
    ‖maskedL2 μ f S hS‖ ≤ ‖f‖ := by
  have hle : eLpNorm (S.indicator (f : α → ℂ)) 2 μ ≤
      eLpNorm (f : α → ℂ) 2 μ :=
    eLpNorm_indicator_le _
  have ht : (eLpNorm (S.indicator (f : α → ℂ)) 2 μ).toReal ≤
      (eLpNorm (f : α → ℂ) 2 μ).toReal :=
    ENNReal.toReal_mono (Lp.eLpNorm_ne_top f) hle
  simpa only [maskedL2, norm_toLp, Lp.norm_def] using ht

/-- A masked L² class vanishes precisely when the original
representative vanishes almost everywhere inside the selected band. -/
theorem maskedL2_eq_zero_iff (μ : Measure α)
    (f : Lp ℂ 2 μ) (S : Set α) (hS : MeasurableSet S) :
    maskedL2 μ f S hS = 0 ↔
      ∀ᵐ x ∂μ, x ∈ S → (f : α → ℂ) x = 0 := by
  rw [Lp.eq_zero_iff_ae_eq_zero]
  constructor
  · intro h
    have he : S.indicator (f : α → ℂ) =ᵐ[μ] (0 : α → ℂ) :=
      (maskedL2_ae μ f S hS).symm.trans h
    filter_upwards [he] with x hx hmem
    simpa [Set.indicator_of_mem hmem] using hx
  · intro h
    have he : S.indicator (f : α → ℂ) =ᵐ[μ] (0 : α → ℂ) := by
      filter_upwards [h] with x hx
      by_cases hmem : x ∈ S
      · simpa [Set.indicator_of_mem hmem] using hx hmem
      · simp [Set.indicator_of_notMem hmem]
    exact (maskedL2_ae μ f S hS).trans he

/-- The selected norm is bounded by the physical Fourier norm. -/
theorem fourier_mask_norm_le {d : ℕ}
    (u : Sobolev.L2 d)
    (S : Set (EuclideanSpace ℝ (Fin d))) (hS : MeasurableSet S) :
    ‖maskedL2 volume (Sobolev.fourierL2 u) S hS‖ ≤ ‖u‖ := by
  calc
    ‖maskedL2 volume (Sobolev.fourierL2 u) S hS‖ ≤
        ‖Sobolev.fourierL2 u‖ := maskedL2_norm_le volume _ S hS
    _ = ‖u‖ := (Sobolev.fourierL2).norm_map u

/-- A nonzero whole-space L² field has a denominator strictly greater than zero. -/
theorem fourier_norm_pos {d : ℕ} (u : Sobolev.L2 d) (hu : u ≠ 0) :
    0 < ‖Sobolev.fourierL2 u‖ := by
  rw [(Sobolev.fourierL2).norm_map]
  exact norm_pos_iff.mpr hu

/-- Genuine whole-space L² concentration fraction formed from the
physical Fourier isometry and a measurable spectral mask. -/
noncomputable def fraction {d : ℕ}
    (u : Sobolev.L2 d)
    (S : Set (EuclideanSpace ℝ (Fin d))) (hS : MeasurableSet S) : ℝ :=
  energyFraction
    (‖maskedL2 volume (Sobolev.fourierL2 u) S hS‖ ^ 2)
    (‖u‖ ^ 2)

/-- The continuous-spectrum L² fraction lies in [0, 1]. -/
theorem fraction_bounds {d : ℕ}
    (u : Sobolev.L2 d)
    (S : Set (EuclideanSpace ℝ (Fin d))) (hS : MeasurableSet S)
    (hu : u ≠ 0) :
    0 ≤ fraction u S hS ∧ fraction u S hS ≤ 1 := by
  apply energyFraction_bounds
  · exact sq_nonneg _
  · nlinarith [fourier_mask_norm_le u S hS,
      norm_nonneg u, norm_nonneg (maskedL2 volume (Sobolev.fourierL2 u) S hS)]
  · exact sq_pos_of_pos (norm_pos_iff.mpr hu)

/-- Zero continuous-spectrum fraction iff the physical field's Fourier
transform vanishes almost everywhere in the chosen band. -/
theorem fraction_zero_iff {d : ℕ}
    (u : Sobolev.L2 d)
    (S : Set (EuclideanSpace ℝ (Fin d))) (hS : MeasurableSet S)
    (hu : u ≠ 0) :
    fraction u S hS = 0 ↔
      ∀ᵐ ξ ∂volume, ξ ∈ S →
        (Sobolev.fourierL2 u : EuclideanSpace ℝ (Fin d) → ℂ) ξ = 0 := by
  unfold fraction
  rw [energyFraction_zero_iff _ _ (sq_pos_of_pos (norm_pos_iff.mpr hu))]
  rw [sq_eq_zero_iff, norm_eq_zero]
  exact maskedL2_eq_zero_iff volume _ S hS

end E62ContinuumL2
end ReyesMath
