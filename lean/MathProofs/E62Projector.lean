import MathProofs.E62Discrete

/-!
# E62: exact spectral coordinate projector and dynamical counterexample

The coordinate mask is an idempotent operator on arbitrary Fourier
coefficient families. Its selected and complementary outputs are
pointwise orthogonal, and their total squared-modulus energies form
the exact Pythagorean partition for every summable family.

This module is a coefficient-space result; it does not identify the
mask with a projector on the torus L² space, which requires the
torus Fourier/Parseval equivalence.
-/

namespace ReyesMath
namespace E62Projector

open RemainingCores E62Discrete

variable {ι : Type*}

/-- Mask a coefficient family to any selected set of frequencies. -/
noncomputable def selectModes (S : Set ι) (c : ι → ℂ) : ι → ℂ := by
  classical
  exact fun k => if k ∈ S then c k else 0

theorem selectModes_idempotent (S : Set ι) (c : ι → ℂ) :
    selectModes S (selectModes S c) = selectModes S c := by
  classical
  funext k
  by_cases hk : k ∈ S <;> simp [selectModes, hk]

theorem selectModes_complement (S : Set ι) (c : ι → ℂ) :
    (fun k => selectModes S c k + selectModes Sᶜ c k) = c := by
  classical
  funext k
  by_cases hk : k ∈ S <;> simp [selectModes, hk]

/-- The selected and rejected coefficients are orthogonal mode by mode. -/
theorem selectModes_pointwise_orthogonal (S : Set ι) (c : ι → ℂ) :
    ∀ k, selectModes S c k * star (selectModes Sᶜ c k) = 0 := by
  classical
  intro k
  by_cases hk : k ∈ S <;> simp [selectModes, hk]

/-- The energy of the masked coefficient family is the original
selected spectral energy, with no finite-support assumption. -/
theorem masked_energy_eq_selected (S : Set ι) (c : ι → ℂ) :
    totalEnergy (selectModes S c) = selectedEnergy c S := by
  classical
  unfold totalEnergy selectedEnergy
  apply tsum_congr
  intro k
  by_cases hk : k ∈ S <;> simp [selectModes, hk]

/-- Spectral coefficient Pythagoras for arbitrary summable complex modes. -/
theorem coefficient_pythagoras (S : Set ι) (c : ι → ℂ)
    (hc : Summable (fun k => ‖c k‖ ^ 2)) :
    totalEnergy c =
      totalEnergy (selectModes S c) + totalEnergy (selectModes Sᶜ c) := by
  calc
    totalEnergy c = selectedEnergy c S + selectedEnergy c Sᶜ :=
      totalEnergy_split c S hc
    _ = totalEnergy (selectModes S c) +
        totalEnergy (selectModes Sᶜ c) := by
          rw [masked_energy_eq_selected, masked_energy_eq_selected]

/-- Two orthogonal modes, with real amplitudes t and 1-t, yield a
normalized fraction that need not be monotone as t changes. -/
noncomputable def twoModeFraction (t : ℝ) : ℝ :=
  energyFraction (t ^ 2) (t ^ 2 + (1 - t) ^ 2)

theorem twoModeFraction_at_one : twoModeFraction 1 = 1 := by
  norm_num [twoModeFraction, energyFraction]

theorem twoModeFraction_at_two : twoModeFraction 2 = 4 / 5 := by
  norm_num [twoModeFraction, energyFraction]

theorem twoModeFraction_not_monotone : ¬ Monotone twoModeFraction := by
  intro hm
  have h := hm (show (1 : ℝ) ≤ 2 by norm_num)
  rw [twoModeFraction_at_one, twoModeFraction_at_two] at h
  norm_num at h

end E62Projector
end ReyesMath
