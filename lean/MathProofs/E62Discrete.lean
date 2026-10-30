import MathProofs.RemainingCores

/-!
# E62: arbitrary-mode discrete spectral energy fractions

This module treats the genuinely infinite coefficient space, not a finite FFT.
For a summable squared-modulus family indexed by an arbitrary type (and therefore
in particular by `Fin d → ℤ`), the selected and complementary spectral
energies add up to the total. Zero- and one-fraction equality are equivalent to
vanishing of the corresponding *individual coefficients*.

The identification of these coefficient families with the Fourier transform of
every `L²(𝕋ᵈ)` field, the independent orthogonal-projector proof, and the
continuous-spectrum counterpart are separate E62 obligations.
-/

namespace ReyesMath
namespace E62Discrete

attribute [local instance] Classical.propDecidable

open ReyesMath.RemainingCores

variable {ι : Type*}

noncomputable def totalEnergy (c : ι → ℂ) : ℝ :=
  ∑' k, ‖c k‖ ^ 2

noncomputable def selectedEnergy (c : ι → ℂ) (S : Set ι) : ℝ := by
  classical
  exact ∑' k, if k ∈ S then ‖c k‖ ^ 2 else 0

noncomputable def fraction (c : ι → ℂ) (S : Set ι) : ℝ :=
  energyFraction (selectedEnergy c S) (totalEnergy c)

theorem summable_selected (c : ι → ℂ) (S : Set ι)
    (hc : Summable (fun k => ‖c k‖ ^ 2)) :
    Summable (fun k => if k ∈ S then ‖c k‖ ^ 2 else 0) := by
  classical
  apply Summable.of_nonneg_of_le
    (fun k => by by_cases hk : k ∈ S <;> simp [hk, sq_nonneg])
    (fun k => by by_cases hk : k ∈ S <;> simp [hk, sq_nonneg]) hc

theorem selectedEnergy_nonneg (c : ι → ℂ) (S : Set ι) :
    0 ≤ selectedEnergy c S := by
  classical
  unfold selectedEnergy
  exact tsum_nonneg (fun k => by split_ifs <;> positivity)

theorem totalEnergy_split (c : ι → ℂ) (S : Set ι)
    (hc : Summable (fun k => ‖c k‖ ^ 2)) :
    totalEnergy c = selectedEnergy c S + selectedEnergy c Sᶜ := by
  classical
  calc
    totalEnergy c =
        ∑' k, ((if k ∈ S then ‖c k‖ ^ 2 else 0) +
          (if k ∈ Sᶜ then ‖c k‖ ^ 2 else 0)) := by
            unfold totalEnergy
            apply tsum_congr
            intro k
            by_cases hk : k ∈ S <;> simp [hk]
    _ = selectedEnergy c S + selectedEnergy c Sᶜ := by
          have hadd := (summable_selected c S hc).tsum_add
            (summable_selected c Sᶜ hc)
          calc
            _ = (∑' k, if k ∈ S then ‖c k‖ ^ 2 else 0) +
                (∑' k, if k ∈ Sᶜ then ‖c k‖ ^ 2 else 0) := by
                  convert hadd using 1 <;>
                    (try { apply tsum_congr; intro k
                           by_cases hk : k ∈ S <;> simp [hk] })
                  all_goals
                    congr 1 <;>
                      (apply tsum_congr
                       intro k
                       by_cases hk : k ∈ S <;> simp [hk])
            _ = selectedEnergy c S + selectedEnergy c Sᶜ := by
                  congr 1 <;> (
                    unfold selectedEnergy
                    apply tsum_congr
                    intro k
                    by_cases hk : k ∈ S <;> simp [hk])

theorem selectedEnergy_le_total (c : ι → ℂ) (S : Set ι)
    (hc : Summable (fun k => ‖c k‖ ^ 2)) :
    selectedEnergy c S ≤ totalEnergy c := by
  have hsplit := totalEnergy_split c S hc
  have hnonneg := selectedEnergy_nonneg c Sᶜ
  linarith

theorem totalEnergy_pos (c : ι → ℂ)
    (hc : Summable (fun k => ‖c k‖ ^ 2))
    (hne : ∃ k, c k ≠ 0) : 0 < totalEnergy c := by
  obtain ⟨k, hk⟩ := hne
  have hkpos : 0 < ‖c k‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr hk)
  have hle : ‖c k‖ ^ 2 ≤ totalEnergy c := by
    unfold totalEnergy
    exact le_tsum hc k (fun j _ => sq_nonneg _)
  linarith

theorem selectedEnergy_eq_zero_iff (c : ι → ℂ) (S : Set ι)
    (hc : Summable (fun k => ‖c k‖ ^ 2)) :
    selectedEnergy c S = 0 ↔ ∀ k ∈ S, c k = 0 := by
  classical
  constructor
  · intro hzero k hk
    have hle : (if k ∈ S then ‖c k‖ ^ 2 else 0) ≤ selectedEnergy c S := by
      unfold selectedEnergy
      exact le_tsum (summable_selected c S hc) k
        (fun j _ => by split_ifs <;> positivity)
    rw [if_pos hk, hzero] at hle
    have hsq : ‖c k‖ ^ 2 = 0 := by
      nlinarith [sq_nonneg (‖c k‖)]
    exact norm_eq_zero.mp (pow_eq_zero hsq)
  · intro hzero
    unfold selectedEnergy
    have hh : (fun k => if k ∈ S then ‖c k‖ ^ 2 else 0) =
        (fun _ => (0 : ℝ)) := by
      funext k
      by_cases hk : k ∈ S
      · simp [hk, hzero k hk]
      · simp [hk]
    rw [hh]
    simp

theorem fraction_bounds (c : ι → ℂ) (S : Set ι)
    (hc : Summable (fun k => ‖c k‖ ^ 2))
    (hne : ∃ k, c k ≠ 0) :
    0 ≤ fraction c S ∧ fraction c S ≤ 1 := by
  exact energyFraction_bounds _ _
    (selectedEnergy_nonneg c S)
    (selectedEnergy_le_total c S hc)
    (totalEnergy_pos c hc hne)

theorem fraction_zero_iff (c : ι → ℂ) (S : Set ι)
    (hc : Summable (fun k => ‖c k‖ ^ 2))
    (hne : ∃ k, c k ≠ 0) :
    fraction c S = 0 ↔ ∀ k ∈ S, c k = 0 := by
  change energyFraction (selectedEnergy c S) (totalEnergy c) = 0 ↔ _
  rw [energyFraction_zero_iff _ _ (totalEnergy_pos c hc hne)]
  exact selectedEnergy_eq_zero_iff c S hc

theorem fraction_one_iff (c : ι → ℂ) (S : Set ι)
    (hc : Summable (fun k => ‖c k‖ ^ 2))
    (hne : ∃ k, c k ≠ 0) :
    fraction c S = 1 ↔ ∀ k ∉ S, c k = 0 := by
  change energyFraction (selectedEnergy c S) (totalEnergy c) = 1 ↔ _
  rw [energyFraction_one_iff _ _ (totalEnergy_pos c hc hne)]
  have hsplit := totalEnergy_split c S hc
  have hzero := selectedEnergy_eq_zero_iff c Sᶜ hc
  constructor
  · intro h k hk
    exact (hzero.mp (show selectedEnergy c Sᶜ = 0 by linarith)) k hk
  · intro h
    have hother : selectedEnergy c Sᶜ = 0 := hzero.mpr (by
      intro k hk
      exact h k hk)
    linarith


/-- The zero field has zero total energy. The raw quotient is therefore
    the indeterminate 0/0 in the intended mathematical interpretation;
    Lean's totalized real division evaluates it to zero. -/
theorem zero_field_total_energy :
    totalEnergy (fun _ : ι => (0 : ℂ)) = 0 := by
  simp [totalEnergy]

theorem zero_field_selected_energy (S : Set ι) :
    selectedEnergy (fun _ : ι => (0 : ℂ)) S = 0 := by
  classical
  simp [selectedEnergy]

theorem zero_field_fraction (S : Set ι) :
    fraction (fun _ : ι => (0 : ℂ)) S = 0 := by
  classical
  simp [fraction, energyFraction, zero_field_total_energy,
    zero_field_selected_energy]


end E62Discrete
end ReyesMath
