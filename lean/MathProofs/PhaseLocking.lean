import Mathlib

/-!
# Discrete weighted phase-locking inequality

This is the finite-sum analogue of the closed-loop weighted Cauchy--Schwarz
bound. It deliberately does not identify a discrete sum with a continuous
closed-curve integral or prove inter-sector dynamics.
-/

namespace ReyesMath

open scoped BigOperators

/-- Weighted finite-sum phase mismatch bound. All weights are strictly
positive. The sum of inverse weights is the effective compliance. -/
theorem finite_weighted_phase_bound {ι : Type*} [Fintype ι]
    (w q σ : ι → ℝ) (hw : ∀ i, 0 < w i) :
    (∑ i : ι, q i - σ i) ^ 2 / (∑ i : ι, (w i)⁻¹) ≤
      ∑ i : ι, w i * (q i - σ i) ^ 2 := by
  classical
  have h := Finset.sq_sum_div_le_sum_sq_div (Finset.univ)
      (fun i => q i - σ i)
      (g := fun i => (w i)⁻¹)
      (by
        intro i _
        exact inv_pos.mpr (hw i))
  calc
    (∑ i : ι, q i - σ i) ^ 2 / (∑ i : ι, (w i)⁻¹)
        ≤ ∑ i : ι, (q i - σ i) ^ 2 / (w i)⁻¹ := h
    _ = ∑ i : ι, w i * (q i - σ i) ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [div_inv_eq_mul]
        ring

end ReyesMath
