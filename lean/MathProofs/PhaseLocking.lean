import Mathlib

/-!
# Discrete weighted phase locking

The exact finite Cauchy--Schwarz lower bound. This result does not replace
the continuous closed-loop variational statement in its source manuscript.
-/

namespace ReyesMath

/-- Finite weighted mismatch: the squared total phase defect, divided by
the sum of inverse weights, bounds the weighted mismatch energy. -/
theorem finite_weighted_phase_bound {ι : Type*}
    (s : Finset ι) (w q σ : ι → ℝ)
    (hw : ∀ i ∈ s, 0 < w i) :
    (s.sum (fun i => q i - σ i)) ^ 2 /
        (s.sum (fun i => (w i)⁻¹)) ≤
      s.sum (fun i => w i * (q i - σ i) ^ 2) := by
  have h := Finset.sq_sum_div_le_sum_sq_div s
      (fun i => q i - σ i)
      (g := fun i => (w i)⁻¹)
      (by
        intro i hi
        exact inv_pos.mpr (hw i hi))
  calc
    (s.sum (fun i => q i - σ i)) ^ 2 /
        (s.sum (fun i => (w i)⁻¹))
        ≤ s.sum (fun i => (q i - σ i) ^ 2 / (w i)⁻¹) := h
    _ = s.sum (fun i => w i * (q i - σ i) ^ 2) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [div_inv_eq_mul]
        ring

end ReyesMath
