import Mathlib

/-!
# Exact finite weighted phase-locking

A completed finite-dimensional counterpart of the weighted loop minimization
theorem.  The continuous H¹ / L² problem in the manuscript is not identified
with a finite sum; it remains a separate formalization obligation.
-/

namespace ReyesMath

open scoped BigOperators

/-- Completing the square with arbitrary real multiplier η.  This is an
exact remainder identity, not merely a Cauchy--Schwarz lower bound. -/
theorem finite_weighted_phase_remainder {ι : Type*}
    (s : Finset ι) (w q σ : ι → ℝ) (η : ℝ)
    (hw : ∀ i ∈ s, w i ≠ 0) :
    s.sum (fun i => w i * (q i - σ i) ^ 2) =
      s.sum (fun i => w i * (q i - σ i - η / w i) ^ 2) +
        2 * η * s.sum (fun i => q i - σ i) -
        η ^ 2 * s.sum (fun i => (w i)⁻¹) := by
  classical
  have hpoint (i : ι) (hi : i ∈ s) :
      w i * (q i - σ i) ^ 2 =
        w i * (q i - σ i - η / w i) ^ 2 +
          2 * η * (q i - σ i) - η ^ 2 * (w i)⁻¹ := by
    have hn : w i ≠ 0 := hw i hi
    field_simp [hn]
    <;> ring
  calc
    s.sum (fun i => w i * (q i - σ i) ^ 2)
        = s.sum (fun i =>
            w i * (q i - σ i - η / w i) ^ 2 +
              2 * η * (q i - σ i) - η ^ 2 * (w i)⁻¹) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hpoint i hi
    _ = s.sum (fun i => w i * (q i - σ i - η / w i) ^ 2) +
          2 * η * s.sum (fun i => q i - σ i) -
          η ^ 2 * s.sum (fun i => (w i)⁻¹) := by
          simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
            ← Finset.mul_sum]

/-- The phase deficit is exactly its optimal fixed-sum value plus a
nonnegative residual.  No compactness or PDE assumptions are used. -/
theorem finite_weighted_phase_exact_gap {ι : Type*}
    (s : Finset ι) (w q σ : ι → ℝ) (C : ℝ)
    (hw : ∀ i ∈ s, w i ≠ 0)
    (hI : s.sum (fun i => (w i)⁻¹) ≠ 0)
    (hC : s.sum (fun i => q i - σ i) = C) :
    s.sum (fun i => w i * (q i - σ i) ^ 2) =
      C ^ 2 / (s.sum (fun i => (w i)⁻¹)) +
        s.sum (fun i =>
          w i * (q i - σ i -
            (C / s.sum (fun j => (w j)⁻¹)) / w i) ^ 2) := by
  let I : ℝ := s.sum (fun i => (w i)⁻¹)
  let η : ℝ := C / I
  have hr := finite_weighted_phase_remainder s w q σ η hw
  change s.sum (fun i => w i * (q i - σ i) ^ 2) =
    C ^ 2 / I +
      s.sum (fun i => w i * (q i - σ i - η / w i) ^ 2)
  rw [hC] at hr
  calc
    s.sum (fun i => w i * (q i - σ i) ^ 2) =
      s.sum (fun i => w i * (q i - σ i - η / w i) ^ 2) +
        2 * η * C - η ^ 2 * I := hr
    _ = C ^ 2 / I +
      s.sum (fun i => w i * (q i - σ i - η / w i) ^ 2) := by
        dsimp [η]
        have hIn : I ≠ 0 := hI
        field_simp [hIn]
        ring

/-- A weighted-energy deficit cannot be negative when all weights
are positive; the sharp gap identity provides a certificate. -/
theorem finite_weighted_phase_sharp_bound {ι : Type*}
    (s : Finset ι) (w q σ : ι → ℝ) (C : ℝ)
    (hw : ∀ i ∈ s, 0 < w i)
    (hI : s.sum (fun i => (w i)⁻¹) ≠ 0)
    (hC : s.sum (fun i => q i - σ i) = C) :
    C ^ 2 / (s.sum (fun i => (w i)⁻¹)) ≤
      s.sum (fun i => w i * (q i - σ i) ^ 2) := by
  have hid := finite_weighted_phase_exact_gap s w q σ C
    (fun i hi => ne_of_gt (hw i hi)) hI hC
  rw [hid]
  have hnonneg : 0 ≤
    s.sum (fun i =>
      w i * (q i - σ i -
        (C / s.sum (fun j => (w j)⁻¹)) / w i) ^ 2) := by
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (le_of_lt (hw i hi)) (sq_nonneg _)
  linarith

end ReyesMath
