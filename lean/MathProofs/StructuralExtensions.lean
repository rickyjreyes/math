import Mathlib

/-!
# General finite-dimensional structural obstructions

This module strengthens the exact matrix-level results. It does not infer
physical dynamics or a spacetime metric from algebraic tensors.
-/

namespace ReyesMath

open scoped BigOperators

/-- For an arbitrary number of scalar carriers, the positive-sign weighted
gradient quadratic form is always nonnegative. This rules out a Lorentzian
quadratic form regardless of the number of carriers. -/
theorem positive_weighted_gradient_family_psd {d carriers : ℕ}
    (weights : Fin carriers → ℝ)
    (gradients : Fin carriers → Fin d → ℝ)
    (v : Fin d → ℝ)
    (hweights : ∀ j, 0 ≤ weights j) :
    0 ≤ ∑ j : Fin carriers,
      weights j * (∑ i : Fin d, gradients j i * v i) ^ 2 := by
  apply Finset.sum_nonneg
  intro j hj
  exact mul_nonneg (hweights j) (sq_nonneg _)

/-- An n-by-k collection of scalar gradients generates a Gram matrix
of rank at most k. This generalizes the rank-two single-complex-field
case already formalized in Structural.lean. -/
theorem gradient_gram_rank_le_carriers {n carriers : ℕ}
    (A : Matrix (Fin n) (Fin carriers) ℝ) :
    (A * A.transpose).rank ≤ carriers := by
  calc
    (A * A.transpose).rank ≤ A.rank := Matrix.rank_mul_le_left _ _
    _ ≤ carriers := Matrix.rank_le_width _

/-- Any m-observable, n-coefficient sensitivity matrix with m ≤ n
has at least n-m locally invisible linear parameter directions.
No numerical Jacobian rank or nonlinear identifiability is asserted. -/
theorem rectangular_sensitivity_nullity
    (m n : ℕ) (J : Matrix (Fin m) (Fin n) ℝ) (hm : m ≤ n) :
    n - m ≤ Module.finrank ℝ (LinearMap.ker J.mulVecLin) := by
  have hrange :
      Module.finrank ℝ (LinearMap.range J.mulVecLin) ≤ m := by
    calc
      Module.finrank ℝ (LinearMap.range J.mulVecLin)
          ≤ Module.finrank ℝ (Fin m → ℝ) := Submodule.finrank_le _
      _ = m := by simp
  have hnull := LinearMap.finrank_range_add_finrank_ker J.mulVecLin
  have hdomain : Module.finrank ℝ (Fin n → ℝ) = n := by simp
  omega

/-- Frequency leakage is detected by any extremal coordinate, in an
arbitrary finite spatial dimension. This is a lattice-arithmetic core;
the full nonlinear coefficient-extraction argument is separate. -/
theorem multidimensional_quintic_frequency_escape {d : ℕ}
    (S : Finset (Fin d → ℤ)) (p q : Fin d → ℤ) (axis : Fin d)
    (hpmax : ∀ r ∈ S, r axis ≤ p axis)
    (hqp : q axis < p axis) :
    (fun i => 3 * p i - 2 * q i) ∉ S := by
  intro hmem
  have hb := hpmax (fun i => 3 * p i - 2 * q i) hmem
  dsimp at hb
  omega

end ReyesMath
