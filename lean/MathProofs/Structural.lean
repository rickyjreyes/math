import Mathlib

/-!
# Structural theorems for the Reyes mathematics catalogue

These results give kernel-checked finite-dimensional or finite-sum claims.
They do not imply that the nonlinear PDE, continuous spectral, or canonical
constraint theorems in the accompanying manuscripts are formalized.
-/

namespace ReyesMath

open scoped BigOperators

/-- The actual 11-by-31 sensitivity matrix, not merely a natural-number
    calculation: at least 20 real kernel dimensions remain. -/
theorem elevenByThirtyOne_matrix_nullity
    (J : Matrix (Fin 11) (Fin 31) ℝ) :
    20 ≤ Module.finrank ℝ (LinearMap.ker J.mulVecLin) := by
  have hrange :
      Module.finrank ℝ (LinearMap.range J.mulVecLin) ≤ 11 := by
    calc
      Module.finrank ℝ (LinearMap.range J.mulVecLin)
          ≤ Module.finrank ℝ (Fin 11 → ℝ) :=
        Submodule.finrank_le _
      _ = 11 := by simp
  have hnull :=
    LinearMap.finrank_range_add_finrank_ker J.mulVecLin
  have hdomain : Module.finrank ℝ (Fin 31 → ℝ) = 31 := by
    simp
  omega

/-- The positive-sign Gram construction of two real scalar gradients. -/
def scalarGradientGram {n : ℕ} (a b : Fin n → ℝ)
    (v w : Fin n → ℝ) : ℝ :=
  (∑ i, a i * v i) * (∑ i, a i * w i) +
  (∑ i, b i * v i) * (∑ i, b i * w i)

/-- No negative-norm direction is possible for the positive-sign Gram tensor,
    in any finite dimension.  This is the Lorentzian-signature obstruction. -/
theorem scalarGradientGram_psd {n : ℕ}
    (a b v : Fin n → ℝ) :
    0 ≤ scalarGradientGram a b v v := by
  unfold scalarGradientGram
  nlinarith [sq_nonneg (∑ i, a i * v i),
             sq_nonneg (∑ i, b i * v i)]

theorem scalarGradientGram_no_timelike {n : ℕ}
    (a b v : Fin n → ℝ) :
    ¬ scalarGradientGram a b v v < 0 := by
  exact not_lt.mpr (scalarGradientGram_psd a b v)

/-- In one spatial Fourier dimension, a highest selected frequency p and a
    lower one q force the quintic frequency 3p-2q outside any finite cutoff
    whose elements are at most p. -/
theorem quintic_frequency_above_cutoff
    (S : Finset ℤ) (p q : ℤ)
    (hpmax : ∀ r ∈ S, r ≤ p) (hqp : q < p) :
    3 * p - 2 * q ∉ S := by
  intro hmem
  have hbound := hpmax (3 * p - 2 * q) hmem
  omega

/-- The analogous lowest-frequency leakage certificate. -/
theorem quintic_frequency_below_cutoff
    (S : Finset ℤ) (p q : ℤ)
    (hpmin : ∀ r ∈ S, p ≤ r) (hpq : p < q) :
    3 * p - 2 * q ∉ S := by
  intro hmem
  have hbound := hpmin (3 * p - 2 * q) hmem
  omega

/-- A finite weighted variance identity.  The weights sum to one; positivity
    is not needed for the algebraic identity. -/
theorem finite_weighted_variance_identity {n : ℕ}
    (w σ : Fin n → ℝ) (hw : (∑ i, w i) = 1) :
    (∑ i, w i * (σ i - (∑ j, w j * σ j)) ^ 2) =
      (∑ i, w i * σ i ^ 2) - (∑ i, w i * σ i) ^ 2 := by
  let μ : ℝ := ∑ i, w i * σ i
  have hlocal (i : Fin n) :
      w i * (σ i - μ) ^ 2 =
        w i * σ i ^ 2 - 2 * μ * (w i * σ i) + μ ^ 2 * w i := by
    ring
  change (∑ i, w i * (σ i - μ) ^ 2) =
    (∑ i, w i * σ i ^ 2) - μ ^ 2
  calc
    (∑ i, w i * (σ i - μ) ^ 2)
      = ∑ i, (w i * σ i ^ 2 - 2 * μ * (w i * σ i) + μ ^ 2 * w i) := by
          apply Finset.sum_congr rfl
          intro i _
          exact hlocal i
    _ = (∑ i, w i * σ i ^ 2) -
          2 * μ * (∑ i, w i * σ i) + μ ^ 2 * (∑ i, w i) := by
          simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
            ← Finset.mul_sum]
    _ = (∑ i, w i * σ i ^ 2) - μ ^ 2 := by
          dsimp [μ]
          rw [hw]
          ring

/-- For nonnegative normalized weights, the weighted square mean bounds
    the squared mean. This proves the finite-dimensional variance analogue. -/
theorem finite_weighted_mean_square_bound {n : ℕ}
    (w σ : Fin n → ℝ)
    (hw : (∑ i, w i) = 1)
    (hpos : ∀ i, 0 ≤ w i) :
    (∑ i, w i * σ i) ^ 2 ≤ ∑ i, w i * σ i ^ 2 := by
  have hvariance : 0 ≤
      (∑ i, w i * (σ i - (∑ j, w j * σ j)) ^ 2) := by
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (hpos i) (sq_nonneg _)
  rw [finite_weighted_variance_identity w σ hw] at hvariance
  linarith


/-- A concrete n-by-2 carrier matrix built from the two real gradients. -/
def scalarGradientCarrier {n : ℕ}
    (a b : Fin n → ℝ) : Matrix (Fin n) (Fin 2) ℝ :=
  fun i j => if j = 0 then a i else b i

/-- Its Gram matrix is precisely the two-gradient tensor, entrywise. -/
theorem scalarGradientCarrier_gram_entry {n : ℕ}
    (a b : Fin n → ℝ) (i j : Fin n) :
    ((scalarGradientCarrier a b) * (scalarGradientCarrier a b).transpose) i j =
      a i * a j + b i * b j := by
  simp [scalarGradientCarrier, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.transpose_apply]

/-- Unlike an elementary sum-of-squares bound, this is a genuine matrix
    rank obstruction: the n-by-n Gram matrix has rank at most two. -/
theorem scalarGradientCarrier_rank_le_two {n : ℕ}
    (a b : Fin n → ℝ) :
    ((scalarGradientCarrier a b) * (scalarGradientCarrier a b).transpose).rank ≤ 2 := by
  calc
    ((scalarGradientCarrier a b) * (scalarGradientCarrier a b).transpose).rank
        ≤ (scalarGradientCarrier a b).rank :=
          Matrix.rank_mul_le_left _ _
    _ ≤ 2 := Matrix.rank_le_width _

end ReyesMath
