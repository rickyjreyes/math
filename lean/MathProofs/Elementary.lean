import Mathlib

/-!
# Independently typed supporting statements

This module formalizes elementary algebraic consequences only.
It is not a formalization of strict binding, concentration compactness,
orbital stability, ultraviolet ill-posedness or the S004 constraint analysis.
-/
namespace ReyesMath

/-- A pointwise Gram form of two real gradients is nonnegative. -/
theorem scalarGradientGram_nonnegative (a b : ℝ) :
    0 ≤ a * a + b * b := by
  nlinarith [sq_nonneg a, sq_nonneg b]

/-- Arithmetic bound conditional on a rank upper bound of 11. -/
theorem elevenByThirtyone_nullity_bound (rank : ℕ)
    (hrank : rank ≤ 11) : 20 ≤ 31 - rank := by
  omega

/-- Arithmetic bound conditional on a separately established rank estimate. -/
theorem nullityBound_arithmetic (rows cols rank : ℕ)
    (hrank : rank ≤ rows) (hsize : rows ≤ cols) :
    cols - rows ≤ cols - rank := by
  omega

/-- The scalar positive-weight squared mismatch is nonnegative. -/
theorem squaredMismatch_nonnegative (w q : ℝ) (hw : 0 ≤ w) :
    0 ≤ w * q ^ 2 := by
  positivity

/-- Two nonnegative energy contributions have nonnegative sum. -/
theorem varianceDeficit_nonnegative (a v : ℝ)
    (ha : 0 ≤ a) (hv : 0 ≤ v) : 0 ≤ a + v := by
  exact add_nonneg ha hv

/-- Positive multiplicative gaps strictly lower negative energy. -/
theorem negativeEnergy_strictGap (e h : ℝ)
    (he : e < 0) (hh : 0 < h) :
    (1 + h) * e < e := by
  have hp : h * e < 0 := mul_neg_of_pos_of_neg hh he
  nlinarith

end ReyesMath
