import Mathlib

/-!
# Curvature weight, positivity and nonattainment criterion

These are analytic ingredients for the whole-space positive-curvature
functional. The exact H² mass-preserving spatial dilation and its
uniform energy bound are not yet proved in Lean, so the nonattainment
criterion is stated with an explicit small-energy competitor hypothesis.
-/

namespace ReyesMath

noncomputable def positiveCurvatureWeight (ε α s : ℝ) : ℝ :=
  s / (s + ε ^ 2 * Real.exp (-2 * α * s)) ^ 2

/-- The regularized curvature denominator is strictly positive for
ε≠0 and nonnegative density s, with no field zero singularity. -/
theorem curvature_weight_denominator_positive
    (ε α s : ℝ) (hε : ε ≠ 0) (hs : 0 ≤ s) :
    0 < s + ε ^ 2 * Real.exp (-2 * α * s) := by
  have he : 0 < ε ^ 2 := sq_pos_of_ne_zero hε
  have hexp : 0 < Real.exp (-2 * α * s) := Real.exp_pos _
  nlinarith [mul_pos he hexp]

/-- The precise density weight used in the positive curvature energy
is nonnegative for all nonnegative densities. -/
theorem curvature_weight_nonnegative
    (ε α s : ℝ) (hε : ε ≠ 0) (hs : 0 ≤ s) :
    0 ≤ positiveCurvatureWeight ε α s := by
  unfold positiveCurvatureWeight
  have hd := curvature_weight_denominator_positive ε α s hε hs
  exact div_nonneg hs (sq_nonneg _)

/-- At nonzero density the curvature weight is strictly positive. -/
theorem curvature_weight_positive
    (ε α s : ℝ) (hε : ε ≠ 0) (hs : 0 < s) :
    0 < positiveCurvatureWeight ε α s := by
  unfold positiveCurvatureWeight
  have hd := curvature_weight_denominator_positive ε α s hε (le_of_lt hs)
  exact div_pos hs (sq_pos_of_pos hd)

/-- General final variational step: if every positive-mass state has
strict positive energy but fixed-mass competitors have arbitrarily
small energy, no positive-mass energy minimizer exists. -/
theorem no_positive_mass_minimizer_of_spreading
    {X : Type*} (Mass Energy : X → ℝ) (m : ℝ)
    (hpositive : ∀ x, Mass x = m → 0 < Energy x)
    (hspread : ∀ η : ℝ, 0 < η →
      ∃ y, Mass y = m ∧ Energy y < η) :
    ∀ x, Mass x = m →
      ∃ y, Mass y = m ∧ Energy y < Energy x := by
  intro x hx
  exact hspread (Energy x) (hpositive x hx)

end ReyesMath
