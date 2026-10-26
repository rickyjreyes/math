import Mathlib

/-!
# Cubic–quintic variational algebra (binding / minimizers / stability)

This module proves the **exact** pointwise coercivity identity for the
focusing-cubic / defocusing-quintic density, and the implication from
strictly decreasing specific constrained energy to strict binding.
Neither substitutes for establishing that specific-energy hypothesis
for the H²(R²) infimum.
-/

namespace ReyesMath

/-- Exact cubic–quintic completion of squares, without inequality loss. -/
theorem cubic_quintic_potential_square
    (β γ r : ℝ) (hγ : γ ≠ 0) :
    -(β / 2) * r ^ 2 + (γ / 3) * r ^ 3 =
      (γ / 3) * r * (r - 3 * β / (4 * γ)) ^ 2 -
        (3 * β ^ 2 / (16 * γ)) * r := by
  field_simp [hγ] <;> ring

/-- The uniform negative mass-density bound underlying constrained
coercivity, at every nonnegative density. -/
theorem cubic_quintic_potential_lower
    (β γ r : ℝ) (hγ : 0 < γ) (hr : 0 ≤ r) :
    -(3 * β ^ 2 / (16 * γ)) * r ≤
      -(β / 2) * r ^ 2 + (γ / 3) * r ^ 3 := by
  rw [cubic_quintic_potential_square β γ r (ne_of_gt hγ)]
  have hterm : 0 ≤ (γ / 3) * r * (r - 3 * β / (4 * γ)) ^ 2 := by
    positivity
  linarith

/-- Strict specific-energy monotonicity at both positive parts of one
mass split implies genuine strict subadditivity. This is a rigorous
bridge for the variational infimum, not an assumption that the
specific-energy inequality itself has been proved for the PDE. -/
theorem strict_binding_of_specific_energy
    (I : ℝ → ℝ) (m μ : ℝ)
    (hμ : 0 < μ) (hmμ : μ < m)
    (hleft : I m / m < I μ / μ)
    (hright : I m / m < I (m - μ) / (m - μ)) :
    I m < I μ + I (m - μ) := by
  have hm : 0 < m := lt_trans hμ hmμ
  have hrest : 0 < m - μ := sub_pos.mpr hmμ
  have hs1 : μ * (I m / m) < I μ := by
    calc
      μ * (I m / m) < μ * (I μ / μ) :=
        mul_lt_mul_of_pos_left hleft hμ
      _ = I μ := by field_simp
  have hs2 : (m - μ) * (I m / m) < I (m - μ) := by
    calc
      (m - μ) * (I m / m) < (m - μ) * (I (m - μ) / (m - μ)) :=
        mul_lt_mul_of_pos_left hright hrest
      _ = I (m - μ) := by field_simp
  have hsum : μ * (I m / m) + (m - μ) * (I m / m) = I m := by
    calc
      _ = m * (I m / m) := by ring
      _ = I m := by field_simp
  linarith

end ReyesMath
