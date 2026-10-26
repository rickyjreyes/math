import Mathlib

/-!
# Exact Gaussian-trial energy algebra

The real coefficients c₂,c₄ are those in the anisotropic Gaussian
carrier calculation. These statements prove sign, scale optimization,
and the scalar trial-energy certificate. The Gaussian is not yet
defined as a Sobolev function, and its norm identities are not checked
in Lean: the full constrained-infimum theorem remains open.
-/

namespace ReyesMath

noncomputable def gaussianC2 (β m k a b : ℝ) : ℝ :=
  2 * m * k ^ 2 / a ^ 2 - β * m ^ 2 / (4 * Real.pi * a * b)

noncomputable def gaussianC4 (γ m a b : ℝ) : ℝ :=
  m * (3 / (4 * a ^ 4) + 1 / (2 * a ^ 2 * b ^ 2) +
    3 / (4 * b ^ 4)) +
    γ * m ^ 3 / (9 * Real.pi ^ 2 * a ^ 2 * b ^ 2)

/-- Exact anisotropic criterion makes the quadratic scale coefficient
negative. It is not a numerical approximation. -/
theorem gaussian_coefficient_c2_negative
    (β m k a b : ℝ)
    (hβ : 0 < β) (hm : 0 < m) (ha : 0 < a) (hb : 0 < b)
    (hanis : 8 * Real.pi * k ^ 2 * b < β * m * a) :
    gaussianC2 β m k a b < 0 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hd : 0 < 4 * Real.pi * a ^ 2 * b := by positivity
  have hd0 : 4 * Real.pi * a ^ 2 * b ≠ 0 := ne_of_gt hd
  have hid :
      gaussianC2 β m k a b =
        (m / (4 * Real.pi * a ^ 2 * b)) *
          (8 * Real.pi * k ^ 2 * b - β * m * a) := by
    unfold gaussianC2
    field_simp
    ring
  rw [hid]
  apply mul_neg_of_pos_of_neg
  · exact div_pos hm hd
  · linarith

/-- The sextic-plus-fourth-order coefficient is strictly positive
for every positive parameter choice. -/
theorem gaussian_coefficient_c4_positive
    (γ m a b : ℝ)
    (hγ : 0 < γ) (hm : 0 < m) (ha : 0 < a) (hb : 0 < b) :
    0 < gaussianC4 γ m a b := by
  unfold gaussianC4
  have hpi : 0 < Real.pi := Real.pi_pos
  positivity

/-- Exact scale energy identity: for c₂ negative and c₄ positive
the quadratic in z=R⁻² takes a strictly negative value at its
positive optimal scale. -/
theorem quadratic_trial_energy_negative
    (c₂ c₄ : ℝ) (hc₂ : c₂ < 0) (hc₄ : 0 < c₄) :
    ∃ z : ℝ, 0 < z ∧
      c₂ * z + c₄ * z ^ 2 = -(c₂ ^ 2 / (4 * c₄)) ∧
      c₂ * z + c₄ * z ^ 2 < 0 := by
  let z : ℝ := -c₂ / (2 * c₄)
  have hz : 0 < z := div_pos (neg_pos.mpr hc₂) (by positivity)
  have heq : c₂ * z + c₄ * z ^ 2 =
      -(c₂ ^ 2 / (4 * c₄)) := by
    dsimp [z]
    field_simp
    ring
  have hneg : -(c₂ ^ 2 / (4 * c₄)) < 0 := by
    have hs : 0 < c₂ ^ 2 := sq_pos_of_ne_zero (ne_of_lt hc₂)
    have hd : 0 < 4 * c₄ := by positivity
    exact neg_neg_of_pos (div_pos hs hd)
  exact ⟨z, hz, heq, heq ▸ hneg⟩

/-- A fully quantified scalar trial certificate for arbitrary positive
physical coefficients and aspect ratios satisfying the exact criterion. -/
theorem gaussian_trial_polynomial_certificate
    (β γ m k a b : ℝ)
    (hβ : 0 < β) (hγ : 0 < γ) (hm : 0 < m)
    (ha : 0 < a) (hb : 0 < b)
    (hanis : 8 * Real.pi * k ^ 2 * b < β * m * a) :
    ∃ z : ℝ, 0 < z ∧
      gaussianC2 β m k a b * z +
        gaussianC4 γ m a b * z ^ 2 < 0 := by
  obtain ⟨z, hz, _, hnegative⟩ :=
    quadratic_trial_energy_negative
      (gaussianC2 β m k a b) (gaussianC4 γ m a b)
      (gaussian_coefficient_c2_negative β m k a b hβ hm ha hb hanis)
      (gaussian_coefficient_c4_positive γ m a b hγ hm ha hb)
  exact ⟨z, hz, hnegative⟩

end ReyesMath
