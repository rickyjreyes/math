import Mathlib

/-!
# GC25: a positive-energy two-field Fourier parent and its effective dispersion

Consider the *specified finite-mode* second-order-in-time quadratic system
with positive kinetic form p₁²+p₂² and stiffness matrix

    [A q       g q   ]
    [g q   M + C q  ]

where q is the squared spatial wavenumber, M is the heavy-field mass squared,
and A*C >= g². The mode energy is nonnegative for every q >= 0.

The exact characteristic polynomial admits the low-q fourth-order-in-spatial-
wavenumber approximation z = A q - (g²/M) q² with an exact O(q³) residual.
This is NOT an exact finite-interval single-field dispersion identity, nor
a proof of full nonlinear ghost-freedom or of the GC25 parent classification.
-/

namespace ReyesMath
namespace GC25

/-- Potential/stiffness quadratic form of a coupled light/heavy mode. -/
def stiffness (A C M g q x y : ℝ) : ℝ :=
  A * q * x ^ 2 + 2 * g * q * x * y + (M + C * q) * y ^ 2

/-- Exact square completion after multiplication by positive A. -/
theorem stiffness_square_identity (A C M g q x y : ℝ) :
    A * stiffness A C M g q x y =
      q * (A * x + g * y) ^ 2 +
        (A * M + (A * C - g ^ 2) * q) * y ^ 2 := by
  unfold stiffness
  ring

/-- The Fourier stiffness is nonnegative at every real Fourier mode when
    the heavy mass is nonnegative and the gradient matrix is PSD. -/
theorem stiffness_nonneg (A C M g q x y : ℝ)
    (hA : 0 < A) (hM : 0 ≤ M) (hdet : g ^ 2 ≤ A * C) (hq : 0 ≤ q) :
    0 ≤ stiffness A C M g q x y := by
  have hsq1 : 0 ≤ q * (A * x + g * y) ^ 2 :=
    mul_nonneg hq (sq_nonneg _)
  have hcoeff : 0 ≤ A * M + (A * C - g ^ 2) * q :=
    add_nonneg (mul_nonneg hA.le hM)
      (mul_nonneg (sub_nonneg.mpr hdet) hq)
  have hsq2 : 0 ≤ (A * M + (A * C - g ^ 2) * q) * y ^ 2 :=
    mul_nonneg hcoeff (sq_nonneg _)
  have hprod : 0 ≤ A * stiffness A C M g q x y := by
    rw [stiffness_square_identity]
    exact add_nonneg hsq1 hsq2
  by_contra h
  have hn : stiffness A C M g q x y < 0 := lt_of_not_ge h
  exact (not_lt_of_ge hprod) (mul_neg_of_pos_of_neg hA hn)

/-- Positive kinetic energies plus the nonnegative parent stiffness. -/
def parentModeEnergy (A C M g q p₁ p₂ x y : ℝ) : ℝ :=
  p₁ ^ 2 + p₂ ^ 2 + stiffness A C M g q x y

theorem parent_mode_energy_nonneg (A C M g q p₁ p₂ x y : ℝ)
    (hA : 0 < A) (hM : 0 ≤ M) (hdet : g ^ 2 ≤ A * C) (hq : 0 ≤ q) :
    0 ≤ parentModeEnergy A C M g q p₁ p₂ x y := by
  unfold parentModeEnergy
  exact add_nonneg
    (add_nonneg (sq_nonneg p₁) (sq_nonneg p₂))
    (stiffness_nonneg A C M g q x y hA hM hdet hq)

/-- The exact two-field characteristic determinant in z = omega². -/
def characteristic (A C M g q z : ℝ) : ℝ :=
  (z - A * q) * (z - (M + C * q)) - g ^ 2 * q ^ 2

/-- The effective light-branch polynomial through fourth spatial order. -/
def lightApproximation (A M g q : ℝ) : ℝ :=
  A * q - (g ^ 2 / M) * q ^ 2

/-- Exact residual after substituting the fourth-order approximation into
    the two-field characteristic equation. Its first term has order q³. -/
theorem light_approximation_residual (A C M g q : ℝ) (hM : M ≠ 0) :
    characteristic A C M g q (lightApproximation A M g q) =
      (g ^ 2 * (C - A) / M) * q ^ 3 +
        (g ^ 4 / M ^ 2) * q ^ 4 := by
  unfold characteristic lightApproximation
  field_simp [hM]
  ring

/-- Matched light/heavy gradient coefficients remove the cubic residual. -/
theorem equal_gradient_residual (A M g q : ℝ) (hM : M ≠ 0) :
    characteristic A A M g q (lightApproximation A M g q) =
      (g ^ 4 / M ^ 2) * q ^ 4 := by
  rw [light_approximation_residual A A M g q hM]
  ring

/-- Exact factorization of the fourth-order light-branch residual. -/
theorem light_approximation_residual_factor
    (A C M g q : ℝ) (hM : M ≠ 0) :
    characteristic A C M g q (lightApproximation A M g q) =
      (g ^ 2 * q ^ 3 / M ^ 2) * (M * (C - A) + g ^ 2 * q) := by
  rw [light_approximation_residual A C M g q hM]
  field_simp [hM]
  ring

/-- With nonzero interfield coupling, the fourth-order truncation can be
    an exact eigenfrequency at *at most one positive* squared wavenumber. -/
theorem light_approximation_exact_positive_unique
    (A C M g q₁ q₂ : ℝ)
    (hM : M ≠ 0) (hg : g ≠ 0)
    (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (h₁ : characteristic A C M g q₁ (lightApproximation A M g q₁) = 0)
    (h₂ : characteristic A C M g q₂ (lightApproximation A M g q₂) = 0) :
    q₁ = q₂ := by
  have hlin (q : ℝ) (hq : 0 < q)
      (hz : characteristic A C M g q (lightApproximation A M g q) = 0) :
      M * (C - A) + g ^ 2 * q = 0 := by
    rw [light_approximation_residual_factor A C M g q hM] at hz
    have hpref : g ^ 2 * q ^ 3 / M ^ 2 ≠ 0 := by
      exact div_ne_zero
        (mul_ne_zero (pow_ne_zero 2 hg) (pow_ne_zero 3 (ne_of_gt hq)))
        (pow_ne_zero 2 hM)
    exact (mul_eq_zero.mp hz).resolve_left hpref
  have hlin₁ := hlin q₁ hq₁ h₁
  have hlin₂ := hlin q₂ hq₂ h₂
  have hdiff : g ^ 2 * (q₁ - q₂) = 0 := by
    linarith
  have heq : q₁ - q₂ = 0 :=
    (mul_eq_zero.mp hdiff).resolve_left (pow_ne_zero 2 hg)
  exact sub_eq_zero.mp heq

/-- No nonempty positive interval can have the truncated q² dispersion as
    its *exact* light eigenvalue when g ≠ 0. The quadratic parent remains
    healthy under the separate hypotheses of parent_mode_energy_nonneg. -/
theorem light_approximation_not_exact_on_interval
    (A C M g a b : ℝ)
    (hM : M ≠ 0) (hg : g ≠ 0)
    (ha : 0 ≤ a) (hab : a < b) :
    ¬ ∀ q : ℝ, a < q → q < b →
      characteristic A C M g q (lightApproximation A M g q) = 0 := by
  intro hall
  let q₁ : ℝ := (2 * a + b) / 3
  let q₂ : ℝ := (a + 2 * b) / 3
  have h₁a : a < q₁ := by
    dsimp [q₁]
    linarith
  have h₁b : q₁ < b := by
    dsimp [q₁]
    linarith
  have h₂a : a < q₂ := by
    dsimp [q₂]
    linarith
  have h₂b : q₂ < b := by
    dsimp [q₂]
    linarith
  have hq₁ : 0 < q₁ := lt_of_le_of_lt ha h₁a
  have hq₂ : 0 < q₂ := lt_of_le_of_lt ha h₂a
  have heq : q₁ = q₂ :=
    light_approximation_exact_positive_unique A C M g q₁ q₂ hM hg hq₁ hq₂
      (hall q₁ h₁a h₁b) (hall q₂ h₂a h₂b)
  have hne : q₁ ≠ q₂ := by
    intro he
    dsimp [q₁, q₂] at he
    linarith
  exact hne heq

end GC25
end ReyesMath
