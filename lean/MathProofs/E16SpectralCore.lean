import Mathlib

/-!
# E16: exact quadratic-in-q spectral growth algebra

The linear band-pass dispersion λ(q) = r + a q - b q² has its unique
maximizer at q = a/(2b) if a,b > 0, and an exact quadratic gap.
This is a prerequisite for the E16 continuous spectral concentration
theorem, NOT that theorem itself (which additionally requires the
Fourier semigroup, initial spectral access, and an argmax argument).
-/

namespace ReyesMath
namespace E16Core

/-- Fourier growth at squared wavenumber q. -/
def growth (r a b q : ℝ) : ℝ := r + a * q - b * q ^ 2

/-- Preferred squared wavenumber. -/
noncomputable def preferredQ (a b : ℝ) : ℝ := a / (2 * b)

/-- Exact completed-square identity for the linearized band-pass symbol. -/
theorem completed_square (r a b q : ℝ) (hb : b ≠ 0) :
    growth r a b q =
      (r + a ^ 2 / (4 * b)) - b * (q - preferredQ a b) ^ 2 := by
  unfold growth preferredQ
  field_simp [hb]
  ring

/-- Exact loss of spectral growth at q relative to the preferred mode. -/
theorem growth_gap (r a b q : ℝ) (hb : b ≠ 0) :
    growth r a b (preferredQ a b) - growth r a b q =
      b * (q - preferredQ a b) ^ 2 := by
  rw [completed_square r a b q hb,
      completed_square r a b (preferredQ a b) hb]
  ring

/-- The preferred squared wavenumber is positive for positive coefficients. -/
theorem preferredQ_pos (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    0 < preferredQ a b := by
  unfold preferredQ
  exact div_pos ha (by positivity)

/-- Unique global maximizer of the *continuous symbol*, without yet
claiming convergence of the full Fourier-power distribution. -/
theorem unique_symbol_maximum (r a b q : ℝ)
    (hb : 0 < b) :
    growth r a b q ≤ growth r a b (preferredQ a b) ∧
      (growth r a b q = growth r a b (preferredQ a b) ↔
        q = preferredQ a b) := by
  have hgap := growth_gap r a b q (ne_of_gt hb)
  have hp : 0 ≤ b * (q - preferredQ a b) ^ 2 :=
    mul_nonneg (le_of_lt hb) (sq_nonneg _)
  constructor
  · linarith
  · constructor
    · intro heq
      have hzero : b * (q - preferredQ a b) ^ 2 = 0 := by
        linarith
      have hsquare : (q - preferredQ a b) ^ 2 = 0 :=
        (mul_eq_zero.mp hzero).resolve_left (ne_of_gt hb)
      have hdiff : q - preferredQ a b = 0 := pow_eq_zero hsquare
      linarith
    · intro h
      rw [h]

end E16Core
end ReyesMath
