import Mathlib
import MathProofs.M6BMass

/-!
# M6B: exact mass of the two smooth stationary fields on (0,π)×(0,π)

The mass is the genuinely iterated Lebesgue integral of |ψ(x,y)|²
over the square, with no discretization or sampled approximation.
The ordinary product Lebesgue measure representation follows from Fubini.
-/

noncomputable section
open Real
namespace ReyesMath.M6B

def squareMass (ψ : ℝ → ℝ → ℂ) : ℝ :=
  ∫ x in (0 : ℝ)..Real.pi,
    ∫ y in (0 : ℝ)..Real.pi, Complex.normSq (ψ x y)

/-- The actual inner integral of the squared amplitude at every x. -/
theorem squarePlus_inner_mass (c x : ℝ) :
    (∫ y in (0 : ℝ)..Real.pi, Complex.normSq (squarePlus c x y)) =
      c ^ 2 * (Real.sin x ^ 2 * (Real.pi / 2) +
        Real.sin (2 * x) ^ 2 * (Real.pi / 2)) := by
  simp_rw [square_normSq_formula]
  have hpoint (y : ℝ) :
      c ^ 2 * (Real.sin x ^ 2 * Real.sin (2 * y) ^ 2 +
        Real.sin (2 * x) ^ 2 * Real.sin y ^ 2) =
      (c ^ 2 * Real.sin x ^ 2) * Real.sin (2 * y) ^ 2 +
        (c ^ 2 * Real.sin (2 * x) ^ 2) * Real.sin y ^ 2 := by ring
  simp_rw [hpoint]
  rw [intervalIntegral.integral_add]
  · simp only [intervalIntegral.integral_const_mul]
    rw [sin_sq_two_integral, sin_sq_one_integral]
    ring
  · apply Continuous.intervalIntegrable
    fun_prop
  · apply Continuous.intervalIntegrable
    fun_prop

/-- Exact L² mass identity on the full bounded square. -/
theorem squarePlus_mass (c : ℝ) :
    squareMass (squarePlus c) = c ^ 2 * Real.pi ^ 2 / 2 := by
  unfold squareMass
  simp_rw [squarePlus_inner_mass]
  have hpoint (x : ℝ) :
      c ^ 2 * (Real.sin x ^ 2 * (Real.pi / 2) +
        Real.sin (2 * x) ^ 2 * (Real.pi / 2)) =
      (c ^ 2 * (Real.pi / 2)) *
        (Real.sin x ^ 2 + Real.sin (2 * x) ^ 2) := by ring
  simp_rw [hpoint]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add]
  · rw [sin_sq_one_integral, sin_sq_two_integral]
    ring
  · apply Continuous.intervalIntegrable
    fun_prop
  · apply Continuous.intervalIntegrable
    fun_prop

/-- The opposite-phase field has precisely the same square L² mass. -/
theorem squareMinus_mass (c : ℝ) :
    squareMass (squareMinus c) = c ^ 2 * Real.pi ^ 2 / 2 := by
  unfold squareMass
  simp_rw [← square_intensity_eq]
  exact squarePlus_mass c

/-- The manuscript's mass-normalizing amplitude for every prescribed
m>0 (not a single numerically selected mass). -/
def amplitude (m : ℝ) : ℝ := Real.sqrt (2 * m) / Real.pi

theorem amplitude_pos (m : ℝ) (hm : 0 < m) :
    0 < amplitude m := by
  unfold amplitude
  positivity

theorem squarePlus_prescribed_mass (m : ℝ) (hm : 0 < m) :
    squareMass (squarePlus (amplitude m)) = m := by
  rw [squarePlus_mass]
  unfold amplitude
  have hsq : (Real.sqrt (2 * m)) ^ 2 = 2 * m :=
    Real.sq_sqrt (by positivity)
  rw [div_pow, hsq]
  field_simp [ne_of_gt Real.pi_pos]
  ring

theorem squareMinus_prescribed_mass (m : ℝ) (hm : 0 < m) :
    squareMass (squareMinus (amplitude m)) = m := by
  rw [squareMinus_mass, ← squarePlus_mass]
  exact squarePlus_prescribed_mass m hm

end ReyesMath.M6B
