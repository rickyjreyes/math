import Mathlib

/-!
# Exact roots of the ultraviolet quadratic dispersion equation

The algebraic characteristic roots are formalized over the complex numbers.
This is not yet a formal proof of unbounded Sobolev evolution: quantitative
high-frequency growth and operator-norm divergence remain outstanding.
-/

namespace ReyesMath

private def ultravioletPolynomial (z q : ℂ) : ℂ :=
  (z - q) - (z - q) ^ 2 - q ^ 2

private def ultravioletRootPlus (q : ℂ) : ℂ :=
  q + (1 + Complex.sqrt (1 - 4 * q ^ 2)) / 2

private def ultravioletRootMinus (q : ℂ) : ℂ :=
  q + (1 - Complex.sqrt (1 - 4 * q ^ 2)) / 2

/-- The explicit plus branch is a root of the exact complex dispersion. -/
theorem ultraviolet_plus_root_exact (q : ℂ) :
    ultravioletPolynomial (ultravioletRootPlus q) q = 0 := by
  have hsq : (Complex.sqrt (1 - 4 * q ^ 2)) ^ 2 = 1 - 4 * q ^ 2 :=
    Complex.sq_sqrt _
  calc
    ultravioletPolynomial (ultravioletRootPlus q) q =
      ((1 - 4 * q ^ 2) - (Complex.sqrt (1 - 4 * q ^ 2)) ^ 2) / 4 := by
        dsimp [ultravioletPolynomial, ultravioletRootPlus]
        ring
    _ = 0 := by rw [hsq]; ring

/-- The explicit minus branch is also a root, including complex-frequency
domains above the real discriminant threshold. -/
theorem ultraviolet_minus_root_exact (q : ℂ) :
    ultravioletPolynomial (ultravioletRootMinus q) q = 0 := by
  have hsq : (Complex.sqrt (1 - 4 * q ^ 2)) ^ 2 = 1 - 4 * q ^ 2 :=
    Complex.sq_sqrt _
  calc
    ultravioletPolynomial (ultravioletRootMinus q) q =
      ((1 - 4 * q ^ 2) - (Complex.sqrt (1 - 4 * q ^ 2)) ^ 2) / 4 := by
        dsimp [ultravioletPolynomial, ultravioletRootMinus]
        ring
    _ = 0 := by rw [hsq]; ring

end ReyesMath
