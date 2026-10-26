import Mathlib

/-!
# Exact roots of the ultraviolet quadratic dispersion equation

The algebraic characteristic roots are formalized for any complex radical\nwhose square equals the discriminant.
This is not yet a formal proof of unbounded Sobolev evolution: quantitative
high-frequency growth and operator-norm divergence remain outstanding.
-/

namespace ReyesMath

private def ultravioletPolynomial (z q : ℂ) : ℂ :=
  (z - q) - (z - q) ^ 2 - q ^ 2

private noncomputable def ultravioletRootPlus (q r : ℂ) : ℂ :=
  q + (1 + r) / 2

private noncomputable def ultravioletRootMinus (q r : ℂ) : ℂ :=
  q + (1 - r) / 2

/-- The explicit plus branch is a root of the exact complex dispersion. -/
theorem ultraviolet_plus_root_exact (q r : ℂ)
    (hsq : r ^ 2 = 1 - 4 * q ^ 2) :
    ultravioletPolynomial (ultravioletRootPlus q r) q = 0 := by
  calc
    ultravioletPolynomial (ultravioletRootPlus q r) q =
      ((1 - 4 * q ^ 2) - r ^ 2) / 4 := by
        dsimp [ultravioletPolynomial, ultravioletRootPlus]
        ring
    _ = 0 := by rw [hsq]; ring

/-- The explicit minus branch is also a root, including complex-frequency
domains above the real discriminant threshold. -/
theorem ultraviolet_minus_root_exact (q r : ℂ)
    (hsq : r ^ 2 = 1 - 4 * q ^ 2) :
    ultravioletPolynomial (ultravioletRootMinus q r) q = 0 := by
  calc
    ultravioletPolynomial (ultravioletRootMinus q r) q =
      ((1 - 4 * q ^ 2) - r ^ 2) / 4 := by
        dsimp [ultravioletPolynomial, ultravioletRootMinus]
        ring
    _ = 0 := by rw [hsq]; ring

end ReyesMath
