import MathProofs.V18BlockJacobian
import MathProofs.V18HeavyJacobian

/-!
# Frozen v18 remaining exact trigonometric middle-sector determinant

The observations at n=12,19,53,73,91 and selected parameters
(offset, quad, amplitude, phase, harmonic) determine the following
5x5 real analytic Jacobian block, with the frozen decimal constants
read as exact rational coefficients.

Theorems below reduce the full 31-to-11 model-specific Jacobian rank
certificate to one explicit real inequality: middle.det ≠ 0.

No extra sin/cos nonvanishing is assumed for the previously certified
light and heavy 3x3 blocks. The remaining middle determinant inequality
has only been checked externally by outward-rounded interval arithmetic
and is NOT asserted as a Lean theorem here.
-/

noncomputable section
namespace ReyesMath.V18MiddleJacobian

def middle : Matrix (Fin 5) (Fin 5) ℝ :=
  !![(1 : ℝ), 144, Real.sin ((5.0632 : ℝ) * 12 + 1.6469),
       (2241.1 : ℝ) * Real.cos ((5.0632 : ℝ) * 12 + 1.6469),
       Real.sin ((9.4062 : ℝ) * 12);
     1, 361, Real.sin ((5.0632 : ℝ) * 19 + 1.6469),
       (2241.1 : ℝ) * Real.cos ((5.0632 : ℝ) * 19 + 1.6469),
       Real.sin ((9.4062 : ℝ) * 19);
     1, 2809, Real.sin ((5.0632 : ℝ) * 53 + 1.6469),
       (2241.1 : ℝ) * Real.cos ((5.0632 : ℝ) * 53 + 1.6469),
       Real.sin ((9.4062 : ℝ) * 53);
     1, 5329, Real.sin ((5.0632 : ℝ) * 73 + 1.6469),
       (2241.1 : ℝ) * Real.cos ((5.0632 : ℝ) * 73 + 1.6469),
       Real.sin ((9.4062 : ℝ) * 73);
     1, 8281, Real.sin ((5.0632 : ℝ) * 91 + 1.6469),
       (2241.1 : ℝ) * Real.cos ((5.0632 : ℝ) * 91 + 1.6469),
       Real.sin ((9.4062 : ℝ) * 91)]

/-- Exactly one remaining middle determinant proof implies
nonvanishing of the full frozen selected analytic 11x11 minor,
independently of the unspecified lower-left derivative blocks. -/
theorem full_minor_ne_zero_of_middle_det
    (alpha epsilon : ℝ)
    (A : Matrix ((Fin 5) ⊕ (Fin 3)) (Fin 3) ℝ)
    (B : Matrix (Fin 3) (Fin 5) ℝ)
    (hmiddle : middle.det ≠ 0) :
    (V18BlockJacobian.minor
      (V18LightJacobian.minor alpha epsilon)
      middle V18HeavyJacobian.heavy A B).det ≠ 0 :=
  V18BlockJacobian.v18_minor_ne_zero_of_middle_heavy
    alpha epsilon middle V18HeavyJacobian.heavy A B
    hmiddle V18HeavyJacobian.heavy_det_ne_zero

end ReyesMath.V18MiddleJacobian
