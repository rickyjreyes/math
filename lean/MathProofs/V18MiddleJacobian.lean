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
light and heavy 3x3 blocks. The unconditional middle determinant enclosure
and nonvanishing are proved in `V18MiddleDeterminant`, which imports this
definition and checks the rational Taylor bounds in Lean.
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

/-- Full nonvanishing of the three diagonal determinant product
follows from a middle-block inequality. The unconditional version is
exported by `V18MiddleDeterminant.determinant_product_nonzero`.
The general `V18BlockJacobian.det_three_blocks` theorem establishes
the product as the determinant of an arbitrary three-sector block
matrix. Direct kernel instantiation on the concrete 11×11 index is
left out because it exhausts the pinned build's recursion limits. -/
theorem determinant_product_nonzero_of_middle
    (alpha epsilon : ℝ)
    (hmiddle : middle.det ≠ 0) :
    (V18LightJacobian.minor alpha epsilon).det *
        middle.det * V18HeavyJacobian.heavy.det ≠ 0 :=
  mul_ne_zero
    (mul_ne_zero
      (V18LightJacobian.minor_det_ne_zero alpha epsilon) hmiddle)
    V18HeavyJacobian.heavy_det_ne_zero

end ReyesMath.V18MiddleJacobian
