import MathProofs.E18WeightDerivative

/-!
# E18 exact complex first-variation algebra

The following pointwise identities are the algebraic components of the
full infinite-dimensional E18 Fréchet remainder estimate. They are NOT
the Fréchet derivative or periodic integration by parts theorem.
-/

namespace ReyesMath.E18VariationAlgebra

/-- Squared complex modulus under a perturbation. This formula is the
real tangent-space version, not a holomorphic derivative. -/
theorem norm_sq_add (z h : ℂ) :
    ‖z + h‖ ^ 2 =
      ‖z‖ ^ 2 + 2 * (Complex.conj z * h).re + ‖h‖ ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
    ← Complex.normSq_eq_norm_sq, Complex.normSq_add]
  have hsym : (z * Complex.conj h).re = (Complex.conj z * h).re := by
    rw [← Complex.conj_re (z * Complex.conj h), map_mul, Complex.conj_conj]
  rw [hsym]
  ring

/-- Density variation: the omitted portion after the real-linear
first variation is exactly |h|². -/
theorem density_remainder (ψ h : ℂ) :
    ‖ψ + h‖ ^ 2 - ‖ψ‖ ^ 2 -
      2 * (Complex.conj ψ * h).re = ‖h‖ ^ 2 := by
  rw [norm_sq_add]
  ring

/-- Laplacian-density variation, with variables q=Δψ and r=Δh. -/
theorem laplacian_density_remainder (q r : ℂ) :
    ‖q + r‖ ^ 2 - ‖q‖ ^ 2 -
      2 * (Complex.conj q * r).re = ‖r‖ ^ 2 :=
  density_remainder q r

/--
Exact six-term remainder for a variable curvature weight.

Use w=F(|ψ|²), dw=F'(|ψ|²)·2Re(conj ψ h), and
B=F(|ψ+h|²)-w-dw. Thus this identity tracks all nonlinear-weight
cross terms rather than freezing w during differentiation.
-/
theorem weighted_laplacian_remainder
    (w dw B : ℝ) (q r : ℂ) :
    (w + dw + B) * ‖q + r‖ ^ 2 - w * ‖q‖ ^ 2 -
      (2 * w * (Complex.conj q * r).re + dw * ‖q‖ ^ 2) =
        w * ‖r‖ ^ 2 +
        2 * dw * (Complex.conj q * r).re +
        dw * ‖r‖ ^ 2 +
        B * ‖q‖ ^ 2 +
        2 * B * (Complex.conj q * r).re +
        B * ‖r‖ ^ 2 := by
  rw [norm_sq_add]
  ring

end ReyesMath.E18VariationAlgebra
