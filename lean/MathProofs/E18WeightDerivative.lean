import MathProofs.E18FourierEnergy

/-!
# E18: exact nonlinear curvature-weight differentiation

This module proves the density derivative of the *actual* corrected E18
weight. It is not a substitute for a Fréchet derivative on H².

All derivatives are real derivatives in the density variable ρ ≥ 0,
with ε > 0. No unregularized or surrogate weight is used.
-/

open scoped Real
noncomputable section

namespace ReyesMath.E18WeightDerivative

open ReyesMath.E18FourierEnergy

/-- Ordinary first derivative of the corrected denominator. -/
def Dprime (ε α ρ : ℝ) : ℝ :=
  1 - 2 * α * ε ^ 2 * Real.exp (-2 * α * ρ)

/-- The exact E18 derivative of the curvature weight, including the
dependence of the regularizing exponential on the density. -/
def Fprime (ε α ρ : ℝ) : ℝ :=
  (ε ^ 2 * Real.exp (-2 * α * ρ) * (1 + 4 * α * ρ) - ρ) /
    (D ε α ρ) ^ 3

/-- Differentiation of D(ρ)=ρ+ε²exp(-2αρ). -/
theorem D_hasDerivAt (ε α ρ : ℝ) :
    HasDerivAt (D ε α) (Dprime ε α ρ) ρ := by
  have hlin : HasDerivAt (fun t : ℝ => (-2 * α) * t) (-2 * α) ρ := by
    simpa using (hasDerivAt_id ρ).const_mul (-2 * α)
  have hExp := hlin.exp
  have hMul := hExp.const_mul (ε ^ 2)
  have h := (hasDerivAt_id ρ).add hMul
  convert h using 1 <;> simp only [D, Dprime, id] <;> ring

/-- The raw quotient-rule formula for the weight. -/
def FprimeRaw (ε α ρ : ℝ) : ℝ :=
  ((D ε α ρ) ^ 2 - ρ * (2 * D ε α ρ * Dprime ε α ρ)) /
    ((D ε α ρ) ^ 2) ^ 2

/-- Apply the real quotient rule at each nonnegative density. -/
theorem F_hasDerivAt_raw {ε ρ : ℝ} (hε : 0 < ε) (hρ : 0 ≤ ρ) (α : ℝ) :
    HasDerivAt (F ε α) (FprimeRaw ε α ρ) ρ := by
  have hD := D_hasDerivAt ε α ρ
  have hD2 := hD.pow 2
  have hden : (D ε α ρ) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (ne_of_gt (D_pos hε hρ α))
  have h := (hasDerivAt_id ρ).div hD2 hden
  convert h using 1 <;> simp only [F, FprimeRaw, one_mul, Pi.pow_apply, id,
    Nat.reduceSub, pow_one] <;>
    field_simp [ne_of_gt (D_pos hε hρ α)] <;> ring

/-- Algebraic cancellation of the positive denominator gives the boxed
F'(ρ) formula in the E18 manuscript. -/
theorem FprimeRaw_eq (ε α ρ : ℝ) (hD : D ε α ρ ≠ 0) :
    FprimeRaw ε α ρ = Fprime ε α ρ := by
  unfold FprimeRaw Fprime
  field_simp [hD]
  unfold D Dprime
  ring

/-- Exact real derivative of F at every nonnegative density, with no
frozen-weight approximation. -/
theorem F_hasDerivAt {ε ρ : ℝ} (hε : 0 < ε) (hρ : 0 ≤ ρ) (α : ℝ) :
    HasDerivAt (F ε α) (Fprime ε α ρ) ρ := by
  rw [← FprimeRaw_eq ε α ρ (ne_of_gt (D_pos hε hρ α))]
  exact F_hasDerivAt_raw hε hρ α

end ReyesMath.E18WeightDerivative
