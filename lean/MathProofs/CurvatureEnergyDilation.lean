import Mathlib
import MathProofs.SobolevH2
import MathProofs.CurvatureUniformBound

/-!
# Exact nonlinear curvature-energy dilation on the whole-space H² model

For u in the existing Schwartz-graph H²(ℝ^d;ℂ) construction and
u_λ(x) = λ^(d/2)u(λx), the nonlinear term
  N(u) = ∫ F(|u|²)|Δu|²
scales EXACTLY as
  N(u_λ) = λ⁴ ∫ F(λ^d |u|²)|Δu|².

The statement involves the actual nonlinear weight and both H² field
components, not a surrogate polynomial energy. Constrained nonattainment
additionally requires integrability/boundedness and positivity arguments.
-/

namespace ReyesMath
namespace CurvatureEnergy

open MeasureTheory Sobolev
open Sobolev.H2

variable {d : ℕ}

/-- The actual positive curvature nonlinear integral on whole-space H². -/
noncomputable def N (ε α : ℝ) (U : Sobolev.H2 d) : ℝ :=
  ∫ x, positiveCurvatureWeight ε α (‖U.val x‖ ^ 2) * ‖U.lap x‖ ^ 2

/-- A real squared Laplacian after mass-preserving dilation scales
pointwise by λ^(d+4), before changing integration variables. -/
theorem nonlinear_integrand_dil_ae
    (ε α : ℝ) {lam : ℝ} (hlam : 0 < lam) (U : Sobolev.H2 d) :
    (fun x : EuclideanSpace ℝ (Fin d) =>
      positiveCurvatureWeight ε α (‖(Sobolev.H2.dil hlam U).val x‖ ^ 2) *
        ‖(Sobolev.H2.dil hlam U).lap x‖ ^ 2)
      =ᵐ[volume]
    (fun x : EuclideanSpace ℝ (Fin d) =>
      (lam ^ d * lam ^ 4) *
        (positiveCurvatureWeight ε α
          (lam ^ d * ‖U.val (lam • x)‖ ^ 2) *
            ‖U.lap (lam • x)‖ ^ 2)) := by
  filter_upwards [coeFn_dilL2 hlam U.val, coeFn_dilL2 hlam U.lap] with x hv hl
  simp only [Sobolev.H2.dil]
  rw [hv, hl, norm_smul, norm_dilF_sq hlam U.val,
    norm_dilF_sq hlam U.lap]
  simp only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (pow_pos hlam 2), mul_pow]
  ring

/-- Exact dilation for the genuinely nonlinear H² curvature integral. -/
theorem N_dil (ε α : ℝ) {lam : ℝ} (hlam : 0 < lam)
    (U : Sobolev.H2 d) :
    N ε α (Sobolev.H2.dil hlam U) =
      lam ^ 4 * ∫ y,
        positiveCurvatureWeight ε α (lam ^ d * ‖U.val y‖ ^ 2) *
          ‖U.lap y‖ ^ 2 := by
  unfold N
  rw [integral_congr_ae (nonlinear_integrand_dil_ae ε α hlam U),
      integral_const_mul, integral_comp_dil hlam]
  have hpow : (lam ^ d) ≠ 0 := ne_of_gt (pow_pos hlam _)
  field_simp
  ring

/-- Actual energy including the squared H² gradient and nonlinear
weighted Laplacian. -/
noncomputable def E (c₁ c₂ ε α : ℝ) (U : Sobolev.H2 d) : ℝ :=
  c₁ * Sobolev.H2.K U + c₂ * N ε α U

/-- The original manuscript's exact nonlinear energy scaling, in
all finite spatial dimensions, on genuine H² fields. -/
theorem E_dil (c₁ c₂ ε α : ℝ) {lam : ℝ} (hlam : 0 < lam)
    (U : Sobolev.H2 d) :
    E c₁ c₂ ε α (Sobolev.H2.dil hlam U) =
      c₁ * lam ^ 2 * Sobolev.H2.K U +
      c₂ * lam ^ 4 * ∫ y,
        positiveCurvatureWeight ε α (lam ^ d * ‖U.val y‖ ^ 2) *
          ‖U.lap y‖ ^ 2 := by
  rw [E, Sobolev.H2.K_dil, N_dil]
  ring

end CurvatureEnergy
end ReyesMath
