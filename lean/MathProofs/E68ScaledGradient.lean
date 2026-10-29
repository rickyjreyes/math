import Mathlib
import MathProofs.E68ChangeVariables

/-!
# E68: actual Fréchet-gradient energy under Euclidean dilation

This is an exact continuum result about the derivative of the *scaled
function*, not just a formal Jacobian or an algebraic exponent comparison.
For R>0 and n>=2, the actual full-space Lebesgue integral of the
squared operator norm of the Fréchet derivative scales by R^(n-2).

The paper's normalized concentration also includes an amplitude factor;
that additional normalization and local-ball support estimate remain
distinct obligations. This theorem supplies the needed analytic
change-of-variables and derivative chain-rule steps.
-/

noncomputable section
open MeasureTheory

namespace ReyesMath.E68

/-- Exact Fréchet chain rule for inverse Euclidean dilation. -/
theorem fderiv_inverse_smul
    (n : ℕ) (R : ℝ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fun y => f ((R⁻¹ : ℝ) • y)) x =
      (R⁻¹ : ℝ) • fderiv ℝ f ((R⁻¹ : ℝ) • x) := by
  exact fderiv_comp_smul (R⁻¹ : ℝ)

/-- Squared operator-norm energy density of the actual scaled function. -/
theorem squared_fderiv_inverse_smul
    (n : ℕ) (R : ℝ) (hR : 0 < R)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖fderiv ℝ (fun y => f ((R⁻¹ : ℝ) • y)) x‖ ^ 2 =
      (R⁻¹) ^ 2 * ‖fderiv ℝ f ((R⁻¹ : ℝ) • x)‖ ^ 2 := by
  rw [fderiv_inverse_smul n R f x, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hR)]
  ring

/-- Exact energy scaling of a genuine Fréchet derivative, including
the Lebesgue change of variables, for all dimensions n>=2. -/
theorem integral_scaled_gradient_energy
    (n : ℕ) (hn : 2 ≤ n) (R : ℝ) (hR : 0 < R)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    (∫ x : EuclideanSpace ℝ (Fin n),
      ‖fderiv ℝ (fun y => f ((R⁻¹ : ℝ) • y)) x‖ ^ 2) =
      R ^ (n - 2) *
        (∫ x : EuclideanSpace ℝ (Fin n), ‖fderiv ℝ f x‖ ^ 2) := by
  have hrne : R ≠ 0 := ne_of_gt hR
  calc
    (∫ x : EuclideanSpace ℝ (Fin n),
      ‖fderiv ℝ (fun y => f ((R⁻¹ : ℝ) • y)) x‖ ^ 2) =
      (∫ x : EuclideanSpace ℝ (Fin n),
        (R⁻¹) ^ 2 * ‖fderiv ℝ f ((R⁻¹ : ℝ) • x)‖ ^ 2) := by
          congr 1
          funext x
          exact squared_fderiv_inverse_smul n R hR f x
    _ = (R⁻¹) ^ 2 *
          (∫ x : EuclideanSpace ℝ (Fin n),
            ‖fderiv ℝ f ((R⁻¹ : ℝ) • x)‖ ^ 2) := by
          rw [integral_const_mul]
    _ = (R⁻¹) ^ 2 * (R ^ n *
          (∫ x : EuclideanSpace ℝ (Fin n), ‖fderiv ℝ f x‖ ^ 2)) := by
          have hInt := integral_inverse_smul_exact n R hR
            (fun z : EuclideanSpace ℝ (Fin n) => ‖fderiv ℝ f z‖ ^ 2)
          exact congrArg (fun t : ℝ => (R⁻¹) ^ 2 * t) hInt
    _ = R ^ (n - 2) *
          (∫ x : EuclideanSpace ℝ (Fin n), ‖fderiv ℝ f x‖ ^ 2) := by
          have hpow : R ^ n = R ^ (n - 2) * R ^ 2 := by
            conv_lhs => rw [← Nat.sub_add_cancel hn]
            rw [pow_add]
          rw [hpow]
          field_simp

/-- The exact compact smooth radial witness now satisfies the complete
unweighted gradient scaling identity with real Lebesgue integration. -/
theorem compactProfile_scaled_gradient_energy
    (n : ℕ) (hn : 2 ≤ n) (R : ℝ) (hR : 0 < R) :
    (∫ x : EuclideanSpace ℝ (Fin n),
      ‖fderiv ℝ (fun y =>
        compactProfile n ((R⁻¹ : ℝ) • y)) x‖ ^ 2) =
      R ^ (n - 2) *
        (∫ x : EuclideanSpace ℝ (Fin n),
          ‖fderiv ℝ (fun y => compactProfile n y) x‖ ^ 2) :=
  integral_scaled_gradient_energy n hn R hR (fun y => compactProfile n y)

/-- The squared L2 mass of an arbitrary real field, under spatial
inverse dilation and an independent real amplitude, has the exact
continuum Jacobian and amplitude factor. No discrete surrogate is
involved, and no differentiability is needed for this identity. -/
theorem integral_scaled_field_mass
    (n : ℕ) (R : ℝ) (hR : 0 < R) (a : ℝ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    (∫ x : EuclideanSpace ℝ (Fin n),
      (a * f ((R⁻¹ : ℝ) • x)) ^ 2) =
      a ^ 2 * R ^ n *
        (∫ x : EuclideanSpace ℝ (Fin n), (f x) ^ 2) := by
  calc
    (∫ x : EuclideanSpace ℝ (Fin n),
      (a * f ((R⁻¹ : ℝ) • x)) ^ 2) =
        (∫ x : EuclideanSpace ℝ (Fin n),
          a ^ 2 * (f ((R⁻¹ : ℝ) • x)) ^ 2) := by
            congr 1
            funext x
            ring
    _ = a ^ 2 * (∫ x : EuclideanSpace ℝ (Fin n),
            (f ((R⁻¹ : ℝ) • x)) ^ 2) := by
          rw [integral_const_mul]
    _ = a ^ 2 * (R ^ n *
          (∫ x : EuclideanSpace ℝ (Fin n), (f x) ^ 2)) := by
          rw [integral_inverse_smul_exact n R hR
            (fun x : EuclideanSpace ℝ (Fin n) => (f x) ^ 2)]
    _ = a ^ 2 * R ^ n *
          (∫ x : EuclideanSpace ℝ (Fin n), (f x) ^ 2) := by ring

/-- The actual paper's normalized concentration family satisfies the
exact global squared-mass integral identity in every dimension. -/
theorem smoothConcentration_mass_exact
    (n : ℕ) (R : ℝ) (hR : 0 < R) :
    (∫ x : EuclideanSpace ℝ (Fin n),
      (smoothConcentration n R x) ^ 2) =
      (R ^ (1 - (n : ℝ) / 2)) ^ 2 * R ^ n *
        (∫ x : EuclideanSpace ℝ (Fin n),
          (compactProfile n x) ^ 2) := by
  simpa only [smoothConcentration] using
    integral_scaled_field_mass n R hR
      (R ^ (1 - (n : ℝ) / 2))
      (fun x : EuclideanSpace ℝ (Fin n) => compactProfile n x)

end ReyesMath.E68
