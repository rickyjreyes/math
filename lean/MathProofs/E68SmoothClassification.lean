import Mathlib
import MathProofs.E68SmoothCounterexample

/-!
# E68 dimensional classification on genuine smooth compactly supported fields

The entire analysis below concerns actual functions on Euclidean space and
actual Lebesgue ball integrals. It does not assert the full equivalence-class
H¹ classification, which still requires the singular H¹ witness, weak-gradient
bridges and the remaining E68' and H² theorems.
-/

noncomputable section

open MeasureTheory
open scoped ContDiff

namespace ReyesMath.E68

/-- The original E68 quantifier order on the C∞ compactly supported
real subclass: one constant works for every field, center, and radius. -/
def SmoothE68 (n : ℕ) : Prop :=
  ∃ C : ℝ, ∀ (ψ : EuclideanSpace ℝ (Fin n) → ℝ),
    ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
    ∀ (center : EuclideanSpace ℝ (Fin n)) (R : ℝ), 0 < R →
      (∫ x in Metric.ball center R, ‖fderiv ℝ ψ x‖ ^ 2) ≤
        C * R ^ (n - 2) *
          ((∫ x : EuclideanSpace ℝ (Fin n), (ψ x) ^ 2) +
           (∫ x : EuclideanSpace ℝ (Fin n), ‖fderiv ℝ ψ x‖ ^ 2))

/-- In dimension two, a smooth compact field has integrable derivative
energy and the sharp local-energy constant is one. -/
theorem smooth_two_dimensional_ball_energy
    (ψ : EuclideanSpace ℝ (Fin 2) → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hs : HasCompactSupport ψ)
    (center : EuclideanSpace ℝ (Fin 2)) (R : ℝ) (_hR : 0 < R) :
    (∫ x in Metric.ball center R, ‖fderiv ℝ ψ x‖ ^ 2) ≤
      (∫ x : EuclideanSpace ℝ (Fin 2), (ψ x) ^ 2) +
      (∫ x : EuclideanSpace ℝ (Fin 2), ‖fderiv ℝ ψ x‖ ^ 2) := by
  have hc : Continuous (fun x : EuclideanSpace ℝ (Fin 2) =>
      ‖fderiv ℝ ψ x‖ ^ 2) :=
    ((hψ.continuous_fderiv (by simp)).norm.pow 2)
  have hcompact : HasCompactSupport
      (fun x : EuclideanSpace ℝ (Fin 2) => ‖fderiv ℝ ψ x‖ ^ 2) := by
    have hnorm : HasCompactSupport
        (fun x : EuclideanSpace ℝ (Fin 2) => ‖fderiv ℝ ψ x‖) :=
      (hs.fderiv ℝ).norm
    simpa [pow_two, Pi.mul_apply] using
      hnorm.mul_right (f' := fun x : EuclideanSpace ℝ (Fin 2) =>
        ‖fderiv ℝ ψ x‖)
  have hi : Integrable
      (fun x : EuclideanSpace ℝ (Fin 2) => ‖fderiv ℝ ψ x‖ ^ 2) :=
    hc.integrable_of_hasCompactSupport hcompact
  have hlocal :
      (∫ x in Metric.ball center R, ‖fderiv ℝ ψ x‖ ^ 2) ≤
        (∫ x : EuclideanSpace ℝ (Fin 2), ‖fderiv ℝ ψ x‖ ^ 2) :=
    setIntegral_le_integral hi
      (Filter.Eventually.of_forall (fun x => sq_nonneg (‖fderiv ℝ ψ x‖)))
  have hmass : 0 ≤
      (∫ x : EuclideanSpace ℝ (Fin 2), (ψ x) ^ 2) :=
    integral_nonneg (fun x => sq_nonneg (ψ x))
  linarith

theorem smoothE68_two : SmoothE68 2 := by
  refine ⟨1, ?_⟩
  intro ψ hψ hs center R hR
  simpa only [Nat.sub_self, pow_zero, mul_one, one_mul] using
    smooth_two_dimensional_ball_energy ψ hψ hs center R hR

/-- A smooth concentration disproves a uniform constant for every
C∞ compactly supported field, with no restrictions on the center. -/
theorem no_uniform_E68_on_smooth_fields
    (n : ℕ) (hn : 2 < n) : ¬ SmoothE68 n := by
  rintro ⟨C, hall⟩
  apply no_uniform_E68_for_smooth_concentrations n hn
  refine ⟨C, ?_⟩
  intro R hR
  exact hall (smoothConcentration n R)
    (smoothConcentration_smooth n R)
    (smoothConcentration_hasCompactSupport n R hR)
    0 R hR

/-- Sharp iff on the actual C∞ compact subclass for n ≥ 2.
Not a replacement for the full Sobolev H¹ iff theorem. -/
theorem smoothE68_iff_two (n : ℕ) (hn : 2 ≤ n) :
    SmoothE68 n ↔ n = 2 := by
  constructor
  · intro h
    by_contra hne
    have hgt : 2 < n := by omega
    exact (no_uniform_E68_on_smooth_fields n hgt) h
  · intro h
    subst n
    exact smoothE68_two

end ReyesMath.E68
