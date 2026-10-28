import Mathlib
import MathProofs.M6BForcing
import MathProofs.M6BFubini
import MathProofs.M6BClosureTheorem

/-!
# Exact quantifier-level M6B manuscript counterexamples

The PDE statement is in the actual bounded open square and the L²
norm is the two-dimensional product Lebesgue integral (via Fubini).
The source is explicit, real-valued and C∞. All parameters are
universally quantified, including arbitrary positive mass.

These are stationary statements, never evolution nonuniqueness.
-/

noncomputable section

namespace ReyesMath.M6B

def squareInterior (x y : ℝ) : Prop :=
  0 < x ∧ x < Real.pi ∧ 0 < y ∧ y < Real.pi

/-- The two designated witness points belong to the actual open square. -/
private theorem pointP_interior :
    squareInterior (Real.pi / 2) (Real.pi / 4) := by
  unfold squareInterior
  have hp := Real.pi_pos
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

private theorem pointQ_interior :
    squareInterior (Real.pi / 4) (Real.pi / 2) := by
  unfold squareInterior
  have hp := Real.pi_pos
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- Inequivalence is shown *inside the open square*, not only by
quantifying over points outside the PDE's prescribed domain. -/
theorem stationary_not_phase_related_on_square (m : ℝ) (hm : 0 < m) :
    ¬ ∃ u : ℂ, ∀ x y : ℝ, squareInterior x y →
      squareMinus (amplitude m) x y =
        u * squarePlus (amplitude m) x y := by
  rintro ⟨u, h⟩
  have hP := h (Real.pi / 2) (Real.pi / 4) pointP_interior
  have hQ := h (Real.pi / 4) (Real.pi / 2) pointQ_interior
  have hP' : ((amplitude m : ℝ) : ℂ) =
      u * ((amplitude m : ℝ) : ℂ) := by
    simpa [squarePlus, squareMinus, squareModeF, squareModeG,
      Real.sin_pi, Real.sin_pi_div_two] using hP
  have hc : ((amplitude m : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (amplitude_pos m hm))
  have hu : u = 1 := by
    have hh : (u - 1) * ((amplitude m : ℝ) : ℂ) = 0 := by
      calc
        _ = u * ((amplitude m : ℝ) : ℂ) -
          ((amplitude m : ℝ) : ℂ) := by ring
        _ = 0 := by rw [← hP']; ring
    rcases mul_eq_zero.mp hh with hh | hh
    · exact sub_eq_zero.mp hh
    · exact False.elim (hc hh)
  rw [hu, one_mul] at hQ
  have him := congrArg Complex.im hQ
  have ha : amplitude m ≠ 0 := ne_of_gt (amplitude_pos m hm)
  simp [squareMinus, squarePlus, squareModeF, squareModeG,
    Real.sin_pi, Real.sin_pi_div_two] at him
  exact ha (by linarith)

/-- The exact manuscript stationary theorem, including an explicit
real smooth source, the actual Ω-product-Lebesgue L² mass, pointwise
stationary PDE on Ω, smooth global extensions and Dirichlet conditions,
and non-equivalence under any global complex phase *on Ω*. -/
theorem manuscript_stationary_noninjectivity
    (ε α m : ℝ) (hε : 0 < ε) (hm : 0 < m) :
    ∃ F : ℝ × ℝ → ℝ,
      ContDiff ℝ ⊤ F ∧
      ∃ ψ₊ ψ₋ : ℝ → ℝ → ℂ,
        ContDiff ℝ ⊤ (fun p : ℝ × ℝ => ψ₊ p.1 p.2) ∧
        ContDiff ℝ ⊤ (fun p : ℝ × ℝ => ψ₋ p.1 p.2) ∧
        planarSquareMass ψ₊ = m ∧
        planarSquareMass ψ₋ = m ∧
        (∀ x y : ℝ, squareInterior x y →
          canonicalStationaryMap ε α ψ₊ x y = (F (x, y) : ℂ) ∧
          canonicalStationaryMap ε α ψ₋ x y = (F (x, y) : ℂ)) ∧
        (∀ x y : ℝ, onSquareEdge x y →
          ψ₊ x y = 0 ∧ ψ₋ x y = 0) ∧
        ¬ ∃ u : ℂ, ∀ x y : ℝ, squareInterior x y →
          ψ₋ x y = u * ψ₊ x y := by
  refine ⟨prescribedForcing ε α m, prescribedForcing_smooth ε α m hε,
    squarePlus (amplitude m), squareMinus (amplitude m),
    squarePlus_smooth (amplitude m), squareMinus_smooth (amplitude m),
    squarePlus_planar_prescribed_mass m hm,
    squareMinus_planar_prescribed_mass m hm, ?_, ?_, ?_⟩
  · intro x y _
    exact ⟨stationary_plus_has_prescribed_forcing ε α m x y,
      stationary_minus_has_prescribed_forcing ε α m x y⟩
  · intro x y hedge
    exact square_fields_dirichlet (amplitude m) x y hedge
  · exact stationary_not_phase_related_on_square m hm

end ReyesMath.M6B
