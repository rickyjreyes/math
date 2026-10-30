import Mathlib
import MathProofs.M6BSquareMass
import MathProofs.M6BSmooth

/-!
# Exact M6B stationary counterexample package

This is the actual canonical nonlinear curvature operator evaluated
using the classical Cartesian Laplacian of the complex field.  The two
fields are global smooth extensions of the manuscript's Dirichlet-square
solutions.  The complete theorem includes pointwise equal curvature,
the prescribed positive L² mass (as exact iterated square integral),
homogeneous Dirichlet values and failure of phase equivalence.
-/

noncomputable section
namespace ReyesMath.M6B

/-- The actual canonical stationary curvature map with ε>0 and α real. -/
def canonicalStationaryMap (ε α : ℝ) (ψ : ℝ → ℝ → ℂ) (x y : ℝ) : ℂ :=
  curvature ε α 0 1 (ψ x y) (laplaceComplex ψ x y)

/-- Two explicitly constructed distinct stationary fields with the
same canonical nonlinear curvature, mass, and Dirichlet data. -/
theorem exact_stationary_counterexample
    (ε α m : ℝ) (hε : 0 < ε) (hm : 0 < m) :
    (∀ x y : ℝ,
      canonicalStationaryMap ε α (squarePlus (amplitude m)) x y =
      canonicalStationaryMap ε α (squareMinus (amplitude m)) x y) ∧
    (∀ x y : ℝ, onSquareEdge x y →
      squarePlus (amplitude m) x y = 0 ∧
      squareMinus (amplitude m) x y = 0) ∧
    squareMass (squarePlus (amplitude m)) = m ∧
    squareMass (squareMinus (amplitude m)) = m ∧
    ContDiff ℝ ⊤ (fun p : ℝ × ℝ =>
      squarePlus (amplitude m) p.1 p.2) ∧
    ContDiff ℝ ⊤ (fun p : ℝ × ℝ =>
      squareMinus (amplitude m) p.1 p.2) ∧
    ¬ ∃ u : ℂ, ∀ x y : ℝ,
      squareMinus (amplitude m) x y =
        u * squarePlus (amplitude m) x y := by
  refine ⟨?_, ?_, squarePlus_prescribed_mass m hm,
    squareMinus_prescribed_mass m hm,
    squarePlus_smooth (amplitude m),
    squareMinus_smooth (amplitude m), ?_⟩
  · intro x y
    exact stationary_curvature_equal ε α 1 (amplitude m) x y
  · intro x y hedge
    exact square_fields_dirichlet (amplitude m) x y hedge
  · exact square_not_related_by_constant_phase (amplitude m)
      (ne_of_gt (amplitude_pos m hm))

end ReyesMath.M6B
