import Mathlib
import MathProofs.M6BClosureTheorem
import MathProofs.M6BDirichletLaplacian
import MathProofs.M6BSmooth

/-!
# M6B: distinct constitutive closures on an actual smooth continuum field

The original closure-family theorem proves pairwise nonidentity as
functions of complex jets. Here the difference is also witnessed by
the *actual Cartesian Laplacian* of a globally smooth complex field.
No independent Laplacian jet is supplied as an assumption.
-/

noncomputable section
namespace ReyesMath.M6B

/-- The manuscript's smooth Dirichlet mode evaluates to one
at its first interior witness point. -/
private theorem actual_field_at_P :
    squarePlus 1 (Real.pi / 2) (Real.pi / 4) = 1 := by
  have hf : squareModeF (Real.pi / 2) (Real.pi / 4) = 1 := by
    unfold squareModeF
    have h : (2 : ℝ) * (Real.pi / 4) = Real.pi / 2 := by ring
    rw [h]
    norm_num
  have hg : squareModeG (Real.pi / 2) (Real.pi / 4) = 0 := by
    unfold squareModeG
    have h : (2 : ℝ) * (Real.pi / 2) = Real.pi := by ring
    rw [h, Real.sin_pi]
    ring
  simpa [squarePlus, hf, hg]

/-- The real-linear source-slot dependence of the exact curvature
quotient is a derived identity of its actual formula. -/
private theorem curvature_linear_in_laplacian
    (ε α lam S : ℝ) (z w t : ℂ) :
    curvature ε α lam S z (t * w) =
      t * curvature ε α lam S z w := by
  unfold curvature
  ring

/-- For any two distinct admissible regularizations, the curvature
images differ *on an actual globally smooth Dirichlet field* at an
interior point, using the field's computed continuum Laplacian.
In particular, the operator-family distinction is not merely a
formally chosen pair of independent jet coordinates. -/
theorem distinct_closures_on_actual_smooth_field
    (ε α S lam mu : ℝ)
    (hε : 0 < ε) (hS : 0 < S) (hne : lam ≠ mu) :
    ∃ (ψ : ℝ → ℝ → ℂ) (x y : ℝ),
      ContDiff ℝ ⊤ (fun p : ℝ × ℝ => ψ p.1 p.2) ∧
      curvature ε α lam S (ψ x y) (laplaceComplex ψ x y) ≠
        curvature ε α mu S (ψ x y) (laplaceComplex ψ x y) := by
  have hdist :=
    curvature_family_pairwise_distinct ε α S lam mu hε hS hne
  have hlam : curvature ε α lam S 1 (-5) =
      (-5 : ℂ) * curvature ε α lam S 1 1 := by
    simpa using
      (curvature_linear_in_laplacian ε α lam S 1 1 (-5))
  have hmu : curvature ε α mu S 1 (-5) =
      (-5 : ℂ) * curvature ε α mu S 1 1 := by
    simpa using
      (curvature_linear_in_laplacian ε α mu S 1 1 (-5))
  have hneq :
      curvature ε α lam S 1 (-5) ≠
        curvature ε α mu S 1 (-5) := by
    intro he
    rw [hlam, hmu] at he
    exact hdist (mul_left_cancel₀ (by norm_num : (-5 : ℂ) ≠ 0) he)
  refine ⟨squarePlus 1, Real.pi / 2, Real.pi / 4,
    squarePlus_smooth 1, ?_⟩
  simp only [squarePlus_laplace, actual_field_at_P, mul_one]
  exact hneq

end ReyesMath.M6B
