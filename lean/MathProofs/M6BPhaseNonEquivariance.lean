import Mathlib
import MathProofs.M6BClosureTheorem

/-!
# M6B: phase invariance is not phase equivariance

Proposition in section 4 of the manuscript. This is an explicit
nonzero admissible complex jet, not an assumption that the curvature
image is nonzero. The phase u=-1 is a valid constant U(1) rotation.
-/

noncomputable section

namespace ReyesMath.M6B

theorem canonical_curvature_one_nonzero (ε α : ℝ) (hε : 0 < ε) :
    curvature ε α 0 1 1 1 ≠ 0 := by
  have hden : denominator ε α 0 1 1 ≠ 0 :=
    (denominator_pos ε α 0 1 1 hε (by norm_num)
      (by norm_num) (by norm_num)).ne'
  have hdenC :
      ((denominator ε α 0 1 1 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hden
  unfold curvature
  apply div_ne_zero
  · norm_num
  · simpa only [Complex.normSq_one] using hdenC

/-- Invariance under U(1) holds, but equivariance under the same
output phase fails already at the concrete jet (1,1) and u=-1. -/
theorem phase_invariant_not_equivariant (ε α : ℝ) (hε : 0 < ε) :
    curvature ε α 0 1 ((-1 : ℂ) * 1) ((-1 : ℂ) * 1) =
      curvature ε α 0 1 1 1 ∧
    curvature ε α 0 1 ((-1 : ℂ) * 1) ((-1 : ℂ) * 1) ≠
      (-1 : ℂ) * curvature ε α 0 1 1 1 := by
  have heq := curvature_phase_invariant ε α 0 1 (-1 : ℂ) 1 1 (by norm_num)
  refine ⟨heq, ?_⟩
  intro hequiv
  have hz : curvature ε α 0 1 1 1 =
      -curvature ε α 0 1 1 1 := by
    calc
      curvature ε α 0 1 1 1 =
          curvature ε α 0 1 ((-1 : ℂ) * 1) ((-1 : ℂ) * 1) := heq.symm
      _ = (-1 : ℂ) * curvature ε α 0 1 1 1 := hequiv
      _ = -curvature ε α 0 1 1 1 := by ring
  have hzero : curvature ε α 0 1 1 1 = 0 := by
    have hmul : (2 : ℂ) * curvature ε α 0 1 1 1 = 0 := by
      calc
        _ = curvature ε α 0 1 1 1 + curvature ε α 0 1 1 1 := by ring
        _ = 0 := by
          have hsum : curvature ε α 0 1 1 1 + curvature ε α 0 1 1 1 =
              curvature ε α 0 1 1 1 + -curvature ε α 0 1 1 1 :=
            congrArg (fun z : ℂ => curvature ε α 0 1 1 1 + z) hz
          simpa only [add_neg_cancel_right] using hsum
    rcases mul_eq_zero.mp hmul with h2 | h0
    · norm_num at h2
    · exact h0
  exact canonical_curvature_one_nonzero ε α hε hzero

end ReyesMath.M6B
