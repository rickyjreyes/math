import MathProofs.RemainingCores

/-!
# M2/E17: corrected phase-covariant regularization, algebraic core

The corrected modulus-squared denominator depends only on ‖z‖²;
it is positive for each epsilon > 0 and remains unchanged under any
global unit-modulus phase. The regularized complex reciprocal therefore
transforms with conjugate phase. This is a proof about the actual
complex-valued regularizer, not a scalar-only surrogate and not yet the
manuscript's entire smoothness/singular-limit theorem.
-/

namespace ReyesMath
namespace E17PhaseRegularizer

open RemainingCores

/-- The corrected denominator at an exact field node is ε². -/
theorem denominator_at_zero (ε α : ℝ) :
    correctedDenominator ε α (0 : ℂ) = ε ^ 2 := by
  simp [correctedDenominator]

/-- Every unit-modulus complex rotation preserves the corrected denominator. -/
theorem denominator_phase_invariant (ε α : ℝ) (phase z : ℂ)
    (hphase : ‖phase‖ = 1) :
    correctedDenominator ε α (phase * z) =
      correctedDenominator ε α z := by
  simp [correctedDenominator, norm_mul, hphase]

/-- Corrected complex reciprocal with the conjugated numerator. -/
noncomputable def correctedReciprocal (ε α : ℝ) (z : ℂ) : ℂ :=
  star z / (correctedDenominator ε α z : ℂ)

/-- The corrected reciprocal is exactly zero at any field node. -/
theorem reciprocal_at_zero (ε α : ℝ) :
    correctedReciprocal ε α (0 : ℂ) = 0 := by
  simp [correctedReciprocal]

/-- The genuine regularized complex reciprocal is U(1)-covariant. -/
theorem reciprocal_phase_covariant (ε α : ℝ) (phase z : ℂ)
    (hphase : ‖phase‖ = 1) :
    correctedReciprocal ε α (phase * z) =
      star phase * correctedReciprocal ε α z := by
  unfold correctedReciprocal
  rw [denominator_phase_invariant ε α phase z hphase]
  rw [star_mul]
  ring

end E17PhaseRegularizer
end ReyesMath
