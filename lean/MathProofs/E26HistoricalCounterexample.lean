import MathProofs.RemainingCores

/-!
# E26: non-separation of the historical additive denominator

The historical curvature regularizer z + ε exp(-α|z|²) is not
the corrected M2/E17 modulus-squared denominator. Even when ε > 0,
it can vanish for smooth signed real data; this already rules out
a universal positive denominator separation assumption. The stronger
Sobolev L² divergence counterexample is a separate obligation.
-/

namespace ReyesMath
namespace E26HistoricalCounterexample

/-- The historical additive complex-valued denominator. -/
noncomputable def additiveDenominator (ε α : ℝ) (z : ℂ) : ℂ :=
  z + ((ε * Real.exp (-α * ‖z‖ ^ 2) : ℝ) : ℂ)

/-- With α=0, the signed complex value z=-ε is a true denominator zero. -/
theorem additiveDenominator_zero_at_negative (ε : ℝ) :
    additiveDenominator ε 0 (-(ε : ℂ)) = 0 := by
  simp [additiveDenominator]

/-- A positive ε alone cannot imply a positive lower bound on
the modulus of the historical denominator for *all* complex values. -/
theorem no_global_separation_for_historical_denominator (ε : ℝ)
    (hε : 0 < ε) :
    ¬ ∃ δ : ℝ, 0 < δ ∧
      ∀ z : ℂ, δ ≤ ‖additiveDenominator ε 0 z‖ := by
  rintro ⟨δ, hδ, hsep⟩
  have h := hsep (-(ε : ℂ))
  rw [additiveDenominator_zero_at_negative, norm_zero] at h
  linarith

end E26HistoricalCounterexample
end ReyesMath
