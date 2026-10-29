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

/-- The actual smooth polynomial field ψ(x)=x²−ε produces
the historical additive denominator D(x)=x² at α=0. -/
theorem polynomial_model_denominator (ε x : ℝ) :
    (x ^ 2 - ε) + ε * Real.exp (-0 * (x ^ 2 - ε) ^ 2) = x ^ 2 := by
  simp

/-- The genuine inverse-fourth-power energy density diverges
on the positive half of the bounded interval (-1,1).
This is an analytic part of the historical E26 smooth-field
counterexample; the full H² quotient-to-this-density bridge
must be proved before the manuscript can be certified. -/
theorem inverse_quartic_not_integrable :
    ¬ MeasureTheory.IntegrableOn
        (fun x : ℝ => x ^ (-4 : ℝ)) (Set.Ioo 0 1) := by
  intro hi
  have hc := (intervalIntegral.integrableOn_Ioo_rpow_iff
    (s := (-4 : ℝ)) (t := 1) (by norm_num)).mp hi
  norm_num at hc

/-- Away from its singularity, the exact polynomial counterexample
curvature has a quartic square, matching the divergent integrand. -/
theorem polynomial_curvature_square (x : ℝ) (hx : x ≠ 0) :
    (-2 / x ^ 2) ^ 2 = 4 / x ^ 4 := by
  field_simp [hx]
  ring


end E26HistoricalCounterexample
end ReyesMath
