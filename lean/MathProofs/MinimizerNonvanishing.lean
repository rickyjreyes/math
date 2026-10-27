import MathProofs.NegativeEnergy

/-!
# A quantitative nonvanishing consequence for minimizing sequences (F01)

For the *actual* two-dimensional focusing-cubic/defocusing-quintic
fourth-order Hamiltonian, a state with energy at most I(m)/2, where
I(m) < 0, must have uniformly positive quartic norm.  This eliminates
quartic vanishing of near-minimizing sequences.

It does NOT establish the geometric concentration-compactness
nonvanishing lemma (the implication from local L² vanishing to
global L⁴ vanishing), exclude dichotomy, or prove strong H² compactness
modulo translations. The whole-space minimizer existence theorem
therefore remains open in Lean.
-/

namespace ReyesMath
namespace MinimizerNonvanishing

open MeasureTheory Sobolev

/-- The nonnegative sextic and dispersive terms force the actual
Hamiltonian to lie above its negative quartic contribution. -/
theorem energy_lower_bound_by_quartic (β γ k : ℝ) (hγ : 0 ≤ γ)
    (U : Sobolev.H2 2) :
    -(β / 2) * Sobolev.H2.Q U ≤ Sobolev.H2.energy β γ k U := by
  have hs : 0 ≤ Sobolev.H2.S U := by
    unfold Sobolev.H2.S
    exact integral_nonneg fun x => pow_nonneg (norm_nonneg _) _
  have ht : 0 ≤ ‖U.lap + ((k ^ 2 : ℝ) : ℂ) • U.val‖ ^ 2 :=
    sq_nonneg _
  unfold Sobolev.H2.energy
  have hsextic : 0 ≤ γ / 3 * Sobolev.H2.S U :=
    mul_nonneg (div_nonneg hγ (by norm_num)) hs
  linarith

/-- Uniform positive quartic contribution for any near-minimizer with
energy bounded above by half the negative constrained infimum. -/
theorem near_minimizer_quartic_lower_bound
    (β γ k m : ℝ) (hγ : 0 ≤ γ) (U : Sobolev.H2 2)
    (hE : Sobolev.H2.energy β γ k U ≤
      Sobolev.H2.Imin β γ k m / 2) :
    -(Sobolev.H2.Imin β γ k m) / 2 ≤
      β / 2 * Sobolev.H2.Q U := by
  have hl := energy_lower_bound_by_quartic β γ k hγ U
  linarith

theorem near_minimizer_quartic_positive
    (β γ k m : ℝ) (hγ : 0 ≤ γ) (U : Sobolev.H2 2)
    (hI : Sobolev.H2.Imin β γ k m < 0)
    (hE : Sobolev.H2.energy β γ k U ≤
      Sobolev.H2.Imin β γ k m / 2) :
    0 < β / 2 * Sobolev.H2.Q U := by
  have h := near_minimizer_quartic_lower_bound β γ k m hγ U hE
  linarith

end MinimizerNonvanishing
end ReyesMath
