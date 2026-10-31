import MathProofs.E18VariationAlgebra

/-!
# E18: verified first variation of the gradient-energy component

The corrected E18 energy consists of the positive H¹ gradient term and the
nonlinearly weighted H² curvature term. This file differentiates the former
on the actual Fourier H² torus model using the existing verified
BandPass.Dj continuous linear maps. The curvature contribution is NOT
silently frozen or included in this proof.
-/

open Filter Topology InnerProductSpace

noncomputable section

namespace ReyesMath.E18EnergyGradient

open ReyesMath.BandPass

variable {L : ℝ} [hL : Fact (0 < L)] {d : ℕ}

/-- The actual E18 gradient-energy summand with physical torus volume. -/
def gradientEnergy (c₁ : ℝ) (ψ : ell2 d) : ℝ :=
  L ^ d * (c₁ * ∑ j : Fin d, ‖Dj L j ψ‖ ^ 2)

/-- Real chain rule for the E18 gradient-energy summand on the Fourier H²
model, valid on arbitrary time-domain subsets. -/
theorem hasDerivWithinAt_gradientEnergy (c₁ : ℝ)
    {γ : ℝ → ell2 d} {γ' : ell2 d} {s : Set ℝ} {t : ℝ}
    (hγ : HasDerivWithinAt γ γ' s t) :
    HasDerivWithinAt (fun u => gradientEnergy (L := L) c₁ (γ u))
      (L ^ d * (c₁ * ∑ j : Fin d,
        2 * inner ℝ (Dj L j (γ t)) (Dj L j γ'))) s t := by
  have hj : ∀ j ∈ (Finset.univ : Finset (Fin d)),
      HasDerivWithinAt (fun u => ‖Dj L j (γ u)‖ ^ 2)
        (2 * inner ℝ (Dj L j (γ t)) (Dj L j γ')) s t :=
    fun j _ => (hasDerivWithinAt_clm (Dj L j) hγ).norm_sq
  have hsum : HasDerivWithinAt
      (fun u => ∑ j : Fin d, ‖Dj L j (γ u)‖ ^ 2)
      (∑ j : Fin d, 2 * inner ℝ (Dj L j (γ t)) (Dj L j γ')) s t :=
    HasDerivWithinAt.fun_sum hj
  exact ((hsum.const_mul c₁).const_mul (L ^ d))

end ReyesMath.E18EnergyGradient
