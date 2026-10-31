import MathProofs.E18EnergyGradient

/-!
# E18: concrete-energy chain rule and conditional rate-reduction theorem

This module does not assume the energy-rate identity. It shows how
*the real Fréchet derivative of the actual E18 energy*, once proved,
and the actual negative L²-gradient equation entail the claimed
dissipation rate, with the factor of two explicit.

The hypotheses below expose, rather than hide, the two analytic inputs:
the Fréchet derivative of the nonlinear energy and its L² representative.
They are proved in `E18Frechet` (`E18.hasFDerivAt_energy`) and
`E18Representative` (`E18.DE_eq_inner`) and discharged in `E18Lyapunov`;
the certification is `E18Certification`.
-/

open Filter Topology InnerProductSpace
open scoped Real

noncomputable section

namespace ReyesMath.E18FlowChainRule

open ReyesMath.BandPass ReyesMath.TorusL2 ReyesMath.E18FourierEnergy

variable {L : ℝ} [hL : Fact (0 < L)] {d : ℕ}

/-- The actual energy has the real chain rule whenever its real
Fréchet derivative is available. This uses the Fourier H² energy
directly, not an artificial differentiable energy placeholder. -/
theorem hasDerivWithinAt_actual_energy
    (hd : d ≤ 3) (c₁ c₂ ε α : ℝ)
    {γ : ℝ → ell2 d} {γ' : ell2 d} {s : Set ℝ} {t : ℝ}
    (hγ : HasDerivWithinAt γ γ' s t)
    (DE : ell2 d →L[ℝ] ℝ)
    (hDE : HasFDerivAt (energy (L := L) hd c₁ c₂ ε α) DE (γ t)) :
    HasDerivWithinAt (fun u => energy (L := L) hd c₁ c₂ ε α (γ u))
      (DE γ') s t :=
  hDE.comp_hasDerivWithinAt t hγ

/-- Combining the *first-variation representation* of the actual
nonlinear E18 energy with the negative L²-gradient flow gives its
exact energy rate; no energy-rate identity is assumed. -/
theorem hasDerivWithinAt_actual_negative_gradient
    (hd : d ≤ 3) (c₁ c₂ ε α : ℝ)
    {γ : ℝ → ell2 d} {γ' : ell2 d} {s : Set ℝ} {t : ℝ}
    (hγ : HasDerivWithinAt γ γ' s t)
    (DE : ell2 d →L[ℝ] ℝ)
    (hDE : HasFDerivAt (energy (L := L) hd c₁ c₂ ε α) DE (γ t))
    (G : L2 L d)
    (hrep : ∀ h : ell2 d,
      DE h = 2 * L ^ d * (⟪G, iota L 1 h⟫_ℂ).re)
    (hflow : iota L 1 γ' = -G) :
    HasDerivWithinAt (fun u => energy (L := L) hd c₁ c₂ ε α (γ u))
      (-2 * L ^ d * ‖G‖ ^ 2) s t := by
  have hrate : DE γ' = -2 * L ^ d * ‖G‖ ^ 2 := by
    rw [hrep γ', hflow, inner_neg_right, Complex.neg_re]
    have h := inner_self_eq_norm_sq (𝕜 := ℂ) G
    rw [RCLike.re_to_complex] at h
    rw [h]
    ring
  rw [← hrate]
  exact hasDerivWithinAt_actual_energy (L := L) hd c₁ c₂ ε α hγ DE hDE


/-- Exact pointwise stationary criterion for the E18 dissipation rate:
its coefficient is strictly negative on every nonzero L² vector. -/
theorem zero_dissipation_iff_stationary (G : L2 L d) :
    -2 * L ^ d * ‖G‖ ^ 2 = 0 ↔ G = 0 := by
  have hLd : 0 < L ^ d := pow_pos hL.out d
  constructor
  · intro h
    have hprod : 2 * L ^ d * ‖G‖ ^ 2 = 0 := by linarith
    have hcoef : 2 * L ^ d ≠ 0 :=
      ne_of_gt (mul_pos (by norm_num) hLd)
    have hnorm : ‖G‖ ^ 2 = 0 :=
      (mul_eq_zero.mp hprod).resolve_left hcoef
    have hz : ‖G‖ = 0 := (sq_eq_zero_iff).mp hnorm
    exact norm_eq_zero.mp hz
  · rintro rfl
    simp

/-- The declared negative-gradient equation identifies instantaneous
stationarity with zero velocity, without assuming a PDE solution exists. -/
theorem stationary_iff_zero_velocity (G V : L2 L d) (hflow : V = -G) :
    V = 0 ↔ G = 0 := by
  rw [hflow]
  simp

end ReyesMath.E18FlowChainRule
