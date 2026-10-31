import MathProofs.E18FlowChainRule

/-!
# E18: exact integrated energy identity from a certified first variation

This is a *conditional reduction*: the hypotheses give the true H²
Fréchet derivative of E18's actual energy, its L² representer, and a
classical negative-gradient trajectory. No assumption about dE/dt or
an integrated energy identity is made. The derivative and representer
hypotheses are discharged in `E18Lyapunov` by `E18.hasFDerivAt_energy`
and `E18.DE_eq_inner`.
-/

open Filter Topology InnerProductSpace MeasureTheory Set
open scoped Real

noncomputable section

namespace ReyesMath.E18IntegratedBalance

open ReyesMath.BandPass ReyesMath.TorusL2
open ReyesMath.E18FourierEnergy ReyesMath.E18FlowChainRule

variable {L : ℝ} [hL : Fact (0 < L)] {d : ℕ}

/-- The exact balance law for the actual E18 energy, reduced to an
independently certified first variation and its L² representation.
No energy-rate equation is assumed in the hypotheses. -/
theorem actual_energy_balance (hd : d ≤ 3) (c₁ c₂ ε α : ℝ)
    {a b : ℝ} (hab : a ≤ b)
    {γ γ' : ℝ → ell2 d} {G : ℝ → L2 L d}
    {DE : ℝ → ell2 d →L[ℝ] ℝ}
    (hγ : ∀ t ∈ Icc a b,
      HasDerivWithinAt γ (γ' t) (Icc a b) t)
    (hDE : ∀ t ∈ Icc a b,
      HasFDerivAt (energy (L := L) hd c₁ c₂ ε α) (DE t) (γ t))
    (hrep : ∀ t ∈ Icc a b, ∀ h : ell2 d,
      DE t h = 2 * L ^ d * (⟪G t, iota L 1 h⟫_ℂ).re)
    (hflow : ∀ t ∈ Icc a b, iota L 1 (γ' t) = -(G t))
    (hG : ContinuousOn G (Icc a b)) :
    energy (L := L) hd c₁ c₂ ε α (γ b) +
        2 * L ^ d * ∫ t in a..b, ‖G t‖ ^ 2 =
      energy (L := L) hd c₁ c₂ ε α (γ a) := by
  have hrate : ∀ t ∈ Icc a b,
      HasDerivWithinAt (fun u => energy (L := L) hd c₁ c₂ ε α (γ u))
        (-2 * L ^ d * ‖G t‖ ^ 2) (Icc a b) t := by
    intro t ht
    exact hasDerivWithinAt_actual_negative_gradient (L := L)
      hd c₁ c₂ ε α (hγ t ht) (DE t) (hDE t ht)
      (G t) (hrep t ht) (hflow t ht)
  have hrateCont : ContinuousOn
      (fun t => -2 * L ^ d * ‖G t‖ ^ 2) (Icc a b) :=
    continuousOn_const.mul (hG.norm.pow 2)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab
    (f := fun t => energy (L := L) hd c₁ c₂ ε α (γ t))
    (f' := fun t => -2 * L ^ d * ‖G t‖ ^ 2)
    (fun t ht => (hrate t ht).continuousWithinAt)
    (fun t ht => by
      have h := hrate t (Ioo_subset_Icc_self ht)
      exact (h.hasDerivAt (Icc_mem_nhds ht.1 ht.2)).hasDerivWithinAt)
    (hrateCont.intervalIntegrable_of_Icc hab)
  rw [intervalIntegral.integral_const_mul] at hftc
  linarith


/-- Nonnegative curvature energy and the exact integrated balance bound the
total dissipation on every finite interval of a regular trajectory. -/
theorem finite_interval_dissipation_bound (hd : d ≤ 3)
    (c₁ c₂ ε α : ℝ) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (T : ℝ) (γ : ℝ → ell2 d) (G : ℝ → L2 L d)
    (hbalance :
      energy (L := L) hd c₁ c₂ ε α (γ T) +
        2 * L ^ d * ∫ t in (0 : ℝ)..T, ‖G t‖ ^ 2 =
          energy (L := L) hd c₁ c₂ ε α (γ 0)) :
    2 * L ^ d * ∫ t in (0 : ℝ)..T, ‖G t‖ ^ 2 ≤
      energy (L := L) hd c₁ c₂ ε α (γ 0) := by
  have hpositive : 0 ≤ energy (L := L) hd c₁ c₂ ε α (γ T) :=
    energy_nonneg (L := L) hd c₁ c₂ ε α hc₁ hc₂ (γ T)
  linarith

end ReyesMath.E18IntegratedBalance
