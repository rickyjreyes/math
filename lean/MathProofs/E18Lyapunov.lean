import MathProofs.E18Representative
import MathProofs.E18IntegratedBalance

/-!
# E18: exact Lyapunov dissipation of the actual energy

Let `d ≤ 3`, `ε > 0`. A trajectory is given in the `ℓ²` model of `H²(𝕋_L^d; ℂ)`: `γ` is
differentiable on the time interval with continuous derivative `γ'`, `A(t) = ι₁γ(t) ∈ H⁴`, and
`A` solves the `L²` negative-gradient equation `∂ₜA = −G[A]`,
`G[A] = −c₁ΔA + c₂Δ(F(|A|²)ΔA) + c₂F′(|A|²)A|ΔA|²`.

Nothing is assumed about `dℰ/dt`, the first variation of `ℰ` or its representative: the
hypotheses `hDE`, `hrep` of `E18FlowChainRule` and `E18IntegratedBalance` are discharged by
`hasFDerivAt_energy` and `DE_eq_inner`.

* `energy_rate_general`: along **any** differentiable `H²` evolution with `A(t) ∈ H⁴`,
  `dℰ/dt = DE(ψ)[∂ₜψ] = 2 Re∫ G ∂ₜψ̄ dx` (no sign without the gradient-flow equation).
* `energy_rate`: along the gradient flow, `dℰ/dt = −2∫|G|² dx = −2∫|∂ₜψ|² dx ≤ 0`.
* `e18_lyapunov`: the integrated identity on every `[t₁, t₂] ⊆ [0, T]`, monotonicity,
  `dℰ/dt = 0 ⇔ G = 0 ⇔ ∂ₜψ = 0`, constancy of `ℰ` on `[t₁, t₂]` forces `G ≡ 0` there, strict
  descent, and (for `c₁, c₂ ≥ 0`) `2∫₀ᵀ∫|G|² dx dt ≤ ℰ[ψ(0)]`.
* `e18_global_dissipation`: on `[0, ∞)`, `∫₀^∞ ∫|G|² dx dt ≤ ℰ[ψ(0)]/2`.

The trajectory is a hypothesis: no existence, uniqueness, global existence, asymptotic stability
or physical validity is asserted, `ε > 0` is fixed (no uniform `ε → 0` statement), and the flow is
the variational `L²` gradient flow of `ℰ`, not an independently proposed physical-time dynamics.
-/

open Filter Topology MeasureTheory Set InnerProductSpace intervalIntegral
open scoped ComplexConjugate

noncomputable section

namespace ReyesMath

namespace E18

open TorusL2 BandPass E18FourierEnergy E18WeightDerivative

variable {L : ℝ} [hL : Fact (0 < L)] {d : ℕ} {ε α : ℝ}

/-- **The chain rule for an arbitrary evolution**: if `A(t) ∈ H⁴`, then
`dℰ/dt = 2 Re∫ G[A] ∂ₜĀ dx`, with no sign in general. -/
theorem energy_rate_general (hd : d ≤ 3) (hε : 0 < ε) (α c₁ c₂ : ℝ) {γ : ℝ → ell2 d}
    {γ' : ell2 d} {s : Set ℝ} {t : ℝ} (hγ : HasDerivWithinAt γ γ' s t)
    (h4 : InH 2 (iota L 1 (γ t))) :
    HasDerivWithinAt (fun u => energy (L := L) hd c₁ c₂ ε α (γ u))
      (2 * (∫ x, (Gt c₁ c₂ ε α (iota L 1 (γ t)) : L2 L d) x *
        conj ((iota L 1 γ' : L2 L d) x)).re) s t := by
  rw [← DE_eq_volume hd hε α c₁ c₂ h4]
  exact E18FlowChainRule.hasDerivWithinAt_actual_energy (L := L) hd c₁ c₂ ε α hγ _
    (hasFDerivAt_energy hd hε α c₁ c₂ (γ t))

/-- **Exact dissipation rate along the gradient flow**: `dℰ/dt = −2∫|G|² dx`. -/
theorem energy_rate (hd : d ≤ 3) (hε : 0 < ε) (α c₁ c₂ : ℝ) {γ : ℝ → ell2 d} {γ' : ell2 d}
    {s : Set ℝ} {t : ℝ} (hγ : HasDerivWithinAt γ γ' s t) (h4 : InH 2 (iota L 1 (γ t)))
    (hflow : iota L 1 γ' = -Gt c₁ c₂ ε α (iota L 1 (γ t))) :
    HasDerivWithinAt (fun u => energy (L := L) hd c₁ c₂ ε α (γ u))
      (-2 * ∫ x, ‖(Gt c₁ c₂ ε α (iota L 1 (γ t)) : L2 L d) x‖ ^ 2) s t := by
  have h := E18FlowChainRule.hasDerivWithinAt_actual_negative_gradient (L := L) hd c₁ c₂ ε α hγ
    (DE L hd hε α c₁ c₂ (γ t)) (hasFDerivAt_energy hd hε α c₁ c₂ (γ t))
    (Gt c₁ c₂ ε α (iota L 1 (γ t)))
    (fun h => by rw [DE_eq_inner hd hε α c₁ c₂ h4, re_inner_comm]) hflow
  rw [integral_norm_sq_vol, ← mul_assoc]
  exact h

/-- **Theorem E18 (exact Lyapunov dissipation).** For a classical trajectory on `[0, T]` of the
`L²` negative-gradient equation `∂ₜA = −G[A]` with `A ∈ C¹([0,T]; H²)`, `A(t) ∈ H⁴`:
1. `dℰ/dt = −2∫|G|² dx`;
2. `∫|G|² dx = ∫|∂ₜA|² dx`, so the rate is `−2‖∂ₜA‖²_{L²(dx)} ≤ 0`;
3. `ℰ[A(t₂)] + 2∫_{t₁}^{t₂}∫|G|² dx dt = ℰ[A(t₁)]` for `0 ≤ t₁ ≤ t₂ ≤ T`;
4. `t ↦ ℰ[A(t)]` is antitone on `[0, T]`;
5. `dℰ/dt = 0 ⇔ G[A(t)] = 0 ⇔ ∂ₜA(t) = 0`;
6. if `ℰ[A(t₂)] = ℰ[A(t₁)]` with `t₁ < t₂`, then `G[A] ≡ 0` on `[t₁, t₂]`;
7. strict descent: if `G[A(t)] ≠ 0` for some `t ∈ [t₁, t₂]`, then `ℰ[A(t₂)] < ℰ[A(t₁)]`. -/
theorem e18_lyapunov (hd : d ≤ 3) (hε : 0 < ε) (α c₁ c₂ : ℝ) {T : ℝ}
    {γ γ' : ℝ → ell2 d} (hγ : ∀ t ∈ Icc 0 T, HasDerivWithinAt γ (γ' t) (Icc 0 T) t)
    (hγ' : ContinuousOn γ' (Icc 0 T)) (h4 : ∀ t ∈ Icc 0 T, InH 2 (iota L 1 (γ t)))
    (hflow : ∀ t ∈ Icc 0 T, iota L 1 (γ' t) = -Gt c₁ c₂ ε α (iota L 1 (γ t))) :
    (∀ t ∈ Icc 0 T, HasDerivWithinAt (fun u => energy (L := L) hd c₁ c₂ ε α (γ u))
      (-2 * ∫ x, ‖(Gt c₁ c₂ ε α (iota L 1 (γ t)) : L2 L d) x‖ ^ 2) (Icc 0 T) t) ∧
    (∀ t ∈ Icc 0 T, ∫ x, ‖(Gt c₁ c₂ ε α (iota L 1 (γ t)) : L2 L d) x‖ ^ 2 =
      ∫ x, ‖(iota L 1 (γ' t) : L2 L d) x‖ ^ 2) ∧
    (∀ t ∈ Icc 0 T, -2 * ∫ x, ‖(Gt c₁ c₂ ε α (iota L 1 (γ t)) : L2 L d) x‖ ^ 2 ≤ 0) ∧
    (∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ ≤ t₂ → t₂ ≤ T →
      energy (L := L) hd c₁ c₂ ε α (γ t₂) +
          2 * ∫ t in t₁..t₂, ∫ x, ‖(Gt c₁ c₂ ε α (iota L 1 (γ t)) : L2 L d) x‖ ^ 2 =
        energy (L := L) hd c₁ c₂ ε α (γ t₁)) ∧
    AntitoneOn (fun t => energy (L := L) hd c₁ c₂ ε α (γ t)) (Icc 0 T) ∧
    (∀ t ∈ Icc 0 T,
      (-2 * ∫ x, ‖(Gt c₁ c₂ ε α (iota L 1 (γ t)) : L2 L d) x‖ ^ 2 = 0 ↔
        Gt c₁ c₂ ε α (iota L 1 (γ t)) = 0) ∧
      (Gt c₁ c₂ ε α (iota L 1 (γ t)) = 0 ↔ iota L 1 (γ' t) = 0)) ∧
    (∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ < t₂ → t₂ ≤ T →
      energy (L := L) hd c₁ c₂ ε α (γ t₂) = energy (L := L) hd c₁ c₂ ε α (γ t₁) →
      ∀ t ∈ Icc t₁ t₂, Gt c₁ c₂ ε α (iota L 1 (γ t)) = 0) ∧
    (∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ < t₂ → t₂ ≤ T →
      (∃ t ∈ Icc t₁ t₂, Gt c₁ c₂ ε α (iota L 1 (γ t)) ≠ 0) →
      energy (L := L) hd c₁ c₂ ε α (γ t₂) < energy (L := L) hd c₁ c₂ ε α (γ t₁)) := by
  set G : ℝ → L2 L d := fun t => Gt c₁ c₂ ε α (iota L 1 (γ t)) with hGdef
  set f : ℝ → ℝ := fun t => ∫ x, ‖(G t : L2 L d) x‖ ^ 2 with hfdef
  have hf0 : ∀ t, 0 ≤ f t := fun t => integral_nonneg fun x => sq_nonneg _
  have hfG : ∀ t, f t = L ^ d * ‖G t‖ ^ 2 := fun t => integral_norm_sq_vol _
  have hGc : ContinuousOn G (Icc 0 T) :=
    ((iota L 1).continuous.comp_continuousOn hγ').neg.congr fun t ht => by
      show G t = -(iota L 1 (γ' t))
      rw [hflow t ht, neg_neg]
  have hfc : ContinuousOn f (Icc 0 T) :=
    (continuousOn_const.mul (hGc.norm.pow 2)).congr fun t _ => hfG t
  have hrate : ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun u => energy (L := L) hd c₁ c₂ ε α (γ u))
      (-2 * f t) (Icc 0 T) t := fun t ht =>
    energy_rate hd hε α c₁ c₂ (hγ t ht) (h4 t ht) (hflow t ht)
  have hbal : ∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ ≤ t₂ → t₂ ≤ T →
      energy (L := L) hd c₁ c₂ ε α (γ t₂) + 2 * ∫ t in t₁..t₂, f t =
        energy (L := L) hd c₁ c₂ ε α (γ t₁) := by
    intro t₁ t₂ h01 h12 h2T
    have hsub : Icc t₁ t₂ ⊆ Icc 0 T := Icc_subset_Icc h01 h2T
    have h := E18IntegratedBalance.actual_energy_balance (L := L) hd c₁ c₂ ε α h12
      (γ := γ) (γ' := γ') (G := G) (DE := fun t => DE L hd hε α c₁ c₂ (γ t))
      (fun t ht => (hγ t (hsub ht)).mono hsub)
      (fun t _ => hasFDerivAt_energy hd hε α c₁ c₂ (γ t))
      (fun t ht h => by rw [DE_eq_inner hd hε α c₁ c₂ (h4 t (hsub ht)), re_inner_comm])
      (fun t ht => hflow t (hsub ht)) (hGc.mono hsub)
    have e : ∫ t in t₁..t₂, f t = L ^ d * ∫ t in t₁..t₂, ‖G t‖ ^ 2 := by
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_congr fun t _ => hfG t
    rw [e, ← mul_assoc]
    exact h
  have hanti : AntitoneOn (fun t => energy (L := L) hd c₁ c₂ ε α (γ t)) (Icc 0 T) := by
    intro t₁ ht₁ t₂ ht₂ h12
    have h := hbal t₁ t₂ ht₁.1 h12 ht₂.2
    have := intervalIntegral.integral_nonneg (μ := volume) h12 fun t _ => hf0 t
    show energy (L := L) hd c₁ c₂ ε α (γ t₂) ≤ energy (L := L) hd c₁ c₂ ε α (γ t₁)
    linarith
  have hzero : ∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ < t₂ → t₂ ≤ T →
      energy (L := L) hd c₁ c₂ ε α (γ t₂) = energy (L := L) hd c₁ c₂ ε α (γ t₁) →
      ∀ t ∈ Icc t₁ t₂, G t = 0 := by
    intro t₁ t₂ h01 h12 h2T hE t ht
    have hsub : Icc t₁ t₂ ⊆ Icc 0 T := Icc_subset_Icc h01 h2T
    have hint : ∫ s in t₁..t₂, f s = 0 := by
      have := hbal t₁ t₂ h01 h12.le h2T
      linarith
    have hae := (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae h12.le
      (Eventually.of_forall fun s => hf0 s) ((hfc.mono hsub).intervalIntegrable_of_Icc h12.le)).1
      hint
    have hae' : f =ᵐ[volume.restrict (Icc t₁ t₂)] 0 := by
      rwa [← Measure.restrict_congr_set Ioc_ae_eq_Icc]
    have hEq := Measure.eqOn_Icc_of_ae_eq volume h12.ne hae' (hfc.mono hsub) continuousOn_const
    have h0 : f t = 0 := hEq ht
    rw [hfG t] at h0
    have h2 := (E18FlowChainRule.zero_dissipation_iff_stationary (L := L) (G t)).1
      (by rw [mul_assoc, h0, mul_zero])
    exact h2
  refine ⟨hrate, fun t ht => ?_, fun t _ => ?_, hbal, hanti, fun t ht => ⟨?_, ?_⟩, hzero,
    fun t₁ t₂ h01 h12 h2T ⟨t, ht, hGt⟩ => ?_⟩
  · rw [hflow t ht, integral_norm_sq_vol, integral_norm_sq_vol, norm_neg]
  · have h0 : 0 ≤ ∫ x, ‖(Gt c₁ c₂ ε α (iota L 1 (γ t)) : L2 L d) x‖ ^ 2 :=
      integral_nonneg fun x => sq_nonneg _
    linarith
  · rw [integral_norm_sq_vol, ← mul_assoc]
    exact E18FlowChainRule.zero_dissipation_iff_stationary _
  · exact (E18FlowChainRule.stationary_iff_zero_velocity _ _ (hflow t ht)).symm
  · refine lt_of_le_of_ne (hanti ⟨h01, (h12.le.trans h2T)⟩ ⟨h01.trans h12.le, h2T⟩ h12.le)
      fun hE => hGt (hzero t₁ t₂ h01 h12 h2T hE t ht)

/-- **Finite-interval dissipation bound**: for `c₁, c₂ ≥ 0`,
`2∫₀ᵀ∫|G|² dx dt ≤ ℰ[ψ(0)]`. -/
theorem e18_finite_dissipation (hd : d ≤ 3) (hε : 0 < ε) (α c₁ c₂ : ℝ) (hc₁ : 0 ≤ c₁)
    (hc₂ : 0 ≤ c₂) {T : ℝ} (hT : 0 < T) {γ γ' : ℝ → ell2 d}
    (hγ : ∀ t ∈ Icc 0 T, HasDerivWithinAt γ (γ' t) (Icc 0 T) t)
    (hγ' : ContinuousOn γ' (Icc 0 T)) (h4 : ∀ t ∈ Icc 0 T, InH 2 (iota L 1 (γ t)))
    (hflow : ∀ t ∈ Icc 0 T, iota L 1 (γ' t) = -Gt c₁ c₂ ε α (iota L 1 (γ t))) :
    2 * ∫ t in (0 : ℝ)..T, ∫ x, ‖(Gt c₁ c₂ ε α (iota L 1 (γ t)) : L2 L d) x‖ ^ 2 ≤
      energy (L := L) hd c₁ c₂ ε α (γ 0) := by
  obtain ⟨-, -, -, hbal, -⟩ := e18_lyapunov hd hε α c₁ c₂ hγ hγ' h4 hflow
  have h := hbal 0 T le_rfl hT.le le_rfl
  have := energy_nonneg (L := L) hd c₁ c₂ ε α hc₁ hc₂ (γ T)
  linarith

/-- **Global dissipation bound** on `[0, ∞)`, with physical-volume normalization:
`∫₀^∞ ∫|G|² dx dt ≤ ℰ[ψ(0)]/2` (no existence of such a trajectory is asserted). -/
theorem e18_global_dissipation (hd : d ≤ 3) (hε : 0 < ε) (α c₁ c₂ : ℝ) (hc₁ : 0 ≤ c₁)
    (hc₂ : 0 ≤ c₂) {γ γ' : ℝ → ell2 d}
    (hγ : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt γ (γ' t) (Ici 0) t)
    (hγ' : ContinuousOn γ' (Ici 0)) (h4 : ∀ t ∈ Ici (0 : ℝ), InH 2 (iota L 1 (γ t)))
    (hflow : ∀ t ∈ Ici (0 : ℝ), iota L 1 (γ' t) = -Gt c₁ c₂ ε α (iota L 1 (γ t))) :
    IntegrableOn (fun t => ∫ x, ‖(Gt c₁ c₂ ε α (iota L 1 (γ t)) : L2 L d) x‖ ^ 2) (Ioi 0) ∧
    ∫ t in Ioi (0 : ℝ), ∫ x, ‖(Gt c₁ c₂ ε α (iota L 1 (γ t)) : L2 L d) x‖ ^ 2 ≤
      energy (L := L) hd c₁ c₂ ε α (γ 0) / 2 := by
  set f : ℝ → ℝ := fun t => ∫ x, ‖(Gt c₁ c₂ ε α (iota L 1 (γ t)) : L2 L d) x‖ ^ 2 with hf
  have hf0 : ∀ t, 0 ≤ f t := fun t => integral_nonneg fun x => sq_nonneg _
  have hGc : ContinuousOn (fun t => Gt c₁ c₂ ε α (iota L 1 (γ t))) (Ici 0) :=
    ((iota L 1).continuous.comp_continuousOn hγ').neg.congr fun t ht => by
      show Gt c₁ c₂ ε α (iota L 1 (γ t)) = -(iota L 1 (γ' t))
      rw [hflow t ht, neg_neg]
  have hcont : ContinuousOn f (Ici 0) :=
    (continuousOn_const.mul (hGc.norm.pow 2)).congr fun t _ => integral_norm_sq_vol _
  have hfi : ∀ i : ℝ, IntegrableOn f (Ioc 0 i) := fun i =>
    ((hcont.mono Icc_subset_Ici_self).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hbound : ∀ T : ℝ, 0 < T → ∫ t in (0 : ℝ)..T, f t ≤
      energy (L := L) hd c₁ c₂ ε α (γ 0) / 2 := by
    intro T hT
    have sub : Icc 0 T ⊆ Ici 0 := Icc_subset_Ici_self
    have h := e18_finite_dissipation hd hε α c₁ c₂ hc₁ hc₂ hT
      (fun t ht => (hγ t (sub ht)).mono sub) (hγ'.mono sub) (fun t ht => h4 t (sub ht))
      (fun t ht => hflow t (sub ht))
    simp only [hf]
    linarith
  have hint : IntegrableOn f (Ioi 0) := by
    refine integrableOn_Ioi_of_intervalIntegral_norm_bounded
      (energy (L := L) hd c₁ c₂ ε α (γ 0) / 2) 0 hfi tendsto_id ?_
    filter_upwards [eventually_gt_atTop 0] with i hi
    have : ∫ x in (0 : ℝ)..i, ‖f x‖ = ∫ x in (0 : ℝ)..i, f x :=
      intervalIntegral.integral_congr fun x _ => Real.norm_of_nonneg (hf0 x)
    rw [this]
    exact hbound i hi
  refine ⟨hint, ?_⟩
  refine le_of_tendsto (intervalIntegral_tendsto_integral_Ioi 0 hint tendsto_id) ?_
  filter_upwards [eventually_gt_atTop 0] with i hi
  exact hbound i hi

/-! ### Trajectories in `C¹([0, T]; H⁴)` -/

variable (L) in
/-- `J c = (w_n⁻¹ c_n)`: the `H²` coordinates of the `H⁴` field `ι₂ c` (`iota_two`). -/
def J4 : ell2 d →L[ℂ] ell2 d := diagL (fun n => ((wt L n)⁻¹ : ℂ) ^ 1) (norm_wt_inv_pow_le 1)

theorem iota_two (c : ell2 d) : iota L 2 c = iota L 1 (J4 L c) := by
  apply ext_coef
  intro n
  rw [coef_iota, coef_iota, J4, diagL_apply]
  ring

/-- **Theorem E18 under the manuscript's hypothesis** `ψ ∈ C¹([0, T]; H⁴(𝕋_L^d; ℂ))`: `c` is the
`C¹` curve of `H⁴` coordinates, `ψ(t) = ι₂ c(t)`, `∂ₜψ = ι₂ c′(t) = −G[ψ]`, and `J c(t)` are the
`H²` coordinates of `ψ(t)` on which `ℰ` is defined. -/
theorem e18_lyapunov_H4 (hd : d ≤ 3) (hε : 0 < ε) (α c₁ c₂ : ℝ) {T : ℝ} {c c' : ℝ → ell2 d}
    (hc : ∀ t ∈ Icc 0 T, HasDerivWithinAt c (c' t) (Icc 0 T) t) (hc' : ContinuousOn c' (Icc 0 T))
    (hflow : ∀ t ∈ Icc 0 T, iota L 2 (c' t) = -Gt c₁ c₂ ε α (iota L 2 (c t))) :
    (∀ t ∈ Icc 0 T, HasDerivWithinAt (fun u => energy (L := L) hd c₁ c₂ ε α (J4 L (c u)))
      (-2 * ∫ x, ‖(Gt c₁ c₂ ε α (iota L 2 (c t)) : L2 L d) x‖ ^ 2) (Icc 0 T) t) ∧
    (∀ t ∈ Icc 0 T, ∫ x, ‖(Gt c₁ c₂ ε α (iota L 2 (c t)) : L2 L d) x‖ ^ 2 =
      ∫ x, ‖(iota L 2 (c' t) : L2 L d) x‖ ^ 2) ∧
    (∀ t ∈ Icc 0 T, -2 * ∫ x, ‖(Gt c₁ c₂ ε α (iota L 2 (c t)) : L2 L d) x‖ ^ 2 ≤ 0) ∧
    (∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ ≤ t₂ → t₂ ≤ T →
      energy (L := L) hd c₁ c₂ ε α (J4 L (c t₂)) +
          2 * ∫ t in t₁..t₂, ∫ x, ‖(Gt c₁ c₂ ε α (iota L 2 (c t)) : L2 L d) x‖ ^ 2 =
        energy (L := L) hd c₁ c₂ ε α (J4 L (c t₁))) ∧
    AntitoneOn (fun t => energy (L := L) hd c₁ c₂ ε α (J4 L (c t))) (Icc 0 T) ∧
    (∀ t ∈ Icc 0 T,
      (-2 * ∫ x, ‖(Gt c₁ c₂ ε α (iota L 2 (c t)) : L2 L d) x‖ ^ 2 = 0 ↔
        Gt c₁ c₂ ε α (iota L 2 (c t)) = 0) ∧
      (Gt c₁ c₂ ε α (iota L 2 (c t)) = 0 ↔ iota L 2 (c' t) = 0)) ∧
    (∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ < t₂ → t₂ ≤ T →
      energy (L := L) hd c₁ c₂ ε α (J4 L (c t₂)) = energy (L := L) hd c₁ c₂ ε α (J4 L (c t₁)) →
      ∀ t ∈ Icc t₁ t₂, Gt c₁ c₂ ε α (iota L 2 (c t)) = 0) ∧
    (∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ < t₂ → t₂ ≤ T →
      (∃ t ∈ Icc t₁ t₂, Gt c₁ c₂ ε α (iota L 2 (c t)) ≠ 0) →
      energy (L := L) hd c₁ c₂ ε α (J4 L (c t₂)) < energy (L := L) hd c₁ c₂ ε α (J4 L (c t₁))) := by
  have h := e18_lyapunov (L := L) hd hε α c₁ c₂ (γ := fun t => J4 L (c t))
    (γ' := fun t => J4 L (c' t)) (fun t ht => hasDerivWithinAt_clm (J4 L) (hc t ht))
    ((J4 L).continuous.comp_continuousOn hc')
    (fun t _ => (inH_iff 2 _).2 ⟨c t, (iota_two (c t)).symm⟩)
    (fun t ht => by simp only [← iota_two]; exact hflow t ht)
  simp only [← iota_two] at h
  exact h

end E18

end ReyesMath
