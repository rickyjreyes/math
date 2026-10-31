import MathProofs.E18Regularity

/-!
# E18: the `L²` representative of the derivative on `H⁴(𝕋_L^d)`

For `ψ ∈ ell2 d` with `A = ι₁ψ ∈ H⁴(𝕋_L^d)`, `d ≤ 3`, the variational derivative is
`G[A] = −c₁ΔA + c₂Δ(F(|A|²)ΔA) + c₂F′(|A|²)A|ΔA|²` (`Gt`); `regularity` gives
`F(|A|²)ΔA ∈ H²` and every term of `G` in `L²`.

* `inner_lap_comm`: periodic integration by parts `⟪u, Δv⟫ = ⟪Δu, v⟫` on `H²`; together with
  `sum_inner_Dj` (`Σ_j⟪∂_jA, ∂_jh⟫ = −⟪ΔA, h⟫`) these are the integration-by-parts identities used.
* `DE_eq_inner`: `DE ψ h = 2 L^d Re⟪ι₁h, G⟫` for **every** `h ∈ H²`; `DE_eq_volume`:
  `DE ψ h = 2 Re∫ G h̄ dx`.
* `real_gradient_eq`: the real `L²(dx)` gradient of `ℰ` at `ψ` is `2G` (and it is unique);
  `G_real_gradient_iff`: `G` itself represents `DE ψ` only when `G = 0`.
* `dpart_ae_eq_of_hasPartial`, `lap_ae_eq_of_hasPartial`: on fields with continuous classical
  partial derivatives, the Fourier `∂_j` and `Δ` are the classical operators.
-/

open Filter Topology MeasureTheory Set InnerProductSpace
open scoped ComplexConjugate

noncomputable section

namespace ReyesMath

namespace E18

open TorusL2 BandPass E18FourierEnergy E18WeightDerivative

variable {L : ℝ} [hL : Fact (0 < L)] {d : ℕ} {ε α : ℝ}

/-- **Periodic integration by parts for `Δ`**: `⟪u, Δv⟫ = ⟪Δu, v⟫` for `u, v ∈ H²`. -/
theorem inner_lap_comm {u v : L2 L d} (hu : InH 1 u) (hv : InH 1 v) :
    ⟪u, lap v⟫_ℂ = ⟪lap u, v⟫_ℂ := by
  refine (hasSum_inner u (lap v)).unique ((hasSum_inner (lap u) v).congr_fun fun n => ?_)
  rw [coef_lap hu, coef_lap hv, map_mul, map_neg, Complex.conj_ofReal]
  ring

/-- On `H²`, `F(|A|²)ΔA` is the bounded continuous weight times `Δψ ∈ L²`. -/
theorem coeFn_Wt (hd : d ≤ 3) (hε : 0 < ε) (α : ℝ) (ψ : ell2 d) :
    (Wt ε α (iota L 1 ψ) : Tor L d → ℂ) =ᵐ[μ L d]
      fun x => (F ε α (‖Phi L hd ψ x‖ ^ 2) : ℂ) * (DL L ψ : L2 L d) x := by
  have hc : Continuous fun x : Tor L d => (F ε α (‖Phi L hd ψ x‖ ^ 2) : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_F_comp hε α (Phi L hd ψ).continuous)
  have he : (fun x => (F ε α (‖(iota L 1 ψ : L2 L d) x‖ ^ 2) : ℂ) *
      (lap (iota L 1 ψ) : Tor L d → ℂ) x) =ᵐ[μ L d]
      fun x => (F ε α (‖Phi L hd ψ x‖ ^ 2) : ℂ) * (DL L ψ : L2 L d) x := by
    filter_upwards [iota_ae_eq_Phi (L := L) hd ψ] with x hx
    rw [hx, lap_iota]
  exact (coeFn_toL2' ((memLp_mul_continuous (DL L ψ) hc).ae_eq he.symm)).trans he

/-- `W_ψ = 2F(|A|²)ΔA`. -/
theorem Wcoef_eq (hd : d ≤ 3) (hε : 0 < ε) (α : ℝ) (ψ : ell2 d) :
    Wcoef hd ε α ψ = (2 : ℂ) • Wt ε α (iota L 1 ψ) := by
  refine Lp.ext ?_
  filter_upwards [coeFn_Wcoef (L := L) hd hε α ψ, Lp.coeFn_smul (2 : ℂ) (Wt ε α (iota L 1 ψ)),
    coeFn_Wt (L := L) hd hε α ψ] with x h1 h2 h3
  rw [h1, h2, Pi.smul_apply, h3, smul_eq_mul]
  push_cast
  ring

/-- **The `L²` representative of the derivative.** For `A = ι₁ψ ∈ H⁴(𝕋_L^d)`, `d ≤ 3`, and every
`h ∈ H²`: `DE ψ h = 2 L^d Re⟪ι₁h, G[A]⟫`. -/
theorem DE_eq_inner (hd : d ≤ 3) (hε : 0 < ε) (α c₁ c₂ : ℝ) {ψ : ell2 d}
    (h4 : InH 2 (iota L 1 ψ)) (h : ell2 d) :
    DE L hd hε α c₁ c₂ ψ h =
      2 * L ^ d * (⟪iota L 1 h, Gt c₁ c₂ ε α (iota L 1 ψ)⟫_ℂ).re := by
  obtain ⟨-, -, hW1, -, hVae, -⟩ := regularity (L := L) hd hε α h4
  have hH1 : InH 1 (iota L 1 h) := (inH_iff 1 _).2 ⟨h, rfl⟩
  have hgrad : ∑ j : Fin d, 2 * inner ℝ (Dj L j ψ) (Dj L j h) =
      -2 * (⟪DL L ψ, iota L 1 h⟫_ℂ).re := by
    simp only [real_inner_eq_re]
    rw [← Finset.mul_sum, ← Complex.re_sum, sum_inner_Dj, Complex.neg_re]
    ring
  have hWt : inner ℝ (Wcoef hd ε α ψ) (DL L h) =
      2 * (⟪iota L 1 h, lap (Wt ε α (iota L 1 ψ))⟫_ℂ).re := by
    rw [Wcoef_eq hd hε α ψ, real_inner_eq_re, inner_smul_left, ← lap_iota h,
      inner_lap_comm hW1 hH1, show (starRingEnd ℂ) (2 : ℂ) = ((2 : ℝ) : ℂ) by rw [Complex.ofReal_ofNat]; exact map_ofNat _ 2,
      Complex.re_ofReal_mul, re_inner_comm]
  have hU : ∫ x, (Ucoef hd ε α ψ x * Phi L hd h x).re ∂(μ L d) =
      2 * (⟪iota L 1 h, Vt ε α (iota L 1 ψ)⟫_ℂ).re := by
    rw [L2.inner_def, ← RCLike.re_to_complex, ← integral_re (L2.integrable_inner _ _),
      ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hVae, iota_ae_eq_Phi (L := L) hd ψ, iota_ae_eq_Phi (L := L) hd h]
      with x hV hA hHx
    rw [Ucoef_mul_re, RCLike.inner_apply, hV, hHx, hA, lap_iota, RCLike.re_to_complex,
      re_ofReal_mul_mul_ofReal_mul_conj]
    ring
  rw [DE_apply, hgrad, hWt, hU]
  simp only [Gt, inner_add_right, inner_neg_right, inner_smul_right, Complex.add_re,
    Complex.neg_re, Complex.re_ofReal_mul, lap_iota]
  rw [re_inner_comm (DL L ψ)]
  ring

/-- **`DE ψ h = 2 Re∫ G h̄ dx`** in physical volume, for every `h ∈ H²`. -/
theorem DE_eq_volume (hd : d ≤ 3) (hε : 0 < ε) (α c₁ c₂ : ℝ) {ψ : ell2 d}
    (h4 : InH 2 (iota L 1 ψ)) (h : ell2 d) :
    DE L hd hε α c₁ c₂ ψ h = 2 * (∫ x, (Gt c₁ c₂ ε α (iota L 1 ψ) : L2 L d) x *
      conj ((iota L 1 h : L2 L d) x)).re := by
  rw [DE_eq_inner hd hε α c₁ c₂ h4, integral_mul_conj_volume, ← Complex.ofReal_pow,
    Complex.re_ofReal_mul]
  ring

/-- **The real `L²(dx)` gradient of `ℰ` is `2G`**: `DE ψ h = (2G, h)_ℝ` with
`(u, v)_ℝ = Re∫ u v̄ dx`, and `2G` is the only element of `L²` with this property. -/
theorem real_gradient_eq (hd : d ≤ 3) (hε : 0 < ε) (α c₁ c₂ : ℝ) {ψ : ell2 d}
    (h4 : InH 2 (iota L 1 ψ)) :
    (∀ h : ell2 d, DE L hd hε α c₁ c₂ ψ h =
      rinner ((2 : ℂ) • Gt c₁ c₂ ε α (iota L 1 ψ)) (iota L 1 h)) ∧
    ∀ R : L2 L d, (∀ h : ell2 d, DE L hd hε α c₁ c₂ ψ h = rinner R (iota L 1 h)) →
      R = (2 : ℂ) • Gt c₁ c₂ ε α (iota L 1 ψ) := by
  have h1 : ∀ h : ell2 d, DE L hd hε α c₁ c₂ ψ h =
      rinner ((2 : ℂ) • Gt c₁ c₂ ε α (iota L 1 ψ)) (iota L 1 h) := fun h => by
    rw [DE_eq_inner hd hε α c₁ c₂ h4, rinner_eq, inner_smul_right,
      show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.re_ofReal_mul]
    ring
  refine ⟨h1, fun R hR => sub_eq_zero.1 (eq_zero_of_rinner fun v hv => ?_)⟩
  obtain ⟨k, rfl⟩ := (inH_iff 1 v).1 hv
  rw [rinner_eq, inner_sub_right, Complex.sub_re, mul_sub, ← rinner_eq, ← rinner_eq, ← hR k,
    ← h1 k, sub_self]

/-- **`G` is not the real gradient**: it represents `DE ψ` for the real `L²(dx)` product only
when it vanishes. -/
theorem G_real_gradient_iff (hd : d ≤ 3) (hε : 0 < ε) (α c₁ c₂ : ℝ) {ψ : ell2 d}
    (h4 : InH 2 (iota L 1 ψ)) :
    (∀ h : ell2 d, DE L hd hε α c₁ c₂ ψ h = rinner (Gt c₁ c₂ ε α (iota L 1 ψ)) (iota L 1 h)) ↔
      Gt c₁ c₂ ε α (iota L 1 ψ) = 0 := by
  obtain ⟨h1, huniq⟩ := real_gradient_eq hd hε α c₁ c₂ h4
  constructor
  · intro hG
    have e := huniq _ hG
    have e2 : (2 : ℂ) • Gt c₁ c₂ ε α (iota L 1 ψ) - Gt c₁ c₂ ε α (iota L 1 ψ) =
        Gt c₁ c₂ ε α (iota L 1 ψ) := by rw [two_smul, add_sub_cancel_right]
    rw [← e2, ← e, sub_self]
  · intro hG h
    rw [h1 h, hG, smul_zero]
/-! ### The Fourier derivatives are the classical derivatives -/

/-- **On fields with a continuous classical partial derivative, `∂_j` is the classical
derivative.** -/
theorem dpart_ae_eq_of_hasPartial {ψ : L2 L d} {f g : Tor L d → ℂ} (hf : Continuous f)
    (hg : Continuous g) (hψ : (ψ : Tor L d → ℂ) =ᵐ[μ L d] f) {j : Fin d} (h : HasPartial j f g) :
    (dpart j ψ : Tor L d → ℂ) =ᵐ[μ L d] g := by
  set G : L2 L d := (⟨g, hg⟩ : C(Tor L d, ℂ)).toLp 2 (μ L d) ℂ
  have hG : (G : Tor L d → ℂ) =ᵐ[μ L d] g :=
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (μ L d) (⟨g, hg⟩ : C(Tor L d, ℂ))
  have hcoef : ∀ k, coef G k = Complex.I * xi L k j * coef ψ k := fun k => by
    rw [coef_eq_cfun, cfun_congr_ae hG, coef_eq_cfun, cfun_congr_ae hψ, cfun_hasPartial hf hg h]
  have hm : Memℓp (fun k => Complex.I * xi L k j * coef ψ k) 2 := by
    rw [memℓp_two_iff]
    simp_rw [← hcoef]
    exact summable_sq G
  have e : dpart j ψ = G := ext_coef fun k => by rw [dpart, coef_pmul hm, hcoef]
  rw [e]
  exact hG

/-- **On fields with continuous classical partial derivatives of order `≤ 2`, `Δ` is the
classical Laplacian `Σ_j ∂_j∂_j`.** -/
theorem lap_ae_eq_of_hasPartial {ψ : L2 L d} {f : Tor L d → ℂ} {fj fjj : Fin d → Tor L d → ℂ}
    (hf : Continuous f) (hfj : ∀ j, Continuous (fj j)) (hfjj : ∀ j, Continuous (fjj j))
    (hψ : (ψ : Tor L d → ℂ) =ᵐ[μ L d] f) (h1 : ∀ j, HasPartial j f (fj j))
    (h2 : ∀ j, HasPartial j (fj j) (fjj j)) :
    (lap ψ : Tor L d → ℂ) =ᵐ[μ L d] fun x => ∑ j, fjj j x := by
  have hc : Continuous fun x => ∑ j, fjj j x := continuous_finset_sum _ fun j _ => hfjj j
  set G : L2 L d := (⟨_, hc⟩ : C(Tor L d, ℂ)).toLp 2 (μ L d) ℂ
  have hG : (G : Tor L d → ℂ) =ᵐ[μ L d] fun x => ∑ j, fjj j x :=
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (μ L d) (⟨_, hc⟩ : C(Tor L d, ℂ))
  have hcoef : ∀ k, coef G k = -(xi2 L k : ℂ) * coef ψ k := fun k => by
    rw [coef_eq_cfun, cfun_congr_ae hG]
    have hs : cfun (fun x => ∑ j, fjj j x) k = ∑ j, cfun (fjj j) k := by
      simp only [cfun, Finset.sum_mul]
      exact integral_finset_sum _ fun j _ =>
        integrable_of_continuous_c ((hfjj j).mul (Complex.continuous_conj.comp (emode k).continuous))
    rw [hs, coef_eq_cfun, cfun_congr_ae hψ]
    simp_rw [cfun_hasPartial (hfj _) (hfjj _) (h2 _), cfun_hasPartial hf (hfj _) (h1 _)]
    rw [xi2]
    push_cast
    rw [neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    linear_combination (xi L k j : ℂ) ^ 2 * cfun f k * Complex.I_sq
  have hm : Memℓp (fun k => -(xi2 L k : ℂ) * coef ψ k) 2 := by
    rw [memℓp_two_iff]
    simp_rw [← hcoef]
    exact summable_sq G
  have e : lap ψ = G := ext_coef fun k => by rw [lap, coef_pmul hm, hcoef]
  rw [e]
  exact hG

end E18

end ReyesMath
