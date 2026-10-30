import MathProofs.E18WeightBounds
import MathProofs.E18VariationAlgebra

/-!
# E18: the Fréchet derivative of the actual nonlinear energy on `H²(𝕋_L^d; ℂ)`

The field space is `H²(𝕋_L^d; ℂ)` in its isometric Fourier model `ψ ∈ ℓ²(ℤ^d)` (`A = ι₁ψ`), as a
real Banach space, `d ≤ 3`. `E18FourierEnergy.energy` is the exact E18 energy
`ℰ[ψ] = ∫_{𝕋_L^d} (c₁|∇ψ|² + c₂F(|ψ|²)|Δψ|²) dx`, `F(ρ) = ρ/(ρ + ε²e^{−2αρ})²`, with the
physical volume `dx` of total mass `L^d` (`energy_eq_volume`).

* `DE ψ : ell2 d →L[ℝ] ℝ`, with (`DE_apply_volume`)
  `DE ψ h = 2c₁ Re∫∇ψ·∇h̄ + 2c₂ Re∫F(|ψ|²)Δψ Δh̄ + 2c₂ Re∫F′(|ψ|²)ψ|Δψ|² h̄`.
* `energy_remainder`: on every ball `‖ψ‖, ‖h‖ ≤ M`,
  `|ℰ[ψ + h] − ℰ[ψ] − DE ψ h| ≤ C_M ‖h‖²_{H²}`.
* `hasFDerivAt_energy`: `ℰ` is Fréchet differentiable at every `ψ` with derivative `DE ψ`.
* `DE_lipschitz`: `‖DE ψ − DE φ‖ ≤ C_M ‖ψ − φ‖` on balls; `contDiff_energy`: `ℰ` is `C¹`.
-/

open Filter Topology MeasureTheory Set Asymptotics
open scoped ComplexConjugate

noncomputable section

namespace ReyesMath

namespace E18

open TorusL2 BandPass E18FourierEnergy E18WeightDerivative

variable {L : ℝ} [hL : Fact (0 < L)] {d : ℕ} {ε α : ℝ}

/-! ### Operator bounds and Cauchy–Schwarz -/

variable (L d) in
/-- The constant of the Sobolev embedding `H²(𝕋_L^d) ⊂ C(𝕋_L^d)`, `d ≤ 3` (`norm_Phi_le`). -/
def sob : ℝ := √(∑' n : Fin d → ℤ, ((wt L n)⁻¹) ^ 2)

omit hL in
theorem sob_nonneg : 0 ≤ sob L d := Real.sqrt_nonneg _

theorem norm_Phi_apply_le (hd : d ≤ 3) (c : ell2 d) (x : Tor L d) :
    ‖Phi L hd c x‖ ≤ sob L d * ‖c‖ :=
  ((Phi L hd c).norm_coe_le_norm x).trans (norm_Phi_le hd c)

theorem norm_opS_le (k : ℕ) {s : (Fin d → ℤ) → ℂ} {C : ℝ} (hs : ∀ n, ‖s n‖ ≤ C * wt L n ^ k)
    (hC : 0 ≤ C) (c : ell2 d) : ‖opS k s hs c‖ ≤ C * ‖c‖ := by
  rw [opS, ContinuousLinearMap.comp_apply]
  have h1 : ‖ofCoef (L := L) (diagL (fun n => s n * ((wt L n)⁻¹ : ℂ) ^ k) (opS_bound k hs) c)‖ =
      ‖diagL (fun n => s n * ((wt L n)⁻¹ : ℂ) ^ k) (opS_bound k hs) c‖ :=
    (basis L d).repr.symm.norm_map _
  rw [h1]
  exact (diagL _ (opS_bound k hs)).le_of_opNorm_le (LinearMap.mkContinuous_norm_le _ hC _) c

/-- `‖Δψ‖_{L²} ≤ ‖ψ‖_{H²}`. -/
theorem norm_DL_le (c : ell2 d) : ‖DL L c‖ ≤ ‖c‖ := by
  have h := norm_opS_le (L := L) 1 norm_xi2_le zero_le_one c
  rw [one_mul] at h
  exact h

/-- `‖∂_jψ‖_{L²} ≤ ‖ψ‖_{H²}`. -/
theorem norm_Dj_le (j : Fin d) (c : ell2 d) : ‖Dj L j c‖ ≤ ‖c‖ := by
  have h := norm_opS_le (L := L) 1 (norm_I_xi_le j) zero_le_one c
  rw [one_mul] at h
  exact h

/-- **Cauchy–Schwarz on `L²(𝕋_L^d)`**: `∫ |u||v| dμ ≤ ‖u‖ ‖v‖`. -/
theorem integral_norm_mul_norm_le (u v : L2 L d) :
    ∫ x, ‖u x‖ * ‖v x‖ ∂(μ L d) ≤ ‖u‖ * ‖v‖ := by
  have hu : MemLp (u : Tor L d → ℂ) (ENNReal.ofReal 2) (μ L d) := by
    rw [ENNReal.ofReal_ofNat]; exact Lp.memLp u
  have hv : MemLp (v : Tor L d → ℂ) (ENNReal.ofReal 2) (μ L d) := by
    rw [ENNReal.ofReal_ofNat]; exact Lp.memLp v
  have h := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two hu hv
  have e : ∀ w : L2 L d, (∫ x, ‖w x‖ ^ (2 : ℝ) ∂(μ L d)) ^ (1 / (2 : ℝ)) = ‖w‖ := fun w => by
    have h2 : ∫ x, ‖w x‖ ^ (2 : ℝ) ∂(μ L d) = ‖w‖ ^ 2 := by
      rw [norm_sq_eq_integral]
      exact integral_congr_ae (Eventually.of_forall fun x => Real.rpow_two _)
    rw [h2, ← Real.sqrt_eq_rpow, Real.sqrt_sq (norm_nonneg _)]
  rwa [e, e] at h

theorem integrable_norm_mul_norm (u v : L2 L d) :
    Integrable (fun x => ‖u x‖ * ‖v x‖) (μ L d) := by
  have h := (L2.integrable_inner (𝕜 := ℂ) u v).norm
  refine h.congr (Eventually.of_forall fun x => ?_)
  simp only [RCLike.inner_apply, norm_mul, RCLike.norm_conj]
  ring

/-! ### Real pairings -/

theorem integrable_pairC {U : Tor L d → ℂ} (hU : Integrable U (μ L d)) (f₁ : C(Tor L d, ℂ)) :
    Integrable (fun x => (U x * f₁ x).re) (μ L d) := by
  have h : Integrable (fun x => f₁ x * U x) (μ L d) :=
    hU.bdd_mul' f₁.continuous.aestronglyMeasurable
      (Eventually.of_forall fun x => f₁.norm_coe_le_norm x)
  exact (h.congr (Eventually.of_forall fun x => mul_comm _ _)).re

/-- The real functional `f₁ ↦ ∫ Re(U f₁) dμ` on `C(𝕋_L^d; ℂ)`, for integrable `U`. -/
def pairC (U : Tor L d → ℂ) (hU : Integrable U (μ L d)) : C(Tor L d, ℂ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun f₁ => ∫ x, (U x * f₁ x).re ∂(μ L d)
      map_add' := fun f₁ f₂ => by
        simp only [ContinuousMap.add_apply, mul_add, Complex.add_re]
        exact integral_add (integrable_pairC hU f₁) (integrable_pairC hU f₂)
      map_smul' := fun r f₁ => by
        simp only [ContinuousMap.smul_apply, RingHom.id_apply, smul_eq_mul, Complex.real_smul]
        rw [← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only
        rw [mul_left_comm, Complex.re_ofReal_mul] }
    (∫ x, ‖U x‖ ∂(μ L d)) (fun f₁ => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      calc ‖∫ x, (U x * f₁ x).re ∂(μ L d)‖ ≤ ∫ x, ‖(U x * f₁ x).re‖ ∂(μ L d) :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ x, ‖U x‖ * ‖f₁‖ ∂(μ L d) := by
            refine integral_mono (integrable_pairC hU f₁).norm (hU.norm.mul_const _)
              fun x => ?_
            calc ‖(U x * f₁ x).re‖ ≤ ‖U x * f₁ x‖ := by
                  rw [Real.norm_eq_abs]; exact Complex.abs_re_le_norm _
              _ = ‖U x‖ * ‖f₁ x‖ := norm_mul _ _
              _ ≤ ‖U x‖ * ‖f₁‖ :=
                  mul_le_mul_of_nonneg_left (f₁.norm_coe_le_norm x) (norm_nonneg _)
        _ = (∫ x, ‖U x‖ ∂(μ L d)) * ‖f₁‖ := integral_mul_const _ _)

theorem pairC_apply (U : Tor L d → ℂ) (hU : Integrable U (μ L d)) (f₁ : C(Tor L d, ℂ)) :
    pairC U hU f₁ = ∫ x, (U x * f₁ x).re ∂(μ L d) := rfl

open Classical in
/-- The `L²` class of `f` (and `0` if `f ∉ L²`). -/
def toL2' (f : Tor L d → ℂ) : L2 L d :=
  if h : MemLp f 2 (μ L d) then h.toLp f else 0

theorem coeFn_toL2' {f : Tor L d → ℂ} (h : MemLp f 2 (μ L d)) :
    (toL2' f : Tor L d → ℂ) =ᵐ[μ L d] f := by
  rw [toL2', dif_pos h]
  exact h.coeFn_toLp

theorem memLp_mul_continuous (A : L2 L d) {φ : Tor L d → ℂ} (hφ : Continuous φ) :
    MemLp (fun x => φ x * A x) 2 (μ L d) := by
  obtain ⟨C, hC⟩ : ∃ C, ∀ x, ‖φ x‖ ≤ C :=
    ⟨‖(⟨φ, hφ⟩ : C(Tor L d, ℂ))‖, fun x => (⟨φ, hφ⟩ : C(Tor L d, ℂ)).norm_coe_le_norm x⟩
  refine (Lp.memLp A).of_le_mul (c := C) (hφ.aestronglyMeasurable.mul (Lp.aestronglyMeasurable A))
    (Eventually.of_forall fun x => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _)

/-! ### The weight along `H²` fields -/

omit hL in
theorem continuous_F_comp (hε : 0 < ε) (α : ℝ) {f : Tor L d → ℂ} (hf : Continuous f) :
    Continuous fun x => F ε α (‖f x‖ ^ 2) :=
  (continuousOn_F ε α).comp_continuous (hf.norm.pow 2) fun _ => mem_Uw hε α (sq_nonneg _)

omit hL in
theorem continuous_Fprime_comp (hε : 0 < ε) (α : ℝ) {f : Tor L d → ℂ} (hf : Continuous f) :
    Continuous fun x => Fprime ε α (‖f x‖ ^ 2) :=
  (continuousOn_Fprime ε α).comp_continuous (hf.norm.pow 2) fun _ => mem_Uw hε α (sq_nonneg _)

/-- `U_ψ = 2F′(|ψ|²)|Δψ|² ψ̄`, the coefficient of the variation of `ψ` inside the weight. -/
def Ucoef (hd : d ≤ 3) (ε α : ℝ) (ψ : ell2 d) (x : Tor L d) : ℂ :=
  ((2 * Fprime ε α (‖Phi L hd ψ x‖ ^ 2) * ‖(DL L ψ : L2 L d) x‖ ^ 2 : ℝ) : ℂ) *
    conj (Phi L hd ψ x)

theorem integrable_Ucoef (hd : d ≤ 3) (hε : 0 < ε) (α : ℝ) (ψ : ell2 d) :
    Integrable (Ucoef (L := L) hd ε α ψ) (μ L d) := by
  have hg : Continuous fun x => ((2 * Fprime ε α (‖Phi L hd ψ x‖ ^ 2) : ℝ) : ℂ) *
      conj (Phi L hd ψ x) :=
    (Complex.continuous_ofReal.comp (continuous_const.mul
      (continuous_Fprime_comp hε α (Phi L hd ψ).continuous))).mul
      (Complex.continuous_conj.comp (Phi L hd ψ).continuous)
  have hb : Integrable (fun x => ((‖(DL L ψ : L2 L d) x‖ ^ 2 : ℝ) : ℂ)) (μ L d) :=
    (integrable_norm_sq (DL L ψ)).ofReal
  refine (hb.bdd_mul' hg.aestronglyMeasurable (Eventually.of_forall fun x =>
    (⟨_, hg⟩ : C(Tor L d, ℂ)).norm_coe_le_norm x)).congr (Eventually.of_forall fun x => ?_)
  simp only [Ucoef]
  push_cast
  ring

/-- `W_ψ = 2F(|ψ|²) Δψ ∈ L²`. -/
def Wcoef (hd : d ≤ 3) (ε α : ℝ) (ψ : ell2 d) : L2 L d :=
  toL2' fun x => ((2 * F ε α (‖Phi L hd ψ x‖ ^ 2) : ℝ) : ℂ) * (DL L ψ : L2 L d) x

theorem coeFn_Wcoef (hd : d ≤ 3) (hε : 0 < ε) (α : ℝ) (ψ : ell2 d) :
    (Wcoef (L := L) hd ε α ψ : Tor L d → ℂ) =ᵐ[μ L d]
      fun x => ((2 * F ε α (‖Phi L hd ψ x‖ ^ 2) : ℝ) : ℂ) * (DL L ψ : L2 L d) x :=
  coeFn_toL2' (memLp_mul_continuous _ (Complex.continuous_ofReal.comp (continuous_const.mul
    (continuous_F_comp hε α (Phi L hd ψ).continuous))))

theorem re_mul_ofReal_conj (r : ℝ) (z w : ℂ) :
    (w * ((r : ℂ) * conj z)).re = r * (conj z * w).re := by
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re,
    Complex.conj_im, Complex.mul_im]
  ring

/-- `⟪W_ψ, g₁⟫_ℝ = ∫ 2F(|ψ|²) Re(conj(Δψ) g₁) dμ`. -/
theorem inner_Wcoef (hd : d ≤ 3) (hε : 0 < ε) (α : ℝ) (ψ : ell2 d) (g₁ : L2 L d) :
    inner ℝ (Wcoef (L := L) hd ε α ψ) g₁ =
      ∫ x, 2 * F ε α (‖Phi L hd ψ x‖ ^ 2) * (conj ((DL L ψ : L2 L d) x) * g₁ x).re ∂(μ L d) := by
  rw [real_inner_eq_re, L2.inner_def, ← RCLike.re_to_complex,
    ← integral_re (L2.integrable_inner (𝕜 := ℂ) _ _)]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_Wcoef (L := L) hd hε α ψ] with x hx
  rw [RCLike.inner_apply, hx, RCLike.re_to_complex, map_mul, Complex.conj_ofReal,
    re_mul_ofReal_conj]

/-! ### The derivative -/

variable (L) in
/-- **The Fréchet derivative of the E18 energy** at `ψ`, as a real-linear map on `H²`. -/
def DE (hd : d ≤ 3) (hε : 0 < ε) (α c₁ c₂ : ℝ) (ψ : ell2 d) : ell2 d →L[ℝ] ℝ :=
  (L ^ d) • (c₁ • ∑ j : Fin d, (2 : ℝ) •
      (innerSL ℝ (Dj L j ψ)).comp ((Dj L j).restrictScalars ℝ) +
    c₂ • ((pairC (Ucoef hd ε α ψ) (integrable_Ucoef hd hε α ψ)).comp
        ((Phi L hd).restrictScalars ℝ) +
      (innerSL ℝ (Wcoef hd ε α ψ)).comp ((DL L).restrictScalars ℝ)))

theorem DE_apply (hd : d ≤ 3) (hε : 0 < ε) (α c₁ c₂ : ℝ) (ψ h : ell2 d) :
    DE L hd hε α c₁ c₂ ψ h = L ^ d * (c₁ * ∑ j : Fin d, 2 * inner ℝ (Dj L j ψ) (Dj L j h) +
      c₂ * (∫ x, (Ucoef hd ε α ψ x * Phi L hd h x).re ∂(μ L d) +
        inner ℝ (Wcoef hd ε α ψ) (DL L h))) := by
  simp only [DE, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', innerSL_apply, smul_eq_mul, pairC_apply]

/-! ### The pointwise second-order remainder -/

/-- The coefficient of `δ²|Δψ|²` in the remainder bound. -/
def Pc (F₀ Δ K K₁ : ℝ) : ℝ := 2 * K * (2 * F₀ + Δ) ^ 2 + 2 * K₁ * F₀ + 2 * K₁

/-- The coefficient of `|Δh|²` in the remainder bound. -/
def Qc (F₀ Δ K K₁ MF : ℝ) : ℝ :=
  2 * K * (2 * F₀ + Δ) ^ 2 * Δ ^ 2 + 2 * K₁ * F₀ * (1 + Δ) + 2 * K₁ * Δ ^ 2 + MF

theorem Pc_nonneg {F₀ Δ K K₁ : ℝ} (hF0 : 0 ≤ F₀) (hK0 : 0 ≤ K) (hK₁0 : 0 ≤ K₁) :
    0 ≤ Pc F₀ Δ K K₁ := by
  unfold Pc
  positivity

theorem Qc_nonneg {F₀ Δ K K₁ MF : ℝ} (hF0 : 0 ≤ F₀) (hΔ : 0 ≤ Δ) (hK0 : 0 ≤ K) (hK₁0 : 0 ≤ K₁)
    (hMF : 0 ≤ MF) : 0 ≤ Qc F₀ Δ K K₁ MF := by
  unfold Qc
  positivity

theorem abs_add6 (a b c e f g : ℝ) :
    |a + b + c + e + f + g| ≤ |a| + |b| + |c| + |e| + |f| + |g| := by
  have h1 := abs_add (a + b + c + e + f) g
  have h2 := abs_add (a + b + c + e) f
  have h3 := abs_add (a + b + c) e
  have h4 := abs_add (a + b) c
  have h5 := abs_add a b
  linarith

theorem abs_re_conj_mul_le (z w : ℂ) : |(conj z * w).re| ≤ ‖z‖ * ‖w‖ := by
  calc |(conj z * w).re| ≤ ‖conj z * w‖ := Complex.abs_re_le_norm _
    _ = ‖z‖ * ‖w‖ := by rw [norm_mul, Complex.norm_conj]

/-- The six terms of `E18VariationAlgebra.weighted_laplacian_remainder`, bounded. -/
theorem six_bound {w dw B q W W₁ F₀ Δ K K₁ MF δ : ℝ} (hw0 : 0 ≤ w) (hw : w ≤ MF)
    (hdw : |dw| ≤ 2 * K₁ * F₀ * δ) (hB : |B| ≤ (K * (2 * F₀ + Δ) ^ 2 + K₁) * δ ^ 2)
    (hq : |q| ≤ W * W₁) (hδ0 : 0 ≤ δ) (hδΔ : δ ≤ Δ)
    (hK0 : 0 ≤ K) (hK₁0 : 0 ≤ K₁) (hF0 : 0 ≤ F₀) :
    |w * W₁ ^ 2 + 2 * dw * q + dw * W₁ ^ 2 + B * W ^ 2 + 2 * B * q + B * W₁ ^ 2| ≤
      Pc F₀ Δ K K₁ * δ ^ 2 * W ^ 2 + Qc F₀ Δ K K₁ MF * W₁ ^ 2 := by
  obtain ⟨Bc, hBc⟩ : ∃ Bc, Bc = K * (2 * F₀ + Δ) ^ 2 + K₁ := ⟨_, rfl⟩
  rw [← hBc] at hB
  have hBc0 : 0 ≤ Bc := by rw [hBc]; positivity
  have hδ2 : δ ^ 2 ≤ Δ ^ 2 := pow_le_pow_left₀ hδ0 hδΔ 2
  have hW₁2 := sq_nonneg W₁
  have hW2 := sq_nonneg W
  have u1 : |w * W₁ ^ 2| ≤ MF * W₁ ^ 2 := by
    rw [abs_mul, abs_of_nonneg hw0, abs_of_nonneg hW₁2]
    exact mul_le_mul_of_nonneg_right hw hW₁2
  have u2 : |2 * dw * q| ≤ 2 * K₁ * F₀ * δ ^ 2 * W ^ 2 + 2 * K₁ * F₀ * W₁ ^ 2 := by
    have hAM : 2 * (δ * W) * W₁ ≤ (δ * W) ^ 2 + W₁ ^ 2 := two_mul_le_add_sq _ _
    calc |2 * dw * q| = 2 * |dw| * |q| := by rw [abs_mul, abs_mul, abs_two]
      _ ≤ 2 * (2 * K₁ * F₀ * δ) * (W * W₁) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hdw zero_le_two) hq (abs_nonneg _)
            (by positivity)
      _ = (2 * K₁ * F₀) * (2 * (δ * W) * W₁) := by ring
      _ ≤ (2 * K₁ * F₀) * ((δ * W) ^ 2 + W₁ ^ 2) :=
          mul_le_mul_of_nonneg_left hAM (by positivity)
      _ = 2 * K₁ * F₀ * δ ^ 2 * W ^ 2 + 2 * K₁ * F₀ * W₁ ^ 2 := by ring
  have u3 : |dw * W₁ ^ 2| ≤ 2 * K₁ * F₀ * Δ * W₁ ^ 2 := by
    calc |dw * W₁ ^ 2| = |dw| * W₁ ^ 2 := by rw [abs_mul, abs_of_nonneg hW₁2]
      _ ≤ (2 * K₁ * F₀ * δ) * W₁ ^ 2 := mul_le_mul_of_nonneg_right hdw hW₁2
      _ ≤ (2 * K₁ * F₀ * Δ) * W₁ ^ 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hδΔ (by positivity)) hW₁2
  have u4 : |B * W ^ 2| ≤ Bc * δ ^ 2 * W ^ 2 := by
    rw [abs_mul, abs_of_nonneg hW2]
    exact mul_le_mul_of_nonneg_right hB hW2
  have u5 : |2 * B * q| ≤ Bc * δ ^ 2 * W ^ 2 + Bc * Δ ^ 2 * W₁ ^ 2 := by
    have hAM : 2 * W * W₁ ≤ W ^ 2 + W₁ ^ 2 := two_mul_le_add_sq _ _
    calc |2 * B * q| = 2 * |B| * |q| := by rw [abs_mul, abs_mul, abs_two]
      _ ≤ 2 * (Bc * δ ^ 2) * (W * W₁) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hB zero_le_two) hq (abs_nonneg _)
            (by positivity)
      _ = (Bc * δ ^ 2) * (2 * W * W₁) := by ring
      _ ≤ (Bc * δ ^ 2) * (W ^ 2 + W₁ ^ 2) := mul_le_mul_of_nonneg_left hAM (by positivity)
      _ = Bc * δ ^ 2 * W ^ 2 + Bc * (δ ^ 2 * W₁ ^ 2) := by ring
      _ ≤ Bc * δ ^ 2 * W ^ 2 + Bc * (Δ ^ 2 * W₁ ^ 2) :=
          add_le_add_left (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hδ2 hW₁2) hBc0) _
      _ = Bc * δ ^ 2 * W ^ 2 + Bc * Δ ^ 2 * W₁ ^ 2 := by ring
  have u6 : |B * W₁ ^ 2| ≤ Bc * Δ ^ 2 * W₁ ^ 2 := by
    rw [abs_mul, abs_of_nonneg hW₁2]
    calc |B| * W₁ ^ 2 ≤ (Bc * δ ^ 2) * W₁ ^ 2 := mul_le_mul_of_nonneg_right hB hW₁2
      _ ≤ (Bc * Δ ^ 2) * W₁ ^ 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hδ2 hBc0) hW₁2
  calc _ ≤ |w * W₁ ^ 2| + |2 * dw * q| + |dw * W₁ ^ 2| + |B * W ^ 2| + |2 * B * q| +
        |B * W₁ ^ 2| := abs_add6 _ _ _ _ _ _
    _ ≤ MF * W₁ ^ 2 + (2 * K₁ * F₀ * δ ^ 2 * W ^ 2 + 2 * K₁ * F₀ * W₁ ^ 2) +
        2 * K₁ * F₀ * Δ * W₁ ^ 2 + Bc * δ ^ 2 * W ^ 2 +
        (Bc * δ ^ 2 * W ^ 2 + Bc * Δ ^ 2 * W₁ ^ 2) + Bc * Δ ^ 2 * W₁ ^ 2 := by
        linarith
    _ = _ := by rw [hBc, Pc, Qc]; ring

/-- The variation of the weight: `B = F(a′) − F(a) − F′(a)·2p` for `a′ = a + 2p + y₁`. -/
theorem weight_variation_bound {a a' p y₁ Fa Fa' Fd K K₁ F₀ Δ δ : ℝ}
    (hR : |Fa' - Fa - Fd * (a' - a)| ≤ K * (a' - a) ^ 2) (ea : a' = a + 2 * p + y₁)
    (hp : |p| ≤ F₀ * δ) (hy₁0 : 0 ≤ y₁) (hy₁ : y₁ ≤ δ ^ 2) (hFd : |Fd| ≤ K₁) (hK0 : 0 ≤ K)
    (hδ0 : 0 ≤ δ) (hδΔ : δ ≤ Δ) :
    |Fa' - Fa - Fd * (2 * p)| ≤ (K * (2 * F₀ + Δ) ^ 2 + K₁) * δ ^ 2 := by
  have hda : |a' - a| ≤ (2 * F₀ + Δ) * δ := by
    rw [ea, show a + 2 * p + y₁ - a = 2 * p + y₁ by ring]
    calc |2 * p + y₁| ≤ |2 * p| + |y₁| := abs_add _ _
      _ = 2 * |p| + y₁ := by rw [abs_mul, abs_two, abs_of_nonneg hy₁0]
      _ ≤ 2 * (F₀ * δ) + δ ^ 2 := by linarith
      _ ≤ (2 * F₀ + Δ) * δ := by nlinarith [mul_nonneg hδ0 (sub_nonneg.2 hδΔ)]
  have hda2 : (a' - a) ^ 2 ≤ (2 * F₀ + Δ) ^ 2 * δ ^ 2 := by
    rw [← mul_pow, ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hda 2
  have e : Fa' - Fa - Fd * (2 * p) = (Fa' - Fa - Fd * (a' - a)) + Fd * y₁ := by rw [ea]; ring
  rw [e]
  calc |(Fa' - Fa - Fd * (a' - a)) + Fd * y₁| ≤ |Fa' - Fa - Fd * (a' - a)| + |Fd * y₁| :=
        abs_add _ _
    _ ≤ K * ((2 * F₀ + Δ) ^ 2 * δ ^ 2) + K₁ * δ ^ 2 := by
        refine add_le_add (hR.trans (mul_le_mul_of_nonneg_left hda2 hK0)) ?_
        rw [abs_mul, abs_of_nonneg hy₁0]
        exact mul_le_mul hFd hy₁ hy₁0 ((abs_nonneg _).trans hFd)
    _ = (K * (2 * F₀ + Δ) ^ 2 + K₁) * δ ^ 2 := by ring

/-- **The pointwise second-order remainder** of `(z, w) ↦ F(|z|²)|w|²`, obtained from the exact
six-term identity `E18VariationAlgebra.weighted_laplacian_remainder`. -/
theorem rem_pointwise (hε : 0 < ε) (α : ℝ) {F₀ Δ K K₁ δ : ℝ}
    (hK : ∀ a ∈ Icc 0 ((F₀ + Δ) ^ 2), ∀ b ∈ Icc 0 ((F₀ + Δ) ^ 2),
      |F ε α b - F ε α a - Fprime ε α a * (b - a)| ≤ K * (b - a) ^ 2)
    (hK₁ : ∀ t ∈ Icc 0 ((F₀ + Δ) ^ 2), |Fprime ε α t| ≤ K₁) (hK0 : 0 ≤ K) (hK₁0 : 0 ≤ K₁)
    {z z₁ w w₁ : ℂ} (hz : ‖z‖ ≤ F₀) (hz₁ : ‖z₁‖ ≤ δ) (hδΔ : δ ≤ Δ) :
    |F ε α (‖z + z₁‖ ^ 2) * ‖w + w₁‖ ^ 2 - F ε α (‖z‖ ^ 2) * ‖w‖ ^ 2 -
        ((2 * Fprime ε α (‖z‖ ^ 2) * ‖w‖ ^ 2) * (conj z * z₁).re +
          2 * F ε α (‖z‖ ^ 2) * (conj w * w₁).re)| ≤
      Pc F₀ Δ K K₁ * δ ^ 2 * ‖w‖ ^ 2 + Qc F₀ Δ K K₁ (Mw ε α ^ 2) * ‖w₁‖ ^ 2 := by
  have hF0 : 0 ≤ F₀ := (norm_nonneg _).trans hz
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans hz₁
  have hamem : ‖z‖ ^ 2 ∈ Icc 0 ((F₀ + Δ) ^ 2) :=
    ⟨sq_nonneg _, pow_le_pow_left₀ (norm_nonneg _) (by linarith) 2⟩
  have ha'mem : ‖z + z₁‖ ^ 2 ∈ Icc 0 ((F₀ + Δ) ^ 2) :=
    ⟨sq_nonneg _, pow_le_pow_left₀ (norm_nonneg _) ((norm_add_le _ _).trans (by linarith)) 2⟩
  obtain ⟨dw, hdw⟩ : ∃ dw, dw = Fprime ε α (‖z‖ ^ 2) * (2 * (conj z * z₁).re) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = F ε α (‖z + z₁‖ ^ 2) - F ε α (‖z‖ ^ 2) - dw := ⟨_, rfl⟩
  have key := E18VariationAlgebra.weighted_laplacian_remainder (F ε α (‖z‖ ^ 2)) dw B w w₁
  have e : F ε α (‖z + z₁‖ ^ 2) * ‖w + w₁‖ ^ 2 - F ε α (‖z‖ ^ 2) * ‖w‖ ^ 2 -
        ((2 * Fprime ε α (‖z‖ ^ 2) * ‖w‖ ^ 2) * (conj z * z₁).re +
          2 * F ε α (‖z‖ ^ 2) * (conj w * w₁).re) =
      (F ε α (‖z‖ ^ 2) + dw + B) * ‖w + w₁‖ ^ 2 - F ε α (‖z‖ ^ 2) * ‖w‖ ^ 2 -
        (2 * F ε α (‖z‖ ^ 2) * (conj w * w₁).re + dw * ‖w‖ ^ 2) := by
    rw [hB, hdw]; ring
  rw [e, key]
  have hpz : |(conj z * z₁).re| ≤ F₀ * δ :=
    (abs_re_conj_mul_le z z₁).trans (mul_le_mul hz hz₁ (norm_nonneg _) hF0)
  refine six_bound (F_nonneg ε α (sq_nonneg _)) (F_le hε α (sq_nonneg _)) ?_ ?_
    (abs_re_conj_mul_le w w₁) hδ0 hδΔ hK0 hK₁0 hF0
  · rw [hdw, abs_mul, abs_mul, abs_two]
    calc |Fprime ε α (‖z‖ ^ 2)| * (2 * |(conj z * z₁).re|) ≤ K₁ * (2 * (F₀ * δ)) :=
          mul_le_mul (hK₁ _ hamem) (mul_le_mul_of_nonneg_left hpz zero_le_two) (by positivity)
            hK₁0
      _ = 2 * K₁ * F₀ * δ := by ring
  · rw [hB, hdw]
    exact weight_variation_bound (hK _ hamem _ ha'mem) (E18VariationAlgebra.norm_sq_add z z₁)
      hpz (sq_nonneg _) (pow_le_pow_left₀ (norm_nonneg _) hz₁ 2) (hK₁ _ hamem) hK0 hδ0 hδΔ

/-! ### The integrated remainder -/

/-- **The second-order remainder of `J(f, g) = ⨍ F(|f|²)|g|²` on `C(𝕋_L^d; ℂ) × L²`.** -/
theorem curvJ_remainder (hε : 0 < ε) (α : ℝ) {F₀ Δ K K₁ : ℝ}
    (hK : ∀ a ∈ Icc 0 ((F₀ + Δ) ^ 2), ∀ b ∈ Icc 0 ((F₀ + Δ) ^ 2),
      |F ε α b - F ε α a - Fprime ε α a * (b - a)| ≤ K * (b - a) ^ 2)
    (hK₁ : ∀ t ∈ Icc 0 ((F₀ + Δ) ^ 2), |Fprime ε α t| ≤ K₁) (hK0 : 0 ≤ K) (hK₁0 : 0 ≤ K₁)
    (f f₁ : C(Tor L d, ℂ)) (g g₁ : L2 L d) (hf : ‖f‖ ≤ F₀) (hf₁ : ‖f₁‖ ≤ Δ)
    (i1 : Integrable (fun x => F ε α (‖f x + f₁ x‖ ^ 2) * ‖g x + g₁ x‖ ^ 2) (μ L d))
    (i2 : Integrable (fun x => F ε α (‖f x‖ ^ 2) * ‖g x‖ ^ 2) (μ L d))
    (i3 : Integrable (fun x => (2 * Fprime ε α (‖f x‖ ^ 2) * ‖g x‖ ^ 2) *
      (conj (f x) * f₁ x).re) (μ L d))
    (i4 : Integrable (fun x => 2 * F ε α (‖f x‖ ^ 2) * (conj (g x) * g₁ x).re) (μ L d)) :
    |∫ x, F ε α (‖f x + f₁ x‖ ^ 2) * ‖g x + g₁ x‖ ^ 2 ∂(μ L d) -
        ∫ x, F ε α (‖f x‖ ^ 2) * ‖g x‖ ^ 2 ∂(μ L d) -
        (∫ x, (2 * Fprime ε α (‖f x‖ ^ 2) * ‖g x‖ ^ 2) * (conj (f x) * f₁ x).re ∂(μ L d) +
          ∫ x, 2 * F ε α (‖f x‖ ^ 2) * (conj (g x) * g₁ x).re ∂(μ L d))| ≤
      Pc F₀ Δ K K₁ * ‖f₁‖ ^ 2 * ‖g‖ ^ 2 + Qc F₀ Δ K K₁ (Mw ε α ^ 2) * ‖g₁‖ ^ 2 := by
  have i12 : Integrable (fun x => F ε α (‖f x + f₁ x‖ ^ 2) * ‖g x + g₁ x‖ ^ 2 -
      F ε α (‖f x‖ ^ 2) * ‖g x‖ ^ 2) (μ L d) := i1.sub i2
  have i34 : Integrable (fun x => (2 * Fprime ε α (‖f x‖ ^ 2) * ‖g x‖ ^ 2) *
      (conj (f x) * f₁ x).re + 2 * F ε α (‖f x‖ ^ 2) * (conj (g x) * g₁ x).re) (μ L d) :=
    i3.add i4
  have ia : Integrable (fun x => Pc F₀ Δ K K₁ * ‖f₁‖ ^ 2 * ‖g x‖ ^ 2) (μ L d) :=
    (integrable_norm_sq g).const_mul _
  have ib : Integrable (fun x => Qc F₀ Δ K K₁ (Mw ε α ^ 2) * ‖g₁ x‖ ^ 2) (μ L d) :=
    (integrable_norm_sq g₁).const_mul _
  have iab : Integrable (fun x => Pc F₀ Δ K K₁ * ‖f₁‖ ^ 2 * ‖g x‖ ^ 2 +
      Qc F₀ Δ K K₁ (Mw ε α ^ 2) * ‖g₁ x‖ ^ 2) (μ L d) := ia.add ib
  rw [← integral_add i3 i4, ← integral_sub i1 i2, ← integral_sub i12 i34, ← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le iab (Eventually.of_forall fun x => ?_)).trans
    (le_of_eq ?_)
  · rw [Real.norm_eq_abs]
    exact rem_pointwise hε α hK hK₁ hK0 hK₁0 ((f.norm_coe_le_norm x).trans hf)
      (f₁.norm_coe_le_norm x) hf₁
  · rw [integral_add ia ib, integral_const_mul, integral_const_mul, ← norm_sq_eq_integral,
      ← norm_sq_eq_integral]

variable (L) in
/-- The curvature part `⨍ F(|ψ|²)|Δψ|²` of the energy. -/
def curv (hd : d ≤ 3) (ε α : ℝ) (ψ : ell2 d) : ℝ :=
  ∫ x, F ε α (‖Phi L hd ψ x‖ ^ 2) * ‖(DL L ψ : L2 L d) x‖ ^ 2 ∂(μ L d)

theorem energy_eq_curv (hd : d ≤ 3) (c₁ c₂ ε α : ℝ) (ψ : ell2 d) :
    energy (L := L) hd c₁ c₂ ε α ψ =
      L ^ d * (c₁ * ∑ j : Fin d, ‖Dj L j ψ‖ ^ 2 + c₂ * curv L hd ε α ψ) := rfl

theorem integrable_W_term (hd : d ≤ 3) (hε : 0 < ε) (α : ℝ) (ψ : ell2 d) (g₁ : L2 L d) :
    Integrable (fun x => 2 * F ε α (‖Phi L hd ψ x‖ ^ 2) *
      (conj ((DL L ψ : L2 L d) x) * g₁ x).re) (μ L d) := by
  refine (L2.integrable_inner (𝕜 := ℂ) (Wcoef (L := L) hd ε α ψ) g₁).re.congr ?_
  filter_upwards [coeFn_Wcoef (L := L) hd hε α ψ] with x hx
  rw [RCLike.inner_apply, hx, RCLike.re_to_complex, map_mul, Complex.conj_ofReal,
    re_mul_ofReal_conj, mul_assoc]

theorem Ucoef_mul_re (hd : d ≤ 3) (ψ h : ell2 d) (x : Tor L d) :
    (Ucoef hd ε α ψ x * Phi L hd h x).re =
      (2 * Fprime ε α (‖Phi L hd ψ x‖ ^ 2) * ‖(DL L ψ : L2 L d) x‖ ^ 2) *
        (conj (Phi L hd ψ x) * Phi L hd h x).re := by
  simp only [Ucoef]
  rw [mul_assoc, Complex.re_ofReal_mul]

/-- **The explicit quadratic remainder on bounded `H²` sets**: for `‖ψ‖, ‖h‖ ≤ M`,
`|ℰ[ψ + h] − ℰ[ψ] − DE ψ h| ≤ C_M ‖h‖²_{H²}`. -/
theorem energy_remainder (hd : d ≤ 3) (hε : 0 < ε) (α c₁ c₂ M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ h : ell2 d, ‖ψ‖ ≤ M → ‖h‖ ≤ M →
      |energy (L := L) hd c₁ c₂ ε α (ψ + h) - energy (L := L) hd c₁ c₂ ε α ψ -
        DE L hd hε α c₁ c₂ ψ h| ≤ C * ‖h‖ ^ 2 := by
  obtain ⟨M₀, hM₀def⟩ : ∃ M₀, M₀ = max M 0 := ⟨_, rfl⟩
  have hM₀ : 0 ≤ M₀ := hM₀def ▸ le_max_right _ _
  obtain ⟨F₀, hF₀def⟩ : ∃ F₀, F₀ = sob L d * M₀ := ⟨_, rfl⟩
  have hF₀ : 0 ≤ F₀ := hF₀def ▸ mul_nonneg sob_nonneg hM₀
  obtain ⟨K, hK0, hK⟩ := taylor_F hε α ((F₀ + F₀) ^ 2)
  obtain ⟨K₁, hK₁0, hK₁⟩ := bound_Fprime hε α ((F₀ + F₀) ^ 2)
  have hP := Pc_nonneg (Δ := F₀) hF₀ hK0 hK₁0
  have hQ := Qc_nonneg hF₀ hF₀ hK0 hK₁0 (sq_nonneg (Mw ε α))
  refine ⟨L ^ d * (|c₁| * d + |c₂| * (Pc F₀ F₀ K K₁ * sob L d ^ 2 * M₀ ^ 2 +
    Qc F₀ F₀ K K₁ (Mw ε α ^ 2))), mul_nonneg (pow_pos hL.out d).le
      (add_nonneg (mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _)) (mul_nonneg (abs_nonneg _)
        (add_nonneg (mul_nonneg (mul_nonneg hP (sq_nonneg _)) (sq_nonneg _)) hQ))),
    fun ψ h hψ hh => ?_⟩
  have hMψ : ‖ψ‖ ≤ M₀ := hM₀def ▸ hψ.trans (le_max_left _ _)
  have hMh : ‖h‖ ≤ M₀ := hM₀def ▸ hh.trans (le_max_left _ _)
  have hfψ : ‖Phi L hd ψ‖ ≤ F₀ :=
    hF₀def ▸ (norm_Phi_le hd ψ).trans (mul_le_mul_of_nonneg_left hMψ sob_nonneg)
  have hfh : ‖Phi L hd h‖ ≤ F₀ :=
    hF₀def ▸ (norm_Phi_le hd h).trans (mul_le_mul_of_nonneg_left hMh sob_nonneg)
  have hadd : (DL L (ψ + h) : Tor L d → ℂ) =ᵐ[μ L d]
      fun x => (DL L ψ : L2 L d) x + (DL L h : L2 L d) x := by
    rw [map_add]; exact Lp.coeFn_add _ _
  have e1 : curv L hd ε α (ψ + h) = ∫ x, F ε α (‖Phi L hd ψ x + Phi L hd h x‖ ^ 2) *
      ‖(DL L ψ : L2 L d) x + (DL L h : L2 L d) x‖ ^ 2 ∂(μ L d) := by
    refine integral_congr_ae ?_
    filter_upwards [hadd] with x hx
    rw [hx]
    simp only [map_add, ContinuousMap.add_apply]
  have i1 : Integrable (fun x => F ε α (‖Phi L hd ψ x + Phi L hd h x‖ ^ 2) *
      ‖(DL L ψ : L2 L d) x + (DL L h : L2 L d) x‖ ^ 2) (μ L d) := by
    refine (curvature_integrable (L := L) hd hε α (ψ + h)).congr ?_
    filter_upwards [hadd] with x hx
    rw [hx]
    simp only [map_add, ContinuousMap.add_apply]
  have i3 : Integrable (fun x => (2 * Fprime ε α (‖Phi L hd ψ x‖ ^ 2) *
      ‖(DL L ψ : L2 L d) x‖ ^ 2) * (conj (Phi L hd ψ x) * Phi L hd h x).re) (μ L d) :=
    (integrable_pairC (integrable_Ucoef (L := L) hd hε α ψ) (Phi L hd h)).congr
      (Eventually.of_forall fun x => Ucoef_mul_re hd ψ h x)
  have e3 : ∫ x, (Ucoef hd ε α ψ x * Phi L hd h x).re ∂(μ L d) =
      ∫ x, (2 * Fprime ε α (‖Phi L hd ψ x‖ ^ 2) * ‖(DL L ψ : L2 L d) x‖ ^ 2) *
        (conj (Phi L hd ψ x) * Phi L hd h x).re ∂(μ L d) :=
    integral_congr_ae (Eventually.of_forall fun x => Ucoef_mul_re hd ψ h x)
  have hJ := curvJ_remainder hε α hK hK₁ hK0 hK₁0 (Phi L hd ψ) (Phi L hd h) (DL L ψ) (DL L h)
    hfψ hfh i1 (curvature_integrable (L := L) hd hε α ψ) i3
    (integrable_W_term (L := L) hd hε α ψ (DL L h))
  have e2 : curv L hd ε α ψ = ∫ x, F ε α (‖Phi L hd ψ x‖ ^ 2) * ‖(DL L ψ : L2 L d) x‖ ^ 2
      ∂(μ L d) := rfl
  rw [← e1, ← e2, ← e3, ← inner_Wcoef hd hε α ψ (DL L h)] at hJ
  have hgrad : ∀ j, ‖Dj L j (ψ + h)‖ ^ 2 =
      ‖Dj L j ψ‖ ^ 2 + 2 * inner ℝ (Dj L j ψ) (Dj L j h) + ‖Dj L j h‖ ^ 2 := fun j => by
    rw [map_add, norm_add_sq_real]
  have eE : energy (L := L) hd c₁ c₂ ε α (ψ + h) - energy (L := L) hd c₁ c₂ ε α ψ -
      DE L hd hε α c₁ c₂ ψ h = L ^ d * (c₁ * ∑ j : Fin d, ‖Dj L j h‖ ^ 2 +
        c₂ * (curv L hd ε α (ψ + h) - curv L hd ε α ψ -
          (∫ x, (Ucoef hd ε α ψ x * Phi L hd h x).re ∂(μ L d) +
            inner ℝ (Wcoef hd ε α ψ) (DL L h)))) := by
    rw [energy_eq_curv, energy_eq_curv, DE_apply]
    simp only [hgrad, Finset.sum_add_distrib]
    ring
  have hsumh : ∑ j : Fin d, ‖Dj L j h‖ ^ 2 ≤ d * ‖h‖ ^ 2 := by
    calc ∑ j : Fin d, ‖Dj L j h‖ ^ 2 ≤ ∑ j : Fin d, ‖h‖ ^ 2 :=
          Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (norm_nonneg _) (norm_Dj_le j h) 2
      _ = d * ‖h‖ ^ 2 := by simp
  have hs0 : 0 ≤ ∑ j : Fin d, ‖Dj L j h‖ ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have h1 : ‖Phi L hd h‖ ^ 2 ≤ sob L d ^ 2 * ‖h‖ ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (norm_Phi_le hd h) 2
  have h2 : ‖DL L ψ‖ ^ 2 ≤ M₀ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) ((norm_DL_le ψ).trans hMψ) 2
  have h3 : ‖DL L h‖ ^ 2 ≤ ‖h‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (norm_DL_le h) 2
  have hcurv := hJ.trans (show Pc F₀ F₀ K K₁ * ‖Phi L hd h‖ ^ 2 * ‖DL L ψ‖ ^ 2 +
      Qc F₀ F₀ K K₁ (Mw ε α ^ 2) * ‖DL L h‖ ^ 2 ≤ (Pc F₀ F₀ K K₁ * sob L d ^ 2 * M₀ ^ 2 +
        Qc F₀ F₀ K K₁ (Mw ε α ^ 2)) * ‖h‖ ^ 2 by
    calc Pc F₀ F₀ K K₁ * ‖Phi L hd h‖ ^ 2 * ‖DL L ψ‖ ^ 2 +
          Qc F₀ F₀ K K₁ (Mw ε α ^ 2) * ‖DL L h‖ ^ 2 ≤
        Pc F₀ F₀ K K₁ * (sob L d ^ 2 * ‖h‖ ^ 2) * M₀ ^ 2 + Qc F₀ F₀ K K₁ (Mw ε α ^ 2) * ‖h‖ ^ 2 :=
          add_le_add (mul_le_mul (mul_le_mul_of_nonneg_left h1 hP) h2 (sq_nonneg _)
            (mul_nonneg hP (by positivity))) (mul_le_mul_of_nonneg_left h3 hQ)
      _ = _ := by ring)
  rw [eE, abs_mul, abs_of_pos (pow_pos hL.out d)]
  calc L ^ d * |c₁ * ∑ j : Fin d, ‖Dj L j h‖ ^ 2 +
        c₂ * (curv L hd ε α (ψ + h) - curv L hd ε α ψ -
          (∫ x, (Ucoef hd ε α ψ x * Phi L hd h x).re ∂(μ L d) +
            inner ℝ (Wcoef hd ε α ψ) (DL L h)))| ≤
      L ^ d * (|c₁| * (d * ‖h‖ ^ 2) + |c₂| * ((Pc F₀ F₀ K K₁ * sob L d ^ 2 * M₀ ^ 2 +
        Qc F₀ F₀ K K₁ (Mw ε α ^ 2)) * ‖h‖ ^ 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ (pow_pos hL.out d).le
        refine (abs_add _ _).trans ?_
        rw [abs_mul, abs_mul, abs_of_nonneg hs0]
        exact add_le_add (mul_le_mul_of_nonneg_left hsumh (abs_nonneg _))
          (mul_le_mul_of_nonneg_left hcurv (abs_nonneg _))
    _ = _ := by ring

/-- **`ℰ` is Fréchet differentiable on `H²(𝕋_L^d; ℂ)` with derivative `DE ψ`.** -/
theorem hasFDerivAt_energy (hd : d ≤ 3) (hε : 0 < ε) (α c₁ c₂ : ℝ) (ψ : ell2 d) :
    HasFDerivAt (energy (L := L) hd c₁ c₂ ε α) (DE L hd hε α c₁ c₂ ψ) ψ := by
  obtain ⟨C, _, hC⟩ := energy_remainder (L := L) hd hε α c₁ c₂ (‖ψ‖ + 1)
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  refine (IsBigO.of_bound C ?_).trans_isLittleO (isLittleO_norm_pow_id one_lt_two)
  filter_upwards [Metric.closedBall_mem_nhds (0 : ell2 d) one_pos] with h hh
  rw [mem_closedBall_zero_iff] at hh
  rw [Real.norm_eq_abs, norm_pow, norm_norm]
  exact hC ψ h (by linarith) (by linarith [norm_nonneg ψ])

end E18

end ReyesMath
