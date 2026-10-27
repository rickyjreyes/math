import Mathlib

/-!
# The Sobolev space `H²(ℝ^d; ℂ)`

Infrastructure for the whole-space fourth-order variational papers.

* Schwartz calculus: `dS` (`∂ᵢ`), `lapS` (`lapS_apply`: Mathlib's Laplacian `Δ`), `toL2`;
  `fourier_dS` (`𝓕(∂ᵢφ) = 2πiξᵢ 𝓕φ`), `fourier_lapS` (`𝓕(Δφ) = −|2πξ|² 𝓕φ`), `parseval`
  (`∫ φ̄ψ = ∫ \overline{𝓕φ} 𝓕ψ`), `norm_toL2_sq_fourier` (Plancherel on `𝓢`),
  `inner_toL2_lapS`, `inner_toL2_dS`, `re_inner_lapS_self`.
* `H2 d`: `H²(ℝ^d; ℂ)` as the closure of `{(φ, ∇φ, Δφ) : φ ∈ 𝓢}` in `L² × (L²)^d × L²`
  (the domain of the closed Laplacian); `H2.ext_of_val`: the strong gradient and Laplacian are
  determined by the function. Functionals `M = ‖u‖²`, `K = ‖∇u‖²`, `D = ‖Δu‖²`, `Q = ‖u‖⁴_{L⁴}`,
  `S = ‖u‖⁶_{L⁶}`; `re_inner_lap_val` (`Re⟪Δu,u⟫ = −K`), `K_le_sqrt` (`K ≤ √(MD)`),
  `normSq_shift` (`‖(Δ+k²)u‖² = D − 2k²K + k⁴M`).
* Two dimensions: `integral_inv_quartic` (`∫_{ℝ²} dξ/(|2πξ|⁴ + η) = 1/(8√η)`),
  `sup_bound_schwartz`, `H2.ae_sup_bound` (`‖u‖²_∞ ≤ (D + ηM)/(8√η)`), `H2.ae_sup_bound_opt`
  (`‖u‖²_∞ ≤ ¼√(MD)`), `H2.integrable_Q`, `H2.integrable_S`, `H2.S_le`.
* Dilations `u_λ = λ^{d/2} u(λ·)`: `H2.dil`, `H2.M_dil`, `H2.K_dil`, `H2.D_dil`,
  `H2.integral_dil`.
-/

open Filter Topology Complex InnerProductSpace MeasureTheory Set
open scoped ContDiff FourierTransform

namespace ReyesMath

namespace Sobolev

variable {d : ℕ}

local notation "Rd" => EuclideanSpace ℝ (Fin d)

/-- `L²(ℝ^d; ℂ)`. -/
noncomputable abbrev L2 (d : ℕ) := Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))

/-- The coordinate vector `eᵢ`. -/
noncomputable def ev (i : Fin d) : Rd := EuclideanSpace.single i (1 : ℝ)

/-- The partial derivative `∂ᵢ` on Schwartz space. -/
noncomputable def dS (i : Fin d) : SchwartzMap Rd ℂ →L[ℂ] SchwartzMap Rd ℂ :=
  SchwartzMap.pderivCLM ℂ (ev i)

theorem dS_apply (i : Fin d) (φ : SchwartzMap Rd ℂ) (x : Rd) :
    dS i φ x = fderiv ℝ (⇑φ) x (ev i) := rfl

/-- The Laplacian `Δ = Σᵢ ∂ᵢ²` on Schwartz space. -/
noncomputable def lapS : SchwartzMap Rd ℂ →L[ℂ] SchwartzMap Rd ℂ :=
  ∑ i : Fin d, (dS i).comp (dS i)

/-- `lapS` is Mathlib's Laplacian. -/
theorem lapS_apply (φ : SchwartzMap Rd ℂ) (x : Rd) : lapS φ x = Δ (⇑φ) x := by
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis (⇑φ) (EuclideanSpace.basisFun (Fin d) ℝ)]
  simp only [lapS, ContinuousLinearMap.coe_sum', ContinuousLinearMap.coe_comp',
    Finset.sum_apply, Function.comp_apply, iteratedFDeriv_two_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, EuclideanSpace.basisFun_apply]
  rw [show ∀ (s : Finset (Fin d)) (f : Fin d → SchwartzMap Rd ℂ), (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x
    from fun s f => by
      classical
      induction s using Finset.induction_on with
      | empty => simp
      | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, SchwartzMap.add_apply, ih]]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dS_apply]
  have h1 : ⇑(dS i φ) = fun y => fderiv ℝ (⇑φ) y (ev i) := rfl
  rw [h1]
  have hd : DifferentiableAt ℝ (fderiv ℝ (⇑φ)) x :=
    ((φ.smooth ⊤).fderiv_right (m := 1) (WithTop.coe_le_coe.2 le_top)).differentiable le_rfl x
  rw [fderiv_clm_apply hd (differentiableAt_const _)]
  simp [ev]

/-- `q(ξ) = |2πξ|²`, the symbol of `−Δ` in Mathlib's Fourier convention. -/
noncomputable def qS (ξ : Rd) : ℝ := (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2

theorem qS_nonneg (ξ : Rd) : 0 ≤ qS ξ := by
  unfold qS
  positivity

theorem conj_fourierChar' (y : ℝ) : (starRingEnd ℂ) (𝐞 y : ℂ) = (𝐞 (-y) : ℂ) := by
  rw [Real.fourierChar_apply, Real.fourierChar_apply, ← Complex.exp_conj, map_mul,
    Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring_nf

/-- `𝓕(conj g) = conj (𝓕⁻ g)`. -/
theorem fourier_conj (g : Rd → ℂ) (x : Rd) :
    𝓕 (fun ξ => (starRingEnd ℂ) (g ξ)) x = (starRingEnd ℂ) (𝓕⁻ g x) := by
  rw [Real.fourierIntegral_eq, Real.fourierIntegralInv_eq, ← integral_conj]
  congr 1
  funext ξ
  simp only [Circle.smul_def, smul_eq_mul, map_mul, conj_fourierChar']

/-- Evaluation commutes with the Fourier transform of an operator-valued function. -/
theorem fourier_clm_apply {F : Rd → (Rd →L[ℝ] ℂ)} (hF : Integrable F) (a ξ : Rd) :
    𝓕 F ξ a = 𝓕 (fun x => F x a) ξ := by
  rw [Real.fourierIntegral_eq, Real.fourierIntegral_eq,
    ContinuousLinearMap.integral_apply ((Real.fourierIntegral_convergent_iff ξ).2 hF)]
  rfl

theorem inner_ev (ξ : Rd) (i : Fin d) : inner ℝ ξ (ev i) = ξ i := by
  simp [ev, EuclideanSpace.inner_single_right]

/-- `𝓕(∂ᵢφ)(ξ) = 2πi ξᵢ 𝓕φ(ξ)`. -/
theorem fourier_dS (i : Fin d) (φ : SchwartzMap Rd ℂ) (ξ : Rd) :
    𝓕 (⇑(dS i φ)) ξ = (2 * Real.pi * Complex.I * (ξ i : ℂ)) * 𝓕 (⇑φ) ξ := by
  have hint : Integrable (fderiv ℝ (⇑φ)) := (SchwartzMap.fderivCLM ℂ φ).integrable
  have h := Real.fourierIntegral_fderiv φ.integrable φ.differentiable hint
  have h1 : ⇑(dS i φ) = fun x => fderiv ℝ (⇑φ) x (ev i) := rfl
  rw [h1, ← fourier_clm_apply hint, h]
  simp only [VectorFourier.fourierSMulRight, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.neg_apply, innerSL_apply, inner_ev]
  rw [smul_eq_mul]
  simp only [Complex.real_smul, Complex.ofReal_neg]
  ring

theorem coe_sum_schwartz (s : Finset (Fin d)) (f : Fin d → SchwartzMap Rd ℂ) (x : Rd) :
    (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, SchwartzMap.add_apply, ih]

/-- `𝓕(Δφ)(ξ) = −|2πξ|² 𝓕φ(ξ)`. -/
theorem fourier_lapS (φ : SchwartzMap Rd ℂ) (ξ : Rd) :
    𝓕 (⇑(lapS φ)) ξ = -(qS ξ : ℂ) * 𝓕 (⇑φ) ξ := by
  have hF : ∀ f : SchwartzMap Rd ℂ, 𝓕 (⇑f) = ⇑(SchwartzMap.fourierTransformCLM ℂ f) :=
    fun f => by rw [SchwartzMap.fourierTransformCLM_apply]
  have hlap : lapS φ = ∑ i : Fin d, dS i (dS i φ) := by
    simp [lapS]
  rw [hF, hlap, map_sum, coe_sum_schwartz]
  simp_rw [← hF, fourier_dS, ← mul_assoc]
  rw [← Finset.sum_mul]
  congr 1
  have hreal : ∑ i : Fin d, (2 * Real.pi * ξ i) ^ 2 = qS ξ := by
    rw [qS, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Real.norm_eq_abs, sq_abs]
    ring
  calc ∑ i : Fin d, 2 * (Real.pi : ℂ) * Complex.I * (ξ i : ℂ) * 2 * (Real.pi : ℂ) *
        Complex.I * (ξ i : ℂ)
      = ∑ i : Fin d, -((((2 * Real.pi * ξ i) ^ 2 : ℝ)) : ℂ) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
        push_cast
        linear_combination (4 * (Real.pi : ℂ) ^ 2 * (ξ i : ℂ) ^ 2) * hI
    _ = -(qS ξ : ℂ) := by rw [Finset.sum_neg_distrib, ← Complex.ofReal_sum, hreal]

/-- **Parseval for Schwartz functions:** `∫ φ̄ ψ = ∫ \overline{𝓕φ} 𝓕ψ`. -/
theorem parseval (φ ψ : SchwartzMap Rd ℂ) :
    ∫ x, (starRingEnd ℂ) (φ x) * ψ x = ∫ ξ, (starRingEnd ℂ) (𝓕 (⇑φ) ξ) * 𝓕 (⇑ψ) ξ := by
  have hFφ : Integrable (𝓕 (⇑φ)) := by
    have := (SchwartzMap.fourierTransformCLM ℂ φ).integrable (μ := volume)
    rwa [SchwartzMap.fourierTransformCLM_apply] at this
  have hg : Integrable fun ξ => (starRingEnd ℂ) (𝓕 (⇑φ) ξ) :=
    hFφ.norm.mono' (Complex.continuous_conj.comp_aestronglyMeasurable hFφ.1)
      (Eventually.of_forall fun x => by simp)
  have hflip := VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ Rd)
    (μ := volume) (ν := volume) Real.continuous_fourierChar continuous_inner ψ.integrable hg
  have hinv : 𝓕⁻ (𝓕 (⇑φ)) = ⇑φ := Continuous.fourier_inversion φ.continuous φ.integrable hFφ
  have h2 : ∀ x, VectorFourier.fourierIntegral 𝐞 volume (innerₗ Rd).flip
      (fun ξ => (starRingEnd ℂ) (𝓕 (⇑φ) ξ)) x = (starRingEnd ℂ) (φ x) := by
    intro x
    have : VectorFourier.fourierIntegral 𝐞 volume (innerₗ Rd).flip
        (fun ξ => (starRingEnd ℂ) (𝓕 (⇑φ) ξ)) x =
        𝓕 (fun ξ => (starRingEnd ℂ) (𝓕 (⇑φ) ξ)) x := by
      simp [Real.fourierIntegral, VectorFourier.fourierIntegral, real_inner_comm]
    rw [this, fourier_conj, hinv]
  simp_rw [h2] at hflip
  have h3 : ∀ ξ, VectorFourier.fourierIntegral 𝐞 volume (innerₗ Rd) (⇑ψ) ξ = 𝓕 (⇑ψ) ξ :=
    fun ξ => rfl
  simp_rw [h3, smul_eq_mul] at hflip
  rw [show (fun x => (starRingEnd ℂ) (φ x) * ψ x) = fun x => ψ x * (starRingEnd ℂ) (φ x) by
    funext x; ring, ← hflip]
  congr 1
  funext ξ
  ring

/-! ### Schwartz functions in `L²` -/

/-- `φ ↦ φ ∈ L²`. -/
noncomputable def toL2 : SchwartzMap Rd ℂ →L[ℂ] L2 d := SchwartzMap.toLpCLM ℂ ℂ 2 volume

theorem coeFn_toL2 (φ : SchwartzMap Rd ℂ) : (toL2 φ : Rd → ℂ) =ᵐ[volume] ⇑φ := by
  rw [toL2, SchwartzMap.toLpCLM_apply]
  exact SchwartzMap.coeFn_toLp φ 2 volume

theorem integrable_normSq (ψ : SchwartzMap Rd ℂ) : Integrable (fun x => ‖ψ x‖ ^ 2) :=
  (memLp_two_iff_integrable_sq_norm ψ.continuous.aestronglyMeasurable).1 (ψ.memLp 2)

theorem inner_toL2 (φ ψ : SchwartzMap Rd ℂ) :
    inner ℂ (toL2 φ) (toL2 ψ) = ∫ x, (starRingEnd ℂ) (φ x) * ψ x := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_toL2 φ, coeFn_toL2 ψ] with x h1 h2
  rw [h1, h2]
  simp [mul_comm]

theorem norm_toL2_sq (φ : SchwartzMap Rd ℂ) : ‖toL2 φ‖ ^ 2 = ∫ x, ‖φ x‖ ^ 2 := by
  rw [@norm_sq_eq_re_inner ℂ, inner_toL2]
  have : (fun x => (starRingEnd ℂ) (φ x) * φ x) = fun x => ((‖φ x‖ ^ 2 : ℝ) : ℂ) := by
    funext x
    rw [Complex.conj_mul']
    push_cast
    ring
  rw [this, integral_complex_ofReal]
  simp

/-- Plancherel for Schwartz functions. -/
theorem norm_toL2_sq_fourier (φ : SchwartzMap Rd ℂ) :
    ‖toL2 φ‖ ^ 2 = ∫ ξ, ‖𝓕 (⇑φ) ξ‖ ^ 2 := by
  rw [@norm_sq_eq_re_inner ℂ, inner_toL2, parseval]
  have : (fun ξ => (starRingEnd ℂ) (𝓕 (⇑φ) ξ) * 𝓕 (⇑φ) ξ) =
      fun ξ => ((‖𝓕 (⇑φ) ξ‖ ^ 2 : ℝ) : ℂ) := by
    funext ξ
    rw [Complex.conj_mul']
    push_cast
    ring
  rw [this, integral_complex_ofReal]
  simp

theorem inner_toL2_fourier (φ ψ : SchwartzMap Rd ℂ) :
    inner ℂ (toL2 φ) (toL2 ψ) = ∫ ξ, (starRingEnd ℂ) (𝓕 (⇑φ) ξ) * 𝓕 (⇑ψ) ξ := by
  rw [inner_toL2, parseval]

/-- The Fourier transform of a Schwartz function, as a Schwartz function. -/
noncomputable def fS (φ : SchwartzMap Rd ℂ) : SchwartzMap Rd ℂ :=
  SchwartzMap.fourierTransformCLM ℂ φ

theorem coe_fS (φ : SchwartzMap Rd ℂ) : ⇑(fS φ) = 𝓕 (⇑φ) := by
  rw [fS, SchwartzMap.fourierTransformCLM_apply]

/-- `Δ` is symmetric on Schwartz functions. -/
theorem inner_toL2_lapS (χ φ : SchwartzMap Rd ℂ) :
    inner ℂ (toL2 χ) (toL2 (lapS φ)) = inner ℂ (toL2 (lapS χ)) (toL2 φ) := by
  rw [inner_toL2_fourier, inner_toL2_fourier]
  congr 1
  funext ξ
  rw [fourier_lapS, fourier_lapS, map_mul, map_neg, Complex.conj_ofReal]
  ring

/-- `∂ᵢ` is skew-symmetric on Schwartz functions. -/
theorem inner_toL2_dS (i : Fin d) (χ φ : SchwartzMap Rd ℂ) :
    inner ℂ (toL2 χ) (toL2 (dS i φ)) = -inner ℂ (toL2 (dS i χ)) (toL2 φ) := by
  rw [inner_toL2_fourier, inner_toL2_fourier, ← integral_neg]
  congr 1
  funext ξ
  rw [fourier_dS, fourier_dS]
  simp only [map_mul, Complex.conj_ofReal, map_ofNat, Complex.conj_I]
  ring

theorem normSq_dS (i : Fin d) (φ : SchwartzMap Rd ℂ) :
    ‖toL2 (dS i φ)‖ ^ 2 = ∫ ξ, (2 * Real.pi * ξ i) ^ 2 * ‖𝓕 (⇑φ) ξ‖ ^ 2 := by
  rw [norm_toL2_sq_fourier]
  congr 1
  funext ξ
  rw [fourier_dS, norm_mul]
  simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_I, mul_one]
  rw [abs_of_pos Real.pi_pos]
  ring_nf
  rw [sq_abs]
  ring

/-- `Σᵢ ‖∂ᵢφ‖² = ∫ |2πξ|² |𝓕φ|²`. -/
theorem sum_normSq_dS (φ : SchwartzMap Rd ℂ) :
    ∑ i : Fin d, ‖toL2 (dS i φ)‖ ^ 2 = ∫ ξ, qS ξ * ‖𝓕 (⇑φ) ξ‖ ^ 2 := by
  simp_rw [normSq_dS]
  rw [← integral_finset_sum]
  · congr 1
    funext ξ
    rw [← Finset.sum_mul]
    congr 1
    rw [qS, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Real.norm_eq_abs, sq_abs]
    ring
  · intro i _
    have h := integrable_normSq (fS (dS i φ))
    refine h.congr (Eventually.of_forall fun ξ => ?_)
    simp only
    rw [coe_fS, fourier_dS, norm_mul]
    simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_I, mul_one]
    rw [abs_of_pos Real.pi_pos]
    ring_nf
    rw [sq_abs]
    ring

theorem normSq_lapS (φ : SchwartzMap Rd ℂ) :
    ‖toL2 (lapS φ)‖ ^ 2 = ∫ ξ, qS ξ ^ 2 * ‖𝓕 (⇑φ) ξ‖ ^ 2 := by
  rw [norm_toL2_sq_fourier]
  congr 1
  funext ξ
  rw [fourier_lapS, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (qS_nonneg ξ)]
  ring

/-- `−Re⟪Δφ, φ⟫ = Σᵢ ‖∂ᵢφ‖²`. -/
theorem re_inner_lapS_self (φ : SchwartzMap Rd ℂ) :
    (inner ℂ (toL2 (lapS φ)) (toL2 φ)).re = -∑ i : Fin d, ‖toL2 (dS i φ)‖ ^ 2 := by
  rw [inner_toL2_fourier, sum_normSq_dS]
  have : (fun ξ => (starRingEnd ℂ) (𝓕 (⇑(lapS φ)) ξ) * 𝓕 (⇑φ) ξ) =
      fun ξ => -((qS ξ * ‖𝓕 (⇑φ) ξ‖ ^ 2 : ℝ) : ℂ) := by
    funext ξ
    rw [fourier_lapS, map_mul, map_neg, Complex.conj_ofReal]
    rw [show -(qS ξ : ℂ) * (starRingEnd ℂ) (𝓕 (⇑φ) ξ) * 𝓕 (⇑φ) ξ =
      -(qS ξ : ℂ) * ((starRingEnd ℂ) (𝓕 (⇑φ) ξ) * 𝓕 (⇑φ) ξ) by ring, Complex.conj_mul']
    push_cast
    ring
  rw [this, integral_neg, integral_complex_ofReal]
  simp

/-- A smooth compactly supported function as a Schwartz map. -/
noncomputable def schwartzOfCompact (f : Rd → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    SchwartzMap Rd ℂ where
  toFun := f
  smooth' := hf
  decay' := fun k n => by
    have hcont : Continuous fun x : Rd => ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ :=
      (continuous_norm.pow k).mul (hf.continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm
    have hsupp : HasCompactSupport fun x : Rd => ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ :=
      (hc.iteratedFDeriv n).norm.mul_left
    obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support hsupp
    refine ⟨C, fun x => ?_⟩
    have := hC x
    rwa [Real.norm_of_nonneg (by positivity)] at this

@[simp] theorem coe_schwartzOfCompact (f : Rd → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) : ⇑(schwartzOfCompact f hf hc) = f := rfl

theorem inner_toL2_left (χ : SchwartzMap Rd ℂ) (w : L2 d) :
    inner ℂ (toL2 χ) w = ∫ x, (starRingEnd ℂ) (χ x) * w x := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_toL2 χ] with x h1
  rw [h1]
  simp [mul_comm]

/-- An `L²` function orthogonal to all Schwartz functions vanishes. -/
theorem eq_zero_of_inner_schwartz {w : L2 d} (h : ∀ χ : SchwartzMap Rd ℂ, inner ℂ (toL2 χ) w = 0) :
    w = 0 := by
  have hloc : LocallyIntegrable (⇑w) volume := (Lp.memLp w).locallyIntegrable (by norm_num)
  have hae := ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc fun g hg hgc => by
    have hgC : ContDiff ℝ ∞ fun x => ((g x : ℝ) : ℂ) := Complex.ofRealCLM.contDiff.comp hg
    have hgcC : HasCompactSupport fun x => ((g x : ℝ) : ℂ) :=
      hgc.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
    have := h (schwartzOfCompact _ hgC hgcC)
    rw [inner_toL2_left] at this
    simp only [coe_schwartzOfCompact, Complex.conj_ofReal] at this
    simpa [Complex.real_smul] using this
  exact (Lp.eq_zero_iff_ae_eq_zero).2 hae

end Sobolev

end ReyesMath

namespace ReyesMath

namespace Sobolev

variable {d : ℕ}

local notation "Rd" => EuclideanSpace ℝ (Fin d)

/-! ### The Sobolev space `H²(ℝ^d; ℂ)` -/

/-- `H²(ℝ^d; ℂ)` as the closure of `{(φ, ∇φ, Δφ) : φ ∈ 𝓢}` in `L² × (L²)^d × L²`: an element
records `u ∈ L²` together with its (strong) gradient and Laplacian. By
`H2.ext_of_val`, the derivatives are determined by `u`. -/
structure H2 (d : ℕ) where
  val : L2 d
  grad : Fin d → L2 d
  lap : L2 d
  approx : ∃ φ : ℕ → SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ,
    Tendsto (fun n => toL2 (φ n)) atTop (𝓝 val) ∧
    (∀ i, Tendsto (fun n => toL2 (dS i (φ n))) atTop (𝓝 (grad i))) ∧
    Tendsto (fun n => toL2 (lapS (φ n))) atTop (𝓝 lap)

namespace H2

/-- A Schwartz function as an element of `H²`. -/
noncomputable def ofSchwartz (φ : SchwartzMap Rd ℂ) : H2 d :=
  ⟨toL2 φ, fun i => toL2 (dS i φ), toL2 (lapS φ),
    ⟨fun _ => φ, tendsto_const_nhds, fun _ => tendsto_const_nhds, tendsto_const_nhds⟩⟩

/-- `M(u) = ‖u‖²_{L²}`. -/
noncomputable def M (U : H2 d) : ℝ := ‖U.val‖ ^ 2

/-- `K(u) = ‖∇u‖²_{L²}`. -/
noncomputable def K (U : H2 d) : ℝ := ∑ i : Fin d, ‖U.grad i‖ ^ 2

/-- `D(u) = ‖Δu‖²_{L²}`. -/
noncomputable def D (U : H2 d) : ℝ := ‖U.lap‖ ^ 2

theorem inner_lap_eq (U : H2 d) (χ : SchwartzMap Rd ℂ) :
    inner ℂ (toL2 χ) U.lap = inner ℂ (toL2 (lapS χ)) U.val := by
  obtain ⟨φ, h0, -, h2⟩ := U.approx
  have hA := (tendsto_const_nhds (x := toL2 χ)).inner (𝕜 := ℂ) h2
  have hB := (tendsto_const_nhds (x := toL2 (lapS χ))).inner (𝕜 := ℂ) h0
  simp_rw [inner_toL2_lapS] at hA
  exact tendsto_nhds_unique hA hB

theorem inner_grad_eq (U : H2 d) (i : Fin d) (χ : SchwartzMap Rd ℂ) :
    inner ℂ (toL2 χ) (U.grad i) = -inner ℂ (toL2 (dS i χ)) U.val := by
  obtain ⟨φ, h0, h1, -⟩ := U.approx
  have hA := (tendsto_const_nhds (x := toL2 χ)).inner (𝕜 := ℂ) (h1 i)
  have hB := ((tendsto_const_nhds (x := toL2 (dS i χ))).inner (𝕜 := ℂ) h0).neg
  simp_rw [inner_toL2_dS] at hA
  exact tendsto_nhds_unique hA hB

/-- **Uniqueness of the strong derivatives**: an element of `H²` is determined by its
underlying `L²` function. -/
theorem ext_of_val {U V : H2 d} (h : U.val = V.val) : U = V := by
  have hlap : U.lap = V.lap := by
    have := eq_zero_of_inner_schwartz (w := U.lap - V.lap) fun χ => by
      rw [inner_sub_right, inner_lap_eq, inner_lap_eq, h, sub_self]
    exact sub_eq_zero.1 this
  have hgrad : U.grad = V.grad := by
    funext i
    have := eq_zero_of_inner_schwartz (w := U.grad i - V.grad i) fun χ => by
      rw [inner_sub_right, inner_grad_eq, inner_grad_eq, h, sub_self]
    exact sub_eq_zero.1 this
  cases U
  cases V
  simp only at h hlap hgrad
  subst h hlap hgrad
  rfl

/-- `Re⟪Δu, u⟫ = −‖∇u‖²`. -/
theorem re_inner_lap_val (U : H2 d) : (inner ℂ U.lap U.val).re = -K U := by
  obtain ⟨φ, h0, h1, h2⟩ := U.approx
  have hA := (Complex.continuous_re.tendsto _).comp (h2.inner (𝕜 := ℂ) h0)
  have hB : Tendsto (fun n => -∑ i : Fin d, ‖toL2 (dS i (φ n))‖ ^ 2) atTop (𝓝 (-K U)) := by
    unfold K
    exact (tendsto_finset_sum _ fun i _ => ((h1 i).norm).pow 2).neg
  have hC : (fun n => (inner ℂ (toL2 (lapS (φ n))) (toL2 (φ n))).re) =
      fun n => -∑ i : Fin d, ‖toL2 (dS i (φ n))‖ ^ 2 :=
    funext fun n => re_inner_lapS_self (φ n)
  exact tendsto_nhds_unique (hC ▸ hA) hB

theorem M_nonneg (U : H2 d) : 0 ≤ M U := sq_nonneg _

theorem K_nonneg (U : H2 d) : 0 ≤ K U := Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem D_nonneg (U : H2 d) : 0 ≤ D U := sq_nonneg _

/-- `‖∇u‖² ≤ ‖u‖ ‖Δu‖`. -/
theorem K_le (U : H2 d) : K U ≤ ‖U.val‖ * ‖U.lap‖ := by
  have h := re_inner_lap_val U
  have h2 := abs_re_le_norm (inner ℂ U.lap U.val)
  have h3 := norm_inner_le_norm (𝕜 := ℂ) U.lap U.val
  rw [h, abs_neg, abs_of_nonneg (K_nonneg U)] at h2
  linarith

theorem K_le_sqrt (U : H2 d) : K U ≤ Real.sqrt (M U * D U) := by
  rw [M, D, ← mul_pow, Real.sqrt_sq (by positivity)]
  have := K_le U
  linarith [mul_comm ‖U.val‖ ‖U.lap‖]

/-- `‖(Δ + k²)u‖² = D − 2k²K + k⁴M`. -/
theorem normSq_shift (U : H2 d) (k : ℝ) :
    ‖U.lap + ((k ^ 2 : ℝ) : ℂ) • U.val‖ ^ 2 = D U - 2 * k ^ 2 * K U + k ^ 4 * M U := by
  rw [@norm_add_sq ℂ, norm_smul, inner_smul_right]
  simp only [RCLike.re_to_complex]
  rw [Complex.re_ofReal_mul, re_inner_lap_val, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity), D, M]
  ring

end H2

/-- `∫₀^∞ du/(c u² + η) = π/(2√(cη))`. -/
theorem integral_Ioi_inv_quadratic {c η : ℝ} (hc : 0 < c) (hη : 0 < η) :
    ∫ u in Ioi (0 : ℝ), 1 / (c * u ^ 2 + η) = Real.pi / (2 * Real.sqrt (c * η)) := by
  set b := Real.sqrt c / Real.sqrt η with hb
  have hsc := Real.sqrt_pos.2 hc
  have hsη := Real.sqrt_pos.2 hη
  have hbpos : 0 < b := div_pos hsc hsη
  have hpt : ∀ u : ℝ, 1 / (c * u ^ 2 + η) = η⁻¹ * (1 + (b * u) ^ 2)⁻¹ := by
    intro u
    have h1 : (b * u) ^ 2 = c / η * u ^ 2 := by
      rw [hb, mul_pow, div_pow, Real.sq_sqrt hc.le, Real.sq_sqrt hη.le]
    rw [h1]
    field_simp
    ring
  simp_rw [hpt]
  rw [integral_const_mul, integral_comp_mul_left_Ioi (fun s => (1 + s ^ 2)⁻¹) 0 hbpos,
    mul_zero, integral_Ioi_inv_one_add_sq, Real.arctan_zero, sub_zero, smul_eq_mul,
    Real.sqrt_mul hc.le, hb]
  field_simp
  rw [Real.sq_sqrt hη.le]

/-- `∫_{ℝ²} dξ / (|2πξ|⁴ + η) = 1/(8√η)`. -/
theorem integral_inv_quartic {η : ℝ} (hη : 0 < η) :
    ∫ ξ : EuclideanSpace ℝ (Fin 2), 1 / (((2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2) ^ 2 + η) =
      1 / (8 * Real.sqrt η) := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hrad := integral_fun_norm_addHaar (volume : Measure (EuclideanSpace ℝ (Fin 2)))
    (fun r : ℝ => 1 / (((2 * Real.pi) ^ 2 * r ^ 2) ^ 2 + η))
  simp only at hrad
  rw [hrad, finrank_euclideanSpace_fin]
  have hball : (volume : Measure (EuclideanSpace ℝ (Fin 2))).real (Metric.ball 0 1) = Real.pi := by
    rw [Measure.real, EuclideanSpace.volume_ball_fin_two]
    simp [ENNReal.toReal_ofReal hπ.le]
  rw [hball]
  have hinner : ∫ y in Ioi (0 : ℝ), y ^ (2 - 1) • (1 / (((2 * Real.pi) ^ 2 * y ^ 2) ^ 2 + η)) =
      1 / 2 * ∫ u in Ioi (0 : ℝ), 1 / ((2 * Real.pi) ^ 4 * u ^ 2 + η) := by
    have hsub := integral_comp_rpow_Ioi_of_pos (g := fun u : ℝ => 1 / ((2 * Real.pi) ^ 4 * u ^ 2 + η))
      (p := 2) two_pos
    rw [← hsub, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
    have hy0 : 0 < y := hy
    simp only [smul_eq_mul]
    rw [show ((2 : ℝ) - 1) = 1 by norm_num, Real.rpow_one, Real.rpow_two]
    norm_num
    ring
  rw [hinner, integral_Ioi_inv_quadratic (by positivity) hη]
  have h4 : Real.sqrt ((2 * Real.pi) ^ 4 * η) = (2 * Real.pi) ^ 2 * Real.sqrt η := by
    rw [Real.sqrt_mul (by positivity), show (2 * Real.pi) ^ 4 = ((2 * Real.pi) ^ 2) ^ 2 by ring,
      Real.sqrt_sq (by positivity)]
  rw [h4]
  have hsη := Real.sqrt_pos.2 hη
  simp only [nsmul_eq_mul, smul_eq_mul, Nat.cast_ofNat]
  field_simp
  ring
/-! ### The two-dimensional Fourier sup-norm estimate -/

section SupBound

local notation "R2" => EuclideanSpace ℝ (Fin 2)

theorem integrable_inv_quartic {η : ℝ} (hη : 0 < η) :
    Integrable fun ξ : R2 => 1 / (qS ξ ^ 2 + η) := by
  set c : ℝ := (2 * Real.pi) ^ 4 with hc
  have hcpos : 0 < c := by positivity
  set C : ℝ := 8 * (1 / c + 1 / η) with hC
  have hint := (integrable_one_add_norm (E := R2) (μ := volume) (r := 4)
    (by rw [finrank_euclideanSpace_fin]; norm_num)).const_mul C
  refine hint.mono' ?_ (Eventually.of_forall fun ξ => ?_)
  · exact (Continuous.aestronglyMeasurable (by
      unfold qS
      refine continuous_const.div (by fun_prop) fun ξ => ?_
      positivity))
  · set r := ‖ξ‖ with hr
    have hr0 : 0 ≤ r := norm_nonneg _
    have hq : qS ξ ^ 2 = c * r ^ 4 := by
      rw [qS, hc, ← hr]
      ring
    rw [Real.norm_of_nonneg (by rw [hq]; positivity), hq,
      Real.rpow_neg (by positivity)]
    have h4 : (1 + r) ^ (4 : ℝ) = (1 + r) ^ (4 : ℕ) := by
      exact_mod_cast Real.rpow_natCast (1 + r) 4
    rw [h4]
    have h1 : (1 + r) ^ 4 ≤ 8 * (1 + r ^ 4) := by
      nlinarith [mul_nonneg (sq_nonneg (r - 1)) (by positivity : (0 : ℝ) ≤ 7 * r ^ 2 + 10 * r + 7)]
    have h2 : 8 * (1 + r ^ 4) ≤ C * (c * r ^ 4 + η) := by
      have hexp : C * (c * r ^ 4 + η) = 8 * (r ^ 4 + 1) + 8 * (η / c + c * r ^ 4 / η) := by
        rw [hC]
        field_simp
        ring
      have : 0 ≤ 8 * (η / c + c * r ^ 4 / η) := by positivity
      linarith
    rw [div_le_iff₀ (by positivity)]
    rw [show C * ((1 + r) ^ 4)⁻¹ * (c * r ^ 4 + η) = C * (c * r ^ 4 + η) / (1 + r) ^ 4 by
      field_simp]
    rw [le_div_iff₀ (by positivity)]
    linarith

theorem integral_inv_quartic' {η : ℝ} (hη : 0 < η) :
    ∫ ξ : R2, 1 / (qS ξ ^ 2 + η) = 1 / (8 * Real.sqrt η) := by
  rw [← integral_inv_quartic hη]
  rfl

theorem integrable_fourier_norm (φ : SchwartzMap R2 ℂ) : Integrable fun ξ => ‖𝓕 (⇑φ) ξ‖ := by
  rw [← coe_fS]
  exact (fS φ).integrable.norm

/-- `∫ (|2πξ|⁴ + η) |𝓕φ|² = ‖Δφ‖² + η‖φ‖²`. -/
theorem integral_weight_fourier (φ : SchwartzMap R2 ℂ) (η : ℝ) :
    ∫ ξ, (qS ξ ^ 2 + η) * ‖𝓕 (⇑φ) ξ‖ ^ 2 = ‖toL2 (lapS φ)‖ ^ 2 + η * ‖toL2 φ‖ ^ 2 := by
  have h1 : Integrable fun ξ : R2 => qS ξ ^ 2 * ‖𝓕 (⇑φ) ξ‖ ^ 2 := by
    refine (integrable_normSq (fS (lapS φ))).congr (Eventually.of_forall fun ξ => ?_)
    simp only
    rw [coe_fS, fourier_lapS, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (qS_nonneg ξ)]
    ring
  have h2 : Integrable fun ξ : R2 => ‖𝓕 (⇑φ) ξ‖ ^ 2 := by
    rw [← coe_fS]
    exact integrable_normSq (fS φ)
  simp_rw [add_mul]
  rw [integral_add h1 (h2.const_mul η), integral_const_mul, normSq_lapS, norm_toL2_sq_fourier]

/-- **Fourier sup-norm estimate (Schwartz):** `|φ(x)|² ≤ (‖Δφ‖² + η‖φ‖²)/(8√η)`. -/
theorem sup_bound_schwartz (φ : SchwartzMap R2 ℂ) {η : ℝ} (hη : 0 < η) (x : R2) :
    ‖φ x‖ ^ 2 ≤ (‖toL2 (lapS φ)‖ ^ 2 + η * ‖toL2 φ‖ ^ 2) / (8 * Real.sqrt η) := by
  set A : ℝ := 1 / (8 * Real.sqrt η) with hA
  set B : ℝ := ‖toL2 (lapS φ)‖ ^ 2 + η * ‖toL2 φ‖ ^ 2 with hB
  have hsη := Real.sqrt_pos.2 hη
  have hApos : 0 < A := by positivity
  have hB0 : 0 ≤ B := by positivity
  have hFφ : Integrable (𝓕 (⇑φ)) := by rw [← coe_fS]; exact (fS φ).integrable
  have hinv : 𝓕⁻ (𝓕 (⇑φ)) = ⇑φ := Continuous.fourier_inversion φ.continuous φ.integrable hFφ
  -- `|φ(x)| ≤ ∫ |𝓕φ|`
  have h1 : ‖φ x‖ ≤ ∫ ξ, ‖𝓕 (⇑φ) ξ‖ := by
    conv_lhs => rw [← hinv, Real.fourierIntegralInv_eq]
    refine le_trans (norm_integral_le_integral_norm _) (le_of_eq ?_)
    congr 1
    funext ξ
    simp [Circle.smul_def]
  -- AM–GM against the weight
  have h2 : ∀ t : ℝ, 0 < t → ∫ ξ, ‖𝓕 (⇑φ) ξ‖ ≤ (t * A + B / t) / 2 := by
    intro t ht
    have hw : ∀ ξ : R2, 0 < qS ξ ^ 2 + η := fun ξ => by positivity
    have hmono : ∀ ξ : R2, ‖𝓕 (⇑φ) ξ‖ ≤
        (t * (1 / (qS ξ ^ 2 + η)) + (qS ξ ^ 2 + η) * ‖𝓕 (⇑φ) ξ‖ ^ 2 / t) / 2 := by
      intro ξ
      have hwξ := hw ξ
      set a := ‖𝓕 (⇑φ) ξ‖
      set w := qS ξ ^ 2 + η
      rw [le_div_iff₀ two_pos]
      have hid : t * (1 / w) + w * a ^ 2 / t - a * 2 = (t - w * a) ^ 2 / (w * t) := by
        field_simp
        ring
      have : 0 ≤ (t - w * a) ^ 2 / (w * t) := by positivity
      linarith
    have hint : Integrable fun ξ : R2 =>
        (t * (1 / (qS ξ ^ 2 + η)) + (qS ξ ^ 2 + η) * ‖𝓕 (⇑φ) ξ‖ ^ 2 / t) / 2 := by
      have hW : Integrable fun ξ : R2 => (qS ξ ^ 2 + η) * ‖𝓕 (⇑φ) ξ‖ ^ 2 := by
        have h1' : Integrable fun ξ : R2 => qS ξ ^ 2 * ‖𝓕 (⇑φ) ξ‖ ^ 2 := by
          refine (integrable_normSq (fS (lapS φ))).congr (Eventually.of_forall fun ξ => ?_)
          simp only
          rw [coe_fS, fourier_lapS, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (qS_nonneg ξ)]
          ring
        have h2' : Integrable fun ξ : R2 => ‖𝓕 (⇑φ) ξ‖ ^ 2 := by
          rw [← coe_fS]
          exact integrable_normSq (fS φ)
        simp_rw [add_mul]
        exact h1'.add (h2'.const_mul η)
      exact (((integrable_inv_quartic hη).const_mul t).add (hW.div_const t)).div_const 2
    calc ∫ ξ, ‖𝓕 (⇑φ) ξ‖
        ≤ ∫ ξ, (t * (1 / (qS ξ ^ 2 + η)) + (qS ξ ^ 2 + η) * ‖𝓕 (⇑φ) ξ‖ ^ 2 / t) / 2 :=
          integral_mono (integrable_fourier_norm φ) hint hmono
      _ = (t * A + B / t) / 2 := by
          have hW : Integrable fun ξ : R2 => (qS ξ ^ 2 + η) * ‖𝓕 (⇑φ) ξ‖ ^ 2 := by
            have h1' : Integrable fun ξ : R2 => qS ξ ^ 2 * ‖𝓕 (⇑φ) ξ‖ ^ 2 := by
              refine (integrable_normSq (fS (lapS φ))).congr (Eventually.of_forall fun ξ => ?_)
              simp only
              rw [coe_fS, fourier_lapS, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
                abs_of_nonneg (qS_nonneg ξ)]
              ring
            have h2' : Integrable fun ξ : R2 => ‖𝓕 (⇑φ) ξ‖ ^ 2 := by
              rw [← coe_fS]
              exact integrable_normSq (fS φ)
            simp_rw [add_mul]
            exact h1'.add (h2'.const_mul η)
          rw [integral_div, integral_add ((integrable_inv_quartic hη).const_mul t)
            (hW.div_const t), integral_const_mul, integral_div, integral_inv_quartic' hη,
            integral_weight_fourier]
  -- optimize
  have hnn : 0 ≤ ‖φ x‖ := norm_nonneg _
  have key : ‖φ x‖ ^ 2 ≤ A * B := by
    rcases hB0.lt_or_eq with hBpos | hB0'
    · set t := Real.sqrt (B / A) with ht
      have htpos : 0 < t := Real.sqrt_pos.2 (div_pos hBpos hApos)
      have h3 := le_trans h1 (h2 t htpos)
      have ht2 : t ^ 2 = B / A := Real.sq_sqrt (div_pos hBpos hApos).le
      have h4 : (t * A + B / t) / 2 = t * A := by
        field_simp
        rw [ht2]
        field_simp
        ring
      rw [h4] at h3
      have h5 : (t * A) ^ 2 = A * B := by
        rw [mul_pow, ht2]
        field_simp
      calc ‖φ x‖ ^ 2 ≤ (t * A) ^ 2 := pow_le_pow_left₀ hnn h3 2
        _ = A * B := h5
    · have h3 : ∀ t : ℝ, 0 < t → ‖φ x‖ ≤ t * A / 2 := fun t ht => by
        have := le_trans h1 (h2 t ht)
        rw [← hB0', zero_div, add_zero] at this
        exact this
      have h4 : ‖φ x‖ ≤ 0 := by
        by_contra hcon
        push_neg at hcon
        have := h3 (‖φ x‖ / A) (div_pos hcon hApos)
        field_simp at this
        linarith
      have : ‖φ x‖ = 0 := le_antisymm h4 hnn
      rw [this, ← hB0']
      simp
  calc ‖φ x‖ ^ 2 ≤ A * B := key
    _ = B / (8 * Real.sqrt η) := by rw [hA]; ring

end SupBound

namespace H2

local notation "R2" => EuclideanSpace ℝ (Fin 2)

/-- The a.e. sup bound on `H²(ℝ²)`: `|u(x)|² ≤ (D(u) + ηM(u))/(8√η)` for a.e. `x`. -/
theorem ae_sup_bound (U : H2 2) {η : ℝ} (hη : 0 < η) :
    ∀ᵐ x ∂(volume : Measure R2), ‖U.val x‖ ^ 2 ≤ (D U + η * M U) / (8 * Real.sqrt η) := by
  obtain ⟨φ, h0, -, h2⟩ := U.approx
  obtain ⟨ns, hmono, hns⟩ := (tendstoInMeasure_of_tendsto_Lp h0).exists_seq_tendsto_ae
  have hcoe : ∀ᵐ x ∂(volume : Measure R2), ∀ n, (toL2 (φ n) : R2 → ℂ) x = φ n x :=
    ae_all_iff.2 fun n => coeFn_toL2 (φ n)
  have hs : Tendsto ns atTop atTop := hmono.tendsto_atTop
  filter_upwards [hns, hcoe] with x hx hc
  have hlim1 : Tendsto (fun i => ‖φ (ns i) x‖ ^ 2) atTop (𝓝 (‖U.val x‖ ^ 2)) := by
    have := (hx.norm).pow 2
    simpa only [hc] using this
  have hlim2 : Tendsto (fun i => (‖toL2 (lapS (φ (ns i)))‖ ^ 2 + η * ‖toL2 (φ (ns i))‖ ^ 2) /
      (8 * Real.sqrt η)) atTop (𝓝 ((D U + η * M U) / (8 * Real.sqrt η))) := by
    have hA := ((h2.comp hs).norm).pow 2
    have hB := (((h0.comp hs).norm).pow 2).const_mul η
    exact (hA.add hB).div_const _
  exact le_of_tendsto_of_tendsto' hlim1 hlim2 fun i => sup_bound_schwartz (φ (ns i)) hη x

theorem val_ae_zero_of_M_zero (U : H2 d) (h : M U = 0) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), U.val x = 0 := by
  have : U.val = 0 := by
    rw [M, sq_eq_zero_iff, norm_eq_zero] at h
    exact h
  rw [this]
  exact Lp.coeFn_zero ℂ 2 volume

/-- **Optimized sup bound:** `‖u‖²_∞ ≤ ¼ √(M(u) D(u))`. -/
theorem ae_sup_bound_opt (U : H2 2) :
    ∀ᵐ x ∂(volume : Measure R2), ‖U.val x‖ ^ 2 ≤ Real.sqrt (M U * D U) / 4 := by
  rcases (M_nonneg U).lt_or_eq with hM | hM
  · rcases (D_nonneg U).lt_or_eq with hD | hD
    · have h := ae_sup_bound U (η := D U / M U) (div_pos hD hM)
      filter_upwards [h] with x hx
      have hsq : Real.sqrt (D U / M U) = Real.sqrt (D U) / Real.sqrt (M U) :=
        Real.sqrt_div' _ hM.le
      have hsD := Real.sqrt_pos.2 hD
      have hsM := Real.sqrt_pos.2 hM
      have heq : (D U + D U / M U * M U) / (8 * Real.sqrt (D U / M U)) =
          Real.sqrt (M U * D U) / 4 := by
        rw [hsq, Real.sqrt_mul hM.le]
        field_simp
        rw [Real.sq_sqrt hD.le]
        ring
      rwa [heq] at hx
    · -- `D = 0` forces `u = 0` a.e.
      have hall : ∀ᵐ x ∂(volume : Measure R2), ∀ n : ℕ,
          ‖U.val x‖ ^ 2 ≤ (D U + (1 / ((n : ℝ) + 1)) ^ 2 * M U) /
            (8 * Real.sqrt ((1 / ((n : ℝ) + 1)) ^ 2)) :=
        ae_all_iff.2 fun n => ae_sup_bound U (by positivity)
      filter_upwards [hall] with x hx
      rw [← hD, mul_zero, Real.sqrt_zero, zero_div]
      have hle : ∀ n : ℕ, ‖U.val x‖ ^ 2 ≤ M U / 8 * (1 / ((n : ℝ) + 1)) := by
        intro n
        have := hx n
        rw [← hD, zero_add, Real.sqrt_sq (by positivity)] at this
        calc ‖U.val x‖ ^ 2 ≤ (1 / ((n : ℝ) + 1)) ^ 2 * M U / (8 * (1 / ((n : ℝ) + 1))) := this
          _ = M U / 8 * (1 / ((n : ℝ) + 1)) := by
            field_simp
      have hlim : Tendsto (fun n : ℕ => M U / 8 * (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
        have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (M U / 8)
        simpa using this
      exact ge_of_tendsto' hlim hle
  · filter_upwards [val_ae_zero_of_M_zero U hM.symm] with x hx
    rw [hx, norm_zero, zero_pow two_ne_zero]
    positivity

/-- `Q(u) = ‖u‖⁴_{L⁴}`. -/
noncomputable def Q (U : H2 d) : ℝ := ∫ x, ‖U.val x‖ ^ 4

/-- `S(u) = ‖u‖⁶_{L⁶}`. -/
noncomputable def S (U : H2 d) : ℝ := ∫ x, ‖U.val x‖ ^ 6

theorem integrable_sq_val (U : H2 d) : Integrable fun x => ‖U.val x‖ ^ 2 :=
  (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable U.val)).1 (Lp.memLp U.val)

theorem integrable_Q (U : H2 2) : Integrable fun x => ‖U.val x‖ ^ 4 := by
  refine ((integrable_sq_val U).const_mul (Real.sqrt (M U * D U) / 4)).mono'
    ((Lp.aestronglyMeasurable U.val).norm.pow 4) ?_
  filter_upwards [ae_sup_bound_opt U] with x hx
  rw [Real.norm_of_nonneg (by positivity)]
  calc ‖U.val x‖ ^ 4 = ‖U.val x‖ ^ 2 * ‖U.val x‖ ^ 2 := by ring
    _ ≤ Real.sqrt (M U * D U) / 4 * ‖U.val x‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hx (sq_nonneg _)

theorem integrable_S (U : H2 2) : Integrable fun x => ‖U.val x‖ ^ 6 := by
  refine ((integrable_Q U).const_mul (Real.sqrt (M U * D U) / 4)).mono'
    ((Lp.aestronglyMeasurable U.val).norm.pow 6) ?_
  filter_upwards [ae_sup_bound_opt U] with x hx
  rw [Real.norm_of_nonneg (by positivity)]
  calc ‖U.val x‖ ^ 6 = ‖U.val x‖ ^ 2 * ‖U.val x‖ ^ 4 := by ring
    _ ≤ Real.sqrt (M U * D U) / 4 * ‖U.val x‖ ^ 4 :=
      mul_le_mul_of_nonneg_right hx (by positivity)

/-- `S(u) ≤ ‖u‖²_∞ Q(u) ≤ ¼√(MD) Q(u)`. -/
theorem S_le (U : H2 2) : S U ≤ Real.sqrt (M U * D U) / 4 * Q U := by
  unfold S Q
  rw [← integral_const_mul]
  refine integral_mono_ae (integrable_S U) ((integrable_Q U).const_mul _) ?_
  filter_upwards [ae_sup_bound_opt U] with x hx
  calc ‖U.val x‖ ^ 6 = ‖U.val x‖ ^ 2 * ‖U.val x‖ ^ 4 := by ring
    _ ≤ Real.sqrt (M U * D U) / 4 * ‖U.val x‖ ^ 4 :=
      mul_le_mul_of_nonneg_right hx (by positivity)

end H2

/-! ### Mass-preserving dilations `u ↦ λ^{d/2} u(λ·)` -/

section Dilation

variable {lam : ℝ}

/-- The dilation on functions. -/
noncomputable def dilF (lam : ℝ) (f : Rd → ℂ) (x : Rd) : ℂ :=
  ((lam ^ ((d : ℝ) / 2) : ℝ) : ℂ) * f (lam • x)

theorem qmp_smul (hlam : 0 < lam) :
    Measure.QuasiMeasurePreserving (fun x : Rd => lam • x) volume volume :=
  Measure.quasiMeasurePreserving_smul volume hlam.ne'

theorem norm_dilF_sq (hlam : 0 < lam) (f : Rd → ℂ) (x : Rd) :
    ‖dilF lam f x‖ ^ 2 = lam ^ d * ‖f (lam • x)‖ ^ 2 := by
  rw [dilF, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hlam.le _), mul_pow, ← Real.rpow_natCast
    (lam ^ ((d : ℝ) / 2)), ← Real.rpow_mul hlam.le, ← Real.rpow_natCast lam d]
  congr 2
  push_cast
  ring

/-- `∫ G(u_λ) = λ^{-d} ∫ G(λ^{d/2} u)`-type change of variables, for the squared modulus. -/
theorem integral_comp_dil (hlam : 0 < lam) (F : Rd → ℝ) :
    ∫ x, F (lam • x) = (lam ^ d)⁻¹ * ∫ x, F x := by
  rw [Measure.integral_comp_smul, finrank_euclideanSpace_fin, smul_eq_mul,
    abs_of_pos (by positivity)]

theorem memLp_dilF (hlam : 0 < lam) {f : Rd → ℂ} (hf : MemLp f 2) : MemLp (dilF lam f) 2 := by
  have hm : AEStronglyMeasurable (dilF lam f) volume :=
    aestronglyMeasurable_const.mul (hf.1.comp_quasiMeasurePreserving (qmp_smul hlam))
  rw [memLp_two_iff_integrable_sq_norm hm]
  simp_rw [norm_dilF_sq hlam]
  have h2 : Integrable fun x => ‖f x‖ ^ 2 := (memLp_two_iff_integrable_sq_norm hf.1).1 hf
  exact ((integrable_comp_smul_iff volume (fun x => ‖f x‖ ^ 2) hlam.ne').2 h2).const_mul _

/-- The dilation on `L²`. -/
noncomputable def dilL2 (hlam : 0 < lam) (f : L2 d) : L2 d :=
  (memLp_dilF hlam (Lp.memLp f)).toLp _

theorem coeFn_dilL2 (hlam : 0 < lam) (f : L2 d) :
    (dilL2 hlam f : Rd → ℂ) =ᵐ[volume] dilF lam f :=
  (memLp_dilF hlam (Lp.memLp f)).coeFn_toLp

theorem dilF_congr_ae (hlam : 0 < lam) {f g : Rd → ℂ} (h : f =ᵐ[volume] g) :
    dilF lam f =ᵐ[volume] dilF lam g := by
  filter_upwards [(qmp_smul hlam).ae_eq h] with x hx
  simp only [dilF, Function.comp_apply] at hx ⊢
  rw [hx]

theorem inner_self_complex (z : ℂ) : inner ℂ z z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [inner_self_eq_norm_sq_to_K]
  simp

theorem norm_dilL2 (hlam : 0 < lam) (f : L2 d) : ‖dilL2 hlam f‖ = ‖f‖ := by
  have h1 : ‖dilL2 hlam f‖ ^ 2 = ‖f‖ ^ 2 := by
    rw [@norm_sq_eq_re_inner ℂ, @norm_sq_eq_re_inner ℂ, L2.inner_def, L2.inner_def]
    have hA : (fun x => inner ℂ ((dilL2 hlam f : Rd → ℂ) x) ((dilL2 hlam f : Rd → ℂ) x)) =ᵐ[volume]
        fun x => (((lam ^ d * ‖(f : Rd → ℂ) (lam • x)‖ ^ 2 : ℝ)) : ℂ) := by
      filter_upwards [coeFn_dilL2 hlam f] with x hx
      rw [hx, inner_self_complex, norm_dilF_sq hlam]
    have hB : (fun x => inner ℂ ((f : Rd → ℂ) x) ((f : Rd → ℂ) x)) =
        fun x => (((‖(f : Rd → ℂ) x‖ ^ 2 : ℝ)) : ℂ) := by
      funext x
      rw [inner_self_complex]
    rw [integral_congr_ae hA, hB, integral_complex_ofReal, integral_complex_ofReal,
      integral_const_mul, integral_comp_dil hlam (fun x => ‖(f : Rd → ℂ) x‖ ^ 2)]
    simp only [RCLike.re_to_complex, Complex.ofReal_re]
    field_simp
  have := congrArg Real.sqrt h1
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at this

theorem dilL2_sub (hlam : 0 < lam) (f g : L2 d) :
    dilL2 hlam (f - g) = dilL2 hlam f - dilL2 hlam g := by
  apply Lp.ext
  filter_upwards [coeFn_dilL2 hlam (f - g), coeFn_dilL2 hlam f, coeFn_dilL2 hlam g,
    Lp.coeFn_sub (dilL2 hlam f) (dilL2 hlam g), dilF_congr_ae hlam (Lp.coeFn_sub f g)]
    with x h1 h2 h3 h4 h5
  rw [h1, h4, Pi.sub_apply, h2, h3, h5]
  simp only [dilF, Pi.sub_apply]
  ring

theorem tendsto_dilL2 (hlam : 0 < lam) {f : ℕ → L2 d} {g : L2 d}
    (h : Tendsto f atTop (𝓝 g)) : Tendsto (fun n => dilL2 hlam (f n)) atTop (𝓝 (dilL2 hlam g)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero] at h ⊢
  simpa only [← dilL2_sub, norm_dilL2] using h

theorem dilL2_smul (hlam : 0 < lam) (c : ℂ) (f : L2 d) :
    dilL2 hlam (c • f) = c • dilL2 hlam f := by
  apply Lp.ext
  filter_upwards [coeFn_dilL2 hlam (c • f), coeFn_dilL2 hlam f,
    Lp.coeFn_smul c (dilL2 hlam f), dilF_congr_ae hlam (Lp.coeFn_smul c f)] with x h1 h2 h3 h4
  rw [h1, h3, Pi.smul_apply, h2, h4]
  simp only [dilF, Pi.smul_apply, smul_eq_mul]
  ring

/-- `x ↦ λx` as a continuous linear equivalence. -/
noncomputable def smulCLE (hlam : 0 < lam) : Rd ≃L[ℝ] Rd :=
  (LinearEquiv.smulOfNeZero ℝ Rd lam hlam.ne').toContinuousLinearEquiv

theorem smulCLE_apply (hlam : 0 < lam) (x : Rd) : smulCLE hlam x = lam • x := rfl

/-- The dilation of a Schwartz function. -/
noncomputable def dilS (hlam : 0 < lam) (φ : SchwartzMap Rd ℂ) : SchwartzMap Rd ℂ :=
  ((lam ^ ((d : ℝ) / 2) : ℝ) : ℂ) • SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (smulCLE hlam) φ

theorem dilS_apply (hlam : 0 < lam) (φ : SchwartzMap Rd ℂ) (x : Rd) :
    dilS hlam φ x = dilF lam φ x := by
  simp [dilS, dilF, smulCLE_apply]

theorem toL2_dilS (hlam : 0 < lam) (φ : SchwartzMap Rd ℂ) :
    toL2 (dilS hlam φ) = dilL2 hlam (toL2 φ) := by
  apply Lp.ext
  filter_upwards [coeFn_toL2 (dilS hlam φ), coeFn_dilL2 hlam (toL2 φ),
    dilF_congr_ae hlam (coeFn_toL2 φ)] with x h1 h2 h3
  rw [h1, h2, h3, dilS_apply]

theorem dS_dilS (hlam : 0 < lam) (i : Fin d) (φ : SchwartzMap Rd ℂ) :
    dS i (dilS hlam φ) = (lam : ℂ) • dilS hlam (dS i φ) := by
  ext x
  rw [dS_apply, SchwartzMap.smul_apply, dilS_apply, dilF, dS_apply]
  have hcomp : ⇑(dilS hlam φ) = fun y => ((lam ^ ((d : ℝ) / 2) : ℝ) : ℂ) * φ (lam • y) := by
    funext y
    rw [dilS_apply, dilF]
  rw [hcomp]
  have h1 : HasFDerivAt (fun y : Rd => lam • y) (lam • ContinuousLinearMap.id ℝ Rd) x :=
    (hasFDerivAt_id x).const_smul lam
  have h2 := (φ.differentiableAt.hasFDerivAt (x := lam • x)).comp x h1
  have h3 := h2.const_mul (((lam ^ ((d : ℝ) / 2) : ℝ) : ℂ))
  have h4 : fderiv ℝ (fun y : Rd => ((lam ^ ((d : ℝ) / 2) : ℝ) : ℂ) * φ (lam • y)) x =
      ((lam ^ ((d : ℝ) / 2) : ℝ) : ℂ) •
        (fderiv ℝ (⇑φ) (lam • x)).comp (lam • ContinuousLinearMap.id ℝ Rd) := h3.fderiv
  rw [h4]
  simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.coe_comp',
    Function.comp_apply, ContinuousLinearMap.coe_id', id_eq, map_smul, smul_eq_mul]
  rw [Complex.real_smul]
  ring

theorem lapS_dilS (hlam : 0 < lam) (φ : SchwartzMap Rd ℂ) :
    lapS (dilS hlam φ) = (((lam ^ 2 : ℝ)) : ℂ) • dilS hlam (lapS φ) := by
  have hl : ∀ ψ : SchwartzMap Rd ℂ, lapS ψ = ∑ i : Fin d, dS i (dS i ψ) := fun ψ => by
    simp [lapS]
  rw [hl, hl]
  simp_rw [dS_dilS, map_smul, dS_dilS, smul_smul]
  ext x
  simp only [coe_sum_schwartz, SchwartzMap.smul_apply, dilS_apply, dilF, smul_eq_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast
  ring

end Dilation

namespace H2

variable {lam : ℝ}

/-- The mass-preserving dilation `u_λ(x) = λ^{d/2} u(λx)` on `H²(ℝ^d)`. -/
noncomputable def dil (hlam : 0 < lam) (U : H2 d) : H2 d where
  val := dilL2 hlam U.val
  grad := fun i => (lam : ℂ) • dilL2 hlam (U.grad i)
  lap := (((lam ^ 2 : ℝ)) : ℂ) • dilL2 hlam U.lap
  approx := by
    obtain ⟨φ, h0, h1, h2⟩ := U.approx
    refine ⟨fun n => dilS hlam (φ n), ?_, fun i => ?_, ?_⟩
    · simpa only [toL2_dilS] using tendsto_dilL2 hlam h0
    · simpa only [dS_dilS, map_smul, toL2_dilS] using (tendsto_dilL2 hlam (h1 i)).const_smul _
    · simpa only [lapS_dilS, map_smul, toL2_dilS] using (tendsto_dilL2 hlam h2).const_smul _

theorem M_dil (hlam : 0 < lam) (U : H2 d) : M (dil hlam U) = M U := by
  simp [M, dil, norm_dilL2]

theorem K_dil (hlam : 0 < lam) (U : H2 d) : K (dil hlam U) = lam ^ 2 * K U := by
  simp only [K, dil, norm_smul, norm_dilL2, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hlam, mul_pow, Finset.mul_sum]

theorem D_dil (hlam : 0 < lam) (U : H2 d) : D (dil hlam U) = lam ^ 4 * D U := by
  simp only [D, dil, norm_smul, norm_dilL2, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < lam ^ 2), mul_pow]
  ring

/-- Nonlinear functionals of the dilation: `∫ G(|u_λ|²) = λ^{-d} ∫ G(λ^d |u|²)`. -/
theorem integral_dil (hlam : 0 < lam) (U : H2 d) (G : ℝ → ℝ) :
    ∫ x, G (‖(dil hlam U).val x‖ ^ 2) = (lam ^ d)⁻¹ * ∫ y, G (lam ^ d * ‖U.val y‖ ^ 2) := by
  have h : (fun x => G (‖(dil hlam U).val x‖ ^ 2)) =ᵐ[volume]
      fun x => G (lam ^ d * ‖(U.val : Rd → ℂ) (lam • x)‖ ^ 2) := by
    filter_upwards [coeFn_dilL2 hlam U.val] with x hx
    simp only [dil]
    rw [hx, norm_dilF_sq hlam]
  rw [integral_congr_ae h,
    integral_comp_dil hlam (fun y => G (lam ^ d * ‖(U.val : Rd → ℂ) y‖ ^ 2))]

end H2

end Sobolev

end ReyesMath
