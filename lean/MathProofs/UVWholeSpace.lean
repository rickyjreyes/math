import Mathlib
import MathProofs.UVIllPosedness

/-!
# Ultraviolet Sobolev ill-posedness on the whole space `ℝ^d` (F02/UV)

Fourier-packet proof of Theorem 1 of
`papers/uv-sobolev-ill-posedness-fourth-order-wave/main.tex` for `M = ℝ^d`, together with the
general-sector Proposition, with Mathlib's Fourier transform
`𝓕 f(ξ) = ∫ e^{−2πi⟨x,ξ⟩} f(x) dx` (physical frequency `k = 2πξ`).

* Differentiation under the integral sign for exponential packets: `hasDerivAt_integral_cexp`,
  `contDiff_integral_cexp` (joint `C^∞`), `laplacian_eq_sum_second_deriv`.
* Packets `W[g](t,x) = ∫_Ω e^{2πi⟨ξ,x⟩ + tS(ξ)} g(ξ) dξ` with `S(ξ) = s(|2πξ|²)`:
  `hasDerivAt_packet` (`∂ₜW[g] = W[Sg]`), `laplacian_packet` (`ΔW[g] = W[−|2πξ|² g]`),
  `contDiff_packet`; `packetSol_isSmoothSolution`: `a Re W[g]` is a jointly smooth exact
  solution of the sector equation whenever `R(|2πξ|²) ≥ 0` on `Ω`.
* Fourier side: `contDiffAt_Sξ` (smoothness of the growing root above the threshold),
  `schwartzOfCompact`, `fourier_re_fourierInv` (`𝓕[a Re 𝓕⁻H] = (a/2)(H + conj H(−·))` by Fourier
  inversion), `sobSqR_re_fourierInv` (disjoint reflected supports).
* Whole-space Sobolev norms `‖f‖²_{H^p} = ∫ (1 + |2πξ|²)^p |𝓕 f|²` (`sobSqR`, `MemSobR`),
  four-jet norms (`jetSqR`, `jetNormR`) and the isometric realization
  `toJetR : X_r(ℝ^d) → L²(ℝ^d)⁴` (`norm_toJetR`).
* Packets `φₙ(ξ − ne₁)` (`bump`, `profile`): exact norms `jetSqR_packetSol`, growth
  `profInt_growth` (`e^{2t₀c_*2π(n−1/2)}`), loss `profInt_loss` (`(1 + (2π(n+1/2))²)^ℓ`).
* Theorem 1 / Proposition on `ℝ^d`: `whole_unbounded`, `whole_no_bounded_estimate`,
  `whole_no_bounded_operator`, `whole_no_bounded_linear_extension`, and `wave_whole_unbounded`
  for `∂ₜ⁴u + (1 − 2Δ)∂ₜ²u − Δu + 2Δ²u = 0`.
-/

open Filter Topology Complex InnerProductSpace MeasureTheory Metric
open scoped ContDiff FourierTransform

namespace ReyesMath

namespace UVIllPosed

section ExpIntegral

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]

theorem norm_cexp_le (z : ℂ) : ‖Complex.exp z‖ ≤ Real.exp ‖z‖ := by
  rw [Complex.norm_exp]
  exact Real.exp_le_exp.2 (le_trans (le_abs_self _) (Complex.abs_re_le_norm z))

/-- Differentiation under the integral sign for `τ ↦ ∫ e^{A + τB} G dμ`. -/
theorem hasDerivAt_integral_cexp {A B G : α → ℂ} (hA : AEStronglyMeasurable A μ)
    (hB : AEStronglyMeasurable B μ) (hG : AEStronglyMeasurable G μ) {CA CB CG : ℝ}
    (hAb : ∀ᵐ ξ ∂μ, ‖A ξ‖ ≤ CA) (hBb : ∀ᵐ ξ ∂μ, ‖B ξ‖ ≤ CB) (hGb : ∀ᵐ ξ ∂μ, ‖G ξ‖ ≤ CG)
    (τ₀ : ℝ) :
    HasDerivAt (fun τ : ℝ => ∫ ξ, Complex.exp (A ξ + τ * B ξ) * G ξ ∂μ)
      (∫ ξ, Complex.exp (A ξ + τ₀ * B ξ) * (B ξ * G ξ) ∂μ) τ₀ := by
  have hE : ∀ τ : ℝ, AEStronglyMeasurable (fun ξ => Complex.exp (A ξ + τ * B ξ)) μ :=
    fun τ => Complex.continuous_exp.comp_aestronglyMeasurable (hA.add (hB.const_mul _))
  set M := Real.exp (CA + (|τ₀| + 1) * CB) with hM
  have hexp : ∀ᵐ ξ ∂μ, ∀ τ ∈ ball τ₀ 1, ‖Complex.exp (A ξ + τ * B ξ)‖ ≤ M := by
    filter_upwards [hAb, hBb] with ξ h1 h2 τ hτ
    have hτ' : |τ| ≤ |τ₀| + 1 := by
      have h := mem_ball_iff_norm.1 hτ
      rw [Real.norm_eq_abs] at h
      have := abs_sub_abs_le_abs_sub τ τ₀
      linarith
    refine le_trans (norm_cexp_le _) (Real.exp_le_exp.2 ?_)
    calc ‖A ξ + τ * B ξ‖ ≤ ‖A ξ‖ + |τ| * ‖B ξ‖ := by
          refine le_trans (norm_add_le _ _) ?_
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ CA + (|τ₀| + 1) * CB := by
          have : 0 ≤ ‖B ξ‖ := norm_nonneg _
          nlinarith [abs_nonneg τ]
  have hF_int : Integrable (fun ξ => Complex.exp (A ξ + τ₀ * B ξ) * G ξ) μ := by
    refine (integrable_const (M * CG)).mono' ((hE τ₀).mul hG) ?_
    filter_upwards [hexp, hGb] with ξ h1 h2
    rw [norm_mul]
    exact mul_le_mul (h1 τ₀ (mem_ball_self one_pos)) h2 (norm_nonneg _) (by positivity)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (x₀ := τ₀)
    (F := fun (τ : ℝ) ξ => Complex.exp (A ξ + τ * B ξ) * G ξ)
    (F' := fun (τ : ℝ) ξ => Complex.exp (A ξ + τ * B ξ) * (B ξ * G ξ))
    (bound := fun _ => M * (CB * CG)) one_pos (Eventually.of_forall fun τ => (hE τ).mul hG)
    hF_int ((hE τ₀).mul (hB.mul hG)) ?_ (integrable_const _) ?_).2
  · filter_upwards [hexp, hBb, hGb] with ξ h1 h2 h3 τ hτ
    rw [norm_mul, norm_mul]
    have hB0 : 0 ≤ CB := le_trans (norm_nonneg _) h2
    exact mul_le_mul (h1 τ hτ) (mul_le_mul h2 h3 (norm_nonneg _) hB0)
      (by positivity) (by positivity)
  · filter_upwards with ξ τ _
    have h1 : HasDerivAt (fun τ : ℝ => A ξ + τ * B ξ) (B ξ) τ := by
      simpa using ((hasDerivAt_id τ).ofReal_comp.mul_const (B ξ)).const_add (A ξ)
    have h2 := h1.cexp.mul_const (G ξ)
    convert h2 using 1
    ring

/-- Smoothness of `p ↦ ∫ e^{Λ(ξ)p} G(ξ) dμ(ξ)` for bounded measurable `Λ : α → P →L[ℝ] ℂ`
and bounded `G`, on a finite measure space. -/
theorem contDiff_integral_cexp {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] {Λ : α → P →L[ℝ] ℂ} (hΛ : AEStronglyMeasurable Λ μ) {CΛ : ℝ}
    (hΛb : ∀ᵐ ξ ∂μ, ‖Λ ξ‖ ≤ CΛ) :
    ∀ (n : ℕ) (G : α → ℂ), AEStronglyMeasurable G μ → (∃ C, ∀ᵐ ξ ∂μ, ‖G ξ‖ ≤ C) →
      ContDiff ℝ n (fun p => ∫ ξ, Complex.exp (Λ ξ p) * G ξ ∂μ) := by
  have hmeasΛ : ∀ p, AEStronglyMeasurable (fun ξ => Λ ξ p) μ := fun p =>
    (ContinuousLinearMap.apply ℝ ℂ p).continuous.comp_aestronglyMeasurable hΛ
  have hE : ∀ p, AEStronglyMeasurable (fun ξ => Complex.exp (Λ ξ p)) μ := fun p =>
    Complex.continuous_exp.comp_aestronglyMeasurable (hmeasΛ p)
  have hexp : ∀ p₀ : P, ∀ᵐ ξ ∂μ, ∀ p ∈ ball p₀ 1,
      ‖Complex.exp (Λ ξ p)‖ ≤ Real.exp (CΛ * (‖p₀‖ + 1)) := by
    intro p₀
    filter_upwards [hΛb] with ξ hξ p hp
    refine le_trans (norm_cexp_le _) (Real.exp_le_exp.2 ?_)
    have hp' : ‖p‖ ≤ ‖p₀‖ + 1 := by
      have h1 := mem_ball_iff_norm.1 hp
      have h2 := norm_le_norm_add_norm_sub' p p₀
      linarith
    calc ‖Λ ξ p‖ ≤ ‖Λ ξ‖ * ‖p‖ := (Λ ξ).le_opNorm p
      _ ≤ CΛ * (‖p₀‖ + 1) := mul_le_mul hξ hp' (norm_nonneg _) (le_trans (norm_nonneg _) hξ)
  have hint : ∀ (G : α → ℂ), AEStronglyMeasurable G μ → (∃ C, ∀ᵐ ξ ∂μ, ‖G ξ‖ ≤ C) →
      ∀ p, Integrable (fun ξ => Complex.exp (Λ ξ p) * G ξ) μ := by
    rintro G hG ⟨C, hC⟩ p
    refine (integrable_const (Real.exp (CΛ * (‖p‖ + 1)) * C)).mono' ((hE p).mul hG) ?_
    filter_upwards [hexp p, hC] with ξ h1 h2
    rw [norm_mul]
    exact mul_le_mul (h1 p (mem_ball_self one_pos)) h2 (norm_nonneg _) (by positivity)
  intro n
  induction n with
  | zero =>
    rintro G hG ⟨C, hC⟩
    simp only [Nat.cast_zero, contDiff_zero]
    refine continuous_iff_continuousAt.2 fun p₀ => ?_
    refine continuousAt_of_dominated (bound := fun _ => Real.exp (CΛ * (‖p₀‖ + 1)) * C)
      (Eventually.of_forall fun p => (hE p).mul hG) ?_ (integrable_const _) ?_
    · filter_upwards [ball_mem_nhds p₀ one_pos] with p hp
      filter_upwards [hexp p₀, hC] with ξ h1 h2
      rw [norm_mul]
      exact mul_le_mul (h1 p hp) h2 (norm_nonneg _) (by positivity)
    · exact Eventually.of_forall fun ξ =>
        ((Complex.continuous_exp.comp (Λ ξ).continuous).mul continuous_const).continuousAt
  | succ n ih =>
    rintro G hG ⟨C, hC⟩
    have hF'int : ∀ p, Integrable (fun ξ => (G ξ * Complex.exp (Λ ξ p)) • Λ ξ) μ := by
      intro p
      refine (integrable_const (C * Real.exp (CΛ * (‖p‖ + 1)) * CΛ)).mono'
        ((hG.mul (hE p)).smul hΛ) ?_
      filter_upwards [hexp p, hC, hΛb] with ξ h1 h2 h3
      rw [norm_smul, norm_mul]
      have hC0 : 0 ≤ C := le_trans (norm_nonneg _) h2
      exact mul_le_mul (mul_le_mul h2 (h1 p (mem_ball_self one_pos)) (norm_nonneg _) hC0) h3
        (norm_nonneg _) (by positivity)
    have hderiv : ∀ p₀, HasFDerivAt (fun p => ∫ ξ, Complex.exp (Λ ξ p) * G ξ ∂μ)
        (∫ ξ, (G ξ * Complex.exp (Λ ξ p₀)) • Λ ξ ∂μ) p₀ := by
      intro p₀
      refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ)
        (F := fun p ξ => Complex.exp (Λ ξ p) * G ξ)
        (F' := fun p ξ => (G ξ * Complex.exp (Λ ξ p)) • Λ ξ)
        (bound := fun _ => C * Real.exp (CΛ * (‖p₀‖ + 1)) * CΛ) one_pos
        (Eventually.of_forall fun p => (hE p).mul hG) (hint G hG ⟨C, hC⟩ p₀)
        ((hG.mul (hE p₀)).smul hΛ) ?_ (integrable_const _) ?_
      · filter_upwards [hexp p₀, hC, hΛb] with ξ h1 h2 h3 p hp
        rw [norm_smul, norm_mul]
        have hC0 : 0 ≤ C := le_trans (norm_nonneg _) h2
        exact mul_le_mul (mul_le_mul h2 (h1 p hp) (norm_nonneg _) hC0) h3 (norm_nonneg _)
          (by positivity)
      · filter_upwards with ξ p _
        have h2 := ((Λ ξ).hasFDerivAt (x := p)).cexp.mul_const (G ξ)
        convert h2 using 1
        rw [smul_smul, mul_comm]
    rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by push_cast; rfl,
      contDiff_succ_iff_fderiv_apply]
    refine ⟨fun p => (hderiv p).differentiableAt, fun h => absurd h (by simp), fun y => ?_⟩
    have hfd : (fun p => fderiv ℝ (fun p => ∫ ξ, Complex.exp (Λ ξ p) * G ξ ∂μ) p y) =
        fun p => ∫ ξ, Complex.exp (Λ ξ p) * (Λ ξ y * G ξ) ∂μ := by
      funext p
      rw [(hderiv p).fderiv, ContinuousLinearMap.integral_apply (hF'int p)]
      congr 1
      funext ξ
      simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]
      ring
    rw [hfd]
    refine ih _ ((hmeasΛ y).mul hG) ⟨CΛ * ‖y‖ * C, ?_⟩
    filter_upwards [hΛb, hC] with ξ h1 h2
    rw [norm_mul]
    have hC0 : 0 ≤ C := le_trans (norm_nonneg _) h2
    exact mul_le_mul (le_trans ((Λ ξ).le_opNorm y) (mul_le_mul_of_nonneg_right h1 (norm_nonneg _)))
      h2 (norm_nonneg _) (by have := le_trans (norm_nonneg _) h1; positivity)

theorem contDiff_infty_integral_cexp {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] {Λ : α → P →L[ℝ] ℂ} (hΛ : AEStronglyMeasurable Λ μ) {CΛ : ℝ}
    (hΛb : ∀ᵐ ξ ∂μ, ‖Λ ξ‖ ≤ CΛ) {G : α → ℂ} (hG : AEStronglyMeasurable G μ)
    (hGb : ∃ C, ∀ᵐ ξ ∂μ, ‖G ξ‖ ≤ C) :
    ContDiff ℝ ∞ (fun p => ∫ ξ, Complex.exp (Λ ξ p) * G ξ ∂μ) :=
  contDiff_infty.2 fun n => contDiff_integral_cexp hΛ hΛb n G hG hGb

end ExpIntegral

section Laplacian

variable {d : ℕ}

local notation "Rd" => EuclideanSpace ℝ (Fin d)

/-- `Δf(x) = Σᵢ (d²/dτ²) f(x + τ eᵢ)|_{τ=0}` for `C²` functions. -/
theorem laplacian_eq_sum_second_deriv {f : Rd → ℂ} (hf : ContDiff ℝ 2 f) (x : Rd) :
    Δ f x = ∑ i, deriv (deriv (fun τ : ℝ => f (x + τ • EuclideanSpace.single i (1 : ℝ)))) 0 := by
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis f (EuclideanSpace.basisFun (Fin d) ℝ)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, EuclideanSpace.basisFun_apply]
  set e : Rd := EuclideanSpace.single i (1 : ℝ)
  have hd1 : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hfd : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hl : ∀ σ : ℝ, HasDerivAt (fun τ : ℝ => x + τ • e) e σ := fun σ => by
    simpa using ((hasDerivAt_id σ).smul_const e).const_add x
  have h1 : deriv (fun τ : ℝ => f (x + τ • e)) = fun σ => fderiv ℝ f (x + σ • e) e := by
    funext σ
    exact ((hd1 _).hasFDerivAt.comp_hasDerivAt σ (hl σ)).deriv
  rw [h1]
  have h2 : HasDerivAt (fun σ : ℝ => fderiv ℝ f (x + σ • e)) (fderiv ℝ (fderiv ℝ f) x e) 0 := by
    have := ((hfd.differentiable le_rfl) (x + (0 : ℝ) • e)).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
      (hl 0)
    simpa using this
  have h3 := (ContinuousLinearMap.apply ℝ ℂ e).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h2
  exact h3.deriv.symm

end Laplacian

section Packet

variable {d : ℕ}

local notation "Rd" => EuclideanSpace ℝ (Fin d)

/-- The physical frequency squared `q(ξ) = |2πξ|²` of the Fourier variable `ξ`
(Mathlib's convention `𝓕 f(ξ) = ∫ e^{−2πi⟨x,ξ⟩} f(x) dx`). -/
noncomputable def qξ (ξ : Rd) : ℝ := (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2

/-- The growing exponent `S(ξ) = s(|2πξ|²)`. -/
noncomputable def Sξ (K G T m2 : ℝ) (ξ : Rd) : ℂ := sExp K G T m2 (qξ ξ)

theorem continuous_sigma (K G T m2 : ℝ) : Continuous (sigma K G T m2) := by
  unfold sigma modz zRe cq bq
  fun_prop

theorem continuous_alpha (K G T m2 : ℝ) : Continuous (alpha K G T m2) := by
  unfold alpha modz zRe cq bq
  fun_prop

theorem continuous_qξ : Continuous (qξ (d := d)) := by
  unfold qξ
  fun_prop

theorem continuous_Sξ (K G T m2 : ℝ) : Continuous (Sξ (d := d) K G T m2) := by
  have h : Sξ (d := d) K G T m2 = fun ξ =>
      (sigma K G T m2 (qξ ξ) : ℂ) + (-(alpha K G T m2 (qξ ξ)) : ℝ) * Complex.I := by
    funext ξ
    apply Complex.ext <;> simp [Sξ, sExp]
  rw [h]
  have h1 := (continuous_sigma K G T m2).comp (continuous_qξ (d := d))
  have h2 := (continuous_alpha K G T m2).comp (continuous_qξ (d := d))
  exact (Complex.continuous_ofReal.comp h1).add
    ((Complex.continuous_ofReal.comp h2.neg).mul continuous_const)

/-- The Fourier packet `W[g](t,x) = ∫_Ω e^{2πi⟨ξ,x⟩ + t S(ξ)} g(ξ) dξ`. -/
noncomputable def packet (K G T m2 : ℝ) (Ω : Set Rd) (g : Rd → ℂ) (t : ℝ) (x : Rd) : ℂ :=
  ∫ ξ in Ω, Complex.exp (((2 * Real.pi * inner ℝ ξ x : ℝ) : ℂ) * Complex.I +
    (t : ℂ) * Sξ K G T m2 ξ) * g ξ

variable {K G T m2 : ℝ} {Ω : Set (EuclideanSpace ℝ (Fin d))}

theorem isFiniteMeasure_restrict_compact (hΩ : IsCompact Ω) :
    IsFiniteMeasure (volume.restrict Ω) :=
  ⟨by rw [Measure.restrict_apply_univ]; exact hΩ.measure_lt_top⟩

theorem ae_bound_of_continuous (hΩ : IsCompact Ω) {f : Rd → ℂ} (hf : Continuous f) :
    ∃ C, ∀ᵐ ξ ∂(volume.restrict Ω), ‖f ξ‖ ≤ C := by
  obtain ⟨C, hC⟩ := hΩ.exists_bound_of_continuousOn hf.continuousOn
  exact ⟨C, ae_restrict_of_forall_mem hΩ.measurableSet hC⟩

/-- `∂ₜ W[g] = W[S g]`. -/
theorem hasDerivAt_packet (hΩ : IsCompact Ω) {g : Rd → ℂ} (hg : Continuous g) (t : ℝ) (x : Rd) :
    HasDerivAt (fun τ => packet K G T m2 Ω g τ x)
      (packet K G T m2 Ω (fun ξ => Sξ K G T m2 ξ * g ξ) t x) t := by
  haveI := isFiniteMeasure_restrict_compact hΩ
  have hA : Continuous fun ξ : Rd => ((2 * Real.pi * inner ℝ ξ x : ℝ) : ℂ) * Complex.I := by
    fun_prop
  obtain ⟨CA, hCA⟩ := ae_bound_of_continuous hΩ hA
  obtain ⟨CB, hCB⟩ := ae_bound_of_continuous hΩ (continuous_Sξ (d := d) K G T m2)
  obtain ⟨CG, hCG⟩ := ae_bound_of_continuous hΩ hg
  exact hasDerivAt_integral_cexp hA.aestronglyMeasurable
    (continuous_Sξ K G T m2).aestronglyMeasurable hg.aestronglyMeasurable hCA hCB hCG t

/-- The packet is jointly smooth in `(t, x)`. -/
theorem contDiff_packet (hΩ : IsCompact Ω) {g : Rd → ℂ} (hg : Continuous g) :
    ContDiff ℝ ∞ (fun p : ℝ × Rd => packet K G T m2 Ω g p.1 p.2) := by
  haveI := isFiniteMeasure_restrict_compact hΩ
  set Λ : Rd → (ℝ × Rd) →L[ℝ] ℂ := fun ξ =>
    Sξ K G T m2 ξ • (Complex.ofRealCLM.comp (ContinuousLinearMap.fst ℝ ℝ Rd)) +
      ((2 * Real.pi : ℝ) • Complex.I) •
        ((Complex.ofRealCLM.comp (innerSL ℝ ξ)).comp (ContinuousLinearMap.snd ℝ ℝ Rd))
    with hΛ
  have hΛapp : ∀ ξ (p : ℝ × Rd), Λ ξ p =
      ((2 * Real.pi * inner ℝ ξ p.2 : ℝ) : ℂ) * Complex.I + (p.1 : ℂ) * Sξ K G T m2 ξ := by
    intro ξ p
    simp only [hΛ, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
      ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', Complex.ofRealCLM_apply, innerSL_apply, smul_eq_mul]
    rw [Complex.real_smul]
    push_cast
    ring
  have hΛc : Continuous Λ := by
    refine ((continuous_Sξ K G T m2).smul continuous_const).add (continuous_const.smul ?_)
    exact (continuous_const.clm_comp (innerSL ℝ).continuous).clm_comp continuous_const
  obtain ⟨CΛ, hCΛ⟩ := hΩ.exists_bound_of_continuousOn hΛc.continuousOn
  obtain ⟨CG, hCG⟩ := ae_bound_of_continuous hΩ hg
  have h := contDiff_infty_integral_cexp (μ := volume.restrict Ω) hΛc.aestronglyMeasurable
    (ae_restrict_of_forall_mem hΩ.measurableSet hCΛ) hg.aestronglyMeasurable ⟨CG, hCG⟩
  convert h using 2 with p
  unfold packet
  congr 1
  funext ξ
  rw [hΛapp]

theorem contDiff_packet_x (hΩ : IsCompact Ω) {g : Rd → ℂ} (hg : Continuous g) (t : ℝ) :
    ContDiff ℝ ∞ (packet K G T m2 Ω g t) := by
  have h2 : ContDiff ℝ ∞ (fun x : Rd => ((t, x) : ℝ × Rd)) :=
    (contDiff_const (c := t)).prodMk contDiff_id
  have h3 := (contDiff_packet (K := K) (G := G) (T := T) (m2 := m2) hΩ hg).comp h2
  have h4 : ((fun p : ℝ × Rd => packet K G T m2 Ω g p.1 p.2) ∘ fun x : Rd => (t, x)) =
      packet K G T m2 Ω g t := by
    funext x
    simp only [Function.comp_apply]
  rw [h4] at h3
  exact h3

/-- `Δₓ W[g] = W[−q g]`. -/
theorem laplacian_packet (hΩ : IsCompact Ω) {g : Rd → ℂ} (hg : Continuous g) (t : ℝ) (x : Rd) :
    Δ (packet K G T m2 Ω g t) x =
      packet K G T m2 Ω (fun ξ => -(qξ ξ : ℂ) * g ξ) t x := by
  haveI := isFiniteMeasure_restrict_compact hΩ
  rw [laplacian_eq_sum_second_deriv ((contDiff_packet_x hΩ hg t).of_le (by norm_cast)) x]
  -- each directional second derivative
  have hdir : ∀ i : Fin d, deriv (deriv (fun τ : ℝ =>
      packet K G T m2 Ω g t (x + τ • EuclideanSpace.single i (1 : ℝ)))) 0 =
      ∫ ξ in Ω, Complex.exp (((2 * Real.pi * inner ℝ ξ x : ℝ) : ℂ) * Complex.I +
        (t : ℂ) * Sξ K G T m2 ξ) *
        ((((2 * Real.pi * ξ i : ℝ) : ℂ) * Complex.I) ^ 2 * g ξ) := by
    intro i
    set e : Rd := EuclideanSpace.single i (1 : ℝ)
    set A : Rd → ℂ := fun ξ => ((2 * Real.pi * inner ℝ ξ x : ℝ) : ℂ) * Complex.I +
      (t : ℂ) * Sξ K G T m2 ξ with hA
    set B : Rd → ℂ := fun ξ => ((2 * Real.pi * ξ i : ℝ) : ℂ) * Complex.I with hB
    have hAc : Continuous A := by
      simp only [hA]
      have := continuous_Sξ (d := d) K G T m2
      fun_prop
    have hBc : Continuous B := by
      simp only [hB]
      have : Continuous fun ξ : Rd => ξ i := (EuclideanSpace.proj i).continuous
      fun_prop
    obtain ⟨CA, hCA⟩ := ae_bound_of_continuous hΩ hAc
    obtain ⟨CB, hCB⟩ := ae_bound_of_continuous hΩ hBc
    have hline : ∀ τ : ℝ, packet K G T m2 Ω g t (x + τ • e) =
        ∫ ξ in Ω, Complex.exp (A ξ + τ * B ξ) * g ξ := by
      intro τ
      unfold packet
      congr 1
      funext ξ
      congr 2
      simp only [hA, hB, e, inner_add_right, inner_smul_right, EuclideanSpace.inner_single_right,
        conj_trivial, one_mul]
      push_cast
      ring
    have hd1 : ∀ σ : ℝ, HasDerivAt (fun τ : ℝ => packet K G T m2 Ω g t (x + τ • e))
        (∫ ξ in Ω, Complex.exp (A ξ + σ * B ξ) * (B ξ * g ξ)) σ := by
      intro σ
      simp_rw [hline]
      obtain ⟨CG, hCG⟩ := ae_bound_of_continuous hΩ hg
      exact hasDerivAt_integral_cexp hAc.aestronglyMeasurable hBc.aestronglyMeasurable
        hg.aestronglyMeasurable hCA hCB hCG σ
    have hfun : deriv (fun τ : ℝ => packet K G T m2 Ω g t (x + τ • e)) =
        fun σ : ℝ => ∫ ξ in Ω, Complex.exp (A ξ + σ * B ξ) * (B ξ * g ξ) :=
      funext fun σ => (hd1 σ).deriv
    rw [hfun]
    obtain ⟨CBG, hCBG⟩ := ae_bound_of_continuous hΩ (hBc.mul hg)
    have hd2 := hasDerivAt_integral_cexp hAc.aestronglyMeasurable hBc.aestronglyMeasurable
      (hBc.mul hg).aestronglyMeasurable hCA hCB hCBG (0 : ℝ)
    rw [hd2.deriv]
    congr 1
    funext ξ
    simp only [hB, Complex.ofReal_zero, zero_mul, add_zero]
    ring
  simp_rw [hdir]
  rw [← integral_finset_sum]
  · unfold packet
    congr 1
    funext ξ
    rw [← Finset.mul_sum, ← Finset.sum_mul]
    congr 2
    have hreal : ∑ i : Fin d, (2 * Real.pi * ξ i) ^ 2 = qξ ξ := by
      rw [qξ, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Real.norm_eq_abs, sq_abs]
      ring
    have hq : ∑ i : Fin d, (((2 * Real.pi * ξ i : ℝ) : ℂ) * Complex.I) ^ 2 = -(qξ ξ : ℂ) := by
      calc ∑ i : Fin d, (((2 * Real.pi * ξ i : ℝ) : ℂ) * Complex.I) ^ 2
          = ∑ i : Fin d, -((((2 * Real.pi * ξ i) ^ 2 : ℝ)) : ℂ) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [mul_pow, Complex.I_sq]
            push_cast
            ring
        _ = -(qξ ξ : ℂ) := by
            rw [Finset.sum_neg_distrib, ← Complex.ofReal_sum, hreal]
    rw [hq]
  · intro i _
    have hc : Continuous fun ξ : Rd => Complex.exp (((2 * Real.pi * inner ℝ ξ x : ℝ) : ℂ) *
        Complex.I + (t : ℂ) * Sξ K G T m2 ξ) *
        ((((2 * Real.pi * ξ i : ℝ) : ℂ) * Complex.I) ^ 2 * g ξ) := by
      have := continuous_Sξ (d := d) K G T m2
      have : Continuous fun ξ : Rd => ξ i := (EuclideanSpace.proj i).continuous
      fun_prop
    exact hc.continuousOn.integrableOn_compact hΩ

end Packet

section PacketSolution

variable {d : ℕ}

local notation "Rd" => EuclideanSpace ℝ (Fin d)

variable {K G T m2 : ℝ} {Ω : Set (EuclideanSpace ℝ (Fin d))}

/-- The real packet solution `u(t,x) = a Re W[g](t,x)`. -/
noncomputable def packetSol (K G T m2 : ℝ) (Ω : Set Rd) (g : Rd → ℂ) (a : ℝ) (t : ℝ)
    (x : Rd) : ℝ :=
  a * (packet K G T m2 Ω g t x).re

theorem iteratedDeriv_packetSol (hΩ : IsCompact Ω) (a : ℝ) (x : Rd) : ∀ (j : ℕ) {g : Rd → ℂ},
    Continuous g → iteratedDeriv j (fun τ => packetSol K G T m2 Ω g a τ x) =
      fun τ => packetSol K G T m2 Ω (fun ξ => Sξ K G T m2 ξ ^ j * g ξ) a τ x
  | 0, g, _ => by
    funext τ
    simp [packetSol]
  | j + 1, g, hg => by
    have hd : deriv (fun τ => packetSol K G T m2 Ω g a τ x) =
        fun τ => packetSol K G T m2 Ω (fun ξ => Sξ K G T m2 ξ * g ξ) a τ x := by
      funext τ
      have h1 := hasDerivAt_packet (K := K) (G := G) (T := T) (m2 := m2) hΩ hg τ x
      have h2 := (Complex.reCLM.hasFDerivAt.comp_hasDerivAt τ h1).const_mul a
      exact h2.deriv
    rw [iteratedDeriv_succ', hd,
      iteratedDeriv_packetSol hΩ a x j ((continuous_Sξ K G T m2).mul hg)]
    funext τ
    simp only [packetSol]
    congr 3
    funext ξ
    ring

theorem dt_packetSol (hΩ : IsCompact Ω) {g : Rd → ℂ} (hg : Continuous g) (a : ℝ) (j : ℕ)
    (t : ℝ) : dt j (packetSol K G T m2 Ω g a) t =
      packetSol K G T m2 Ω (fun ξ => Sξ K G T m2 ξ ^ j * g ξ) a t := by
  funext x
  rw [dt, iteratedDeriv_packetSol hΩ a x j hg]

theorem laplacian_packetSol (hΩ : IsCompact Ω) {g : Rd → ℂ} (hg : Continuous g) (a t : ℝ) :
    Δ (packetSol K G T m2 Ω g a t) =
      packetSol K G T m2 Ω (fun ξ => -(qξ ξ : ℂ) * g ξ) a t := by
  funext x
  have hf : ContDiffAt ℝ 2 (packet K G T m2 Ω g t) x :=
    ((contDiff_packet_x hΩ hg t).of_le (by norm_cast)).contDiffAt
  have h := hf.laplacian_CLM_comp_left (l := a • Complex.reCLM)
  have he : packetSol K G T m2 Ω g a t = ⇑(a • Complex.reCLM) ∘ packet K G T m2 Ω g t := by
    funext y
    simp [packetSol]
  rw [he, h]
  simp only [Function.comp_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    Complex.reCLM_apply, smul_eq_mul, packetSol]
  rw [laplacian_packet hΩ hg]

theorem packetSol_smooth (hΩ : IsCompact Ω) {g : Rd → ℂ} (hg : Continuous g) (a : ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ × Rd => packetSol K G T m2 Ω g a p.1 p.2) :=
  contDiff_const.mul (Complex.reCLM.contDiff.comp (contDiff_packet hΩ hg))

/-- The packet built on the growing root solves the sector equation exactly. -/
theorem packetSol_isSmoothSolution (hK : 0 < K) (hΩ : IsCompact Ω)
    (hR : ∀ ξ ∈ Ω, 0 ≤ radic K G T m2 (qξ ξ)) {g : Rd → ℂ} (hg : Continuous g) (a : ℝ) :
    IsSmoothSolution K G T m2 (packetSol K G T m2 Ω g a) := by
  refine ⟨packetSol_smooth hΩ hg a, fun t x => ?_⟩
  have hS := continuous_Sξ (d := d) K G T m2
  have hq := continuous_qξ (d := d)
  have hS2 : Continuous fun ξ => Sξ K G T m2 ξ ^ 2 * g ξ := (hS.pow 2).mul hg
  have hqg : Continuous fun ξ => -(qξ ξ : ℂ) * g ξ :=
    (Complex.continuous_ofReal.comp hq).neg.mul hg
  have hu : packetSol K G T m2 Ω g a t = packetSol K G T m2 Ω g a t := rfl
  unfold sectorOp
  rw [dt_packetSol hΩ hg, dt_packetSol hΩ hg, laplacian_packetSol hΩ hS2,
    laplacian_packetSol hΩ hg, laplacian_packetSol hΩ hqg]
  simp only [packetSol]
  -- the complex combination vanishes
  have hZ : (K : ℂ) * packet K G T m2 Ω (fun ξ => Sξ K G T m2 ξ ^ 4 * g ξ) t x +
      packet K G T m2 Ω (fun ξ => Sξ K G T m2 ξ ^ 2 * g ξ) t x -
      ((2 * K + G : ℝ) : ℂ) * packet K G T m2 Ω
        (fun ξ => -(qξ ξ : ℂ) * (Sξ K G T m2 ξ ^ 2 * g ξ)) t x -
      packet K G T m2 Ω (fun ξ => -(qξ ξ : ℂ) * g ξ) t x +
      (m2 : ℂ) * packet K G T m2 Ω (fun ξ => Sξ K G T m2 ξ ^ 0 * g ξ) t x +
      ((K + G + T : ℝ) : ℂ) * packet K G T m2 Ω
        (fun ξ => -(qξ ξ : ℂ) * (-(qξ ξ : ℂ) * g ξ)) t x = 0 := by
    unfold packet
    have hint : ∀ f : Rd → ℂ, Continuous f → Integrable f (volume.restrict Ω) :=
      fun f hf => hf.continuousOn.integrableOn_compact hΩ
    have hE : Continuous fun ξ : Rd => Complex.exp (((2 * Real.pi * inner ℝ ξ x : ℝ) : ℂ) *
        Complex.I + (t : ℂ) * Sξ K G T m2 ξ) := by fun_prop
    rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul, ← integral_const_mul,
      ← integral_add (hint _ (by fun_prop)) (hint _ (by fun_prop)),
      ← integral_sub (hint _ (by fun_prop)) (hint _ (by fun_prop)),
      ← integral_sub (hint _ (by fun_prop)) (hint _ (by fun_prop)),
      ← integral_add (hint _ (by fun_prop)) (hint _ (by fun_prop)),
      ← integral_add (hint _ (by fun_prop)) (hint _ (by fun_prop))]
    refine setIntegral_eq_zero_of_forall_eq_zero fun ξ hξ => ?_
    have hc := sExp_char hK (hR ξ hξ)
    unfold bq cq at hc
    generalize Complex.exp (((2 * Real.pi * inner ℝ ξ x : ℝ) : ℂ) * Complex.I +
      (t : ℂ) * Sξ K G T m2 ξ) = E
    simp only [Sξ]
    push_cast at hc ⊢
    linear_combination E * g ξ * hc
  have hlin : ∀ z₁ z₂ z₃ z₄ z₅ z₆ : ℂ,
      K * (a * z₁.re) + a * z₂.re - (2 * K + G) * (a * z₃.re) - a * z₄.re + m2 * (a * z₅.re) +
        (K + G + T) * (a * z₆.re) =
      a * ((K : ℂ) * z₁ + z₂ - ((2 * K + G : ℝ) : ℂ) * z₃ - z₄ + (m2 : ℂ) * z₅ +
        ((K + G + T : ℝ) : ℂ) * z₆).re := by
    intro z₁ z₂ z₃ z₄ z₅ z₆
    simp only [Complex.add_re, Complex.sub_re, Complex.re_ofReal_mul]
    ring
  have h0 : packet K G T m2 Ω g t x = packet K G T m2 Ω (fun ξ => Sξ K G T m2 ξ ^ 0 * g ξ) t x := by
    simp
  rw [h0, hlin, hZ, Complex.zero_re, mul_zero]

end PacketSolution

/-! ### Smoothness of the growing exponent away from the threshold -/

section SmoothExponent

variable {K G T m2 q : ℝ}

theorem modz_gt_abs_zRe (hK : 0 < K) (hR : 0 < radic K G T m2 q) :
    |zRe K G q| < modz K G T m2 q := by
  have hIm : 0 < zIm K G T m2 q := div_pos (Real.sqrt_pos.2 hR) (by linarith)
  have hsq := modz_sq hK hR.le
  have hmod : 0 ≤ modz K G T m2 q := Real.sqrt_nonneg _
  have : zRe K G q ^ 2 < modz K G T m2 q ^ 2 := by nlinarith
  exact abs_lt_of_sq_lt_sq this hmod

theorem cq_div_pos (hK : 0 < K) (hR : 0 < radic K G T m2 q) : 0 < cq K G T m2 q / K := by
  have hIm : 0 < zIm K G T m2 q := div_pos (Real.sqrt_pos.2 hR) (by linarith)
  rw [← zRe_sq_add_zIm_sq hK hR.le]
  positivity

theorem contDiffAt_modz (hK : 0 < K) (hR : 0 < radic K G T m2 q) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n (modz K G T m2) q := by
  have h1 : ContDiffAt ℝ n (fun q' => cq K G T m2 q' / K) q := by
    unfold cq
    fun_prop
  exact h1.sqrt (cq_div_pos hK hR).ne'

theorem contDiffAt_zRe {n : WithTop ℕ∞} : ContDiffAt ℝ n (zRe K G) q := by
  unfold zRe bq
  fun_prop

theorem contDiffAt_sigma (hK : 0 < K) (hR : 0 < radic K G T m2 q) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n (sigma K G T m2) q := by
  have h := abs_lt.1 (modz_gt_abs_zRe hK hR)
  have h3 : ContDiffAt ℝ n (fun q' => (modz K G T m2 q' - zRe K G q') / 2) q :=
    ((contDiffAt_modz hK hR).sub contDiffAt_zRe).div_const 2
  exact h3.sqrt (by linarith [h.2])

theorem contDiffAt_alpha (hK : 0 < K) (hR : 0 < radic K G T m2 q) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n (alpha K G T m2) q := by
  have h := abs_lt.1 (modz_gt_abs_zRe hK hR)
  have h3 : ContDiffAt ℝ n (fun q' => (modz K G T m2 q' + zRe K G q') / 2) q :=
    ((contDiffAt_modz hK hR).add contDiffAt_zRe).div_const 2
  exact h3.sqrt (by linarith [h.1])

end SmoothExponent

section SchwartzProfiles

variable {d : ℕ}

local notation "Rd" => EuclideanSpace ℝ (Fin d)

variable {K G T m2 : ℝ}

theorem Sξ_eq (K G T m2 : ℝ) : Sξ (d := d) K G T m2 = fun ξ =>
    ((sigma K G T m2 (qξ ξ) : ℝ) : ℂ) + ((-(alpha K G T m2 (qξ ξ)) : ℝ) : ℂ) * Complex.I := by
  funext ξ
  apply Complex.ext <;> simp [Sξ, sExp]

theorem contDiff_qξ {n : WithTop ℕ∞} : ContDiff ℝ n (qξ (d := d)) := by
  unfold qξ
  exact contDiff_const.mul (contDiff_norm_sq ℝ)

/-- `S` is smooth on `{ξ : q(ξ) > q_R}` (where `R(q(ξ)) > 0`). -/
theorem contDiffAt_Sξ (hK : 0 < K) (hB : 0 < 4 * K * T - G ^ 2) {ξ : Rd}
    (hξ : qR K G T m2 < qξ ξ) {n : WithTop ℕ∞} : ContDiffAt ℝ n (Sξ K G T m2) ξ := by
  have hR := radic_pos (m2 := m2) hB hξ.le
  rw [Sξ_eq]
  have h1 := (contDiffAt_sigma hK hR (n := n)).comp ξ (contDiff_qξ.contDiffAt)
  have h2 := (contDiffAt_alpha hK hR (n := n)).comp ξ (contDiff_qξ.contDiffAt)
  exact (Complex.ofRealCLM.contDiff.contDiffAt.comp ξ h1).add
    ((Complex.ofRealCLM.contDiff.contDiffAt.comp ξ h2.neg).mul contDiffAt_const)

/-- A product `F · g` is smooth if `g` is smooth and `F` is smooth near `tsupport g`. -/
theorem contDiff_mul_of_tsupport {F g : Rd → ℂ} {U : Set Rd}
    (hsub : tsupport g ⊆ U) (hg : ContDiff ℝ ∞ g) (hF : ∀ ξ ∈ U, ContDiffAt ℝ ∞ F ξ) :
    ContDiff ℝ ∞ (fun ξ => F ξ * g ξ) := by
  refine contDiff_iff_contDiffAt.2 fun ξ => ?_
  by_cases hξ : ξ ∈ tsupport g
  · exact (hF ξ (hsub hξ)).mul hg.contDiffAt
  · have hz : (fun ξ => F ξ * g ξ) =ᶠ[𝓝 ξ] fun _ => (0 : ℂ) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hξ] with η hη
      simp [hη]
    exact contDiffAt_const.congr_of_eventuallyEq hz

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

@[simp] theorem schwartzOfCompact_apply (f : Rd → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (x : Rd) : schwartzOfCompact f hf hc x = f x := rfl

theorem conj_fourierChar (y : ℝ) : (starRingEnd ℂ) (𝐞 y : ℂ) = (𝐞 (-y) : ℂ) := by
  rw [Real.fourierChar_apply, Real.fourierChar_apply, ← Complex.exp_conj, map_mul,
    Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring_nf

/-- The Fourier transform of the real part of an inverse Fourier transform:
`𝓕[a Re 𝓕⁻H](ξ) = (a/2)(H(ξ) + conj H(−ξ))`. -/
theorem fourier_re_fourierInv (H : SchwartzMap Rd ℂ) (a : ℝ) (ξ : Rd) :
    𝓕 (fun x => ((a * (𝓕⁻ (⇑H) x).re : ℝ) : ℂ)) ξ =
      (a / 2 : ℂ) * (H ξ + (starRingEnd ℂ) (H (-ξ))) := by
  set v : Rd → ℂ := 𝓕⁻ (⇑H) with hv
  have hvS : ⇑((SchwartzMap.fourierTransformCLE ℂ).symm H) = v := by
    rw [SchwartzMap.fourierTransformCLE_symm_apply]
  have hvint : Integrable v :=
    hvS ▸ ((SchwartzMap.fourierTransformCLE ℂ).symm H).integrable (μ := volume)
  have hFH : Integrable (𝓕 (⇑H)) := by
    have := (SchwartzMap.fourierTransformCLM ℂ H).integrable (μ := volume)
    rwa [SchwartzMap.fourierTransformCLM_apply] at this
  have hinv : 𝓕 v = ⇑H := Continuous.fourier_inversion_inv H.continuous H.integrable hFH
  have hvconj : Integrable fun x => (starRingEnd ℂ) (v x) :=
    hvint.norm.mono' (Complex.continuous_conj.comp_aestronglyMeasurable hvint.1)
      (Eventually.of_forall fun x => by simp)
  have hf : (fun x => ((a * (v x).re : ℝ) : ℂ)) =
      fun x => (a / 2 : ℂ) * v x + (a / 2 : ℂ) * (starRingEnd ℂ) (v x) := by
    funext x
    push_cast
    rw [Complex.re_eq_add_conj]
    ring
  have hi1 : Integrable (fun x => 𝐞 (-inner ℝ x ξ) • v x) :=
    (Real.fourierIntegral_convergent_iff ξ).2 hvint
  have hi2 : Integrable (fun x => 𝐞 (-inner ℝ x ξ) • (starRingEnd ℂ) (v x)) :=
    (Real.fourierIntegral_convergent_iff ξ).2 hvconj
  have hc : ∫ x, 𝐞 (-inner ℝ x ξ) • (starRingEnd ℂ) (v x) =
      (starRingEnd ℂ) (∫ x, 𝐞 (-inner ℝ x (-ξ)) • v x) := by
    rw [← integral_conj]
    congr 1
    funext x
    simp only [Circle.smul_def, smul_eq_mul, map_mul, conj_fourierChar, inner_neg_right, neg_neg]
  calc 𝓕 (fun x => ((a * (v x).re : ℝ) : ℂ)) ξ
      = ∫ x, ((a / 2 : ℂ) * (𝐞 (-inner ℝ x ξ) • v x) +
          (a / 2 : ℂ) * (𝐞 (-inner ℝ x ξ) • (starRingEnd ℂ) (v x))) := by
        rw [Real.fourierIntegral_eq]
        congr 1
        funext x
        rw [congrFun hf x]
        simp only [Circle.smul_def, smul_eq_mul]
        ring
    _ = (a / 2 : ℂ) * (∫ x, 𝐞 (-inner ℝ x ξ) • v x) +
          (a / 2 : ℂ) * ∫ x, 𝐞 (-inner ℝ x ξ) • (starRingEnd ℂ) (v x) := by
        rw [integral_add (hi1.const_mul _) (hi2.const_mul _), integral_const_mul,
          integral_const_mul]
    _ = (a / 2 : ℂ) * (H ξ + (starRingEnd ℂ) (H (-ξ))) := by
        rw [hc, ← Real.fourierIntegral_eq, ← Real.fourierIntegral_eq, hinv]
        ring

end SchwartzProfiles

/-! ### Sobolev four-jet norms on `ℝ^d` -/

section WholeSpaceNorms

variable {d : ℕ}

local notation "Rd" => EuclideanSpace ℝ (Fin d)

/-- `‖f‖²_{H^p(ℝ^d)} = ∫ (1 + |2πξ|²)^p |𝓕f(ξ)|² dξ`. -/
noncomputable def sobSqR (p : ℝ) (f : Rd → ℂ) : ℝ := ∫ ξ, (1 + qξ ξ) ^ p * ‖𝓕 f ξ‖ ^ 2

/-- `f ∈ L¹ ∩ H^p(ℝ^d)`: `f` is integrable (so `𝓕 f` is its classical Fourier transform) and
`(1 + |2πξ|²)^p |𝓕 f|²` is integrable. -/
def MemSobR (p : ℝ) (f : Rd → ℂ) : Prop :=
  Integrable f ∧ Integrable fun ξ => (1 + qξ ξ) ^ p * ‖𝓕 f ξ‖ ^ 2

/-- `U(t) ∈ X_r(ℝ^d)`. -/
def MemJetR (r : ℝ) (u : ℝ → Rd → ℝ) (t : ℝ) : Prop :=
  ∀ j : Fin 4, MemSobR (r + 3 - (j : ℕ)) (fun x => (dt j u t x : ℂ))

/-- `‖U(t)‖²_{X_r(ℝ^d)} = Σ_{j=0}^{3} ‖∂ₜʲu(t)‖²_{H^{r+3−j}}`. -/
noncomputable def jetSqR (r : ℝ) (u : ℝ → Rd → ℝ) (t : ℝ) : ℝ :=
  ∑ j : Fin 4, sobSqR (r + 3 - (j : ℕ)) (fun x => (dt j u t x : ℂ))

/-- `‖U(t)‖_{X_r(ℝ^d)}`. -/
noncomputable def jetNormR (r : ℝ) (u : ℝ → Rd → ℝ) (t : ℝ) : ℝ := Real.sqrt (jetSqR r u t)

theorem qξ_neg (ξ : Rd) : qξ (-ξ) = qξ ξ := by simp [qξ]

theorem qξ_nonneg (ξ : Rd) : 0 ≤ qξ ξ := by
  unfold qξ
  positivity

/-- Sobolev norm of `a Re 𝓕⁻H` when `H` and its reflection have disjoint supports:
`‖a Re 𝓕⁻H‖²_{H^p} = (a²/2) ∫ (1 + |2πξ|²)^p |H|²`. -/
theorem sobSqR_re_fourierInv (H : SchwartzMap Rd ℂ) (hc : HasCompactSupport ⇑H)
    (hdisj : ∀ ξ, H ξ = 0 ∨ H (-ξ) = 0) (a p : ℝ) :
    MemSobR p (fun x => ((a * (𝓕⁻ (⇑H) x).re : ℝ) : ℂ)) ∧
      sobSqR p (fun x => ((a * (𝓕⁻ (⇑H) x).re : ℝ) : ℂ)) =
        a ^ 2 / 2 * ∫ ξ, (1 + qξ ξ) ^ p * ‖H ξ‖ ^ 2 := by
  set F : Rd → ℝ := fun ξ => (1 + qξ ξ) ^ p * ‖H ξ‖ ^ 2 with hF
  have hw : Continuous fun ξ : Rd => (1 + qξ ξ) ^ p :=
    (continuous_const.add continuous_qξ).rpow_const fun ξ => Or.inl (by
      linarith [qξ_nonneg ξ])
  have hFc : Continuous F := hw.mul (H.continuous.norm.pow 2)
  have hFs : HasCompactSupport F := by
    have h2 : HasCompactSupport fun ξ => ‖H ξ‖ ^ 2 :=
      hc.norm.comp_left (g := fun x : ℝ => x ^ 2) (by norm_num)
    exact h2.mul_left
  have hFint : Integrable F := hFc.integrable_of_hasCompactSupport hFs
  have hFneg : Integrable fun ξ => F (-ξ) :=
    (hFc.comp continuous_neg).integrable_of_hasCompactSupport
      (hFs.comp_homeomorph (Homeomorph.neg Rd))
  have hpt : ∀ ξ, (1 + qξ ξ) ^ p * ‖𝓕 (fun x => ((a * (𝓕⁻ (⇑H) x).re : ℝ) : ℂ)) ξ‖ ^ 2 =
      a ^ 2 / 4 * (F ξ + F (-ξ)) := by
    intro ξ
    rw [fourier_re_fourierInv, hF]
    simp only [qξ_neg]
    rcases hdisj ξ with h | h
    · rw [h, zero_add, norm_mul, norm_conj]
      simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
        zero_add]
      rw [show ‖(a / 2 : ℂ)‖ = |a| / 2 by
        rw [norm_div, Complex.norm_real, Real.norm_eq_abs, Complex.norm_ofNat]]
      rw [mul_pow, div_pow, sq_abs]
      ring
    · rw [h, map_zero, add_zero, norm_mul]
      simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
        add_zero]
      rw [show ‖(a / 2 : ℂ)‖ = |a| / 2 by
        rw [norm_div, Complex.norm_real, Real.norm_eq_abs, Complex.norm_ofNat]]
      rw [mul_pow, div_pow, sq_abs]
      ring
  have hv : Continuous (𝓕⁻ (⇑H)) := by
    rw [← SchwartzMap.fourierTransformCLE_symm_apply ℂ H]
    exact ((SchwartzMap.fourierTransformCLE ℂ).symm H).continuous
  have hvint : Integrable (𝓕⁻ (⇑H)) := by
    rw [← SchwartzMap.fourierTransformCLE_symm_apply ℂ H]
    exact ((SchwartzMap.fourierTransformCLE ℂ).symm H).integrable
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · refine (hvint.norm.const_mul |a|).mono' ?_ (Eventually.of_forall fun x => ?_)
    · exact (Complex.continuous_ofReal.comp
        (continuous_const.mul (Complex.continuous_re.comp hv))).aestronglyMeasurable
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (abs_nonneg _)
  · simp_rw [hpt]
    exact (hFint.add hFneg).const_mul _
  · unfold sobSqR
    simp_rw [hpt]
    rw [integral_const_mul, integral_add hFint hFneg, integral_neg_eq_self F volume]
    ring

end WholeSpaceNorms

theorem packet_eq_fourierInv {d : ℕ} {K G T m2 : ℝ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {g : EuclideanSpace ℝ (Fin d) → ℂ} (hg0 : ∀ ξ ∉ Ω, g ξ = 0)
    (t : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    packet K G T m2 Ω g t x =
      𝓕⁻ (fun ξ => Complex.exp ((t : ℂ) * Sξ K G T m2 ξ) * g ξ) x := by
  rw [Real.fourierIntegralInv_eq', packet, setIntegral_eq_integral_of_forall_compl_eq_zero]
  · congr 1
    funext ξ
    rw [Complex.exp_add, smul_eq_mul]
    ring
  · intro ξ hξ
    rw [hg0 ξ hξ, mul_zero]

/-! ### The whole-space packet sequence -/

section WholeSpacePackets

variable {d : ℕ}

local notation "Rd" => EuclideanSpace ℝ (Fin d)

variable {K G T m2 : ℝ}

/-- The packet center `n e₁` (Fourier variable). -/
noncomputable def center (hd : 0 < d) (n : ℕ) : Rd :=
  (n : ℝ) • EuclideanSpace.single (⟨0, hd⟩ : Fin d) (1 : ℝ)

theorem norm_center (hd : 0 < d) (n : ℕ) : ‖center hd n‖ = n := by
  simp [center, norm_smul, EuclideanSpace.norm_single]

/-- The bump `φₙ`: smooth, `0 ≤ φₙ ≤ 1`, `φₙ = 1` on `B̄(ne₁, 1/4)`, support `B(ne₁, 1/2)`. -/
noncomputable def bump (hd : 0 < d) (n : ℕ) : ContDiffBump (center hd n) :=
  ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

/-- `φₙ` as a complex function. -/
noncomputable def gφ (hd : 0 < d) (n : ℕ) (ξ : Rd) : ℂ := ((bump hd n ξ : ℝ) : ℂ)

/-- The packet frequency set `Ωₙ = B̄(ne₁, 1/2)`. -/
def Ωn (hd : 0 < d) (n : ℕ) : Set Rd := Metric.closedBall (center hd n) (1 / 2)

theorem isCompact_Ωn (hd : 0 < d) (n : ℕ) : IsCompact (Ωn hd n) := isCompact_closedBall _ _

theorem continuous_gφ (hd : 0 < d) (n : ℕ) : Continuous (gφ hd n) :=
  Complex.continuous_ofReal.comp (bump hd n).continuous

theorem contDiff_gφ (hd : 0 < d) (n : ℕ) : ContDiff ℝ ∞ (gφ hd n) :=
  Complex.ofRealCLM.contDiff.comp ((bump hd n).contDiff (n := ⊤))

theorem mem_ball_of_gφ_ne (hd : 0 < d) (n : ℕ) {ξ : Rd} (h : gφ hd n ξ ≠ 0) :
    ξ ∈ Metric.ball (center hd n) (1 / 2) := by
  have : bump hd n ξ ≠ 0 := fun h' => h (by simp [gφ, h'])
  have hs := (bump hd n).support_eq
  have hm : ξ ∈ Function.support (bump hd n) := this
  rw [hs] at hm
  exact hm

theorem gφ_eq_zero_of_notMem (hd : 0 < d) (n : ℕ) {ξ : Rd} (h : ξ ∉ Ωn hd n) : gφ hd n ξ = 0 := by
  by_contra h'
  exact h (Metric.ball_subset_closedBall (mem_ball_of_gφ_ne hd n h'))

theorem tsupport_gφ (hd : 0 < d) (n : ℕ) : tsupport (gφ hd n) = Ωn hd n := by
  have : Function.support (gφ hd n) = Function.support (bump hd n) := by
    ext ξ
    simp [gφ]
  rw [tsupport, this, ← tsupport, (bump hd n).tsupport_eq]
  rfl

theorem hasCompactSupport_gφ (hd : 0 < d) (n : ℕ) : HasCompactSupport (gφ hd n) := by
  rw [HasCompactSupport, tsupport_gφ]
  exact isCompact_Ωn hd n

theorem norm_bounds_of_mem (hd : 0 < d) {n : ℕ} {ξ : Rd} (h : ξ ∈ Ωn hd n) :
    (n : ℝ) - 1 / 2 ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ n + 1 / 2 := by
  have h1 : ‖ξ - center hd n‖ ≤ 1 / 2 := by
    rw [← dist_eq_norm]
    exact h
  have h2 := norm_sub_norm_le ξ (center hd n)
  have h3 := norm_sub_norm_le (center hd n) ξ
  rw [norm_center] at h2 h3
  rw [norm_sub_rev] at h3
  constructor <;> linarith

/-- Reflected supports are disjoint. -/
theorem gφ_disj (hd : 0 < d) {n : ℕ} (hn : 1 ≤ n) (ξ : Rd) :
    gφ hd n ξ = 0 ∨ gφ hd n (-ξ) = 0 := by
  by_contra h
  push_neg at h
  have h1 := mem_ball_of_gφ_ne hd n h.1
  have h2 := mem_ball_of_gφ_ne hd n h.2
  rw [Metric.mem_ball, dist_eq_norm] at h1 h2
  have h3 : ‖(ξ - center hd n) - (-ξ - center hd n)‖ < 1 := by
    calc ‖(ξ - center hd n) - (-ξ - center hd n)‖ ≤ ‖ξ - center hd n‖ + ‖-ξ - center hd n‖ :=
          norm_sub_le _ _
      _ < 1 := by linarith
  have h4 : (ξ - center hd n) - (-ξ - center hd n) = (2 : ℝ) • ξ := by
    rw [two_smul]
    abel
  rw [h4, norm_smul, Real.norm_two] at h3
  have h5 : ‖center hd n‖ ≤ ‖ξ‖ + 1 / 2 := by
    have := norm_sub_norm_le (center hd n) ξ
    rw [norm_sub_rev] at this
    linarith
  rw [norm_center] at h5
  have : (1 : ℝ) ≤ n := by exact_mod_cast hn
  linarith

/-- The Fourier profile `H_{n,t,j}(ξ) = e^{tS(ξ)} S(ξ)^j φₙ(ξ)` of `∂ₜʲ` of the packet. -/
noncomputable def profile (K G T m2 : ℝ) (hd : 0 < d) (n : ℕ) (t : ℝ) (j : ℕ) (ξ : Rd) : ℂ :=
  Complex.exp ((t : ℂ) * Sξ K G T m2 ξ) * (Sξ K G T m2 ξ ^ j * gφ hd n ξ)

/-- `n` is admissible: on `Ωₙ`, `q(ξ) > q_R` and `2π|ξ| ≥ R`. -/
def Admissible (K G T m2 : ℝ) (hd : 0 < d) (R : ℝ) (n : ℕ) : Prop :=
  1 ≤ n ∧ ∀ ξ ∈ Ωn hd n, qR K G T m2 < qξ ξ ∧ R ≤ 2 * Real.pi * ‖ξ‖

theorem contDiff_profile (hK : 0 < K) (hB : 0 < 4 * K * T - G ^ 2) (hd : 0 < d) {R : ℝ} {n : ℕ}
    (hn : Admissible K G T m2 hd R n) (t : ℝ) (j : ℕ) :
    ContDiff ℝ ∞ (profile K G T m2 hd n t j) := by
  have h := contDiff_mul_of_tsupport (F := fun ξ => Complex.exp ((t : ℂ) * Sξ K G T m2 ξ) *
      Sξ K G T m2 ξ ^ j) (g := gφ hd n) (U := {ξ : Rd | qR K G T m2 < qξ ξ})
    (by rw [tsupport_gφ]; exact fun ξ hξ => (hn.2 ξ hξ).1) (contDiff_gφ hd n) (fun ξ hξ => by
      have hS := contDiffAt_Sξ (n := ∞) hK hB hξ
      exact (Complex.contDiff_exp.contDiffAt.comp ξ (contDiffAt_const.mul hS)).mul (hS.pow j))
  convert h using 2 with ξ
  unfold profile
  ring

theorem hasCompactSupport_profile (hd : 0 < d) (n : ℕ) (t : ℝ) (j : ℕ) :
    HasCompactSupport (profile K G T m2 hd n t j) := by
  have h := (hasCompactSupport_gφ hd n).mul_left (f := fun ξ =>
    Complex.exp ((t : ℂ) * Sξ K G T m2 ξ) * Sξ K G T m2 ξ ^ j)
  convert h using 1
  funext ξ
  simp only [profile, Pi.mul_apply]
  ring

theorem norm_profile_sq (hd : 0 < d) (n : ℕ) (t : ℝ) (j : ℕ) (ξ : Rd) :
    ‖profile K G T m2 hd n t j ξ‖ ^ 2 =
      Real.exp (2 * t * sigma K G T m2 (qξ ξ)) *
        (‖Sξ K G T m2 ξ‖ ^ (2 * j) * bump hd n ξ ^ 2) := by
  unfold profile gφ
  rw [norm_mul, norm_mul, norm_pow, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
  have : ((t : ℂ) * Sξ K G T m2 ξ).re = t * sigma K G T m2 (qξ ξ) := by
    simp [Sξ, sExp]
  rw [this, mul_pow, mul_pow, sq_abs, ← Real.exp_nat_mul, ← pow_mul]
  push_cast
  ring_nf

theorem profile_disj (hd : 0 < d) {n : ℕ} (hn : 1 ≤ n) (t : ℝ) (j : ℕ) (ξ : Rd) :
    profile K G T m2 hd n t j ξ = 0 ∨ profile K G T m2 hd n t j (-ξ) = 0 := by
  rcases gφ_disj hd hn ξ with h | h
  · left; simp [profile, h]
  · right; simp [profile, h]

/-- The derivative `∂ₜʲ` of the packet solution is `a Re 𝓕⁻ H_{n,t,j}`. -/
theorem dt_packetSol_eq (hd : 0 < d) (n : ℕ) (a t : ℝ) (j : ℕ) (x : Rd) :
    dt j (packetSol K G T m2 (Ωn hd n) (gφ hd n) a) t x =
      a * (𝓕⁻ (profile K G T m2 hd n t j) x).re := by
  rw [dt_packetSol (isCompact_Ωn hd n) (continuous_gφ hd n)]
  unfold packetSol
  congr 2
  rw [packet_eq_fourierInv]
  · rfl
  · intro ξ hξ
    rw [gφ_eq_zero_of_notMem hd n hξ, mul_zero]

end WholeSpacePackets

/-! ### Growth and loss estimates on the packet profiles -/

section PacketEstimates

variable {d : ℕ}

local notation "Rd" => EuclideanSpace ℝ (Fin d)

variable {K G T m2 : ℝ}

/-- `I_n(p, j, t) = ∫ (1 + |2πξ|²)^p |H_{n,t,j}(ξ)|² dξ`. -/
noncomputable def profInt (K G T m2 : ℝ) (hd : 0 < d) (n : ℕ) (p : ℝ) (j : ℕ) (t : ℝ) : ℝ :=
  ∫ ξ, (1 + qξ ξ) ^ p * ‖profile K G T m2 hd n t j ξ‖ ^ 2

theorem continuous_weight (p : ℝ) : Continuous fun ξ : Rd => (1 + qξ ξ) ^ p :=
  (continuous_const.add continuous_qξ).rpow_const fun ξ => Or.inl (by linarith [qξ_nonneg ξ])

theorem continuous_profile (hd : 0 < d) (n : ℕ) (t : ℝ) (j : ℕ) :
    Continuous (profile K G T m2 hd n t j) := by
  unfold profile
  have := continuous_Sξ (d := d) K G T m2
  have := continuous_gφ hd n
  fun_prop

theorem integrable_profInt (hd : 0 < d) (n : ℕ) (p : ℝ) (j : ℕ) (t : ℝ) :
    Integrable fun ξ : Rd => (1 + qξ ξ) ^ p * ‖profile K G T m2 hd n t j ξ‖ ^ 2 := by
  refine ((continuous_weight p).mul ((continuous_profile hd n t j).norm.pow 2))
    |>.integrable_of_hasCompactSupport ?_
  have h2 : HasCompactSupport fun ξ => ‖profile K G T m2 hd n t j ξ‖ ^ 2 :=
    (hasCompactSupport_profile hd n t j).norm.comp_left (g := fun x : ℝ => x ^ 2) (by norm_num)
  exact h2.mul_left

theorem profInt_nonneg (hd : 0 < d) (n : ℕ) (p : ℝ) (j : ℕ) (t : ℝ) :
    0 ≤ profInt K G T m2 hd n p j t :=
  integral_nonneg fun ξ => mul_nonneg (Real.rpow_nonneg (by linarith [qξ_nonneg ξ]) _)
    (sq_nonneg _)

theorem qξ_eq_sq (ξ : Rd) : qξ ξ = (2 * Real.pi * ‖ξ‖) ^ 2 := by
  unfold qξ
  ring

/-- Growth: `I_n(p,j,t₀) ≥ e^{2t₀ c_* 2π(n − 1/2)} I_n(p,j,0)`. -/
theorem profInt_growth (hd : 0 < d) {n : ℕ} {cs R : ℝ} (hcs : 0 ≤ cs)
    (hlow : ∀ ρ ≥ R, cs * ρ ≤ sigma K G T m2 (ρ ^ 2))
    (hn : Admissible K G T m2 hd R n) (p : ℝ) (j : ℕ) {t₀ : ℝ} (ht₀ : 0 < t₀) :
    Real.exp (2 * t₀ * (cs * (2 * Real.pi * ((n : ℝ) - 1 / 2)))) *
        profInt K G T m2 hd n p j 0 ≤ profInt K G T m2 hd n p j t₀ := by
  unfold profInt
  rw [← integral_const_mul]
  refine integral_mono ((integrable_profInt hd n p j 0).const_mul _)
    (integrable_profInt hd n p j t₀) fun ξ => ?_
  simp only [norm_profile_sq, mul_zero, zero_mul, Real.exp_zero, one_mul]
  by_cases hb : bump hd n ξ = 0
  · simp [hb]
  · have hξ : ξ ∈ Ωn hd n :=
      Metric.ball_subset_closedBall (mem_ball_of_gφ_ne hd n (by simp [gφ, hb]))
    have hR := (hn.2 ξ hξ).2
    have hσ := hlow _ hR
    rw [← qξ_eq_sq] at hσ
    have hnorm := (norm_bounds_of_mem hd hξ).1
    have h1 : cs * (2 * Real.pi * ((n : ℝ) - 1 / 2)) ≤ sigma K G T m2 (qξ ξ) := by
      have : cs * (2 * Real.pi * ((n : ℝ) - 1 / 2)) ≤ cs * (2 * Real.pi * ‖ξ‖) := by
        apply mul_le_mul_of_nonneg_left _ hcs
        nlinarith [Real.pi_pos]
      linarith
    have h2 : Real.exp (2 * t₀ * (cs * (2 * Real.pi * ((n : ℝ) - 1 / 2)))) ≤
        Real.exp (2 * t₀ * sigma K G T m2 (qξ ξ)) :=
      Real.exp_le_exp.2 (by nlinarith)
    have h3 : 0 ≤ (1 + qξ ξ) ^ p * (‖Sξ K G T m2 ξ‖ ^ (2 * j) * bump hd n ξ ^ 2) :=
      mul_nonneg (Real.rpow_nonneg (by linarith [qξ_nonneg ξ]) _) (by positivity)
    calc Real.exp (2 * t₀ * (cs * (2 * Real.pi * ((n : ℝ) - 1 / 2)))) *
          ((1 + qξ ξ) ^ p * (‖Sξ K G T m2 ξ‖ ^ (2 * j) * bump hd n ξ ^ 2))
        ≤ Real.exp (2 * t₀ * sigma K G T m2 (qξ ξ)) *
          ((1 + qξ ξ) ^ p * (‖Sξ K G T m2 ξ‖ ^ (2 * j) * bump hd n ξ ^ 2)) :=
          mul_le_mul_of_nonneg_right h2 h3
      _ = (1 + qξ ξ) ^ p * (Real.exp (2 * t₀ * sigma K G T m2 (qξ ξ)) *
          (‖Sξ K G T m2 ξ‖ ^ (2 * j) * bump hd n ξ ^ 2)) := by ring

/-- Loss: `I_n(p+ℓ,j,0) ≤ (1 + (2π(n+1/2))²)^ℓ I_n(p,j,0)`. -/
theorem profInt_loss (hd : 0 < d) (n : ℕ) (p : ℝ) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (j : ℕ) :
    profInt K G T m2 hd n (p + ℓ) j 0 ≤
      (1 + (2 * Real.pi * ((n : ℝ) + 1 / 2)) ^ 2) ^ ℓ * profInt K G T m2 hd n p j 0 := by
  unfold profInt
  rw [← integral_const_mul]
  refine integral_mono (integrable_profInt hd n (p + ℓ) j 0)
    ((integrable_profInt hd n p j 0).const_mul _) fun ξ => ?_
  have hq : 0 < 1 + qξ ξ := by linarith [qξ_nonneg ξ]
  simp only
  rw [Real.rpow_add hq]
  by_cases hb : profile K G T m2 hd n 0 j ξ = 0
  · simp [hb]
  · have hg : gφ hd n ξ ≠ 0 := fun h => hb (by simp [profile, h])
    have hξ : ξ ∈ Ωn hd n := Metric.ball_subset_closedBall (mem_ball_of_gφ_ne hd n hg)
    have hnorm := (norm_bounds_of_mem hd hξ).2
    have h1 : 1 + qξ ξ ≤ 1 + (2 * Real.pi * ((n : ℝ) + 1 / 2)) ^ 2 := by
      rw [qξ_eq_sq]
      have : 2 * Real.pi * ‖ξ‖ ≤ 2 * Real.pi * ((n : ℝ) + 1 / 2) := by
        nlinarith [Real.pi_pos]
      have h0 : 0 ≤ 2 * Real.pi * ‖ξ‖ := by positivity
      linarith [pow_le_pow_left₀ h0 this 2]
    have h2 := Real.rpow_le_rpow hq.le h1 hℓ
    have h3 : 0 ≤ (1 + qξ ξ) ^ p * ‖profile K G T m2 hd n 0 j ξ‖ ^ 2 :=
      mul_nonneg (Real.rpow_nonneg hq.le _) (sq_nonneg _)
    nlinarith

/-- Positivity of the lowest profile integral. -/
theorem profInt_pos (hd : 0 < d) (n : ℕ) (p : ℝ) : 0 < profInt K G T m2 hd n p 0 0 := by
  unfold profInt
  refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := center hd n)
    ((continuous_weight p).mul ((continuous_profile hd n 0 0).norm.pow 2)) ?_ ?_ ?_
  · have h2 : HasCompactSupport fun ξ => ‖profile K G T m2 hd n 0 0 ξ‖ ^ 2 :=
      (hasCompactSupport_profile hd n 0 0).norm.comp_left (g := fun x : ℝ => x ^ 2)
        (by norm_num)
    exact h2.mul_left
  · intro ξ
    exact mul_nonneg (Real.rpow_nonneg (by linarith [qξ_nonneg ξ]) _) (sq_nonneg _)
  · have hb : bump hd n (center hd n) = 1 :=
      (bump hd n).one_of_mem_closedBall (Metric.mem_closedBall_self (by norm_num [bump]))
    have hq : 0 < 1 + qξ (center hd n) := by linarith [qξ_nonneg (center hd n)]
    simp only [profile, gφ, hb, Complex.ofReal_zero, zero_mul, Complex.exp_zero, pow_zero,
      Complex.ofReal_one, norm_one, one_pow, mul_one]
    exact (Real.rpow_pos_of_pos hq _).ne'

end PacketEstimates

/-! ### The whole-space theorem -/

section WholeSpaceTheorem

variable {d : ℕ}

local notation "Rd" => EuclideanSpace ℝ (Fin d)

variable {K G T m2 : ℝ}

/-- Exact four-jet norms of the packet solutions:
`‖U(t)‖²_{X_r} = (a²/2) Σⱼ I_n(r+3−j, j, t)`. -/
theorem jetSqR_packetSol (hK : 0 < K) (hB : 0 < 4 * K * T - G ^ 2) (hd : 0 < d) {R : ℝ}
    {n : ℕ} (hn : Admissible K G T m2 hd R n) (a t r : ℝ) :
    MemJetR r (packetSol K G T m2 (Ωn hd n) (gφ hd n) a) t ∧
      jetSqR r (packetSol K G T m2 (Ωn hd n) (gφ hd n) a) t =
        a ^ 2 / 2 * ∑ j : Fin 4, profInt K G T m2 hd n (r + 3 - (j : ℕ)) j t := by
  have key : ∀ (j : ℕ) (p : ℝ),
      MemSobR p (fun x => (dt j (packetSol K G T m2 (Ωn hd n) (gφ hd n) a) t x : ℂ)) ∧
      sobSqR p (fun x => (dt j (packetSol K G T m2 (Ωn hd n) (gφ hd n) a) t x : ℂ)) =
        a ^ 2 / 2 * profInt K G T m2 hd n p j t := by
    intro j p
    set H := schwartzOfCompact (profile K G T m2 hd n t j) (contDiff_profile hK hB hd hn t j)
      (hasCompactSupport_profile hd n t j)
    have hfun : (fun x => (dt j (packetSol K G T m2 (Ωn hd n) (gφ hd n) a) t x : ℂ)) =
        fun x => ((a * (𝓕⁻ (⇑H) x).re : ℝ) : ℂ) := by
      funext x
      rw [dt_packetSol_eq]
      rfl
    rw [hfun]
    exact sobSqR_re_fourierInv H (hasCompactSupport_profile hd n t j) (profile_disj hd hn.1 t j)
      a p
  refine ⟨fun j => (key j _).1, ?_⟩
  unfold jetSqR
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => (key j _).2

theorem tendsto_rpow_mul_exp_shift (ℓ b C : ℝ) (hb : 0 < b) (N₀ : ℕ) :
    Tendsto (fun n : ℕ => C * (((n + N₀ : ℕ) : ℝ) ^ ℓ * Real.exp (-b * ((n + N₀ : ℕ) : ℝ))))
      atTop (𝓝 0) := by
  have hν : Tendsto (fun n : ℕ => ((n + N₀ : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat N₀)
  have := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ℓ b hb).comp hν).const_mul C
  simpa using this

/-- **Theorem (unbounded positive-time Sobolev evolution on `ℝ^d`).**  For the sector with
`K > 0`, `4KT − G² > 0`, every `r`, every `ℓ ≥ 0` and every `t₀ > 0`, there are smooth exact
real Fourier-packet solutions with `Uₙ(t) ∈ X_r(ℝ^d) ∩ X_{r+ℓ}(ℝ^d)`,
`‖Uₙ(0)‖_{X_{r+ℓ}} → 0` and `‖Uₙ(t₀)‖_{X_r} = 1`. -/
theorem whole_unbounded (hK : 0 < K) (hB : 0 < 4 * K * T - G ^ 2) (hd : 0 < d)
    (r ℓ t₀ : ℝ) (hℓ : 0 ≤ ℓ) (ht₀ : 0 < t₀) :
    ∃ u : ℕ → ℝ → Rd → ℝ,
      (∀ n, IsSmoothSolution K G T m2 (u n)) ∧
      (∀ n t, MemJetR r (u n) t ∧ MemJetR (r + ℓ) (u n) t) ∧
      Tendsto (fun n => jetNormR (r + ℓ) (u n) 0) atTop (𝓝 0) ∧
      ∀ n, jetNormR r (u n) t₀ = 1 := by
  have hc := cUV_pos (G := G) hK hB
  set cs := cUV K G T / 2 with hcs
  have hcs0 : 0 < cs := half_pos hc
  obtain ⟨R, hR, hlow⟩ := sigma_lower (m2 := m2) hK hB (half_lt_self hc)
  set M₀ := max (max R (qR K G T m2 + 1)) 1 with hM₀
  have hM₀1 : 1 ≤ M₀ := le_max_right _ _
  have hπ : 0 < 2 * Real.pi := by positivity
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge (M₀ / (2 * Real.pi) + 1)
  set ν : ℕ → ℕ := fun n => n + N₀ with hνdef
  have hνbig : ∀ n, M₀ / (2 * Real.pi) + 1 ≤ (ν n : ℝ) := fun n => by
    simp only [hνdef]
    push_cast
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hν1 : ∀ n, (1 : ℝ) ≤ ν n := fun n => by
    have : 0 ≤ M₀ / (2 * Real.pi) := div_nonneg (by linarith) hπ.le
    linarith [hνbig n]
  have hadm : ∀ n, Admissible K G T m2 hd R (ν n) := by
    intro n
    refine ⟨by exact_mod_cast hν1 n, fun ξ hξ => ?_⟩
    have hb := (norm_bounds_of_mem hd hξ).1
    have h2 : M₀ ≤ 2 * Real.pi * ‖ξ‖ := by
      have h3 : M₀ / (2 * Real.pi) ≤ ‖ξ‖ := by linarith [hνbig n]
      rw [div_le_iff₀ hπ] at h3
      linarith
    constructor
    · rw [qξ_eq_sq]
      have h4 : qR K G T m2 + 1 ≤ M₀ := le_trans (le_max_right _ _) (le_max_left _ _)
      nlinarith
    · exact le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) h2
  set J : ℕ → ℝ → ℝ := fun n t =>
    (∑ j : Fin 4, profInt K G T m2 hd (ν n) (r + 3 - (j : ℕ)) j t) / 2 with hJ
  set γ : ℕ → ℝ := fun n => cs * (2 * Real.pi * ((ν n : ℝ) - 1 / 2)) with hγ
  have hJ0pos : ∀ n, 0 < J n 0 := by
    intro n
    simp only [hJ]
    apply div_pos _ two_pos
    rw [Fin.sum_univ_succ]
    refine add_pos_of_pos_of_nonneg ?_ (Finset.sum_nonneg fun j _ => profInt_nonneg _ _ _ _ _)
    exact profInt_pos hd _ _
  have hJgrowth : ∀ n, Real.exp (2 * t₀ * γ n) * J n 0 ≤ J n t₀ := by
    intro n
    simp only [hJ, hγ]
    rw [mul_div_assoc', Finset.mul_sum]
    apply div_le_div_of_nonneg_right _ two_pos.le
    exact Finset.sum_le_sum fun j _ => profInt_growth hd hcs0.le hlow (hadm n) _ _ ht₀
  have hJt₀pos : ∀ n, 0 < J n t₀ := fun n =>
    lt_of_lt_of_le (mul_pos (Real.exp_pos _) (hJ0pos n)) (hJgrowth n)
  set a : ℕ → ℝ := fun n => 1 / Real.sqrt (J n t₀) with ha
  have ha2 : ∀ n, a n ^ 2 = 1 / J n t₀ := fun n => by
    simp only [ha]
    rw [div_pow, one_pow, Real.sq_sqrt (hJt₀pos n).le]
  have hjet : ∀ n t r', jetSqR r' (packetSol K G T m2 (Ωn hd (ν n)) (gφ hd (ν n)) (a n)) t =
      a n ^ 2 * ((∑ j : Fin 4, profInt K G T m2 hd (ν n) (r' + 3 - (j : ℕ)) j t) / 2) := by
    intro n t r'
    rw [(jetSqR_packetSol hK hB hd (hadm n) (a n) t r').2]
    ring
  refine ⟨fun n => packetSol K G T m2 (Ωn hd (ν n)) (gφ hd (ν n)) (a n), fun n => ?_,
    fun n t => ⟨(jetSqR_packetSol hK hB hd (hadm n) (a n) t r).1,
      (jetSqR_packetSol hK hB hd (hadm n) (a n) t (r + ℓ)).1⟩, ?_, fun n => ?_⟩
  · exact packetSol_isSmoothSolution hK (isCompact_Ωn hd (ν n))
      (fun ξ hξ => (radic_pos hB ((hadm n).2 ξ hξ).1.le).le) (continuous_gφ hd (ν n)) (a n)
  · -- the initial `X_{r+ℓ}` norms tend to zero
    set Q : ℕ → ℝ := fun n => 1 + (2 * Real.pi * ((ν n : ℝ) + 1 / 2)) ^ 2 with hQ
    have hQpos : ∀ n, 0 < Q n := fun n => by simp only [hQ]; positivity
    have hsq : ∀ n, jetSqR (r + ℓ) (packetSol K G T m2 (Ωn hd (ν n)) (gφ hd (ν n)) (a n)) 0 ≤
        Q n ^ ℓ * Real.exp (-(2 * t₀ * γ n)) := by
      intro n
      rw [hjet, ha2]
      have hloss : (∑ j : Fin 4, profInt K G T m2 hd (ν n) (r + ℓ + 3 - (j : ℕ)) j 0) / 2 ≤
          Q n ^ ℓ * J n 0 := by
        simp only [hJ, hQ]
        rw [mul_div_assoc', Finset.mul_sum]
        apply div_le_div_of_nonneg_right _ two_pos.le
        refine Finset.sum_le_sum fun j _ => ?_
        rw [show r + ℓ + 3 - ((j : ℕ) : ℝ) = (r + 3 - (j : ℕ)) + ℓ by ring]
        exact profInt_loss hd _ _ hℓ _
      have hJ0 : J n 0 ≤ Real.exp (-(2 * t₀ * γ n)) * J n t₀ := by
        rw [Real.exp_neg, inv_mul_eq_div, le_div_iff₀ (Real.exp_pos _), mul_comm]
        exact hJgrowth n
      calc 1 / J n t₀ * ((∑ j : Fin 4, profInt K G T m2 hd (ν n) (r + ℓ + 3 - (j : ℕ)) j 0) / 2)
          ≤ 1 / J n t₀ * (Q n ^ ℓ * J n 0) :=
            mul_le_mul_of_nonneg_left hloss (by have := hJt₀pos n; positivity)
        _ ≤ 1 / J n t₀ * (Q n ^ ℓ * (Real.exp (-(2 * t₀ * γ n)) * J n t₀)) := by
            have := hJt₀pos n
            have := hQpos n
            gcongr
        _ = Q n ^ ℓ * Real.exp (-(2 * t₀ * γ n)) := by
            field_simp [(hJt₀pos n).ne']
    have hnorm : ∀ n, jetNormR (r + ℓ) (packetSol K G T m2 (Ωn hd (ν n)) (gφ hd (ν n)) (a n)) 0 ≤
        Q n ^ (ℓ / 2) * Real.exp (-(t₀ * γ n)) := by
      intro n
      rw [jetNormR]
      calc Real.sqrt (jetSqR (r + ℓ) (packetSol K G T m2 (Ωn hd (ν n)) (gφ hd (ν n)) (a n)) 0)
          ≤ Real.sqrt (Q n ^ ℓ * Real.exp (-(2 * t₀ * γ n))) := Real.sqrt_le_sqrt (hsq n)
        _ = Q n ^ (ℓ / 2) * Real.exp (-(t₀ * γ n)) := by
            rw [show Q n ^ ℓ * Real.exp (-(2 * t₀ * γ n)) =
                (Q n ^ (ℓ / 2) * Real.exp (-(t₀ * γ n))) ^ 2 by
              rw [mul_pow, ← Real.rpow_natCast (Q n ^ (ℓ / 2)), ← Real.rpow_mul (hQpos n).le,
                ← Real.exp_nat_mul]
              congr 2
              · push_cast; ring
              · push_cast; ring]
            exact Real.sqrt_sq (by have := hQpos n; positivity)
    set C : ℝ := (1 + 16 * Real.pi ^ 2) ^ (ℓ / 2) * Real.exp (t₀ * cs * Real.pi) with hC
    set b : ℝ := 2 * Real.pi * t₀ * cs with hb
    have hbpos : 0 < b := by positivity
    have hbound : ∀ n, Q n ^ (ℓ / 2) * Real.exp (-(t₀ * γ n)) ≤
        C * (((n + N₀ : ℕ) : ℝ) ^ ℓ * Real.exp (-b * ((n + N₀ : ℕ) : ℝ))) := by
      intro n
      have hν := hν1 n
      have hνeq : ((n + N₀ : ℕ) : ℝ) = (ν n : ℝ) := rfl
      rw [hνeq]
      have h1 : Q n ≤ (1 + 16 * Real.pi ^ 2) * (ν n : ℝ) ^ 2 := by
        simp only [hQ]
        have h2 : 2 * Real.pi * ((ν n : ℝ) + 1 / 2) ≤ 4 * Real.pi * (ν n : ℝ) := by
          nlinarith [Real.pi_pos]
        have h3 : 0 ≤ 2 * Real.pi * ((ν n : ℝ) + 1 / 2) := by positivity
        have h4 := pow_le_pow_left₀ h3 h2 2
        nlinarith [Real.pi_pos]
      have h5 : Q n ^ (ℓ / 2) ≤ (1 + 16 * Real.pi ^ 2) ^ (ℓ / 2) * (ν n : ℝ) ^ ℓ := by
        calc Q n ^ (ℓ / 2) ≤ ((1 + 16 * Real.pi ^ 2) * (ν n : ℝ) ^ 2) ^ (ℓ / 2) :=
              Real.rpow_le_rpow (hQpos n).le h1 (by linarith)
          _ = (1 + 16 * Real.pi ^ 2) ^ (ℓ / 2) * (ν n : ℝ) ^ ℓ := by
              rw [Real.mul_rpow (by positivity) (by positivity),
                ← Real.rpow_natCast ((ν n : ℝ)) 2, ← Real.rpow_mul (by positivity)]
              congr 2
              push_cast
              ring
      have h6 : Real.exp (-(t₀ * γ n)) = Real.exp (t₀ * cs * Real.pi) *
          Real.exp (-b * (ν n : ℝ)) := by
        rw [← Real.exp_add]
        congr 1
        simp only [hγ, hb]
        ring
      rw [h6]
      calc Q n ^ (ℓ / 2) * (Real.exp (t₀ * cs * Real.pi) * Real.exp (-b * (ν n : ℝ)))
          ≤ ((1 + 16 * Real.pi ^ 2) ^ (ℓ / 2) * (ν n : ℝ) ^ ℓ) *
              (Real.exp (t₀ * cs * Real.pi) * Real.exp (-b * (ν n : ℝ))) :=
            mul_le_mul_of_nonneg_right h5 (by positivity)
        _ = C * ((ν n : ℝ) ^ ℓ * Real.exp (-b * (ν n : ℝ))) := by
            simp only [hC]
            ring
    exact squeeze_zero (fun n => Real.sqrt_nonneg _) (fun n => (hnorm n).trans (hbound n))
      (tendsto_rpow_mul_exp_shift ℓ b C hbpos N₀)
  · rw [jetNormR, hjet, ha2]
    simp only [hJ]
    rw [one_div_mul_cancel (hJt₀pos n).ne', Real.sqrt_one]

/-- **No bounded extension (`ℝ^d`).** -/
theorem whole_no_bounded_estimate (hK : 0 < K) (hB : 0 < 4 * K * T - G ^ 2) (hd : 0 < d)
    (r ℓ t₀ : ℝ) (hℓ : 0 ≤ ℓ) (ht₀ : 0 < t₀) :
    ∃ u : ℕ → ℝ → Rd → ℝ,
      (∀ n, IsSmoothSolution K G T m2 (u n)) ∧
      (∀ n t, MemJetR r (u n) t ∧ MemJetR (r + ℓ) (u n) t) ∧
      ¬∃ C : ℝ, ∀ n, jetNormR r (u n) t₀ ≤ C * jetNormR (r + ℓ) (u n) 0 := by
  obtain ⟨u, hsol, hmem, hlim, hone⟩ := whole_unbounded (m2 := m2) hK hB hd r ℓ t₀ hℓ ht₀
  refine ⟨u, hsol, hmem, fun ⟨C, hC⟩ => ?_⟩
  have h := (hlim.const_mul C).eventually (gt_mem_nhds (show C * 0 < 1 by simp))
  obtain ⟨n, hn⟩ := h.exists
  have := hC n
  rw [hone n] at this
  linarith

end WholeSpaceTheorem

/-! ### The Hilbert-space realization of `X_r(ℝ^d)` and bounded operators -/

section WholeSpaceOperator

variable {d : ℕ}

local notation "Rd" => EuclideanSpace ℝ (Fin d)

variable {K G T m2 : ℝ}

/-- `L²(ℝ^d)⁴` with the Euclidean sum norm, which realizes `X_r(ℝ^d)` isometrically for every
`r` through `U ↦ ((1 + |2πξ|²)^{(r+3−j)/2} 𝓕(∂ₜʲu)(ξ))_{j}`. -/
abbrev JetSpaceR (d : ℕ) :=
  PiLp 2 (fun _ : Fin 4 => Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))))

/-- `(1 + |2πξ|²)^{p/2} 𝓕 f(ξ)`. -/
noncomputable def weighted (p : ℝ) (f : Rd → ℂ) (ξ : Rd) : ℂ :=
  (((1 + qξ ξ) ^ (p / 2) : ℝ) : ℂ) * 𝓕 f ξ

theorem norm_weighted_sq (p : ℝ) (f : Rd → ℂ) (ξ : Rd) :
    ‖weighted p f ξ‖ ^ 2 = (1 + qξ ξ) ^ p * ‖𝓕 f ξ‖ ^ 2 := by
  have hq : 0 < 1 + qξ ξ := by linarith [qξ_nonneg ξ]
  rw [weighted, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    ← Real.rpow_natCast, ← Real.rpow_mul hq.le]
  norm_num

theorem memLp_weighted {p : ℝ} {f : Rd → ℂ} (h : MemSobR p f) : MemLp (weighted p f) 2 := by
  have hcont : Continuous (𝓕 f) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (by simpa only [innerₗ_apply] using continuous_inner) h.1
  have hmeas : AEStronglyMeasurable (weighted p f) volume :=
    ((Complex.continuous_ofReal.comp ((continuous_weight (p / 2)))).mul hcont).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  simp_rw [norm_weighted_sq]
  exact h.2

theorem norm_toLp_weighted {p : ℝ} {f : Rd → ℂ} (h : MemSobR p f) :
    ‖(memLp_weighted h).toLp (weighted p f)‖ ^ 2 = sobSqR p f := by
  rw [Lp.norm_toLp, (memLp_weighted h).eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat]
  have hnn : 0 ≤ ∫ ξ, ‖weighted p f ξ‖ ^ (2 : ℝ) :=
    integral_nonneg fun ξ => by positivity
  rw [ENNReal.toReal_ofReal (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hnn]
  norm_num
  unfold sobSqR
  congr 1
  funext ξ
  rw [norm_weighted_sq]

open Classical in
/-- The four-jet `U(t)` as an element of `X_r(ℝ^d) ≅ L²(ℝ^d)⁴` (zero if `U(t) ∉ X_r`). -/
noncomputable def toJetR (r : ℝ) (u : ℝ → Rd → ℝ) (t : ℝ) : JetSpaceR d :=
  WithLp.toLp 2 fun j : Fin 4 =>
    if h : MemSobR (r + 3 - (j : ℕ)) (fun x => (dt j u t x : ℂ)) then
      (memLp_weighted h).toLp _
    else 0

/-- `‖U(t)‖_{L²⁴} = ‖U(t)‖_{X_r(ℝ^d)}` for `U(t) ∈ X_r(ℝ^d)`. -/
theorem norm_toJetR {r : ℝ} {u : ℝ → Rd → ℝ} {t : ℝ} (h : MemJetR r u t) :
    ‖toJetR r u t‖ = jetNormR r u t := by
  rw [PiLp.norm_eq_of_L2, jetNormR, jetSqR]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [toJetR, PiLp.toLp_apply, dif_pos (h j), norm_toLp_weighted (h j)]

/-- **No bounded extension (`ℝ^d`), operator form.** -/
theorem whole_no_bounded_operator (hK : 0 < K) (hB : 0 < 4 * K * T - G ^ 2) (hd : 0 < d)
    (r ℓ t₀ : ℝ) (hℓ : 0 ≤ ℓ) (ht₀ : 0 < t₀) :
    ∃ u : ℕ → ℝ → Rd → ℝ,
      (∀ n, IsSmoothSolution K G T m2 (u n)) ∧
      (∀ n t, MemJetR r (u n) t ∧ MemJetR (r + ℓ) (u n) t) ∧
      Tendsto (fun n => ‖toJetR (r + ℓ) (u n) 0‖) atTop (𝓝 0) ∧
      (∀ n, ‖toJetR r (u n) t₀‖ = 1) ∧
      ∀ (S : JetSpaceR d → JetSpaceR d) (C : ℝ), (∀ V, ‖S V‖ ≤ C * ‖V‖) →
        ¬∀ n, S (toJetR (r + ℓ) (u n) 0) = toJetR r (u n) t₀ := by
  obtain ⟨u, hsol, hmem, hlim, hone⟩ := whole_unbounded (m2 := m2) hK hB hd r ℓ t₀ hℓ ht₀
  have hlim' : Tendsto (fun n => ‖toJetR (r + ℓ) (u n) 0‖) atTop (𝓝 0) := by
    simpa only [norm_toJetR (hmem _ _).2] using hlim
  have hone' : ∀ n, ‖toJetR r (u n) t₀‖ = 1 := fun n => by
    rw [norm_toJetR (hmem n t₀).1, hone n]
  refine ⟨u, hsol, hmem, hlim', hone', fun S C hS hev => ?_⟩
  have h := (hlim'.const_mul C).eventually (gt_mem_nhds (show C * 0 < 1 by simp))
  obtain ⟨n, hn⟩ := h.exists
  have := hS (toJetR (r + ℓ) (u n) 0)
  rw [hev n, hone' n] at this
  linarith

/-- In particular no bounded linear operator `S(t₀) : X_{r+ℓ}(ℝ^d) → X_r(ℝ^d)` extends the
classical evolution. -/
theorem whole_no_bounded_linear_extension (hK : 0 < K) (hB : 0 < 4 * K * T - G ^ 2)
    (hd : 0 < d) (r ℓ t₀ : ℝ) (hℓ : 0 ≤ ℓ) (ht₀ : 0 < t₀) :
    ∃ u : ℕ → ℝ → Rd → ℝ, (∀ n, IsSmoothSolution K G T m2 (u n)) ∧
      ∀ S : JetSpaceR d →L[ℂ] JetSpaceR d,
        ¬∀ n, S (toJetR (r + ℓ) (u n) 0) = toJetR r (u n) t₀ := by
  obtain ⟨u, hsol, -, -, -, hS⟩ := whole_no_bounded_operator (m2 := m2) hK hB hd r ℓ t₀ hℓ ht₀
  exact ⟨u, hsol, fun S => hS S ‖S‖ S.le_opNorm⟩

/-- **Theorem 1 (`M = ℝ^d`)** for `∂ₜ⁴u + (1 − 2Δ)∂ₜ²u − Δu + 2Δ²u = 0`. -/
theorem wave_whole_unbounded (hd : 0 < d) (r ℓ t₀ : ℝ) (hℓ : 0 ≤ ℓ) (ht₀ : 0 < t₀) :
    ∃ u : ℕ → ℝ → Rd → ℝ,
      (∀ n, ContDiff ℝ ∞ (fun p : ℝ × Rd => u n p.1 p.2) ∧ ∀ t x, waveOp (u n) t x = 0) ∧
      (∀ n t, MemJetR r (u n) t ∧ MemJetR (r + ℓ) (u n) t) ∧
      Tendsto (fun n => jetNormR (r + ℓ) (u n) 0) atTop (𝓝 0) ∧ (∀ n, jetNormR r (u n) t₀ = 1) ∧
      ∀ (S : JetSpaceR d → JetSpaceR d) (C : ℝ), (∀ V, ‖S V‖ ≤ C * ‖V‖) →
        ¬∀ n, S (toJetR (r + ℓ) (u n) 0) = toJetR r (u n) t₀ := by
  have hK : (0 : ℝ) < 1 := one_pos
  have hB : (0 : ℝ) < 4 * 1 * 1 - 0 ^ 2 := by norm_num
  obtain ⟨u, hsol, hmem, hlim, hone⟩ := whole_unbounded (m2 := 0) hK hB hd r ℓ t₀ hℓ ht₀
  refine ⟨u, fun n => (isSmoothSolution_wave_iff _).1 (hsol n), hmem, hlim, hone,
    fun S C hSC hev => ?_⟩
  have hlim'' : Tendsto (fun n => ‖toJetR (r + ℓ) (u n) 0‖) atTop (𝓝 0) := by
    simpa only [norm_toJetR (hmem _ _).2] using hlim
  have h := (hlim''.const_mul C).eventually (gt_mem_nhds (show C * 0 < 1 by simp))
  obtain ⟨n, hn⟩ := h.exists
  have := hSC (toJetR (r + ℓ) (u n) 0)
  rw [hev n, norm_toJetR (hmem n t₀).1, hone n] at this
  linarith

end WholeSpaceOperator

end UVIllPosed

end ReyesMath
