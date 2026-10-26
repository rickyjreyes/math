import Mathlib

/-!
# Continuous spectral–phase identity and the 4/5 counterexample (F03)

Complete formalization of the main theorem, the remark on the equality case,
both propositions and the exact gap accounting of
`papers/spectral-rms-averaged-curvature/main.tex`.

* `Eigenmode`: a `C²`, `L`-periodic, nowhere-vanishing eigenfunction
  `−χ'' = λχ` of the free periodic operator with a `C¹` polar form
  `χ = R e^{iφ}`, `R > 0`.  `exists_polar_lift` proves that every nowhere-vanishing
  `C¹` function admits such a polar form, so the hypotheses are never vacuous.
* `sharp_spectral_phase_decomposition`: the exact continuous identity
  `λ − ⟨σ⟩² = ∫|R'|²/∫R² + Var_w(σ) ≥ 0` (proved by periodic integration by
  parts), the equality characterization (`R` and `σ` constant), and `√λ ≥ |⟨σ⟩|`.
  `Eigenmode.equality_form` gives the equality-case form `χ = R₀ e^{i(σ₀ s + φ₀)}`
  with `σ₀ L ∈ 2πℤ`; `root_identity` is the spectral-root form.
* `ellipseMode_mean`, `ellipseMode_mean_ne`, `four_fifths`: for
  `χ_a = cos s + i a sin s`, `λ = 1` and `⟨σ⟩ = 2a/(1+a²)` for every polar form.
* `gap_accounting`: at `a = 1/2`, `⟨σ²⟩ = 4/5`, `Var = 4/25`, amplitude energy `1/5`.
* `ellipseCurve_contDiff`, `ellipseCurve_unit_speed`, `ellipseCurve_closed`,
  `ellipseCurve_length`, `ellipseCurve_curvature`, `planar_torsion_numerator`,
  `geometric_lock_four_fifths`: the smooth closed unit-speed planar curve whose
  curvature equals `σ_a`, with `⟨κ⟩ = 4/5` while `√λ = 1`.
-/

open MeasureTheory Set Filter Topology Complex

namespace ReyesMath

namespace SpectralPhase

/-- Standing hypotheses: an `L`-periodic, `C²`, nowhere-vanishing eigenfunction
`−χ'' = λχ` of the free periodic operator, with a `C¹` polar form `χ = R e^{iφ}`,
`R > 0`, on the universal cover. -/
structure Eigenmode (L lam : ℝ) (χ : ℝ → ℂ) (R φ : ℝ → ℝ) : Prop where
  L_pos : 0 < L
  smooth : ContDiff ℝ 2 χ
  periodic : Function.Periodic χ L
  eigen : ∀ s, -(deriv (deriv χ) s) = (lam : ℂ) * χ s
  R_smooth : ContDiff ℝ 1 R
  φ_smooth : ContDiff ℝ 1 φ
  R_pos : ∀ s, 0 < R s
  polar : ∀ s, χ s = (R s : ℂ) * Complex.exp ((φ s : ℂ) * Complex.I)

variable {L lam : ℝ} {χ : ℝ → ℂ} {R φ : ℝ → ℝ}

/-- `χ' = e^{iφ} (R' + i R σ)`. -/
theorem hasDerivAt_polar {R φ : ℝ → ℝ} (hR : Differentiable ℝ R) (hφ : Differentiable ℝ φ)
    (s : ℝ) :
    HasDerivAt (fun s => (R s : ℂ) * Complex.exp ((φ s : ℂ) * Complex.I))
      ((((deriv R s : ℝ) : ℂ) + (R s : ℂ) * ((deriv φ s : ℝ) : ℂ) * Complex.I) *
        Complex.exp ((φ s : ℂ) * Complex.I)) s := by
  have h1 : HasDerivAt (fun s => (R s : ℂ)) ((deriv R s : ℝ) : ℂ) s :=
    (hR s).hasDerivAt.ofReal_comp
  have h2 : HasDerivAt (fun s => (φ s : ℂ) * Complex.I) (((deriv φ s : ℝ) : ℂ) * Complex.I) s :=
    (hφ s).hasDerivAt.ofReal_comp.mul_const Complex.I
  convert h1.mul h2.cexp using 1
  ring

theorem Eigenmode.chi_eq (h : Eigenmode L lam χ R φ) :
    χ = fun s => (R s : ℂ) * Complex.exp ((φ s : ℂ) * Complex.I) :=
  funext h.polar

theorem Eigenmode.deriv_chi (h : Eigenmode L lam χ R φ) (s : ℝ) :
    deriv χ s = (((deriv R s : ℝ) : ℂ) + (R s : ℂ) * ((deriv φ s : ℝ) : ℂ) * Complex.I) *
        Complex.exp ((φ s : ℂ) * Complex.I) := by
  rw [h.chi_eq]
  exact (hasDerivAt_polar (h.R_smooth.differentiable le_rfl)
    (h.φ_smooth.differentiable le_rfl) s).deriv

theorem norm_exp_phase (x : ℝ) : ‖Complex.exp ((x : ℂ) * Complex.I)‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I x

/-- `|χ'|² = |R'|² + R² σ²`. -/
theorem Eigenmode.norm_sq_deriv (h : Eigenmode L lam χ R φ) (s : ℝ) :
    ‖deriv χ s‖ ^ 2 = deriv R s ^ 2 + R s ^ 2 * deriv φ s ^ 2 := by
  rw [h.deriv_chi, norm_mul, norm_exp_phase, mul_one, ← Complex.normSq_eq_norm_sq]
  rw [Complex.normSq_apply]
  simp
  ring

/-- `|χ|² = R²`. -/
theorem Eigenmode.norm_sq_chi (h : Eigenmode L lam χ R φ) (s : ℝ) :
    ‖χ s‖ ^ 2 = R s ^ 2 := by
  rw [h.polar, norm_mul, norm_exp_phase, mul_one, Complex.norm_real, Real.norm_eq_abs,
    sq_abs]

theorem Eigenmode.deriv_periodic (h : Eigenmode L lam χ R φ) :
    Function.Periodic (deriv χ) L := by
  intro s
  have := deriv_comp_add_const (f := χ) (a := L) (x := s)
  rw [← this]
  congr 1
  funext x
  exact h.periodic x

theorem Eigenmode.contDiff_deriv (h : Eigenmode L lam χ R φ) : ContDiff ℝ 1 (deriv χ) :=
  h.smooth.iterate_deriv' 1 1 |>.of_le le_rfl |> fun h' => by simpa using h'

/-- Periodic integration by parts (the boundary terms cancel): `λ ∫₀ᴸ |χ|² = ∫₀ᴸ |χ'|²`. -/
theorem Eigenmode.dirichlet (h : Eigenmode L lam χ R φ) :
    lam * ∫ s in (0:ℝ)..L, ‖χ s‖ ^ 2 = ∫ s in (0:ℝ)..L, ‖deriv χ s‖ ^ 2 := by
  have hχd : Differentiable ℝ χ := h.smooth.differentiable (by norm_num)
  have hd : ContDiff ℝ 1 (deriv χ) := h.contDiff_deriv
  have hdd : Differentiable ℝ (deriv χ) := hd.differentiable le_rfl
  have hcont_dd : Continuous (deriv (deriv χ)) := hd.continuous_deriv le_rfl
  have hcont_d : Continuous (deriv χ) := hd.continuous
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := L)
    (u := fun s => star (χ s)) (u' := fun s => star (deriv χ s))
    (v := deriv χ) (v' := deriv (deriv χ))
    (fun x _ => (hχd x).hasDerivAt.star) (fun x _ => (hdd x).hasDerivAt)
    (hcont_d.star.intervalIntegrable _ _) (hcont_dd.intervalIntegrable _ _)
  simp only at hibp
  rw [h.periodic.eq, h.deriv_periodic.eq, sub_self, zero_sub] at hibp
  have heig : (fun s => star (χ s) * deriv (deriv χ) s) =
      fun s => -((lam : ℂ) * (star (χ s) * χ s)) := by
    funext s
    have := h.eigen s
    rw [show deriv (deriv χ) s = -((lam : ℂ) * χ s) by rw [← this, neg_neg]]
    ring
  rw [heig, intervalIntegral.integral_neg, intervalIntegral.integral_const_mul, neg_inj] at hibp
  have hconj : ∀ z : ℂ, star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    intro z
    rw [Complex.star_def, Complex.conj_mul']
    push_cast
    ring
  simp only [hconj] at hibp
  rw [intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal] at hibp
  exact_mod_cast hibp

/-- `N = ∫₀ᴸ R²`. -/
noncomputable def mass (L : ℝ) (R : ℝ → ℝ) : ℝ := ∫ s in (0:ℝ)..L, R s ^ 2

/-- The probability weight `w = R²/N`. -/
noncomputable def weight (L : ℝ) (R : ℝ → ℝ) (s : ℝ) : ℝ := R s ^ 2 / mass L R

/-- The weighted mean `⟨f⟩_w = ∫₀ᴸ f w`. -/
noncomputable def wMean (L : ℝ) (R f : ℝ → ℝ) : ℝ := ∫ s in (0:ℝ)..L, f s * weight L R s

/-- The weighted variance `Var_w(f) = ∫₀ᴸ w (f − ⟨f⟩_w)²`. -/
noncomputable def wVar (L : ℝ) (R f : ℝ → ℝ) : ℝ :=
  ∫ s in (0:ℝ)..L, weight L R s * (f s - wMean L R f) ^ 2

/-- The normalized amplitude-gradient energy `∫|R'|² / ∫R²`. -/
noncomputable def amplitudeEnergy (L : ℝ) (R : ℝ → ℝ) : ℝ :=
  (∫ s in (0:ℝ)..L, deriv R s ^ 2) / mass L R

theorem periodic_deriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E}
    {c : ℝ} (hf : Function.Periodic f c) : Function.Periodic (deriv f) c := by
  intro s
  rw [← deriv_comp_add_const]
  congr 1
  funext x
  exact hf x

theorem Eigenmode.R_eq_norm (h : Eigenmode L lam χ R φ) (s : ℝ) : R s = ‖χ s‖ := by
  rw [h.polar, norm_mul, norm_exp_phase, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (h.R_pos s)]

theorem Eigenmode.R_periodic (h : Eigenmode L lam χ R φ) : Function.Periodic R L := by
  intro s
  rw [h.R_eq_norm, h.R_eq_norm, h.periodic s]

/-- The phase gradient is intrinsic: `R² σ = Im(χ̄ χ')`. -/
theorem Eigenmode.im_conj_mul_deriv (h : Eigenmode L lam χ R φ) (s : ℝ) :
    (star (χ s) * deriv χ s).im = R s ^ 2 * deriv φ s := by
  rw [h.deriv_chi, h.polar, Complex.star_def, map_mul, Complex.conj_ofReal]
  have hexp : (starRingEnd ℂ) (Complex.exp ((φ s : ℂ) * Complex.I)) *
      Complex.exp ((φ s : ℂ) * Complex.I) = 1 := by
    rw [Complex.conj_mul', norm_exp_phase]
    simp
  have : (R s : ℂ) * (starRingEnd ℂ) (Complex.exp ((φ s : ℂ) * Complex.I)) *
      ((((deriv R s : ℝ) : ℂ) + (R s : ℂ) * ((deriv φ s : ℝ) : ℂ) * Complex.I) *
        Complex.exp ((φ s : ℂ) * Complex.I)) =
      (R s : ℂ) * (((deriv R s : ℝ) : ℂ) + (R s : ℂ) * ((deriv φ s : ℝ) : ℂ) * Complex.I) *
        ((starRingEnd ℂ) (Complex.exp ((φ s : ℂ) * Complex.I)) *
          Complex.exp ((φ s : ℂ) * Complex.I)) := by ring
  rw [this, hexp, mul_one]
  simp
  ring

theorem Eigenmode.sigma_eq (h : Eigenmode L lam χ R φ) (s : ℝ) :
    deriv φ s = (star (χ s) * deriv χ s).im / R s ^ 2 := by
  rw [h.im_conj_mul_deriv]
  field_simp [(h.R_pos s).ne']

theorem Eigenmode.sigma_periodic (h : Eigenmode L lam χ R φ) :
    Function.Periodic (deriv φ) L := by
  intro s
  rw [h.sigma_eq, h.sigma_eq, h.periodic s, h.deriv_periodic s, h.R_periodic s]

theorem Eigenmode.R_continuous (h : Eigenmode L lam χ R φ) : Continuous R :=
  h.R_smooth.continuous

theorem Eigenmode.dR_continuous (h : Eigenmode L lam χ R φ) : Continuous (deriv R) :=
  h.R_smooth.continuous_deriv le_rfl

theorem Eigenmode.σ_continuous (h : Eigenmode L lam χ R φ) : Continuous (deriv φ) :=
  h.φ_smooth.continuous_deriv le_rfl

theorem Eigenmode.mass_pos (h : Eigenmode L lam χ R φ) : 0 < mass L R := by
  unfold mass
  refine intervalIntegral.intervalIntegral_pos_of_pos_on
    ((h.R_continuous.pow 2).intervalIntegrable _ _) (fun x _ => pow_pos (h.R_pos x) 2) h.L_pos

theorem Eigenmode.weight_integral (h : Eigenmode L lam χ R φ) :
    ∫ s in (0:ℝ)..L, weight L R s = 1 := by
  unfold weight
  rw [intervalIntegral.integral_div]
  exact div_self h.mass_pos.ne'

theorem Eigenmode.wVar_eq (h : Eigenmode L lam χ R φ) :
    wVar L R (deriv φ) = wMean L R (fun s => deriv φ s ^ 2) - wMean L R (deriv φ) ^ 2 := by
  set μ := wMean L R (deriv φ)
  have hw : Continuous (weight L R) := by
    unfold weight
    exact (h.R_continuous.pow 2).div_const _
  have hσ := h.σ_continuous
  have hint1 : IntervalIntegrable (fun s => deriv φ s ^ 2 * weight L R s) volume 0 L :=
    ((hσ.pow 2).mul hw).intervalIntegrable _ _
  have hint2 : IntervalIntegrable (fun s => deriv φ s * weight L R s) volume 0 L :=
    (hσ.mul hw).intervalIntegrable _ _
  have hint3 : IntervalIntegrable (weight L R) volume 0 L := hw.intervalIntegrable _ _
  have hexp : (fun s => weight L R s * (deriv φ s - μ) ^ 2) =
      fun s => (deriv φ s ^ 2 * weight L R s - 2 * μ * (deriv φ s * weight L R s)) +
        μ ^ 2 * weight L R s := by
    funext s
    ring
  unfold wVar
  rw [hexp, intervalIntegral.integral_add (hint1.sub (hint2.const_mul _)) (hint3.const_mul _),
    intervalIntegral.integral_sub hint1 (hint2.const_mul _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, h.weight_integral]
  rw [show (∫ x in (0:ℝ)..L, deriv φ x * weight L R x) = μ from rfl]
  unfold wMean
  ring

/-- `λ = ∫|R'|²/N + ⟨σ²⟩_w`. -/
theorem Eigenmode.phase_second_moment (h : Eigenmode L lam χ R φ) :
    lam = amplitudeEnergy L R + wMean L R (fun s => deriv φ s ^ 2) := by
  have hN := h.mass_pos
  have hd := h.dirichlet
  have h1 : (fun s => ‖χ s‖ ^ 2) = fun s => R s ^ 2 := funext h.norm_sq_chi
  have h2 : (fun s => ‖deriv χ s‖ ^ 2) = fun s => deriv R s ^ 2 + R s ^ 2 * deriv φ s ^ 2 :=
    funext h.norm_sq_deriv
  rw [h1, h2, intervalIntegral.integral_add ((h.dR_continuous.pow 2).intervalIntegrable _ _)
    (((h.R_continuous.pow 2).mul (h.σ_continuous.pow 2)).intervalIntegrable _ _)] at hd
  have hmean : wMean L R (fun s => deriv φ s ^ 2) =
      (∫ s in (0:ℝ)..L, R s ^ 2 * deriv φ s ^ 2) / mass L R := by
    unfold wMean weight
    rw [← intervalIntegral.integral_div]
    congr 1
    funext s
    ring
  rw [hmean, amplitudeEnergy, ← add_div, eq_div_iff hN.ne', ← hd]
  unfold mass
  ring

/-- **Theorem (sharp spectral–phase decomposition).** -/
theorem Eigenmode.decomposition (h : Eigenmode L lam χ R φ) :
    lam - wMean L R (deriv φ) ^ 2 = amplitudeEnergy L R + wVar L R (deriv φ) := by
  rw [h.wVar_eq, h.phase_second_moment]
  ring

theorem Eigenmode.amplitudeEnergy_nonneg (h : Eigenmode L lam χ R φ) :
    0 ≤ amplitudeEnergy L R := by
  unfold amplitudeEnergy
  apply div_nonneg _ h.mass_pos.le
  exact intervalIntegral.integral_nonneg h.L_pos.le (fun s _ => sq_nonneg _)

theorem Eigenmode.wVar_nonneg (h : Eigenmode L lam χ R φ) : 0 ≤ wVar L R (deriv φ) := by
  unfold wVar
  refine intervalIntegral.integral_nonneg h.L_pos.le (fun s _ => ?_)
  unfold weight
  exact mul_nonneg (div_nonneg (sq_nonneg _) h.mass_pos.le) (sq_nonneg _)

theorem Eigenmode.decomposition_nonneg (h : Eigenmode L lam χ R φ) :
    0 ≤ amplitudeEnergy L R + wVar L R (deriv φ) :=
  add_nonneg h.amplitudeEnergy_nonneg h.wVar_nonneg

/-- The root bound `√λ ≥ |⟨σ⟩_w|`, with no sign restriction on `σ`. -/
theorem Eigenmode.root_bound (h : Eigenmode L lam χ R φ) :
    |wMean L R (deriv φ)| ≤ Real.sqrt lam := by
  have h1 := h.decomposition
  have h2 := h.decomposition_nonneg
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (by linarith)

/-- A continuous, nonnegative, `L`-periodic function with zero integral over a period
vanishes identically. -/
theorem eq_zero_of_periodic_integral_eq_zero {g : ℝ → ℝ} (hL : 0 < L) (hg : Continuous g)
    (hper : Function.Periodic g L) (hnn : ∀ s, 0 ≤ g s)
    (hint : ∫ s in (0:ℝ)..L, g s = 0) : ∀ s, g s = 0 := by
  have hae : g =ᵐ[volume.restrict (Ioc 0 L)] 0 :=
    (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae hL.le
      (Eventually.of_forall hnn) (hg.intervalIntegrable _ _)).1 hint
  have hon : EqOn g 0 (Ioc 0 L) :=
    Measure.eqOn_Ioc_of_ae_eq volume hae hg.continuousOn continuousOn_const
  intro s
  obtain ⟨y, hy, hsy⟩ := hper.exists_mem_Ico₀ hL s
  rw [hsy]
  rcases eq_or_lt_of_le hy.1 with h0 | h0
  · rw [← h0, ← hper.eq]
    exact hon ⟨hL, le_rfl⟩
  · exact hon ⟨h0, hy.2.le⟩

/-- **Equality case**: `λ = ⟨σ⟩_w²` holds if and only if both `R` and `σ` are constant. -/
theorem Eigenmode.equality_iff (h : Eigenmode L lam χ R φ) :
    lam = wMean L R (deriv φ) ^ 2 ↔ (∃ c, ∀ s, R s = c) ∧ (∃ c, ∀ s, deriv φ s = c) := by
  have hN := h.mass_pos
  have hdec := h.decomposition
  have hA := h.amplitudeEnergy_nonneg
  have hV := h.wVar_nonneg
  have hw : Continuous (weight L R) := by
    unfold weight
    exact (h.R_continuous.pow 2).div_const _
  have hwpos : ∀ s, 0 < weight L R s := fun s => div_pos (pow_pos (h.R_pos s) 2) hN
  constructor
  · intro heq
    have hA0 : amplitudeEnergy L R = 0 := by linarith
    have hV0 : wVar L R (deriv φ) = 0 := by linarith
    refine ⟨⟨R 0, fun s => ?_⟩, ⟨wMean L R (deriv φ), fun s => ?_⟩⟩
    · have hint : ∫ s in (0:ℝ)..L, deriv R s ^ 2 = 0 := by
        rw [amplitudeEnergy, div_eq_zero_iff, or_iff_left hN.ne'] at hA0
        exact hA0
      have h0 := eq_zero_of_periodic_integral_eq_zero h.L_pos (h.dR_continuous.pow 2)
        (fun s => by rw [periodic_deriv h.R_periodic s]) (fun s => sq_nonneg _) hint
      have hd0 : ∀ x, deriv R x = 0 := fun x => pow_eq_zero_iff two_ne_zero |>.1 (h0 x)
      exact is_const_of_deriv_eq_zero (h.R_smooth.differentiable le_rfl) hd0 s 0
    · have hper : Function.Periodic
          (fun s => weight L R s * (deriv φ s - wMean L R (deriv φ)) ^ 2) L := by
        intro x
        simp only [weight, h.R_periodic x, h.sigma_periodic x]
      have h0 := eq_zero_of_periodic_integral_eq_zero h.L_pos
        (hw.mul ((h.σ_continuous.sub continuous_const).pow 2)) hper
        (fun x => mul_nonneg (hwpos x).le (sq_nonneg _)) hV0 s
      rcases mul_eq_zero.1 h0 with h1 | h1
      · exact absurd h1 (hwpos s).ne'
      · exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h1)
  · rintro ⟨⟨c₁, hc₁⟩, ⟨c₂, hc₂⟩⟩
    have hRc : R = fun _ => c₁ := funext hc₁
    have hσc : deriv φ = fun _ => c₂ := funext hc₂
    have hA0 : amplitudeEnergy L R = 0 := by
      rw [amplitudeEnergy, hRc]
      simp
    have hmean : wMean L R (deriv φ) = c₂ := by
      rw [wMean, hσc, intervalIntegral.integral_const_mul, h.weight_integral, mul_one]
    have hV0 : wVar L R (deriv φ) = 0 := by
      rw [wVar, hmean, hσc]
      simp
    linarith

/-- In the equality case, `χ = R₀ e^{i(σ₀ s + φ₀)}` with `σ₀ L ∈ 2πℤ` and `λ = σ₀²`. -/
theorem Eigenmode.equality_form (h : Eigenmode L lam χ R φ)
    (heq : lam = wMean L R (deriv φ) ^ 2) :
    ∃ R₀ σ₀ : ℝ, ∃ n : ℤ, (∀ s, χ s = (R₀ : ℂ) *
        Complex.exp (((σ₀ * s + φ 0 : ℝ) : ℂ) * Complex.I)) ∧
      σ₀ * L = 2 * Real.pi * n ∧ lam = σ₀ ^ 2 := by
  obtain ⟨⟨R₀, hR₀⟩, ⟨σ₀, hσ₀⟩⟩ := h.equality_iff.1 heq
  have hφ : ∀ s, φ s = σ₀ * s + φ 0 := by
    intro s
    have hdiff : Differentiable ℝ (fun x => φ x - σ₀ * x) :=
      (h.φ_smooth.differentiable le_rfl).sub (differentiable_id.const_mul σ₀)
    have hd0 : ∀ x, deriv (fun x => φ x - σ₀ * x) x = 0 := by
      intro x
      have : HasDerivAt (fun x => φ x - σ₀ * x) (deriv φ x - σ₀ * 1) x :=
        ((h.φ_smooth.differentiable le_rfl) x).hasDerivAt.sub
          ((hasDerivAt_id' x).const_mul σ₀)
      rw [this.deriv, hσ₀ x]
      ring
    have := is_const_of_deriv_eq_zero hdiff hd0 s 0
    simp at this
    linarith
  have hχ : ∀ s, χ s = (R₀ : ℂ) * Complex.exp (((σ₀ * s + φ 0 : ℝ) : ℂ) * Complex.I) := by
    intro s
    rw [h.polar, hR₀, hφ s]
  have hR₀pos : 0 < R₀ := hR₀ 0 ▸ h.R_pos 0
  have hper := h.periodic 0
  rw [hχ, hχ] at hper
  have hne : (R₀ : ℂ) ≠ 0 := by exact_mod_cast hR₀pos.ne'
  have hexp := mul_left_cancel₀ hne hper
  rw [Complex.exp_eq_exp_iff_exists_int] at hexp
  obtain ⟨n, hn⟩ := hexp
  refine ⟨R₀, σ₀, n, hχ, ?_, ?_⟩
  · have := congrArg Complex.im hn
    simp at this
    linarith
  · have hmean : wMean L R (deriv φ) = σ₀ := by
      rw [wMean, show deriv φ = fun _ => σ₀ from funext hσ₀,
        intervalIntegral.integral_const_mul, h.weight_integral, mul_one]
    rw [heq, hmean]

/-- **Theorem (sharp spectral–phase decomposition).**  For every `C²`, `L`-periodic,
nowhere-vanishing eigenfunction `−χ'' = λχ` with `C¹` polar form `χ = R e^{iφ}`:
`λ − ⟨σ⟩² = ∫|R'|²/∫R² + Var_w(σ) ≥ 0`, with equality iff `R` and `σ = φ'` are
constant, and `√λ ≥ |⟨σ⟩|`.  No sign restriction on `σ` is needed. -/
theorem sharp_spectral_phase_decomposition (h : Eigenmode L lam χ R φ) :
    lam - wMean L R (deriv φ) ^ 2 = amplitudeEnergy L R + wVar L R (deriv φ) ∧
      0 ≤ amplitudeEnergy L R + wVar L R (deriv φ) ∧
      (lam = wMean L R (deriv φ) ^ 2 ↔
        (∃ c, ∀ s, R s = c) ∧ (∃ c, ∀ s, deriv φ s = c)) ∧
      |wMean L R (deriv φ)| ≤ Real.sqrt lam :=
  ⟨h.decomposition, h.decomposition_nonneg, h.equality_iff, h.root_bound⟩

/-- Spectral-root form: `√λ = (⟨σ⟩² + Var_w(σ) + ‖R'‖²/‖R‖²)^{1/2}`. -/
theorem root_identity (h : Eigenmode L lam χ R φ) :
    Real.sqrt lam = Real.sqrt (wMean L R (deriv φ) ^ 2 + wVar L R (deriv φ) +
      amplitudeEnergy L R) := by
  congr 1
  linarith [h.decomposition]

/-- Every nowhere-vanishing `C¹` function `ℝ → ℂ` has a `C¹` polar lift `χ = R e^{iφ}`
with `R > 0`; hence the hypotheses of the decomposition are never vacuous. -/
theorem exists_polar_lift {χ : ℝ → ℂ} (hχ : ContDiff ℝ 1 χ) (h0 : ∀ s, χ s ≠ 0) :
    ∃ R φ : ℝ → ℝ, ContDiff ℝ 1 R ∧ ContDiff ℝ 1 φ ∧ (∀ s, 0 < R s) ∧
      ∀ s, χ s = (R s : ℂ) * Complex.exp ((φ s : ℂ) * Complex.I) := by
  have hcd : Continuous (deriv χ) := hχ.continuous_deriv le_rfl
  have hcc : Continuous χ := hχ.continuous
  have hdiff : Differentiable ℝ χ := hχ.differentiable le_rfl
  have hnorm : ∀ s, (‖χ s‖ ^ 2 : ℝ) ≠ 0 := fun s => pow_ne_zero 2 (norm_ne_zero_iff.2 (h0 s))
  set z : ℝ → ℂ := fun t => star (χ t) * deriv χ t with hz
  have hzc : Continuous z := (continuous_star.comp hcc).mul hcd
  set r : ℝ → ℝ := fun t => (z t).re / ‖χ t‖ ^ 2 with hr
  set g : ℝ → ℝ := fun t => (z t).im / ‖χ t‖ ^ 2 with hg
  have hrc : Continuous r :=
    (Complex.continuous_re.comp hzc).div (hcc.norm.pow 2) hnorm
  have hgc : Continuous g :=
    (Complex.continuous_im.comp hzc).div (hcc.norm.pow 2) hnorm
  set Rf : ℝ → ℝ := fun s => ‖χ 0‖ * Real.exp (∫ t in (0:ℝ)..s, r t) with hRf
  set φf : ℝ → ℝ := fun s => Complex.arg (χ 0) + ∫ t in (0:ℝ)..s, g t with hφf
  have hIr : ∀ s, HasDerivAt (fun s => ∫ t in (0:ℝ)..s, r t) (r s) s := fun s =>
    intervalIntegral.integral_hasDerivAt_right (hrc.intervalIntegrable _ _)
      (hrc.stronglyMeasurableAtFilter _ _) hrc.continuousAt
  have hIg : ∀ s, HasDerivAt (fun s => ∫ t in (0:ℝ)..s, g t) (g s) s := fun s =>
    intervalIntegral.integral_hasDerivAt_right (hgc.intervalIntegrable _ _)
      (hgc.stronglyMeasurableAtFilter _ _) hgc.continuousAt
  have hRd : ∀ s, HasDerivAt Rf (‖χ 0‖ * (Real.exp (∫ t in (0:ℝ)..s, r t) * r s)) s :=
    fun s => ((hIr s).exp).const_mul _
  have hφd : ∀ s, HasDerivAt φf (g s) s := fun s =>
    (hIg s).const_add (Complex.arg (χ 0))
  refine ⟨Rf, φf, ?_, ?_, ?_, ?_⟩
  · rw [contDiff_one_iff_deriv]
    refine ⟨fun s => (hRd s).differentiableAt, ?_⟩
    have : deriv Rf = fun s => ‖χ 0‖ * (Real.exp (∫ t in (0:ℝ)..s, r t) * r s) :=
      funext fun s => (hRd s).deriv
    rw [this]
    have hcI : Continuous (fun s => ∫ t in (0:ℝ)..s, r t) :=
      continuous_iff_continuousAt.2 fun s => (hIr s).continuousAt
    exact continuous_const.mul ((Real.continuous_exp.comp hcI).mul hrc)
  · rw [contDiff_one_iff_deriv]
    refine ⟨fun s => (hφd s).differentiableAt, ?_⟩
    rw [show deriv φf = g from funext fun s => (hφd s).deriv]
    exact hgc
  · intro s
    exact mul_pos (norm_pos_iff.2 (h0 0)) (Real.exp_pos _)
  · -- `H = χ e^{-iφ} e^{-∫ r}` has zero derivative
    set H : ℝ → ℂ := fun s => χ s * Complex.exp (-((φf s : ℂ) * Complex.I)) *
      ((Real.exp (-(∫ t in (0:ℝ)..s, r t)) : ℝ) : ℂ) with hH
    have hHd : ∀ s, HasDerivAt H 0 s := by
      intro s
      have e1 : HasDerivAt (fun s => Complex.exp (-((φf s : ℂ) * Complex.I)))
          (Complex.exp (-((φf s : ℂ) * Complex.I)) * (-((g s : ℂ) * Complex.I))) s :=
        (((hφd s).ofReal_comp.mul_const Complex.I).neg).cexp
      have e2 : HasDerivAt (fun s => ((Real.exp (-(∫ t in (0:ℝ)..s, r t)) : ℝ) : ℂ))
          (((Real.exp (-(∫ t in (0:ℝ)..s, r t)) * -(r s) : ℝ) : ℂ)) s :=
        ((hIr s).neg.exp).ofReal_comp
      have hprod := ((hdiff s).hasDerivAt.mul e1).mul e2
      convert hprod using 1
      -- the derivative vanishes because `χ' = (χ̄ χ' / |χ|²) χ`
      have hkey : deriv χ s = ((r s : ℂ) + (g s : ℂ) * Complex.I) * χ s := by
        have hns : ((‖χ s‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hnorm s
        have hre : ((r s : ℝ) : ℂ) + ((g s : ℝ) : ℂ) * Complex.I =
            z s / ((‖χ s‖ ^ 2 : ℝ) : ℂ) := by
          have hzs : z s = ((z s).re : ℂ) + ((z s).im : ℂ) * Complex.I :=
            (Complex.re_add_im (z s)).symm
          conv_rhs => rw [hzs]
          simp only [hr, hg]
          push_cast
          ring
        have hcm : star (χ s) * χ s = ((‖χ s‖ ^ 2 : ℝ) : ℂ) := by
          rw [Complex.star_def, Complex.conj_mul']
          push_cast
          ring
        rw [hre]
        calc deriv χ s = deriv χ s * (star (χ s) * χ s) / ((‖χ s‖ ^ 2 : ℝ) : ℂ) := by
              rw [hcm, mul_div_assoc, div_self hns, mul_one]
          _ = z s / ((‖χ s‖ ^ 2 : ℝ) : ℂ) * χ s := by
              rw [hz]
              ring
      rw [hkey]
      simp only [Pi.mul_apply]
      push_cast
      ring
    have hconst : ∀ s, H s = H 0 := fun s =>
      is_const_of_deriv_eq_zero (fun x => (hHd x).differentiableAt)
        (fun x => (hHd x).deriv) s 0
    have hH0 : H 0 = (‖χ 0‖ : ℂ) := by
      simp only [hH, hφf, intervalIntegral.integral_same, add_zero, neg_zero, Real.exp_zero,
        Complex.ofReal_one, mul_one]
      have := Complex.norm_mul_exp_arg_mul_I (χ 0)
      calc χ 0 * Complex.exp (-((Complex.arg (χ 0) : ℂ) * Complex.I))
          = (‖χ 0‖ : ℂ) * Complex.exp ((Complex.arg (χ 0) : ℂ) * Complex.I) *
              Complex.exp (-((Complex.arg (χ 0) : ℂ) * Complex.I)) := by rw [this]
        _ = (‖χ 0‖ : ℂ) := by
            rw [mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one]
    intro s
    have hs := hconst s
    rw [hH0] at hs
    have hexp1 : Complex.exp (-((φf s : ℂ) * Complex.I)) *
        Complex.exp ((φf s : ℂ) * Complex.I) = 1 := by
      rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
    have hexp2 : ((Real.exp (-(∫ t in (0:ℝ)..s, r t)) : ℝ) : ℂ) *
        ((Real.exp (∫ t in (0:ℝ)..s, r t) : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero,
        Complex.ofReal_one]
    calc χ s = χ s * (Complex.exp (-((φf s : ℂ) * Complex.I)) *
          Complex.exp ((φf s : ℂ) * Complex.I)) *
          (((Real.exp (-(∫ t in (0:ℝ)..s, r t)) : ℝ) : ℂ) *
            ((Real.exp (∫ t in (0:ℝ)..s, r t) : ℝ) : ℂ)) := by rw [hexp1, hexp2]; ring
      _ = H s * ((Real.exp (∫ t in (0:ℝ)..s, r t) : ℝ) : ℂ) *
          Complex.exp ((φf s : ℂ) * Complex.I) := by rw [hH]; ring
      _ = (Rf s : ℂ) * Complex.exp ((φf s : ℂ) * Complex.I) := by
          rw [hs, hRf]
          push_cast
          ring

/-! ### The explicit counterexample `χ_a(s) = cos s + i a sin s` -/

/-- `χ_a(s) = cos s + i a sin s`. -/
noncomputable def ellipseMode (a : ℝ) (s : ℝ) : ℂ :=
  (Real.cos s : ℂ) + ((a * Real.sin s : ℝ) : ℂ) * Complex.I

theorem ellipseMode_hasDerivAt (a s : ℝ) :
    HasDerivAt (ellipseMode a)
      ((-Real.sin s : ℝ) + ((a * Real.cos s : ℝ) : ℂ) * Complex.I) s := by
  have h1 : HasDerivAt (fun s => (Real.cos s : ℂ)) ((-Real.sin s : ℝ) : ℂ) s :=
    (Real.hasDerivAt_cos s).ofReal_comp
  have h2 : HasDerivAt (fun s => ((a * Real.sin s : ℝ) : ℂ)) ((a * Real.cos s : ℝ) : ℂ) s :=
    ((Real.hasDerivAt_sin s).const_mul a).ofReal_comp
  exact h1.add (h2.mul_const Complex.I)

theorem ellipseMode_deriv (a : ℝ) :
    deriv (ellipseMode a) = fun s =>
      ((-Real.sin s : ℝ) : ℂ) + ((a * Real.cos s : ℝ) : ℂ) * Complex.I :=
  funext fun s => (ellipseMode_hasDerivAt a s).deriv

theorem ellipseMode_deriv_deriv (a s : ℝ) :
    deriv (deriv (ellipseMode a)) s = -ellipseMode a s := by
  rw [ellipseMode_deriv]
  have h1 : HasDerivAt (fun s => ((-Real.sin s : ℝ) : ℂ)) ((-Real.cos s : ℝ) : ℂ) s :=
    (Real.hasDerivAt_sin s).neg.ofReal_comp
  have h2 : HasDerivAt (fun s => ((a * Real.cos s : ℝ) : ℂ)) ((a * -Real.sin s : ℝ) : ℂ) s :=
    ((Real.hasDerivAt_cos s).const_mul a).ofReal_comp
  have h3 : HasDerivAt (fun s => ((-Real.sin s : ℝ) : ℂ) + ((a * Real.cos s : ℝ) : ℂ) * Complex.I)
      (((-Real.cos s : ℝ) : ℂ) + ((a * -Real.sin s : ℝ) : ℂ) * Complex.I) s :=
    h1.add (h2.mul_const Complex.I)
  rw [h3.deriv, ellipseMode]
  push_cast
  ring

theorem ellipseMode_contDiff (a : ℝ) : ContDiff ℝ 2 (ellipseMode a) := by
  unfold ellipseMode
  have h1 : ContDiff ℝ 2 (fun s : ℝ => (Real.cos s : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp Real.contDiff_cos
  have h2 : ContDiff ℝ 2 (fun s : ℝ => ((a * Real.sin s : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_const.mul Real.contDiff_sin)
  exact h1.add (h2.mul contDiff_const)

theorem ellipseMode_periodic (a : ℝ) : Function.Periodic (ellipseMode a) (2 * Real.pi) := by
  intro s
  simp [ellipseMode, Real.cos_add_two_pi, Real.sin_add_two_pi]

theorem ellipseMode_norm_sq (a s : ℝ) :
    ‖ellipseMode a s‖ ^ 2 = Real.cos s ^ 2 + a ^ 2 * Real.sin s ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, ellipseMode, Complex.normSq_add_mul_I]
  ring

theorem ellipseMode_norm_sq_pos {a : ℝ} (ha : 0 < a) (s : ℝ) :
    0 < Real.cos s ^ 2 + a ^ 2 * Real.sin s ^ 2 := by
  rcases eq_or_ne (Real.sin s) 0 with h | h
  · have := Real.sin_sq_add_cos_sq s
    rw [h] at this ⊢
    nlinarith
  · have := pow_pos ha 2
    have := sq_pos_of_ne_zero h
    positivity

theorem ellipseMode_ne_zero {a : ℝ} (ha : 0 < a) (s : ℝ) : ellipseMode a s ≠ 0 := by
  intro h0
  have := ellipseMode_norm_sq a s
  rw [h0, norm_zero] at this
  have := ellipseMode_norm_sq_pos ha s
  nlinarith

/-- `Im(χ̄_a χ_a') = a`. -/
theorem ellipseMode_im_conj_mul_deriv (a s : ℝ) :
    (star (ellipseMode a s) * deriv (ellipseMode a) s).im = a := by
  rw [ellipseMode_deriv, ellipseMode]
  simp only [Complex.star_def, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  simp only [Complex.mul_im, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.neg_re,
    Complex.neg_im]
  have := Real.sin_sq_add_cos_sq s
  linear_combination a * this

theorem integral_ellipse_mass (a : ℝ) :
    ∫ s in (0:ℝ)..(2 * Real.pi), (Real.cos s ^ 2 + a ^ 2 * Real.sin s ^ 2) =
      Real.pi * (1 + a ^ 2) := by
  rw [intervalIntegral.integral_add, intervalIntegral.integral_const_mul, integral_cos_sq,
    integral_sin_sq]
  · simp
    ring
  · exact (Real.continuous_cos.pow 2).intervalIntegrable _ _
  · exact (continuous_const.mul (Real.continuous_sin.pow 2)).intervalIntegrable _ _

/-- Any polar representation of `χ_a` is an admissible eigenmode with `λ = 1`. -/
theorem ellipseMode_eigenmode {a : ℝ} {R φ : ℝ → ℝ} (hR : ContDiff ℝ 1 R)
    (hφ : ContDiff ℝ 1 φ) (hRpos : ∀ s, 0 < R s)
    (hpolar : ∀ s, ellipseMode a s = (R s : ℂ) * Complex.exp ((φ s : ℂ) * Complex.I)) :
    Eigenmode (2 * Real.pi) 1 (ellipseMode a) R φ where
  L_pos := by positivity
  smooth := ellipseMode_contDiff a
  periodic := ellipseMode_periodic a
  eigen := fun s => by rw [ellipseMode_deriv_deriv, neg_neg, Complex.ofReal_one, one_mul]
  R_smooth := hR
  φ_smooth := hφ
  R_pos := hRpos
  polar := hpolar

theorem ellipseMode_has_polar {a : ℝ} (ha : 0 < a) :
    ∃ R φ : ℝ → ℝ, Eigenmode (2 * Real.pi) 1 (ellipseMode a) R φ := by
  obtain ⟨R, φ, hR, hφ, hRpos, hpolar⟩ :=
    exists_polar_lift ((ellipseMode_contDiff a).of_le (by norm_num)) (ellipseMode_ne_zero ha)
  exact ⟨R, φ, ellipseMode_eigenmode hR hφ hRpos hpolar⟩

theorem ellipseMode_mass {a : ℝ} {R φ : ℝ → ℝ}
    (h : Eigenmode (2 * Real.pi) 1 (ellipseMode a) R φ) :
    mass (2 * Real.pi) R = Real.pi * (1 + a ^ 2) := by
  unfold mass
  rw [← integral_ellipse_mass a]
  congr 1
  funext s
  rw [← h.norm_sq_chi, ellipseMode_norm_sq]

/-- **Proposition (nonconstant amplitude defeats mean closure).** For every `a > 0`,
`χ_a` is a smooth nowhere-vanishing `2π`-periodic eigenfunction with `λ = 1`, and for
every polar representation its weighted mean phase gradient is `2a/(1 + a²)`. -/
theorem ellipseMode_mean {a : ℝ} (ha : 0 < a) {R φ : ℝ → ℝ}
    (h : Eigenmode (2 * Real.pi) 1 (ellipseMode a) R φ) :
    wMean (2 * Real.pi) R (deriv φ) = 2 * a / (1 + a ^ 2) := by
  have hN := ellipseMode_mass h
  have hpt : (fun s => deriv φ s * weight (2 * Real.pi) R s) =
      fun s => a / mass (2 * Real.pi) R := by
    funext s
    have := h.im_conj_mul_deriv s
    rw [ellipseMode_im_conj_mul_deriv] at this
    unfold weight
    rw [this]
    ring
  unfold wMean
  rw [hpt, intervalIntegral.integral_const, hN]
  simp only [sub_zero, smul_eq_mul]
  field_simp

theorem ellipseMode_gap (a : ℝ) : 1 - 2 * a / (1 + a ^ 2) = (a - 1) ^ 2 / (1 + a ^ 2) := by
  have : 0 < 1 + a ^ 2 := by positivity
  field_simp
  ring

/-- `√λ ≠ ⟨σ⟩_w` for every `a > 0`, `a ≠ 1`. -/
theorem ellipseMode_mean_ne {a : ℝ} (ha : 0 < a) (ha1 : a ≠ 1) {R φ : ℝ → ℝ}
    (h : Eigenmode (2 * Real.pi) 1 (ellipseMode a) R φ) :
    Real.sqrt 1 ≠ wMean (2 * Real.pi) R (deriv φ) := by
  rw [ellipseMode_mean ha h, Real.sqrt_one]
  intro heq
  have := ellipseMode_gap a
  rw [← heq, sub_self] at this
  have h1 : 0 < (a - 1) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.2 ha1)
  have h2 : 0 < 1 + a ^ 2 := by positivity
  have := div_pos h1 h2
  linarith

/-- At `a = 1/2`: `√λ = 1` but `⟨σ⟩_w = 4/5`. -/
theorem four_fifths {R φ : ℝ → ℝ} (h : Eigenmode (2 * Real.pi) 1 (ellipseMode (1 / 2)) R φ) :
    Real.sqrt 1 = 1 ∧ wMean (2 * Real.pi) R (deriv φ) = 4 / 5 := by
  refine ⟨Real.sqrt_one, ?_⟩
  rw [ellipseMode_mean (by norm_num) h]
  norm_num

/-! ### Exact gap accounting -/

theorem ellipse_P_pos {a : ℝ} (ha : 0 < a) (s : ℝ) :
    0 < Real.cos s ^ 2 + a * Real.sin s ^ 2 := by
  rcases eq_or_ne (Real.sin s) 0 with h | h
  · have := Real.sin_sq_add_cos_sq s
    rw [h] at this ⊢
    nlinarith
  · have := sq_pos_of_ne_zero h
    positivity

/-- An explicit smooth global angle function for the ellipse `(cos s, a sin s)`. -/
noncomputable def ellipseAngle (a s : ℝ) : ℝ :=
  s + Real.arctan ((a - 1) * Real.sin s * Real.cos s /
    (Real.cos s ^ 2 + a * Real.sin s ^ 2))

theorem ellipseAngle_deriv_alg (a c sn : ℝ) (hP : 0 < c ^ 2 + a * sn ^ 2)
    (hR : 0 < c ^ 2 + a ^ 2 * sn ^ 2) (hpyth : sn ^ 2 + c ^ 2 = 1) :
    1 + 1 / (1 + ((a - 1) * sn * c / (c ^ 2 + a * sn ^ 2)) ^ 2) *
        ((((a - 1) * c * c + (a - 1) * sn * -sn) * (c ^ 2 + a * sn ^ 2) -
            (a - 1) * sn * c * (2 * c * -sn + a * (2 * sn * c))) /
          (c ^ 2 + a * sn ^ 2) ^ 2) =
      a / (c ^ 2 + a ^ 2 * sn ^ 2) := by
  set P := c ^ 2 + a * sn ^ 2 with hPdef
  set Q := (a - 1) * sn * c with hQdef
  set D := ((a - 1) * c * c + (a - 1) * sn * -sn) * P - Q * (2 * c * -sn + a * (2 * sn * c))
    with hDdef
  set R2 := c ^ 2 + a ^ 2 * sn ^ 2 with hR2def
  have h1 : P ^ 2 + Q ^ 2 = R2 := by
    rw [hPdef, hQdef, hR2def]
    linear_combination (a ^ 2 * sn ^ 2 + c ^ 2) * hpyth
  have h2 : R2 + D = a := by
    rw [hR2def, hDdef, hPdef, hQdef]
    linear_combination (-a ^ 2 * sn ^ 2 + a * c ^ 2 + a * sn ^ 2 + a - c ^ 2) * hpyth
  have hP0 : P ≠ 0 := hP.ne'
  have hR0 : R2 ≠ 0 := hR.ne'
  have hPQ : P ^ 2 + Q ^ 2 ≠ 0 := by rw [h1]; exact hR0
  calc 1 + 1 / (1 + (Q / P) ^ 2) * (D / P ^ 2) = 1 + D / (P ^ 2 + Q ^ 2) := by
        field_simp
    _ = 1 + D / R2 := by rw [h1]
    _ = (R2 + D) / R2 := by field_simp
    _ = a / R2 := by rw [h2]

theorem ellipseAngle_hasDerivAt {a : ℝ} (ha : 0 < a) (s : ℝ) :
    HasDerivAt (ellipseAngle a) (a / (Real.cos s ^ 2 + a ^ 2 * Real.sin s ^ 2)) s := by
  have hP := ellipse_P_pos ha s
  have hR := ellipseMode_norm_sq_pos ha s
  have hQ : HasDerivAt (fun s => (a - 1) * Real.sin s * Real.cos s)
      ((a - 1) * Real.cos s * Real.cos s + (a - 1) * Real.sin s * -Real.sin s) s := by
    have := ((Real.hasDerivAt_sin s).const_mul (a - 1)).mul (Real.hasDerivAt_cos s)
    simpa using this
  have hPd : HasDerivAt (fun s => Real.cos s ^ 2 + a * Real.sin s ^ 2)
      (2 * Real.cos s * -Real.sin s + a * (2 * Real.sin s * Real.cos s)) s := by
    have h1 := (Real.hasDerivAt_cos s).pow 2
    have h2 := ((Real.hasDerivAt_sin s).pow 2).const_mul a
    convert h1.add h2 using 1
    simp
  have hu := (hQ.div hPd hP.ne').arctan
  have := (hasDerivAt_id s).add hu
  convert this using 1
  simp only [Pi.div_apply]
  exact (ellipseAngle_deriv_alg a (Real.cos s) (Real.sin s) hP hR
    (Real.sin_sq_add_cos_sq s)).symm

theorem integral_inv_ellipse {a : ℝ} (ha : 0 < a) :
    ∫ s in (0:ℝ)..(2 * Real.pi), 1 / (Real.cos s ^ 2 + a ^ 2 * Real.sin s ^ 2) =
      2 * Real.pi / a := by
  have hcont : Continuous fun s => a / (Real.cos s ^ 2 + a ^ 2 * Real.sin s ^ 2) :=
    continuous_const.div ((Real.continuous_cos.pow 2).add
      (continuous_const.mul (Real.continuous_sin.pow 2))) fun s => (ellipseMode_norm_sq_pos ha s).ne'
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => ellipseAngle_hasDerivAt ha x) (hcont.intervalIntegrable 0 (2 * Real.pi))
  have hend : ellipseAngle a (2 * Real.pi) - ellipseAngle a 0 = 2 * Real.pi := by
    simp [ellipseAngle]
  have hscale : (fun s => 1 / (Real.cos s ^ 2 + a ^ 2 * Real.sin s ^ 2)) =
      fun s => a⁻¹ * (a / (Real.cos s ^ 2 + a ^ 2 * Real.sin s ^ 2)) := by
    funext s
    field_simp
  rw [hscale, intervalIntegral.integral_const_mul, hFTC, hend]
  field_simp

/-- `⟨σ²⟩_w = 2a/(1 + a²)` for every polar representation of `χ_a`. -/
theorem ellipseMode_second_moment {a : ℝ} (ha : 0 < a) {R φ : ℝ → ℝ}
    (h : Eigenmode (2 * Real.pi) 1 (ellipseMode a) R φ) :
    wMean (2 * Real.pi) R (fun s => deriv φ s ^ 2) = 2 * a / (1 + a ^ 2) := by
  have hN := ellipseMode_mass h
  have hpt : (fun s => deriv φ s ^ 2 * weight (2 * Real.pi) R s) =
      fun s => a ^ 2 / mass (2 * Real.pi) R *
        (1 / (Real.cos s ^ 2 + a ^ 2 * Real.sin s ^ 2)) := by
    funext s
    have hσ := h.im_conj_mul_deriv s
    rw [ellipseMode_im_conj_mul_deriv] at hσ
    have hR2 : R s ^ 2 = Real.cos s ^ 2 + a ^ 2 * Real.sin s ^ 2 := by
      rw [← h.norm_sq_chi, ellipseMode_norm_sq]
    have hRpos : 0 < R s ^ 2 := pow_pos (h.R_pos s) 2
    have hR0 : R s ≠ 0 := (h.R_pos s).ne'
    have hσ' : deriv φ s = a / R s ^ 2 := by
      rw [hσ]
      field_simp
    unfold weight
    rw [hσ', ← hR2]
    field_simp
  unfold wMean
  rw [hpt, intervalIntegral.integral_const_mul, integral_inv_ellipse ha, hN]
  field_simp

/-- **Exact gap accounting at `a = 1/2`**:
`1 − (4/5)² = 1/5 (amplitude-gradient energy) + 4/25 (phase variance) = 9/25`. -/
theorem gap_accounting {R φ : ℝ → ℝ}
    (h : Eigenmode (2 * Real.pi) 1 (ellipseMode (1 / 2)) R φ) :
    wMean (2 * Real.pi) R (fun s => deriv φ s ^ 2) = 4 / 5 ∧
      wVar (2 * Real.pi) R (deriv φ) = 4 / 25 ∧
      amplitudeEnergy (2 * Real.pi) R = 1 / 5 ∧
      1 - (4 / 5 : ℝ) ^ 2 = amplitudeEnergy (2 * Real.pi) R + wVar (2 * Real.pi) R (deriv φ) ∧
      1 - (4 / 5 : ℝ) ^ 2 = 9 / 25 := by
  have h2 := ellipseMode_second_moment (by norm_num) h
  have h1 := (four_fifths h).2
  have hvar := h.wVar_eq
  have hsec := h.phase_second_moment
  norm_num at h2
  refine ⟨h2, by rw [hvar, h1, h2]; norm_num, ?_, ?_, by norm_num⟩
  · have : amplitudeEnergy (2 * Real.pi) R = 1 - 4 / 5 := by
      rw [h2] at hsec
      linarith
    rw [this]
    norm_num
  · have hdec := h.decomposition
    rw [h1] at hdec
    linarith

/-! ### Realization by a smooth closed planar curve -/

open scoped ContDiff in
theorem ellipseMode_contDiff_infty (a : ℝ) : ContDiff ℝ ∞ (ellipseMode a) := by
  unfold ellipseMode
  have h1 : ContDiff ℝ ∞ (fun s : ℝ => (Real.cos s : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp Real.contDiff_cos
  have h2 : ContDiff ℝ ∞ (fun s : ℝ => ((a * Real.sin s : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_const.mul Real.contDiff_sin)
  exact h1.add (h2.mul contDiff_const)

/-- The complex unit tangent `T_a = χ_a/|χ_a|`. -/
noncomputable def ellipseTangent (a s : ℝ) : ℂ := ellipseMode a s / (‖ellipseMode a s‖ : ℂ)

/-- The plane curve `Γ_a(s) = ∫₀ˢ T_a`, with `ℂ ≅ ℝ²`. -/
noncomputable def ellipseCurve (a s : ℝ) : ℂ := ∫ t in (0:ℝ)..s, ellipseTangent a t

open scoped ContDiff in
theorem ellipseTangent_contDiff {a : ℝ} (ha : 0 < a) : ContDiff ℝ ∞ (ellipseTangent a) := by
  have hχ := ellipseMode_contDiff_infty a
  have hn : ContDiff ℝ ∞ (fun s => ‖ellipseMode a s‖) := hχ.norm ℝ (ellipseMode_ne_zero ha)
  have hn' : ContDiff ℝ ∞ (fun s => ((‖ellipseMode a s‖ : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hn
  unfold ellipseTangent
  simp_rw [div_eq_mul_inv]
  exact hχ.mul (hn'.inv fun s => by exact_mod_cast norm_ne_zero_iff.2 (ellipseMode_ne_zero ha s))

theorem ellipseCurve_hasDerivAt {a : ℝ} (ha : 0 < a) (s : ℝ) :
    HasDerivAt (ellipseCurve a) (ellipseTangent a s) s := by
  have hc := (ellipseTangent_contDiff ha).continuous
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt

theorem ellipseCurve_deriv {a : ℝ} (ha : 0 < a) : deriv (ellipseCurve a) = ellipseTangent a :=
  funext fun s => (ellipseCurve_hasDerivAt ha s).deriv

open scoped ContDiff in
/-- `Γ_a` is smooth. -/
theorem ellipseCurve_contDiff {a : ℝ} (ha : 0 < a) : ContDiff ℝ ∞ (ellipseCurve a) := by
  rw [contDiff_infty_iff_deriv]
  exact ⟨fun s => (ellipseCurve_hasDerivAt ha s).differentiableAt,
    by rw [ellipseCurve_deriv ha]; exact ellipseTangent_contDiff ha⟩

/-- `Γ_a` has unit speed. -/
theorem ellipseCurve_unit_speed {a : ℝ} (ha : 0 < a) (s : ℝ) :
    ‖deriv (ellipseCurve a) s‖ = 1 := by
  rw [ellipseCurve_deriv ha, ellipseTangent, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_norm]
  exact div_self (norm_ne_zero_iff.2 (ellipseMode_ne_zero ha s))

theorem ellipseMode_add_pi (a s : ℝ) : ellipseMode a (s + Real.pi) = -ellipseMode a s := by
  simp only [ellipseMode, Real.cos_add_pi, Real.sin_add_pi]
  push_cast
  ring

theorem ellipseTangent_add_pi (a s : ℝ) :
    ellipseTangent a (s + Real.pi) = -ellipseTangent a s := by
  rw [ellipseTangent, ellipseTangent, ellipseMode_add_pi, norm_neg, neg_div]

/-- `Γ_a` is closed. -/
theorem ellipseCurve_closed {a : ℝ} (ha : 0 < a) :
    ellipseCurve a (2 * Real.pi) = ellipseCurve a 0 := by
  have hc := (ellipseTangent_contDiff ha).continuous
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := volume) 0 Real.pi)
    (hc.intervalIntegrable (μ := volume) Real.pi (2 * Real.pi))
  have hshift : ∫ t in Real.pi..(2 * Real.pi), ellipseTangent a t =
      -∫ t in (0:ℝ)..Real.pi, ellipseTangent a t := by
    have := intervalIntegral.integral_comp_add_right (fun t => ellipseTangent a t) Real.pi
      (a := 0) (b := Real.pi)
    rw [zero_add, show Real.pi + Real.pi = 2 * Real.pi by ring] at this
    rw [← this, ← intervalIntegral.integral_neg]
    congr 1
    funext t
    exact ellipseTangent_add_pi a t
  unfold ellipseCurve
  rw [← hsplit, hshift, add_neg_cancel, intervalIntegral.integral_same]

/-- `Γ_a` has length `2π`. -/
theorem ellipseCurve_length {a : ℝ} (ha : 0 < a) :
    ∫ s in (0:ℝ)..(2 * Real.pi), ‖deriv (ellipseCurve a) s‖ = 2 * Real.pi := by
  simp only [ellipseCurve_unit_speed ha, intervalIntegral.integral_const, sub_zero, smul_eq_mul,
    mul_one]

/-- Its curvature `κ_a = |Γ_a''|` equals the phase gradient `σ_a = a/(cos² + a² sin²) > 0`,
for every polar representation. -/
theorem ellipseCurve_curvature {a : ℝ} (ha : 0 < a) {R φ : ℝ → ℝ}
    (h : Eigenmode (2 * Real.pi) 1 (ellipseMode a) R φ) (s : ℝ) :
    ‖deriv (deriv (ellipseCurve a)) s‖ = deriv φ s ∧
      deriv φ s = a / (Real.cos s ^ 2 + a ^ 2 * Real.sin s ^ 2) ∧ 0 < deriv φ s := by
  have hT : ellipseTangent a = fun s => Complex.exp ((φ s : ℂ) * Complex.I) := by
    funext t
    rw [ellipseTangent, h.polar t, norm_mul, norm_exp_phase, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (h.R_pos t)]
    field_simp [Complex.ofReal_ne_zero.2 (h.R_pos t).ne']
  have hσ : deriv φ s = a / (Real.cos s ^ 2 + a ^ 2 * Real.sin s ^ 2) := by
    have := h.im_conj_mul_deriv s
    rw [ellipseMode_im_conj_mul_deriv] at this
    have hR2 : R s ^ 2 = Real.cos s ^ 2 + a ^ 2 * Real.sin s ^ 2 := by
      rw [← h.norm_sq_chi, ellipseMode_norm_sq]
    rw [← hR2, this]
    field_simp [(h.R_pos s).ne']
  have hpos : 0 < deriv φ s := by
    rw [hσ]
    exact div_pos ha (ellipseMode_norm_sq_pos ha s)
  refine ⟨?_, hσ, hpos⟩
  have hd : HasDerivAt (fun s => Complex.exp ((φ s : ℂ) * Complex.I))
      (Complex.exp ((φ s : ℂ) * Complex.I) * (((deriv φ s : ℝ) : ℂ) * Complex.I)) s :=
    ((h.φ_smooth.differentiable le_rfl s).hasDerivAt.ofReal_comp.mul_const Complex.I).cexp
  rw [ellipseCurve_deriv ha, hT, hd.deriv, norm_mul, norm_exp_phase, one_mul, norm_mul,
    Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]

/-- Viewed in `ℝ³` via `z ↦ (Re z, Im z, 0)`, the torsion numerator (the triple product
of the first three derivatives) vanishes identically, so the planar curve has torsion `0`. -/
theorem planar_torsion_numerator (x1 y1 x2 y2 x3 y3 : ℝ) :
    Matrix.det !![x1, y1, 0; x2, y2, 0; x3, y3, 0] = 0 := by
  simp [Matrix.det_fin_three]

/-- **Proposition (geometrically locked counterexample).** At `a = 1/2` the curvature
satisfies the pointwise lock `σ = √(κ² + τ²)` with `τ = 0`, while `√λ = 1` and
`⟨κ⟩_w = 4/5`. -/
theorem geometric_lock_four_fifths {R φ : ℝ → ℝ}
    (h : Eigenmode (2 * Real.pi) 1 (ellipseMode (1 / 2)) R φ) :
    (∀ s, deriv φ s = Real.sqrt (‖deriv (deriv (ellipseCurve (1 / 2))) s‖ ^ 2 + 0 ^ 2)) ∧
      Real.sqrt 1 = 1 ∧
      wMean (2 * Real.pi) R (fun s => ‖deriv (deriv (ellipseCurve (1 / 2))) s‖) = 4 / 5 := by
  have hk := fun s => (ellipseCurve_curvature (by norm_num) h s)
  refine ⟨fun s => ?_, Real.sqrt_one, ?_⟩
  · rw [(hk s).1, zero_pow two_ne_zero, add_zero, Real.sqrt_sq (hk s).2.2.le]
  · have : (fun s => ‖deriv (deriv (ellipseCurve (1 / 2))) s‖) = deriv φ :=
      funext fun s => (hk s).1
    rw [this]
    exact (four_fifths h).2

end SpectralPhase

end ReyesMath
