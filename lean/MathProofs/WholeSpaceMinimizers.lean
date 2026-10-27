import Mathlib
import MathProofs.CurvatureNonattainment

/-!
# Whole-space constrained minimizers for the fourth-order cubic–quintic Hamiltonian (F01/T2)

Formalization of `papers/whole-space-fourth-order-cubic-quintic-minimizers/main.tex` on the
Sobolev space `H²(ℝ²; ℂ)` of `MathProofs.SobolevH2`, with
`H(u) = ‖(Δ + k²)u‖² − (β/2)‖u‖⁴_{L⁴} + (γ/3)‖u‖⁶_{L⁶}` and
`I(m) = inf {H(u) : ‖u‖²₂ = m}` (`Sobolev.H2.energy`, `Sobolev.H2.Imin`).

* Linear structure and symmetries of `H²`: `Sobolev.H2.add`, `Sobolev.H2.sub` and the spatial
  translations `Sobolev.H2.translate` (via `Sobolev.transS` on `𝓢` and the isometry
  `Sobolev.transL2` on `L²`), with `M_translate`, `K_translate`, `D_translate`, `T_translate`,
  `Q_translate`, `S_translate`, `energy_translate`.
* Lemma (local Hölder estimate, the quantitative form of local Rellich compactness):
  `Sobolev.holder_schwartz` (`|φ(x) − φ(y)|² ≤ C_H |x − y| (‖Δφ‖² + ‖φ‖²)` on `𝓢(ℝ²)`, by
  Fourier inversion and weighted Cauchy–Schwarz) and its disc-average form on `H²`,
  `Sobolev.H2.ae_ball_avg` / `Sobolev.H2.ae_norm_le_avg`.
* Lemma (no vanishing): `Sobolev.H2.exists_ball_avg` and `WholeSpace.exists_translations` —
  along a minimizing sequence (`Q(uₙ) ≥ −I(m)/β > 0` eventually, `WholeSpace.eventually_bounds`)
  some disc `B(yₙ, r)` of fixed radius carries `|∫_{B(yₙ,r)} uₙ| ≥ c₀ > 0`.
* Weak compactness: `WeakCompact.exists_weak_subseq` (bounded sequences in a separable Hilbert
  space have weakly convergent subsequences: Tychonoff on a dense countable set, Banach–Steinhaus
  and the Riesz representation) and `Sobolev.H2.exists_weak_limit` (weak closedness of `H²`,
  via `Kᗮᗮ = closure K` for the Schwartz graph in `L² × L² × (L²)²`).
* `Sobolev.H2.ae_tendsto_zero_of_weak`: weakly null bounded sequences in `H²(ℝ²)` converge to
  `0` almost everywhere.
* `BrezisLieb.brezis_lieb` (the Brezis–Lieb lemma for `∫‖·‖ᵖ`, `p ≥ 1`) and the splittings
  `Sobolev.H2.tendsto_M_split`, `Sobolev.H2.tendsto_pow_split`, `Sobolev.H2.tendsto_energy_split`
  (`H(wₙ) = H(u) + H(wₙ − u) + o(1)`; no weak lower semicontinuity of `H` is used).
* Mass correction: `Sobolev.H2.exists_energy_ge_Imin`.
* `WholeSpace.conclusion`: strict binding forces `M(u) = m`, then `H(u) = I(m)` and strong
  convergence in `H²` (`H2.distH2 → 0`).
* **Theorem (iii)** `WholeSpace.compactness`: for `β, γ > 0`, `0 < m ≤ m_B`, every minimizing
  sequence has a subsequence converging strongly in `H²` after translations to a minimizer;
  `WholeSpace.exists_minimizer` (`𝒢_m ≠ ∅`) and `WholeSpace.minimizers_seq_compact`
  (sequential compactness of `𝒢_m` modulo translations).
* **Theorem** `WholeSpace.main`: parts (i)–(iii) together, with (i) from
  `NegativeEnergy.negative_constrained_energy` and (ii) from `StrictBinding.strict_binding`.
-/

open Filter Topology Complex InnerProductSpace MeasureTheory Set
open scoped ContDiff FourierTransform

namespace ReyesMath

namespace Sobolev

variable {d : ℕ}

local notation "Rd" => EuclideanSpace ℝ (Fin d)

/-! ### Translations -/

/-- `x ↦ x + y` has temperate growth. -/
theorem hasTemperateGrowth_add_right (y : Rd) :
    Function.HasTemperateGrowth fun x : Rd => x + y := by
  refine Function.HasTemperateGrowth.of_fderiv (k := 1) (C := 1 + ‖y‖) ?_
    (differentiable_id.add_const y) fun x => ?_
  · have : fderiv ℝ (fun x : Rd => x + y) = fun _ => ContinuousLinearMap.id ℝ Rd := by
      funext x
      exact ((hasFDerivAt_id x).add_const y).fderiv
    rw [this]
    exact .const _
  · calc ‖x + y‖ ≤ ‖x‖ + ‖y‖ := norm_add_le _ _
      _ ≤ (1 + ‖y‖) * (1 + ‖x‖) ^ 1 := by nlinarith [norm_nonneg x, norm_nonneg y]

/-- Translation `φ ↦ φ(· + y)` on Schwartz space. -/
noncomputable def transS (y : Rd) : SchwartzMap Rd ℂ →L[ℂ] SchwartzMap Rd ℂ :=
  SchwartzMap.compCLMOfAntilipschitz ℂ (hasTemperateGrowth_add_right y)
    (IsometryEquiv.addRight y).isometry.antilipschitz

theorem transS_apply (y : Rd) (φ : SchwartzMap Rd ℂ) (x : Rd) : transS y φ x = φ (x + y) := rfl

theorem dS_transS (y : Rd) (i : Fin d) (φ : SchwartzMap Rd ℂ) :
    dS i (transS y φ) = transS y (dS i φ) := by
  ext x
  rw [dS_apply, transS_apply, dS_apply]
  have : ⇑(transS y φ) = fun z => φ (z + y) := rfl
  rw [this, fderiv_comp_add_right]

theorem lapS_transS (y : Rd) (φ : SchwartzMap Rd ℂ) : lapS (transS y φ) = transS y (lapS φ) := by
  simp only [lapS, ContinuousLinearMap.coe_sum', ContinuousLinearMap.coe_comp', Finset.sum_apply,
    Function.comp_apply, dS_transS, map_sum]

theorem mp_add_right (y : Rd) : MeasurePreserving (fun x : Rd => x + y) volume volume :=
  measurePreserving_add_right volume y

/-- Translation `f ↦ f(· + y)` on `L²`, a linear isometry. -/
noncomputable def transL2 (y : Rd) : L2 d →ₗᵢ[ℂ] L2 d :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun x : Rd => x + y) (mp_add_right y)

theorem coeFn_transL2 (y : Rd) (f : L2 d) : (transL2 y f : Rd → ℂ) =ᵐ[volume] fun x => f (x + y) :=
  Lp.coeFn_compMeasurePreserving f (mp_add_right y)

theorem toL2_transS (y : Rd) (φ : SchwartzMap Rd ℂ) : toL2 (transS y φ) = transL2 y (toL2 φ) := by
  apply Lp.ext
  have h3 : (fun x => (toL2 φ : Rd → ℂ) (x + y)) =ᵐ[volume] fun x => φ (x + y) :=
    (mp_add_right y).quasiMeasurePreserving.ae_eq_comp (coeFn_toL2 φ)
  filter_upwards [coeFn_toL2 (transS y φ), coeFn_transL2 y (toL2 φ), h3] with x h1 h2 h3'
  rw [h1, h2, h3', transS_apply]

/-! ### Linear operations on `H²` -/

namespace H2

/-- Sum on `H²`. -/
noncomputable def add (U V : H2 d) : H2 d where
  val := U.val + V.val
  grad := fun i => U.grad i + V.grad i
  lap := U.lap + V.lap
  approx := by
    obtain ⟨φ, h0, h1, h2⟩ := U.approx
    obtain ⟨ψ, g0, g1, g2⟩ := V.approx
    refine ⟨fun n => φ n + ψ n, ?_, fun i => ?_, ?_⟩
    · simpa only [map_add] using h0.add g0
    · simpa only [map_add] using (h1 i).add (g1 i)
    · simpa only [map_add] using h2.add g2

/-- Difference on `H²`. -/
noncomputable def sub (U V : H2 d) : H2 d where
  val := U.val - V.val
  grad := fun i => U.grad i - V.grad i
  lap := U.lap - V.lap
  approx := by
    obtain ⟨φ, h0, h1, h2⟩ := U.approx
    obtain ⟨ψ, g0, g1, g2⟩ := V.approx
    refine ⟨fun n => φ n - ψ n, ?_, fun i => ?_, ?_⟩
    · simpa only [map_sub] using h0.sub g0
    · simpa only [map_sub] using (h1 i).sub (g1 i)
    · simpa only [map_sub] using h2.sub g2

/-- Spatial translation `u ↦ u(· + y)` on `H²`. -/
noncomputable def translate (y : Rd) (U : H2 d) : H2 d where
  val := transL2 y U.val
  grad := fun i => transL2 y (U.grad i)
  lap := transL2 y U.lap
  approx := by
    obtain ⟨φ, h0, h1, h2⟩ := U.approx
    refine ⟨fun n => transS y (φ n), ?_, fun i => ?_, ?_⟩
    · simp_rw [toL2_transS]
      exact ((transL2 y).continuous.tendsto _).comp h0
    · simp_rw [dS_transS, toL2_transS]
      exact ((transL2 y).continuous.tendsto _).comp (h1 i)
    · simp_rw [lapS_transS, toL2_transS]
      exact ((transL2 y).continuous.tendsto _).comp h2

theorem M_translate (y : Rd) (U : H2 d) : M (translate y U) = M U := by
  simp only [M, translate, LinearIsometry.norm_map]

theorem K_translate (y : Rd) (U : H2 d) : K (translate y U) = K U := by
  simp only [K, translate, LinearIsometry.norm_map]

theorem D_translate (y : Rd) (U : H2 d) : D (translate y U) = D U := by
  simp only [D, translate, LinearIsometry.norm_map]

theorem T_translate (k : ℝ) (y : Rd) (U : H2 d) : T k (translate y U) = T k U := by
  simp only [T, translate]
  rw [← LinearIsometry.map_smul, ← map_add, LinearIsometry.norm_map]

theorem integral_pow_translate (y : Rd) (U : H2 d) (n : ℕ) :
    ∫ x, ‖(translate y U).val x‖ ^ n = ∫ x, ‖U.val x‖ ^ n := by
  have h : ∫ x, ‖(translate y U).val x‖ ^ n = ∫ x, ‖U.val (x + y)‖ ^ n := by
    refine integral_congr_ae ?_
    filter_upwards [coeFn_transL2 y U.val] with x hx
    simp only [translate]
    rw [hx]
  rw [h]
  exact integral_add_right_eq_self (fun x => ‖U.val x‖ ^ n) y

theorem Q_translate (y : Rd) (U : H2 d) : Q (translate y U) = Q U :=
  integral_pow_translate y U 4

theorem S_translate (y : Rd) (U : H2 d) : S (translate y U) = S U :=
  integral_pow_translate y U 6

theorem energy_translate (β γ k : ℝ) (y : EuclideanSpace ℝ (Fin 2)) (U : H2 2) :
    energy β γ k (translate y U) = energy β γ k U := by
  rw [energy_eq, energy_eq, T_translate, Q_translate, S_translate]

/-- `∫_{B(0,r)} u(· + y) = ∫_{B(y,r)} u`. -/
theorem setIntegral_ball_translate (y : Rd) (U : H2 d) (r : ℝ) :
    ∫ x in Metric.ball 0 r, (translate y U).val x = ∫ x in Metric.ball y r, U.val x := by
  have h : ∫ x in Metric.ball 0 r, (translate y U).val x =
      ∫ x in Metric.ball 0 r, U.val (x + y) := by
    refine setIntegral_congr_ae measurableSet_ball ?_
    filter_upwards [coeFn_transL2 y U.val] with x hx _
    simp only [translate]
    rw [hx]
  rw [h]
  have hpre : (fun x : Rd => x + y) ⁻¹' Metric.ball y r = Metric.ball 0 r := by
    ext x
    simp [Metric.mem_ball, dist_eq_norm]
  rw [← hpre]
  exact (mp_add_right y).setIntegral_preimage_emb (measurableEmbedding_addRight y) _ _

end H2

/-! ### The phase-difference bound -/

/-- `|e^{iθ} − 1| ≤ |θ|`. -/
theorem norm_exp_mul_I_sub_one_le (θ : ℝ) : ‖Complex.exp (θ * Complex.I) - 1‖ ≤ |θ| := by
  have h : ‖Complex.exp (θ * Complex.I) - 1‖ ^ 2 = 2 - 2 * Real.cos θ := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im, Complex.one_re, Complex.one_im, sub_zero]
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have hc := Real.one_sub_sq_div_two_le_cos (x := θ)
  have h2 : ‖Complex.exp (θ * Complex.I) - 1‖ ^ 2 ≤ |θ| ^ 2 := by
    rw [h, sq_abs]
    linarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (abs_nonneg _) two_ne_zero).1 h2

/-- `|𝐞(a) − 𝐞(b)| ≤ 2π|a − b|`. -/
theorem norm_fourierChar_sub_le (a b : ℝ) :
    ‖(𝐞 a : ℂ) - (𝐞 b : ℂ)‖ ≤ 2 * Real.pi * |a - b| := by
  have e : (𝐞 a : ℂ) - (𝐞 b : ℂ) = (𝐞 b : ℂ) * (Complex.exp (((2 * Real.pi * (a - b) : ℝ)) *
      Complex.I) - 1) := by
    rw [Real.fourierChar_apply, Real.fourierChar_apply, mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [e, norm_mul, Circle.norm_coe, one_mul]
  refine (norm_exp_mul_I_sub_one_le _).trans (le_of_eq ?_)
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]

/-- `|𝐞(a) − 𝐞(b)| ≤ 2`. -/
theorem norm_fourierChar_sub_le_two (a b : ℝ) : ‖(𝐞 a : ℂ) - (𝐞 b : ℂ)‖ ≤ 2 := by
  calc ‖(𝐞 a : ℂ) - (𝐞 b : ℂ)‖ ≤ ‖(𝐞 a : ℂ)‖ + ‖(𝐞 b : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [Circle.norm_coe, Circle.norm_coe]; norm_num

end Sobolev

end ReyesMath

namespace ReyesMath

namespace Sobolev

local notation "R2" => EuclideanSpace ℝ (Fin 2)

/-- `|e^{ia} − e^{ib}| ≤ |a − b|`. -/
theorem norm_exp_I_sub_exp_I_le (a b : ℝ) :
    ‖Complex.exp (a * Complex.I) - Complex.exp (b * Complex.I)‖ ≤ |a - b| := by
  have e : Complex.exp (a * Complex.I) - Complex.exp (b * Complex.I) =
      Complex.exp (b * Complex.I) * (Complex.exp (((a - b : ℝ) : ℂ) * Complex.I) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [e, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  exact norm_exp_mul_I_sub_one_le _

/-- `|e^{ia} − e^{ib}| ≤ 2`. -/
theorem norm_exp_I_sub_exp_I_le_two (a b : ℝ) :
    ‖Complex.exp (a * Complex.I) - Complex.exp (b * Complex.I)‖ ≤ 2 := by
  calc ‖Complex.exp (a * Complex.I) - Complex.exp (b * Complex.I)‖
      ≤ ‖Complex.exp (a * Complex.I)‖ + ‖Complex.exp (b * Complex.I)‖ := norm_sub_le _ _
    _ = 2 := by rw [Complex.norm_exp_ofReal_mul_I, Complex.norm_exp_ofReal_mul_I]; norm_num

/-- `‖ξ‖/(|2πξ|⁴ + 1)` is integrable on `ℝ²`. -/
theorem integrable_norm_div_quartic : Integrable fun ξ : R2 => ‖ξ‖ / (qS ξ ^ 2 + 1) := by
  set c : ℝ := (2 * Real.pi) ^ 4 with hc
  have hcpos : 0 < c := by positivity
  set C : ℝ := 8 * (1 / c + 1) with hC
  have hint := (integrable_one_add_norm (E := R2) (μ := volume) (r := 3)
    (by rw [finrank_euclideanSpace_fin]; norm_num)).const_mul C
  refine hint.mono' ?_ (Eventually.of_forall fun ξ => ?_)
  · exact Continuous.aestronglyMeasurable (continuous_norm.div (by unfold qS; fun_prop)
      fun ξ => by positivity)
  · set r := ‖ξ‖ with hr
    have hr0 : 0 ≤ r := norm_nonneg _
    have hq : qS ξ ^ 2 = c * r ^ 4 := by
      rw [qS, hc, ← hr]
      ring
    rw [Real.norm_of_nonneg (by rw [hq]; positivity), hq, Real.rpow_neg (by positivity)]
    have h3 : (1 + r) ^ (3 : ℝ) = (1 + r) ^ (3 : ℕ) := by
      exact_mod_cast Real.rpow_natCast (1 + r) 3
    rw [h3]
    have h1 : r * (1 + r) ^ 3 ≤ 8 * (1 + r ^ 4) := by
      have ha : r * (1 + r) ^ 3 ≤ (1 + r) * (1 + r) ^ 3 :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      have hb : (1 + r) ^ 4 ≤ 8 * (1 + r ^ 4) := by
        nlinarith [mul_nonneg (sq_nonneg (r - 1)) (by positivity : (0 : ℝ) ≤ 7 * r ^ 2 + 10 * r + 7)]
      nlinarith
    have h2 : 8 * (1 + r ^ 4) ≤ C * (c * r ^ 4 + 1) := by
      have hexp : C * (c * r ^ 4 + 1) = 8 * (r ^ 4 + 1) + 8 * (1 / c + c * r ^ 4) := by
        rw [hC]
        field_simp
        ring
      have : 0 ≤ 8 * (1 / c + c * r ^ 4) := by positivity
      linarith
    rw [div_le_iff₀ (by positivity)]
    rw [show C * ((1 + r) ^ 3)⁻¹ * (c * r ^ 4 + 1) = C * (c * r ^ 4 + 1) / (1 + r) ^ 3 by
      field_simp]
    rw [le_div_iff₀ (by positivity)]
    linarith

/-- `J = ∫_{ℝ²} ‖ξ‖/(|2πξ|⁴ + 1) dξ`. -/
noncomputable def holderJ : ℝ := ∫ ξ : R2, ‖ξ‖ / (qS ξ ^ 2 + 1)

theorem holderJ_nonneg : 0 ≤ holderJ :=
  integral_nonneg fun ξ => by have := qS_nonneg ξ; positivity

/-- The Hölder constant `C_H = 4πJ`. -/
noncomputable def CH : ℝ := 4 * Real.pi * holderJ

theorem CH_nonneg : 0 ≤ CH := by
  unfold CH
  have := holderJ_nonneg
  positivity

theorem integrable_weight_fourier (φ : SchwartzMap R2 ℂ) :
    Integrable fun ξ : R2 => (qS ξ ^ 2 + 1) * ‖𝓕 (⇑φ) ξ‖ ^ 2 := by
  have h1' : Integrable fun ξ : R2 => qS ξ ^ 2 * ‖𝓕 (⇑φ) ξ‖ ^ 2 := by
    refine (integrable_normSq (fS (lapS φ))).congr (Eventually.of_forall fun ξ => ?_)
    simp only
    rw [coe_fS, fourier_lapS, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (qS_nonneg ξ)]
    ring
  have h2' : Integrable fun ξ : R2 => ‖𝓕 (⇑φ) ξ‖ ^ 2 := by
    rw [← coe_fS]
    exact integrable_normSq (fS φ)
  simp_rw [add_mul, one_mul]
  exact h1'.add h2'

/-- **Hölder-`½` estimate on `𝓢(ℝ²)`:**
`|φ(x) − φ(y)|² ≤ C_H |x − y| (‖Δφ‖² + ‖φ‖²)`. -/
theorem holder_schwartz (φ : SchwartzMap R2 ℂ) (x y : R2) :
    ‖φ x - φ y‖ ^ 2 ≤ CH * ‖x - y‖ * (‖toL2 (lapS φ)‖ ^ 2 + ‖toL2 φ‖ ^ 2) := by
  have hFφ : Integrable (𝓕 (⇑φ)) := by rw [← coe_fS]; exact (fS φ).integrable
  have hinv : 𝓕⁻ (𝓕 (⇑φ)) = ⇑φ := Continuous.fourier_inversion φ.continuous φ.integrable hFφ
  have hcF : Continuous (𝓕 (⇑φ)) := continuous_fourier φ
  set w : R2 → ℝ := fun ξ => ‖Complex.exp (↑(2 * Real.pi * inner ℝ ξ x) * Complex.I) -
    Complex.exp (↑(2 * Real.pi * inner ℝ ξ y) * Complex.I)‖ with hw
  have hwc : Continuous w := by
    rw [hw]
    fun_prop
  have hw0 : ∀ ξ, 0 ≤ w ξ := fun ξ => norm_nonneg _
  have hw2 : ∀ ξ, w ξ ≤ 2 := fun ξ => norm_exp_I_sub_exp_I_le_two _ _
  have hwl : ∀ ξ, w ξ ≤ 2 * Real.pi * (‖ξ‖ * ‖x - y‖) := by
    intro ξ
    refine (norm_exp_I_sub_exp_I_le _ _).trans ?_
    rw [← mul_sub, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi), ← inner_sub_right]
    gcongr
    exact abs_real_inner_le_norm _ _
  have hint : ∀ z : R2, Integrable fun v : R2 =>
      Complex.exp (↑(2 * Real.pi * inner ℝ v z) * Complex.I) • 𝓕 (⇑φ) v := by
    intro z
    refine hFφ.norm.mono' (Continuous.aestronglyMeasurable (by fun_prop))
      (Eventually.of_forall fun v => ?_)
    rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]
  -- `|φ(x) − φ(y)| ≤ ∫ w |𝓕φ|`
  have h1 : ‖φ x - φ y‖ ≤ ∫ ξ, w ξ * ‖𝓕 (⇑φ) ξ‖ := by
    conv_lhs => rw [← hinv, Real.fourierIntegralInv_eq', Real.fourierIntegralInv_eq',
      ← integral_sub (hint x) (hint y)]
    refine le_trans (norm_integral_le_integral_norm _) (le_of_eq ?_)
    congr 1
    funext ξ
    rw [← sub_smul, norm_smul]
  -- AM–GM against the weight `W = |2πξ|⁴ + 1`
  have hW : ∀ ξ : R2, 0 < qS ξ ^ 2 + 1 := fun ξ => by positivity
  have hA : Integrable fun ξ : R2 => w ξ ^ 2 / (qS ξ ^ 2 + 1) := by
    refine ((integrable_inv_quartic one_pos).const_mul 4).mono'
      ((hwc.pow 2).div (by unfold qS; fun_prop) fun ξ => (hW ξ).ne').aestronglyMeasurable
      (Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_of_nonneg (by have := hW ξ; positivity), mul_one_div]
    exact div_le_div_of_nonneg_right (by nlinarith [hw0 ξ, hw2 ξ]) (hW ξ).le
  have h2 : ∀ t : ℝ, 0 < t → ∫ ξ, w ξ * ‖𝓕 (⇑φ) ξ‖ ≤
      (t * (∫ ξ, w ξ ^ 2 / (qS ξ ^ 2 + 1)) + (∫ ξ, (qS ξ ^ 2 + 1) * ‖𝓕 (⇑φ) ξ‖ ^ 2) / t) / 2 := by
    intro t ht
    have hR : Integrable fun ξ : R2 =>
        (t * (w ξ ^ 2 / (qS ξ ^ 2 + 1)) + (qS ξ ^ 2 + 1) * ‖𝓕 (⇑φ) ξ‖ ^ 2 / t) / 2 :=
      ((hA.const_mul t).add ((integrable_weight_fourier φ).div_const t)).div_const 2
    have hL : Integrable fun ξ : R2 => w ξ * ‖𝓕 (⇑φ) ξ‖ :=
      (hFφ.norm.const_mul 2).mono' (hwc.mul hcF.norm).aestronglyMeasurable
        (Eventually.of_forall fun ξ => by
          rw [Real.norm_of_nonneg (mul_nonneg (hw0 ξ) (norm_nonneg _))]
          exact mul_le_mul_of_nonneg_right (hw2 ξ) (norm_nonneg _))
    calc ∫ ξ, w ξ * ‖𝓕 (⇑φ) ξ‖
        ≤ ∫ ξ, (t * (w ξ ^ 2 / (qS ξ ^ 2 + 1)) + (qS ξ ^ 2 + 1) * ‖𝓕 (⇑φ) ξ‖ ^ 2 / t) / 2 :=
          integral_mono hL hR fun ξ => mul_le_amgm (hW ξ) ht
      _ = (t * (∫ ξ, w ξ ^ 2 / (qS ξ ^ 2 + 1)) +
            (∫ ξ, (qS ξ ^ 2 + 1) * ‖𝓕 (⇑φ) ξ‖ ^ 2) / t) / 2 := by
          rw [integral_div, integral_add (hA.const_mul t) ((integrable_weight_fourier φ).div_const t),
            integral_const_mul, integral_div]
  have hBeq : ∫ ξ, (qS ξ ^ 2 + 1) * ‖𝓕 (⇑φ) ξ‖ ^ 2 = ‖toL2 (lapS φ)‖ ^ 2 + ‖toL2 φ‖ ^ 2 := by
    rw [integral_weight_fourier, one_mul]
  have hAle : ∫ ξ, w ξ ^ 2 / (qS ξ ^ 2 + 1) ≤ CH * ‖x - y‖ := by
    have hpt : ∀ ξ : R2, w ξ ^ 2 / (qS ξ ^ 2 + 1) ≤
        4 * Real.pi * ‖x - y‖ * (‖ξ‖ / (qS ξ ^ 2 + 1)) := by
      intro ξ
      rw [mul_div_assoc']
      refine div_le_div_of_nonneg_right ?_ (hW ξ).le
      have := hwl ξ
      have := hw2 ξ
      have := hw0 ξ
      nlinarith
    calc ∫ ξ, w ξ ^ 2 / (qS ξ ^ 2 + 1)
        ≤ ∫ ξ, 4 * Real.pi * ‖x - y‖ * (‖ξ‖ / (qS ξ ^ 2 + 1)) :=
          integral_mono hA (integrable_norm_div_quartic.const_mul _) hpt
      _ = CH * ‖x - y‖ := by
          rw [integral_const_mul, CH, holderJ]
          ring
  have hx0 : 0 ≤ ∫ ξ, w ξ * ‖𝓕 (⇑φ) ξ‖ :=
    integral_nonneg fun ξ => mul_nonneg (hw0 ξ) (norm_nonneg _)
  have hA0 : 0 ≤ ∫ ξ, w ξ ^ 2 / (qS ξ ^ 2 + 1) :=
    integral_nonneg fun ξ => by have := hW ξ; positivity
  have hB0 : 0 ≤ ∫ ξ, (qS ξ ^ 2 + 1) * ‖𝓕 (⇑φ) ξ‖ ^ 2 :=
    integral_nonneg fun ξ => by have := hW ξ; positivity
  have key := sq_le_of_forall_amgm hx0 hA0 hB0 h2
  calc ‖φ x - φ y‖ ^ 2 ≤ (∫ ξ, w ξ * ‖𝓕 (⇑φ) ξ‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ (∫ ξ, w ξ ^ 2 / (qS ξ ^ 2 + 1)) * ∫ ξ, (qS ξ ^ 2 + 1) * ‖𝓕 (⇑φ) ξ‖ ^ 2 := key
    _ ≤ CH * ‖x - y‖ * (‖toL2 (lapS φ)‖ ^ 2 + ‖toL2 φ‖ ^ 2) := by
        rw [hBeq]
        exact mul_le_mul_of_nonneg_right hAle (by positivity)

end Sobolev

end ReyesMath

namespace ReyesMath

namespace Sobolev

variable {d : ℕ}

local notation "Rd" => EuclideanSpace ℝ (Fin d)

local notation "R2" => EuclideanSpace ℝ (Fin 2)

/-- The indicator of the ball `B(x, r)` as an element of `L²`. -/
noncomputable def ballInd (x : Rd) (r : ℝ) : L2 d :=
  indicatorConstLp 2 Metric.isOpen_ball.measurableSet
    (measure_ball_lt_top (μ := volume) (x := x) (r := r)).ne (1 : ℂ)

theorem inner_ballInd (x : Rd) (r : ℝ) (f : L2 d) :
    inner ℂ (ballInd x r) f = ∫ z in Metric.ball x r, f z :=
  L2.inner_indicatorConstLp_one _ _ f

theorem setIntegral_toL2 (φ : SchwartzMap Rd ℂ) (s : Set Rd) (hs : MeasurableSet s) :
    ∫ z in s, (toL2 φ : Rd → ℂ) z = ∫ z in s, φ z :=
  setIntegral_congr_ae hs (by filter_upwards [coeFn_toL2 φ] with z hz _; exact hz)

/-- The area `|B(x, r)| = πr²` of a disc does not depend on its center. -/
noncomputable def vol2 (r : ℝ) : ℝ := (volume (Metric.ball (0 : R2) r)).toReal

theorem volume_real_ball (x : R2) (r : ℝ) : volume.real (Metric.ball x r) = vol2 r := by
  rw [vol2, Measure.real, EuclideanSpace.volume_ball_fin_two, EuclideanSpace.volume_ball_fin_two]

theorem vol2_pos {r : ℝ} (hr : 0 < r) : 0 < vol2 r :=
  ENNReal.toReal_pos (Metric.measure_ball_pos volume _ hr).ne' measure_ball_lt_top.ne

/-- **Ball-average form of the Hölder estimate on `𝓢(ℝ²)`.** -/
theorem ball_avg_schwartz (φ : SchwartzMap R2 ℂ) (x : R2) (r : ℝ) :
    ‖vol2 r • φ x - ∫ z in Metric.ball x r, φ z‖ ≤
      vol2 r * Real.sqrt (CH * r * (‖toL2 (lapS φ)‖ ^ 2 + ‖toL2 φ‖ ^ 2)) := by
  have hc : IntegrableOn (fun _ : R2 => φ x) (Metric.ball x r) volume :=
    integrableOn_const measure_ball_lt_top.ne
  have hφ : IntegrableOn (⇑φ) (Metric.ball x r) volume := φ.integrable.integrableOn
  rw [← volume_real_ball x r, ← setIntegral_const (φ x), ← integral_sub hc hφ]
  rw [mul_comm]
  refine norm_setIntegral_le_of_norm_le_const measure_ball_lt_top fun z hz => ?_
  have h := holder_schwartz φ x z
  have hz' : ‖x - z‖ ≤ r := by
    rw [Metric.mem_ball, dist_eq_norm] at hz
    rw [norm_sub_rev]
    exact hz.le
  refine Real.le_sqrt_of_sq_le (h.trans ?_)
  have := CH_nonneg
  gcongr

namespace H2

/-- **Ball-average Hölder estimate on `H²(ℝ²)`:** for a.e. `x` and every `r > 0`,
`‖|B_r| u(x) − ∫_{B(x,r)} u‖ ≤ |B_r| √(C_H r (D(u) + M(u)))`. -/
theorem ae_ball_avg (U : H2 2) : ∀ᵐ x ∂(volume : Measure R2), ∀ r : ℝ, 0 < r →
    ‖vol2 r • U.val x - inner ℂ (ballInd x r) U.val‖ ≤
      vol2 r * Real.sqrt (CH * r * (D U + M U)) := by
  obtain ⟨φ, h0, -, h2⟩ := U.approx
  obtain ⟨ns, hmono, hns⟩ := (tendstoInMeasure_of_tendsto_Lp h0).exists_seq_tendsto_ae
  have hcoe : ∀ᵐ x ∂(volume : Measure R2), ∀ n, (toL2 (φ n) : R2 → ℂ) x = φ n x :=
    ae_all_iff.2 fun n => coeFn_toL2 (φ n)
  have hs : Tendsto ns atTop atTop := hmono.tendsto_atTop
  filter_upwards [hns, hcoe] with x hx hc
  intro r hr
  have hL : Tendsto (fun i => ‖vol2 r • φ (ns i) x - inner ℂ (ballInd x r) (toL2 (φ (ns i)))‖)
      atTop (𝓝 ‖vol2 r • U.val x - inner ℂ (ballInd x r) U.val‖) := by
    have h1 : Tendsto (fun i => φ (ns i) x) atTop (𝓝 (U.val x)) := by
      simpa only [hc] using hx
    have h2' : Tendsto (fun i => inner ℂ (ballInd x r) (toL2 (φ (ns i)))) atTop
        (𝓝 (inner ℂ (ballInd x r) U.val)) :=
      (tendsto_const_nhds (x := ballInd x r)).inner (h0.comp hs)
    exact ((h1.const_smul _).sub h2').norm
  have hR : Tendsto (fun i => vol2 r * Real.sqrt (CH * r * (‖toL2 (lapS (φ (ns i)))‖ ^ 2 +
      ‖toL2 (φ (ns i))‖ ^ 2))) atTop (𝓝 (vol2 r * Real.sqrt (CH * r * (D U + M U)))) :=
    (((((h2.comp hs).norm).pow 2).add (((h0.comp hs).norm).pow 2)).const_mul (CH * r)).sqrt.const_mul _
  refine le_of_tendsto_of_tendsto' hL hR fun i => ?_
  have := ball_avg_schwartz (φ (ns i)) x r
  rwa [inner_ballInd, setIntegral_toL2 _ _ Metric.isOpen_ball.measurableSet]

/-- Pointwise consequence: `|u(x)| ≤ |∫_{B(x,r)} u|/|B_r| + √(C_H r (D(u) + M(u)))`. -/
theorem ae_norm_le_avg (U : H2 2) : ∀ᵐ x ∂(volume : Measure R2), ∀ r : ℝ, 0 < r →
    ‖U.val x‖ ≤ ‖inner ℂ (ballInd x r) U.val‖ / vol2 r + Real.sqrt (CH * r * (D U + M U)) := by
  filter_upwards [ae_ball_avg U] with x hx
  intro r hr
  have hV := vol2_pos hr
  have h := hx r hr
  have h1 : vol2 r * ‖U.val x‖ ≤ ‖inner ℂ (ballInd x r) U.val‖ +
      vol2 r * Real.sqrt (CH * r * (D U + M U)) := by
    have : ‖vol2 r • U.val x‖ ≤ ‖vol2 r • U.val x - inner ℂ (ballInd x r) U.val‖ +
        ‖inner ℂ (ballInd x r) U.val‖ := norm_le_norm_sub_add _ _
    rw [norm_smul, Real.norm_of_nonneg hV.le] at this
    linarith
  rw [div_add' _ _ _ hV.ne', le_div_iff₀ hV]
  linarith

/-- `∫_{B(0,r)} u(· + y) = ∫_{B(y,r)} u`, in inner-product form. -/
theorem inner_ballInd_translate (y : R2) (U : H2 2) (r : ℝ) :
    inner ℂ (ballInd 0 r) (translate y U).val = inner ℂ (ballInd y r) U.val := by
  rw [inner_ballInd, inner_ballInd, setIntegral_ball_translate]

/-- An a.e. bound `|u|² ≤ L` gives `Q(u) ≤ L M(u)`. -/
theorem Q_le_of_ae_bound (U : H2 2) {L : ℝ} (h : ∀ᵐ x ∂(volume : Measure R2), ‖U.val x‖ ^ 2 ≤ L) :
    Q U ≤ L * M U := by
  rw [M_eq_integral, ← integral_const_mul]
  refine integral_mono_ae (integrable_Q U) ((integrable_sq_val U).const_mul L) ?_
  filter_upwards [h] with x hx
  rw [show ‖U.val x‖ ^ 4 = ‖U.val x‖ ^ 2 * ‖U.val x‖ ^ 2 by ring]
  exact mul_le_mul_of_nonneg_right hx (sq_nonneg _)

/-- **Local non-vanishing.**  If `M(u) > 0`, `Q(u) ≥ q₀ > 0`, and the radius `r` is so small
that `C_H r (D(u) + M(u)) ≤ q₀/(9M(u))`, then some disc `B(y, r)` carries
`|∫_{B(y,r)} u| ≥ |B_r| √(q₀/M(u))/3`. -/
theorem exists_ball_avg {U : H2 2} {q₀ r : ℝ} (hM : 0 < M U) (hq : 0 < q₀) (hQ : q₀ ≤ Q U)
    (hr : 0 < r) (hsmall : CH * r * (D U + M U) ≤ q₀ / (9 * M U)) :
    ∃ y : R2, vol2 r * (Real.sqrt (q₀ / M U) / 3) ≤ ‖inner ℂ (ballInd y r) U.val‖ := by
  by_contra hcon
  push_neg at hcon
  set η := Real.sqrt (q₀ / M U) / 3 with hη
  have hη0 : 0 ≤ η := by positivity
  have hsq : Real.sqrt (CH * r * (D U + M U)) ≤ η := by
    rw [hη, show q₀ / (9 * M U) = (q₀ / M U) / 9 by field_simp] at *
    calc Real.sqrt (CH * r * (D U + M U)) ≤ Real.sqrt ((q₀ / M U) / 9) := Real.sqrt_le_sqrt hsmall
      _ = Real.sqrt (q₀ / M U) / 3 := by
        rw [Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 9),
          show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hV := vol2_pos hr
  have hb : ∀ᵐ x ∂(volume : Measure R2), ‖U.val x‖ ^ 2 ≤ (2 * η) ^ 2 := by
    filter_upwards [ae_norm_le_avg U] with x hx
    have h1 := hx r hr
    have h2 : ‖inner ℂ (ballInd x r) U.val‖ / vol2 r ≤ η := by
      rw [div_le_iff₀ hV]
      linarith [(hcon x).le]
    exact pow_le_pow_left₀ (norm_nonneg _) (by linarith) 2
  have hQle := Q_le_of_ae_bound U hb
  have hη2 : (2 * η) ^ 2 * M U = 4 / 9 * q₀ := by
    rw [hη, mul_pow, div_pow, Real.sq_sqrt (by positivity)]
    field_simp
    ring
  linarith

end H2

end Sobolev

end ReyesMath

namespace ReyesMath

namespace WeakCompact

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [TopologicalSpace.SeparableSpace E]

omit [CompleteSpace E] [TopologicalSpace.SeparableSpace E] in
/-- Convergence of `⟪xₙ, z⟫` on a dense set of `z` and boundedness give convergence for every
`z`. -/
theorem exists_tendsto_inner_of_dense {x : ℕ → E} {R : ℝ} (hR : ∀ n, ‖x n‖ ≤ R) {e : ℕ → E}
    (he : DenseRange e) (hconv : ∀ k, ∃ a, Tendsto (fun n => inner ℂ (x n) (e k)) atTop (𝓝 a))
    (z : E) : ∃ l, Tendsto (fun n => inner ℂ (x n) z) atTop (𝓝 l) := by
  refine cauchySeq_tendsto_of_complete (Metric.cauchySeq_iff.2 fun ε hε => ?_)
  have hR0 : 0 ≤ R := (norm_nonneg _).trans (hR 0)
  obtain ⟨k, hk⟩ : ∃ k, dist z (e k) < ε / (3 * (R + 1)) :=
    (he.exists_dist_lt z (by positivity))
  obtain ⟨a, ha⟩ := hconv k
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 ha.cauchySeq (ε / 3) (by positivity)
  refine ⟨N, fun m hm n hn => ?_⟩
  have hsplit : ∀ p, dist (inner ℂ (x p) z) (inner ℂ (x p) (e k)) ≤ R * dist z (e k) := by
    intro p
    rw [dist_eq_norm, dist_eq_norm, ← inner_sub_right]
    exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hR p) (norm_nonneg _))
  have h1 := hsplit m
  have h2 := hsplit n
  have h3 := hN m hm n hn
  have hRk : R * dist z (e k) ≤ ε / 3 := by
    have : R * dist z (e k) ≤ (R + 1) * (ε / (3 * (R + 1))) := by
      gcongr
      · linarith
    calc R * dist z (e k) ≤ (R + 1) * (ε / (3 * (R + 1))) := this
      _ = ε / 3 := by field_simp
  calc dist (inner ℂ (x m) z) (inner ℂ (x n) z)
      ≤ dist (inner ℂ (x m) z) (inner ℂ (x m) (e k)) +
          dist (inner ℂ (x m) (e k)) (inner ℂ (x n) (e k)) +
          dist (inner ℂ (x n) (e k)) (inner ℂ (x n) z) := dist_triangle4 _ _ _ _
    _ < ε / 3 + ε / 3 + ε / 3 := by
        rw [dist_comm (inner ℂ (x n) (e k))]
        have : R * dist z (e k) ≤ ε / 3 := hRk
        linarith
    _ = ε := by ring

/-- **Weak sequential compactness of bounded sets** in a separable complex Hilbert space,
simultaneously for a countable family of bounded sequences: there are a common subsequence and
weak limits `yᵢ` with `⟪z, x_{φ n, i}⟫ → ⟪z, yᵢ⟫` for every `z`. -/
theorem exists_weak_subseq {ι : Type*} [Countable ι] (x : ℕ → ι → E) {R : ℝ}
    (hR : ∀ n i, ‖x n i‖ ≤ R) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ y : ι → E, ∀ i z,
      Tendsto (fun n => inner ℂ z (x (φ n) i)) atTop (𝓝 (inner ℂ z (y i))) := by
  set e := TopologicalSpace.denseSeq E with he_def
  have he : DenseRange e := TopologicalSpace.denseRange_denseSeq E
  set f : ℕ → (ℕ × ι → ℂ) := fun n p => inner ℂ (x n p.2) (e p.1) with hf
  have hK : IsCompact (Set.pi univ fun p : ℕ × ι => Metric.closedBall (0 : ℂ) (R * ‖e p.1‖)) :=
    isCompact_univ_pi fun p => isCompact_closedBall _ _
  have hmem : ∀ n, f n ∈ Set.pi univ fun p : ℕ × ι => Metric.closedBall (0 : ℂ) (R * ‖e p.1‖) := by
    intro n p _
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hR n p.2) (norm_nonneg _))
  obtain ⟨a, -, φ, hφ, hlim⟩ := hK.tendsto_subseq hmem
  rw [tendsto_pi_nhds] at hlim
  refine ⟨φ, hφ, ?_⟩
  have hex : ∀ i z, ∃ l, Tendsto (fun n => inner ℂ (x (φ n) i) z) atTop (𝓝 l) := fun i z =>
    exists_tendsto_inner_of_dense (fun n => hR (φ n) i) he (fun k => ⟨a (k, i), hlim (k, i)⟩) z
  choose l hl using hex
  have hT : ∀ i, Tendsto (fun n z => innerSL ℂ (x (φ n) i) z) atTop (𝓝 (l i)) := fun i =>
    tendsto_pi_nhds.2 fun z => by simpa only [innerSL_apply] using hl i z
  let ℓ : ι → StrongDual ℂ E := fun i => continuousLinearMapOfTendsto _ (hT i)
  have hℓ : ∀ i z, ℓ i z = l i z := fun i z => rfl
  refine ⟨fun i => (toDual ℂ E).symm (ℓ i), fun i z => ?_⟩
  have h1 : inner ℂ ((toDual ℂ E).symm (ℓ i)) z = l i z := by
    rw [toDual_symm_apply, hℓ]
  have h2 := (Complex.continuous_conj.tendsto _).comp (hl i z)
  rw [← inner_conj_symm, h1]
  refine h2.congr fun n => ?_
  simp only [Function.comp_apply, inner_conj_symm]

end WeakCompact

end ReyesMath

namespace ReyesMath

namespace Sobolev

variable {d : ℕ}

local notation "Rd" => EuclideanSpace ℝ (Fin d)

/-! ### `H²` as a closed subspace of `L² × L² × (L²)^d` -/

/-- Packing `(u, Δu, ∇u)` into one family indexed by `Option (Option (Fin d))`. -/
def comp3 (a b : L2 d) (c : Fin d → L2 d) : Option (Option (Fin d)) → L2 d
  | none => a
  | some none => b
  | some (some i) => c i

/-- The product Hilbert space `L² × L² × (L²)^d`. -/
abbrev E3 (d : ℕ) := PiLp 2 fun _ : Option (Option (Fin d)) => L2 d

theorem comp3_add (a b a' b' : L2 d) (c c' : Fin d → L2 d) :
    comp3 (a + a') (b + b') (c + c') = comp3 a b c + comp3 a' b' c' := by
  funext o
  rcases o with _ | _ | i <;> rfl

theorem comp3_smul (r : ℂ) (a b : L2 d) (c : Fin d → L2 d) :
    comp3 (r • a) (r • b) (r • c) = r • comp3 a b c := by
  funext o
  rcases o with _ | _ | i <;> rfl

/-- The Schwartz graph `φ ↦ (φ, Δφ, ∇φ)` as a linear map into `E3`. -/
noncomputable def graphS : SchwartzMap Rd ℂ →ₗ[ℂ] E3 d where
  toFun φ := WithLp.toLp 2 (comp3 (toL2 φ) (toL2 (lapS φ)) fun i => toL2 (dS i φ))
  map_add' φ ψ := by
    simp only [map_add]
    rw [← WithLp.toLp_add, ← comp3_add]
    rfl
  map_smul' r φ := by
    simp only [map_smul, RingHom.id_apply]
    rw [← WithLp.toLp_smul, ← comp3_smul]
    rfl

/-- The graph subspace `{(φ, Δφ, ∇φ) : φ ∈ 𝓢}`. -/
noncomputable def graphSub (d : ℕ) : Submodule ℂ (E3 d) := LinearMap.range (graphS (d := d))

namespace H2

/-- The embedding `u ↦ (u, Δu, ∇u)` of `H²` into `E3`. -/
noncomputable def emb (U : H2 d) : E3 d := WithLp.toLp 2 (comp3 U.val U.lap U.grad)

theorem tendsto_E3 {F : ℕ → E3 d} {a b : L2 d} {c : Fin d → L2 d}
    (h0 : Tendsto (fun n => F n none) atTop (𝓝 a))
    (h1 : Tendsto (fun n => F n (some none)) atTop (𝓝 b))
    (h2 : ∀ i, Tendsto (fun n => F n (some (some i))) atTop (𝓝 (c i))) :
    Tendsto F atTop (𝓝 (WithLp.toLp 2 (comp3 a b c))) := by
  have : Tendsto (fun n => WithLp.ofLp (F n)) atTop (𝓝 (comp3 a b c)) := by
    rw [tendsto_pi_nhds]
    intro o
    rcases o with _ | _ | i
    · exact h0
    · exact h1
    · exact h2 i
  exact ((PiLp.continuous_toLp 2 _).tendsto _).comp this

theorem emb_mem_closure (U : H2 d) : emb U ∈ (graphSub d).topologicalClosure := by
  obtain ⟨φ, h0, h1, h2⟩ := U.approx
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
  refine mem_closure_of_tendsto (tendsto_E3 (F := fun n => graphS (φ n)) h0 h2 h1) ?_
  exact Eventually.of_forall fun n => ⟨φ n, rfl⟩

theorem exists_of_mem_closure {e : E3 d} (he : e ∈ (graphSub d).topologicalClosure) :
    ∃ U : H2 d, emb U = e := by
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at he
  obtain ⟨g, hg, hlim⟩ := mem_closure_iff_seq_limit.1 he
  choose φ hφ using fun n => (hg n : g n ∈ LinearMap.range (graphS (d := d)))
  have hc : ∀ o, Tendsto (fun n => g n o) atTop (𝓝 (e o)) := fun o =>
    ((PiLp.continuous_apply 2 _ o).tendsto e).comp hlim
  refine ⟨⟨e none, fun i => e (some (some i)), e (some none), φ, ?_, fun i => ?_, ?_⟩, ?_⟩
  · simpa only [← hφ] using hc none
  · simpa only [← hφ] using hc (some (some i))
  · simpa only [← hφ] using hc (some none)
  · simp only [emb]
    ext o
    rcases o with _ | _ | i <;> rfl

/-- **Weak closedness of `H²`:** if `Uₙ ∈ H²` and the components `uₙ, Δuₙ, ∇uₙ` converge weakly
in `L²` to `u, ℓ, g`, then `(u, g, ℓ)` is (the data of) an element of `H²`. -/
theorem exists_weak_limit (U : ℕ → H2 d) {u l : L2 d} {g : Fin d → L2 d}
    (h0 : ∀ z, Tendsto (fun n => inner ℂ z (U n).val) atTop (𝓝 (inner ℂ z u)))
    (h1 : ∀ i z, Tendsto (fun n => inner ℂ z ((U n).grad i)) atTop (𝓝 (inner ℂ z (g i))))
    (h2 : ∀ z, Tendsto (fun n => inner ℂ z (U n).lap) atTop (𝓝 (inner ℂ z l))) :
    ∃ V : H2 d, V.val = u ∧ V.grad = g ∧ V.lap = l := by
  set e : E3 d := WithLp.toLp 2 (comp3 u l g) with he
  have hmem : e ∈ (graphSub d)ᗮᗮ := by
    rw [Submodule.mem_orthogonal]
    intro w hw
    have hzero : ∀ n, inner ℂ w (emb (U n)) = 0 := by
      intro n
      have := emb_mem_closure (U n)
      rw [← Submodule.orthogonal_orthogonal_eq_closure] at this
      exact Submodule.inner_right_of_mem_orthogonal hw this
    have hlim : Tendsto (fun n => inner ℂ w (emb (U n))) atTop (𝓝 (inner ℂ w e)) := by
      simp only [PiLp.inner_apply]
      refine tendsto_finset_sum _ fun o _ => ?_
      rcases o with _ | _ | i
      · exact h0 (w none)
      · exact h2 (w (some none))
      · exact h1 i (w (some (some i)))
    simp only [hzero] at hlim
    exact tendsto_nhds_unique hlim tendsto_const_nhds
  rw [Submodule.orthogonal_orthogonal_eq_closure] at hmem
  obtain ⟨V, hV⟩ := exists_of_mem_closure hmem
  have hc : ∀ o, emb V o = e o := fun o => by rw [hV]
  refine ⟨V, hc none, funext fun i => hc (some (some i)), hc (some none)⟩

end H2

end Sobolev

end ReyesMath

namespace ReyesMath

namespace Sobolev

local notation "R2" => EuclideanSpace ℝ (Fin 2)

namespace H2

/-- **Weakly null bounded sequences in `H²(ℝ²)` converge to `0` almost everywhere.**  This is
the pointwise form of local compactness: the ball-average Hölder estimate turns weak
convergence into convergence at a.e. point. -/
theorem ae_tendsto_zero_of_weak (V : ℕ → H2 2) {B : ℝ} (hB : ∀ n, D (V n) + M (V n) ≤ B)
    (hw : ∀ z, Tendsto (fun n => inner ℂ z (V n).val) atTop (𝓝 0)) :
    ∀ᵐ x ∂(volume : Measure R2), Tendsto (fun n => (V n).val x) atTop (𝓝 0) := by
  have hB0 : 0 ≤ B := (add_nonneg (D_nonneg _) (M_nonneg _)).trans (hB 0)
  have hCH := CH_nonneg
  filter_upwards [ae_all_iff.2 fun n => ae_norm_le_avg (V n)] with x hx
  rw [tendsto_zero_iff_norm_tendsto_zero, Metric.tendsto_atTop]
  intro ε hε
  set r : ℝ := ε ^ 2 / (4 * (CH * B + 1)) with hr
  have hrpos : 0 < r := by positivity
  have hsq : ∀ n, Real.sqrt (CH * r * (D (V n) + M (V n))) ≤ ε / 2 := by
    intro n
    have h1 : CH * r * (D (V n) + M (V n)) ≤ (ε / 2) ^ 2 := by
      calc CH * r * (D (V n) + M (V n)) ≤ CH * r * B := by gcongr; exact hB n
        _ ≤ (CH * B + 1) * r := by nlinarith
        _ = (ε / 2) ^ 2 := by rw [hr]; field_simp; ring
    calc Real.sqrt (CH * r * (D (V n) + M (V n))) ≤ Real.sqrt ((ε / 2) ^ 2) := Real.sqrt_le_sqrt h1
      _ = ε / 2 := Real.sqrt_sq (by positivity)
  have hV := vol2_pos hrpos
  have hev : ∀ᶠ n in atTop, ‖inner ℂ (ballInd x r) (V n).val‖ < ε / 2 * vol2 r := by
    have := (hw (ballInd x r)).norm
    rw [norm_zero] at this
    exact this.eventually (gt_mem_nhds (by positivity))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_zero_right, norm_norm]
  have h1 := hx n r hrpos
  have h2 : ‖inner ℂ (ballInd x r) (V n).val‖ / vol2 r < ε / 2 := by
    rw [div_lt_iff₀ hV]
    exact hN n hn
  linarith [hsq n]

end H2

end Sobolev

/-! ### The Brezis–Lieb lemma -/

namespace BrezisLieb

/-- The elementary inequality behind Brezis–Lieb: for `p ≥ 1` and `ε > 0` there is `C` with
`|‖a + b‖ᵖ − ‖a‖ᵖ| ≤ ε‖a‖ᵖ + C‖b‖ᵖ`. -/
theorem pow_norm_add_sub_le {p : ℕ} (hp : 1 ≤ p) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a b : ℂ, |‖a + b‖ ^ p - ‖a‖ ^ p| ≤ ε * ‖a‖ ^ p + C * ‖b‖ ^ p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  set δ : ℝ := min 1 (ε / (p * 2 ^ (p - 1))) with hδ
  have hpos : (0 : ℝ) < p * 2 ^ (p - 1) := by positivity
  have hδpos : 0 < δ := lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδε : δ * (p * 2 ^ (p - 1)) ≤ ε := by
    have : δ ≤ ε / (p * 2 ^ (p - 1)) := min_le_right _ _
    calc δ * (p * 2 ^ (p - 1)) ≤ ε / (p * 2 ^ (p - 1)) * (p * 2 ^ (p - 1)) :=
          mul_le_mul_of_nonneg_right this hpos.le
      _ = ε := div_mul_cancel₀ _ hpos.ne'
  refine ⟨p * (1 / δ + 1) ^ (p - 1), by positivity, fun a b => ?_⟩
  have hs : 0 ≤ ‖a‖ := norm_nonneg _
  have ht : 0 ≤ ‖b‖ := norm_nonneg _
  have hρ : 0 ≤ ‖a + b‖ := norm_nonneg _
  have hρs : |‖a + b‖ - ‖a‖| ≤ ‖b‖ := by
    have := abs_norm_sub_norm_le (a + b) a
    rwa [add_sub_cancel_left] at this
  have hmax : max ‖a + b‖ ‖a‖ ≤ ‖a‖ + ‖b‖ := max_le (norm_add_le _ _) (by linarith)
  have key : |‖a + b‖ ^ p - ‖a‖ ^ p| ≤ ‖b‖ * p * (‖a‖ + ‖b‖) ^ (p - 1) := by
    have h := abs_pow_sub_pow_le ‖a + b‖ ‖a‖ p
    rw [abs_of_nonneg hρ, abs_of_nonneg hs] at h
    refine h.trans ?_
    gcongr
  have hsp : ∀ s : ℝ, s * s ^ (p - 1) = s ^ p := fun s => by
    rw [← pow_succ', Nat.sub_add_cancel hp]
  rcases le_or_gt ‖b‖ (δ * ‖a‖) with hts | hts
  · have h1 : ‖a‖ + ‖b‖ ≤ 2 * ‖a‖ := by nlinarith
    have h2 : ‖b‖ * p * (‖a‖ + ‖b‖) ^ (p - 1) ≤ ε * ‖a‖ ^ p := by
      calc ‖b‖ * p * (‖a‖ + ‖b‖) ^ (p - 1) ≤ (δ * ‖a‖) * p * (2 * ‖a‖) ^ (p - 1) := by gcongr
        _ = δ * (p * 2 ^ (p - 1)) * (‖a‖ * ‖a‖ ^ (p - 1)) := by rw [mul_pow]; ring
        _ = δ * (p * 2 ^ (p - 1)) * ‖a‖ ^ p := by rw [hsp]
        _ ≤ ε * ‖a‖ ^ p := mul_le_mul_of_nonneg_right hδε (by positivity)
    have : 0 ≤ p * (1 / δ + 1) ^ (p - 1) * ‖b‖ ^ p := by positivity
    linarith
  · have hs' : ‖a‖ ≤ ‖b‖ / δ := by
      rw [le_div_iff₀ hδpos]
      linarith [mul_comm δ ‖a‖]
    have h2 : ‖b‖ * p * (‖a‖ + ‖b‖) ^ (p - 1) ≤ p * (1 / δ + 1) ^ (p - 1) * ‖b‖ ^ p := by
      calc ‖b‖ * p * (‖a‖ + ‖b‖) ^ (p - 1) ≤ ‖b‖ * p * (‖b‖ / δ + ‖b‖) ^ (p - 1) := by gcongr
        _ = p * (1 / δ + 1) ^ (p - 1) * (‖b‖ * ‖b‖ ^ (p - 1)) := by
            rw [show ‖b‖ / δ + ‖b‖ = (1 / δ + 1) * ‖b‖ by ring, mul_pow]
            ring
        _ = p * (1 / δ + 1) ^ (p - 1) * ‖b‖ ^ p := by rw [hsp]
    have : 0 ≤ ε * ‖a‖ ^ p := by positivity
    linarith

/-- **Brezis–Lieb lemma.**  If `vₙ → 0` a.e., `∫‖vₙ‖ᵖ ≤ B` and `‖u‖ᵖ` is integrable, then
`∫‖vₙ + u‖ᵖ − ∫‖vₙ‖ᵖ − ∫‖u‖ᵖ → 0`. -/
theorem brezis_lieb {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℕ} (hp : 1 ≤ p)
    {v : ℕ → α → ℂ} {u : α → ℂ} {B : ℝ}
    (hv : ∀ n, AEStronglyMeasurable (v n) μ) (hu : AEStronglyMeasurable u μ)
    (hvp : ∀ n, Integrable (fun x => ‖v n x‖ ^ p) μ) (hup : Integrable (fun x => ‖u x‖ ^ p) μ)
    (hwp : ∀ n, Integrable (fun x => ‖v n x + u x‖ ^ p) μ)
    (hB : ∀ n, ∫ x, ‖v n x‖ ^ p ∂μ ≤ B)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => v n x) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, ‖v n x + u x‖ ^ p ∂μ - ∫ x, ‖v n x‖ ^ p ∂μ - ∫ x, ‖u x‖ ^ p ∂μ)
      atTop (𝓝 0) := by
  have hp0 : p ≠ 0 := by omega
  have hB0 : 0 ≤ B := (integral_nonneg fun x => by positivity).trans (hB 0)
  rw [Metric.tendsto_atTop]
  intro δ hδ
  set ε := δ / (2 * (B + 1)) with hε
  have hεpos : 0 < ε := by positivity
  obtain ⟨C, hC0, hC⟩ := pow_norm_add_sub_le hp hεpos
  obtain ⟨h, hh⟩ : ∃ h : ℕ → α → ℝ, h = fun n x =>
      max (|‖v n x + u x‖ ^ p - ‖v n x‖ ^ p - ‖u x‖ ^ p| - ε * ‖v n x‖ ^ p) 0 := ⟨_, rfl⟩
  have hhx : ∀ n x, h n x =
      max (|‖v n x + u x‖ ^ p - ‖v n x‖ ^ p - ‖u x‖ ^ p| - ε * ‖v n x‖ ^ p) 0 := fun n x => by
    rw [hh]
  have hcont : Continuous fun q : ℂ × ℂ =>
      max (|‖q.1 + q.2‖ ^ p - ‖q.1‖ ^ p - ‖q.2‖ ^ p| - ε * ‖q.1‖ ^ p) 0 := by fun_prop
  have hmeas : ∀ n, AEStronglyMeasurable (h n) μ := fun n => by
    have := hcont.comp_aestronglyMeasurable ((hv n).prodMk hu)
    rw [hh]
    exact this
  have hpt : ∀ n x, |‖v n x + u x‖ ^ p - ‖v n x‖ ^ p - ‖u x‖ ^ p| ≤
      ε * ‖v n x‖ ^ p + (C + 1) * ‖u x‖ ^ p := by
    intro n x
    have h1 := hC (v n x) (u x)
    have h2 : |‖v n x + u x‖ ^ p - ‖v n x‖ ^ p - ‖u x‖ ^ p| ≤
        |‖v n x + u x‖ ^ p - ‖v n x‖ ^ p| + |‖u x‖ ^ p| := abs_sub _ _
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖u x‖ ^ p)] at h2
    linarith
  have hbound : ∀ n, ∀ᵐ x ∂μ, ‖h n x‖ ≤ (C + 1) * ‖u x‖ ^ p := fun n =>
    Eventually.of_forall fun x => by
      rw [hhx, Real.norm_of_nonneg (le_max_right _ _)]
      exact max_le (by linarith [hpt n x]) (by positivity)
  have hhint : ∀ n, Integrable (h n) μ := fun n =>
    (hup.const_mul (C + 1)).mono' (hmeas n) (hbound n)
  have hlim' : ∀ᵐ x ∂μ, Tendsto (fun n => h n x) atTop (𝓝 0) := by
    filter_upwards [hlim] with x hx
    have hc : Continuous fun z : ℂ =>
        max (|‖z + u x‖ ^ p - ‖z‖ ^ p - ‖u x‖ ^ p| - ε * ‖z‖ ^ p) 0 := by fun_prop
    have h1 := (hc.tendsto 0).comp hx
    have h0 : max (|‖(0 : ℂ) + u x‖ ^ p - ‖(0 : ℂ)‖ ^ p - ‖u x‖ ^ p| - ε * ‖(0 : ℂ)‖ ^ p) 0 =
        0 := by
      simp [zero_pow hp0]
    rw [h0] at h1
    refine h1.congr fun n => ?_
    simp only [Function.comp_apply, hhx]
  have hDCT := tendsto_integral_of_dominated_convergence _ hmeas (hup.const_mul (C + 1)) hbound
    hlim'
  rw [integral_zero] at hDCT
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hDCT (δ / 2) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hgint : Integrable (fun x => ‖v n x + u x‖ ^ p - ‖v n x‖ ^ p - ‖u x‖ ^ p) μ :=
    ((hwp n).sub (hvp n)).sub hup
  rw [dist_zero_right, Real.norm_eq_abs, ← integral_sub (hwp n) (hvp n),
    ← integral_sub (f := fun a => ‖v n a + u a‖ ^ p - ‖v n a‖ ^ p) (g := fun a => ‖u a‖ ^ p)
      ((hwp n).sub (hvp n)) hup]
  have h1 := abs_integral_le_integral_abs (f := fun x => ‖v n x + u x‖ ^ p - ‖v n x‖ ^ p -
    ‖u x‖ ^ p) (μ := μ)
  have h2 : ∫ x, |‖v n x + u x‖ ^ p - ‖v n x‖ ^ p - ‖u x‖ ^ p| ∂μ ≤
      ∫ x, h n x ∂μ + ε * ∫ x, ‖v n x‖ ^ p ∂μ := by
    rw [← integral_const_mul, ← integral_add (hhint n) ((hvp n).const_mul ε)]
    refine integral_mono hgint.abs ((hhint n).add ((hvp n).const_mul ε)) fun x => ?_
    have := le_max_left (|‖v n x + u x‖ ^ p - ‖v n x‖ ^ p - ‖u x‖ ^ p| - ε * ‖v n x‖ ^ p) 0
    rw [hhx]
    linarith
  have h3 := hN n hn
  rw [dist_zero_right, Real.norm_eq_abs] at h3
  have h4 : ε * ∫ x, ‖v n x‖ ^ p ∂μ ≤ ε * B := mul_le_mul_of_nonneg_left (hB n) hεpos.le
  have h5 : ε * B ≤ δ / 2 := by
    rw [hε, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) two_pos]
    nlinarith
  have h6 := le_abs_self (∫ x, h n x ∂μ)
  linarith

end BrezisLieb

end ReyesMath

namespace ReyesMath

/-- Hilbert-space splitting: if `aₙ ⇀ b` weakly, `‖aₙ‖² − ‖b‖² − ‖aₙ − b‖² → 0`. -/
theorem tendsto_norm_sq_split {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {a : ℕ → E} {b : E} (h : ∀ z, Tendsto (fun n => inner ℂ z (a n)) atTop (𝓝 (inner ℂ z b))) :
    Tendsto (fun n => ‖a n‖ ^ 2 - ‖b‖ ^ 2 - ‖a n - b‖ ^ 2) atTop (𝓝 0) := by
  have heq : ∀ n, ‖a n‖ ^ 2 - ‖b‖ ^ 2 - ‖a n - b‖ ^ 2 =
      2 * (inner ℂ b (a n)).re - 2 * ‖b‖ ^ 2 := by
    intro n
    rw [@norm_sub_sq ℂ, ← inner_conj_symm, RCLike.conj_re, RCLike.re_to_complex]
    ring
  simp_rw [heq]
  have h1 := ((Complex.continuous_re.tendsto _).comp (h b)).const_mul 2
  have h2 : 2 * (inner ℂ b b).re - 2 * ‖b‖ ^ 2 = 0 := by
    rw [show (inner ℂ b b).re = RCLike.re (inner ℂ b b) from rfl, inner_self_eq_norm_sq]
    ring
  rw [← h2]
  exact h1.sub_const _

/-- `fₙ → 0` and `|gₙ| ≤ C` give `fₙ gₙ → 0`. -/
theorem tendsto_mul_bdd {f g : ℕ → ℝ} {C : ℝ} (hf : Tendsto f atTop (𝓝 0))
    (hg : ∀ n, |g n| ≤ C) : Tendsto (fun n => f n * g n) atTop (𝓝 0) := by
  have : Tendsto (fun n => |f n| * C) atTop (𝓝 0) := by simpa using hf.abs.mul_const C
  refine squeeze_zero_norm (fun n => ?_) this
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_left (hg n) (abs_nonneg _)

namespace Sobolev

local notation "R2" => EuclideanSpace ℝ (Fin 2)

namespace H2

/-- An a.e. bound `|u|² ≤ L` gives `S(u) ≤ L² M(u)`. -/
theorem S_le_of_ae_bound (U : H2 2) {L : ℝ}
    (h : ∀ᵐ x ∂(volume : Measure R2), ‖U.val x‖ ^ 2 ≤ L) : S U ≤ L ^ 2 * M U := by
  rw [M_eq_integral, ← integral_const_mul]
  refine integral_mono_ae (integrable_S U) ((integrable_sq_val U).const_mul _) ?_
  filter_upwards [h] with x hx
  rw [show ‖U.val x‖ ^ 6 = (‖U.val x‖ ^ 2) ^ 2 * ‖U.val x‖ ^ 2 by ring]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (sq_nonneg _) hx 2) (sq_nonneg _)

theorem sqrt_MD_le {U : H2 2} {B : ℝ} (hB : D U + M U ≤ B) : Real.sqrt (M U * D U) ≤ B := by
  have hM := M_nonneg U
  have hD := D_nonneg U
  have hB0 : 0 ≤ B := by linarith
  calc Real.sqrt (M U * D U) ≤ Real.sqrt (B * B) :=
        Real.sqrt_le_sqrt (mul_le_mul (by linarith) (by linarith) hD hB0)
    _ = B := Real.sqrt_mul_self hB0

theorem Q_le_of_bound {U : H2 2} {B : ℝ} (hB : D U + M U ≤ B) : Q U ≤ B / 4 * M U := by
  have h := Q_le_of_ae_bound U (ae_sup_bound_opt U)
  have : Real.sqrt (M U * D U) / 4 ≤ B / 4 := by linarith [sqrt_MD_le hB]
  exact h.trans (mul_le_mul_of_nonneg_right this (M_nonneg U))

theorem S_le_of_bound {U : H2 2} {B : ℝ} (hB : D U + M U ≤ B) : S U ≤ (B / 4) ^ 2 * M U := by
  have h := S_le_of_ae_bound U (ae_sup_bound_opt U)
  have h1 : Real.sqrt (M U * D U) / 4 ≤ B / 4 := by linarith [sqrt_MD_le hB]
  have h2 : (Real.sqrt (M U * D U) / 4) ^ 2 ≤ (B / 4) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h1 2
  exact h.trans (mul_le_mul_of_nonneg_right h2 (M_nonneg U))

theorem T_le_of_bound (k : ℝ) {U : H2 2} {B : ℝ} (hB : D U + M U ≤ B) :
    T k U ≤ (1 + k ^ 2) ^ 2 * B := by
  have hM := M_nonneg U
  have hD := D_nonneg U
  have hB0 : 0 ≤ B := by linarith
  have hv : ‖U.val‖ ≤ Real.sqrt B := by
    rw [← Real.sqrt_sq (norm_nonneg U.val)]
    exact Real.sqrt_le_sqrt (by rw [← M]; linarith)
  have hl : ‖U.lap‖ ≤ Real.sqrt B := by
    rw [← Real.sqrt_sq (norm_nonneg U.lap)]
    exact Real.sqrt_le_sqrt (by rw [← D]; linarith)
  have h1 : ‖U.lap + ((k ^ 2 : ℝ) : ℂ) • U.val‖ ≤ (1 + k ^ 2) * Real.sqrt B := by
    calc ‖U.lap + ((k ^ 2 : ℝ) : ℂ) • U.val‖ ≤ ‖U.lap‖ + ‖((k ^ 2 : ℝ) : ℂ) • U.val‖ :=
          norm_add_le _ _
      _ = ‖U.lap‖ + k ^ 2 * ‖U.val‖ := by
          rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      _ ≤ Real.sqrt B + k ^ 2 * Real.sqrt B := by gcongr
      _ = (1 + k ^ 2) * Real.sqrt B := by ring
  calc T k U = ‖U.lap + ((k ^ 2 : ℝ) : ℂ) • U.val‖ ^ 2 := rfl
    _ ≤ ((1 + k ^ 2) * Real.sqrt B) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = (1 + k ^ 2) ^ 2 * B := by rw [mul_pow, Real.sq_sqrt hB0]

/-- `‖a − b‖² ≤ 2‖a‖² + 2‖b‖²`. -/
theorem norm_sub_sq_le_two {E : Type*} [NormedAddCommGroup E] (a b : E) :
    ‖a - b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h := norm_sub_le a b
  have h0 := norm_nonneg (a - b)
  nlinarith [sq_nonneg (‖a‖ - ‖b‖), norm_nonneg a, norm_nonneg b]

theorem DM_sub_le (W U : H2 2) :
    D (sub W U) + M (sub W U) ≤ 2 * (D W + M W) + 2 * (D U + M U) := by
  have h1 := norm_sub_sq_le_two W.lap U.lap
  have h2 := norm_sub_sq_le_two W.val U.val
  simp only [D, M, sub]
  linarith

/-- `(u − v) + v = u` a.e. -/
theorem sub_val_add_ae (W U : H2 2) :
    ∀ᵐ x ∂(volume : Measure R2), (sub W U).val x + U.val x = W.val x := by
  filter_upwards [Lp.coeFn_sub W.val U.val] with x hx
  simp only [sub]
  rw [hx, Pi.sub_apply, sub_add_cancel]

/-- Brezis–Lieb splitting of `∫|u|^p` for `p ∈ {4, 6}` along a weakly convergent bounded
sequence in `H²(ℝ²)`. -/
theorem tendsto_pow_split (W : ℕ → H2 2) (U : H2 2) {B : ℝ} (hB : ∀ n, D (W n) + M (W n) ≤ B)
    (h0 : ∀ z, Tendsto (fun n => inner ℂ z (W n).val) atTop (𝓝 (inner ℂ z U.val)))
    {p : ℕ} (hp : p = 4 ∨ p = 6) :
    Tendsto (fun n => (∫ x, ‖(W n).val x‖ ^ p) - (∫ x, ‖(sub (W n) U).val x‖ ^ p) -
      ∫ x, ‖U.val x‖ ^ p) atTop (𝓝 0) := by
  set B₂ := 2 * B + 2 * (D U + M U) with hB₂
  have hbd : ∀ n, D (sub (W n) U) + M (sub (W n) U) ≤ B₂ := fun n =>
    (DM_sub_le (W n) U).trans (by linarith [hB n])
  have hint : ∀ V : H2 2, Integrable (fun x => ‖V.val x‖ ^ p) := fun V => by
    rcases hp with rfl | rfl
    · exact integrable_Q V
    · exact integrable_S V
  have hweak : ∀ z, Tendsto (fun n => inner ℂ z (sub (W n) U).val) atTop (𝓝 0) := by
    intro z
    have := (h0 z).sub_const (inner ℂ z U.val)
    rw [sub_self] at this
    refine this.congr fun n => ?_
    simp only [sub, inner_sub_right]
  have hae := ae_tendsto_zero_of_weak (fun n => sub (W n) U) hbd hweak
  have hboundp : ∀ n, ∫ x, ‖(sub (W n) U).val x‖ ^ p ≤
      max (B₂ / 4 * B₂) ((B₂ / 4) ^ 2 * B₂) := by
    intro n
    have hM := M_nonneg (sub (W n) U)
    have hMB : M (sub (W n) U) ≤ B₂ := by linarith [hbd n, D_nonneg (sub (W n) U)]
    have hB₂0 : 0 ≤ B₂ := by linarith [hbd n, D_nonneg (sub (W n) U)]
    rcases hp with rfl | rfl
    · refine (Q_le_of_bound (hbd n)).trans ((?_ : B₂ / 4 * M (sub (W n) U) ≤ B₂ / 4 * B₂).trans
        (le_max_left _ _))
      exact mul_le_mul_of_nonneg_left hMB (by positivity)
    · refine (S_le_of_bound (hbd n)).trans ((?_ : (B₂ / 4) ^ 2 * M (sub (W n) U) ≤
        (B₂ / 4) ^ 2 * B₂).trans (le_max_right _ _))
      exact mul_le_mul_of_nonneg_left hMB (by positivity)
  have hp1 : 1 ≤ p := by rcases hp with rfl | rfl <;> norm_num
  have hwp : ∀ n, Integrable (fun x => ‖(sub (W n) U).val x + U.val x‖ ^ p) := fun n =>
    (hint (W n)).congr (by
      filter_upwards [sub_val_add_ae (W n) U] with x hx
      rw [hx])
  have hBL := BrezisLieb.brezis_lieb hp1 (v := fun n => (sub (W n) U).val) (u := U.val)
    (fun n => Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _)
    (fun n => hint (sub (W n) U)) (hint U) hwp hboundp hae
  refine hBL.congr fun n => ?_
  congr 2
  refine integral_congr_ae ?_
  filter_upwards [sub_val_add_ae (W n) U] with x hx
  rw [hx]

/-- `A u = Δu + k²u` on `H²`, as an element of `L²`. -/
noncomputable def Aop (k : ℝ) (U : H2 2) : L2 2 := U.lap + ((k ^ 2 : ℝ) : ℂ) • U.val

theorem Aop_sub (k : ℝ) (W U : H2 2) : Aop k (sub W U) = Aop k W - Aop k U := by
  simp only [Aop, sub, smul_sub]
  abel

/-- **Splitting of the energy** along a weakly convergent bounded sequence:
`H(wₙ) − H(u) − H(wₙ − u) → 0`. -/
theorem tendsto_energy_split (β γ k : ℝ) (W : ℕ → H2 2) (U : H2 2) {B : ℝ}
    (hB : ∀ n, D (W n) + M (W n) ≤ B)
    (h0 : ∀ z, Tendsto (fun n => inner ℂ z (W n).val) atTop (𝓝 (inner ℂ z U.val)))
    (h2 : ∀ z, Tendsto (fun n => inner ℂ z (W n).lap) atTop (𝓝 (inner ℂ z U.lap))) :
    Tendsto (fun n => energy β γ k (W n) - energy β γ k U - energy β γ k (sub (W n) U))
      atTop (𝓝 0) := by
  have hA : ∀ z, Tendsto (fun n => inner ℂ z (Aop k (W n))) atTop (𝓝 (inner ℂ z (Aop k U))) := by
    intro z
    simp only [Aop, inner_add_right, inner_smul_right]
    exact (h2 z).add ((h0 z).const_mul _)
  have hT : Tendsto (fun n => T k (W n) - T k U - T k (sub (W n) U)) atTop (𝓝 0) := by
    have := tendsto_norm_sq_split hA
    refine this.congr fun n => ?_
    rw [← Aop_sub]
    rfl
  have hQ := tendsto_pow_split W U hB h0 (p := 4) (Or.inl rfl)
  have hS := tendsto_pow_split W U hB h0 (p := 6) (Or.inr rfl)
  have := (hT.sub (hQ.const_mul (β / 2))).add (hS.const_mul (γ / 3))
  simp only [mul_zero, sub_zero, add_zero] at this
  refine this.congr fun n => ?_
  simp only [energy_eq, Q, S]
  ring

/-- **Mass splitting** along a weakly convergent sequence. -/
theorem tendsto_M_split (W : ℕ → H2 2) (U : H2 2)
    (h0 : ∀ z, Tendsto (fun n => inner ℂ z (W n).val) atTop (𝓝 (inner ℂ z U.val))) :
    Tendsto (fun n => M (W n) - M U - M (sub (W n) U)) atTop (𝓝 0) :=
  tendsto_norm_sq_split h0

/-- **Mass correction.**  If `M(vₙ) → μ > 0` and `(vₙ)` is bounded in `H²`, then
`H(vₙ) ≥ I(μ) − eₙ` eventually, for some `eₙ → 0`. -/
theorem exists_energy_ge_Imin (β γ k : ℝ) (hγ : 0 < γ) (V : ℕ → H2 2) {μ B : ℝ} (hμ : 0 < μ)
    (hM : Tendsto (fun n => M (V n)) atTop (𝓝 μ)) (hB : ∀ n, D (V n) + M (V n) ≤ B) :
    ∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧
      ∀ᶠ n in atTop, Imin β γ k μ ≤ energy β γ k (V n) + e n := by
  set t : ℕ → ℝ := fun n => μ / M (V n) with ht
  have ht0 : ∀ n, 0 ≤ t n := fun n => div_nonneg hμ.le (M_nonneg _)
  have htlim : Tendsto t atTop (𝓝 1) := by
    have := (tendsto_const_nhds (x := μ)).div hM hμ.ne'
    rwa [div_self hμ.ne'] at this
  set c : ℕ → ℂ := fun n => ((Real.sqrt (t n) : ℝ) : ℂ) with hc
  have hcn : ∀ n, ‖c n‖ ^ 2 = t n := fun n => by
    rw [hc, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt (ht0 n)]
  have hcn4 : ∀ n, ‖c n‖ ^ 4 = t n ^ 2 := fun n => by
    rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, hcn]
  have hcn6 : ∀ n, ‖c n‖ ^ 6 = t n ^ 3 := fun n => by
    rw [show (6 : ℕ) = 2 * 3 by rfl, pow_mul, hcn]
  refine ⟨fun n => energy β γ k (smul (c n) (V n)) - energy β γ k (V n), ?_, ?_⟩
  · have heq : ∀ n, energy β γ k (smul (c n) (V n)) - energy β γ k (V n) =
        (t n - 1) * T k (V n) - β / 2 * ((t n ^ 2 - 1) * Q (V n)) +
          γ / 3 * ((t n ^ 3 - 1) * S (V n)) := by
      intro n
      rw [energy_eq, energy_eq, T_smul, Q_smul, S_smul, hcn, hcn4, hcn6]
      ring
    simp_rw [heq]
    have h1 : Tendsto (fun n => t n - 1) atTop (𝓝 0) := by
      simpa using htlim.sub_const 1
    have h2 : Tendsto (fun n => t n ^ 2 - 1) atTop (𝓝 0) := by
      simpa using (htlim.pow 2).sub_const 1
    have h3 : Tendsto (fun n => t n ^ 3 - 1) atTop (𝓝 0) := by
      simpa using (htlim.pow 3).sub_const 1
    have hBT : ∀ n, |T k (V n)| ≤ (1 + k ^ 2) ^ 2 * B := fun n => by
      rw [abs_of_nonneg (T_nonneg k _)]
      exact T_le_of_bound k (hB n)
    have hMB : ∀ n, M (V n) ≤ B := fun n => by linarith [hB n, D_nonneg (V n)]
    have hB0 : 0 ≤ B := by linarith [hB 0, D_nonneg (V 0), M_nonneg (V 0)]
    have hBQ : ∀ n, |Q (V n)| ≤ B / 4 * B := fun n => by
      rw [abs_of_nonneg (Q_nonneg _)]
      exact (Q_le_of_bound (hB n)).trans (mul_le_mul_of_nonneg_left (hMB n) (by positivity))
    have hBS : ∀ n, |S (V n)| ≤ (B / 4) ^ 2 * B := fun n => by
      rw [abs_of_nonneg (S_nonneg _)]
      exact (S_le_of_bound (hB n)).trans (mul_le_mul_of_nonneg_left (hMB n) (by positivity))
    have := ((tendsto_mul_bdd h1 hBT).sub ((tendsto_mul_bdd h2 hBQ).const_mul (β / 2))).add
      ((tendsto_mul_bdd h3 hBS).const_mul (γ / 3))
    simpa using this
  · have hpos : ∀ᶠ n in atTop, 0 < M (V n) := hM.eventually (lt_mem_nhds hμ)
    filter_upwards [hpos] with n hn
    have hmass : M (smul (c n) (V n)) = μ := by
      rw [M_smul, hcn, ht]
      field_simp
    have := StrictBinding.Imin_le_energy (β := β) (k := k) hγ hmass
    linarith

end H2

end Sobolev

end ReyesMath

namespace ReyesMath

namespace WholeSpace

open Sobolev Sobolev.H2

local notation "R2" => EuclideanSpace ℝ (Fin 2)

variable {β γ k : ℝ}

instance fact_two_ne_top : Fact ((2 : ENNReal) ≠ ⊤) := ⟨ENNReal.ofNat_ne_top⟩

/-- **Preparation.**  Along a minimizing sequence at a mass with `I(m) < 0`, eventually
`Q(uₙ) ≥ −I(m)/β` and `D(uₙ)` is uniformly bounded. -/
theorem eventually_bounds (hβ : 0 < β) (hγ : 0 < γ) {m : ℝ} (hI : Imin β γ k m < 0)
    {u : ℕ → H2 2} (hM : ∀ n, M (u n) = m)
    (hE : Tendsto (fun n => energy β γ k (u n)) atTop (𝓝 (Imin β γ k m))) :
    ∃ N₀ : ℕ, ∀ n, N₀ ≤ n → -Imin β γ k m / β ≤ Q (u n) ∧
      D (u n) ≤ (Real.sqrt (0 + 3 * β ^ 2 / (16 * γ) * m) + k ^ 2 * Real.sqrt m) ^ 2 := by
  have hlt : ∀ᶠ n in atTop, energy β γ k (u n) < Imin β γ k m / 2 :=
    hE.eventually_lt_const (by linarith)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hlt
  refine ⟨N₀, fun n hn => ⟨?_, ?_⟩⟩
  · have h1 := hN₀ n hn
    have hT := T_nonneg k (u n)
    have hS := S_nonneg (u n)
    rw [energy_eq] at h1
    rw [div_le_iff₀ hβ]
    nlinarith
  · exact (StrictBinding.bounded_of_energy_le hγ (hM n) (by linarith [hN₀ n hn])).1

/-- **Choice of translations.**  A sequence of fixed mass `m > 0` with `Q ≥ q₀ > 0` and `D ≤ C`
can be translated so that the unit-free disc `B(0, r)` carries `|∫_{B(0,r)} uₙ| ≥ c₀ > 0`. -/
theorem exists_translations {m q₀ C : ℝ} (hm : 0 < m) (hq : 0 < q₀) {u : ℕ → H2 2}
    (hM : ∀ n, M (u n) = m) (hQ : ∀ n, q₀ ≤ Q (u n)) (hD : ∀ n, D (u n) ≤ C) :
    ∃ r > 0, ∃ c₀ > 0, ∃ y : ℕ → R2, ∀ n,
      c₀ ≤ ‖inner ℂ (ballInd 0 r) (translate (y n) (u n)).val‖ := by
  have hC0 : 0 ≤ C := (D_nonneg _).trans (hD 0)
  have hCH := CH_nonneg
  set r : ℝ := q₀ / (9 * m * (CH * (C + m) + 1)) with hr
  have hrpos : 0 < r := by positivity
  have hsmall : ∀ n, CH * r * (D (u n) + M (u n)) ≤ q₀ / (9 * M (u n)) := by
    intro n
    rw [hM n]
    calc CH * r * (D (u n) + m) ≤ CH * r * (C + m) := by gcongr; exact hD n
      _ ≤ (CH * (C + m) + 1) * r := by nlinarith
      _ = q₀ / (9 * m) := by rw [hr]; field_simp
  have hex : ∀ n, ∃ y : R2, vol2 r * (Real.sqrt (q₀ / m) / 3) ≤
      ‖inner ℂ (ballInd y r) (u n).val‖ := by
    intro n
    have := exists_ball_avg (by rw [hM n]; exact hm) hq (hQ n) hrpos (hsmall n)
    rwa [hM n] at this
  choose y hy using hex
  refine ⟨r, hrpos, vol2 r * (Real.sqrt (q₀ / m) / 3), ?_, y, fun n => ?_⟩
  · have := vol2_pos hrpos
    have : 0 < Real.sqrt (q₀ / m) := Real.sqrt_pos.2 (by positivity)
    positivity
  · rw [inner_ballInd_translate]
    exact hy n

/-- **Profile extraction.**  A sequence bounded in `H²(ℝ²)` whose members keep
`|∫_{B(0,r)} wₙ| ≥ c₀ > 0` has a subsequence converging weakly (in every component) to some
`U ∈ H²` with `M(U) > 0`. -/
theorem exists_profile {m C r c₀ : ℝ} (hc₀ : 0 < c₀) {w : ℕ → H2 2} (hM : ∀ n, M (w n) = m)
    (hD : ∀ n, D (w n) ≤ C) (hball : ∀ n, c₀ ≤ ‖inner ℂ (ballInd 0 r) (w n).val‖) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ U : H2 2, 0 < M U ∧
      (∀ z, Tendsto (fun n => inner ℂ z (w (φ n)).val) atTop (𝓝 (inner ℂ z U.val))) ∧
      (∀ i z, Tendsto (fun n => inner ℂ z ((w (φ n)).grad i)) atTop (𝓝 (inner ℂ z (U.grad i)))) ∧
      (∀ z, Tendsto (fun n => inner ℂ z (w (φ n)).lap) atTop (𝓝 (inner ℂ z U.lap))) := by
  have hm : 0 ≤ m := (M_nonneg _).trans_eq (hM 0)
  have hC0 : 0 ≤ C := (D_nonneg _).trans (hD 0)
  have hv : ∀ n, ‖(w n).val‖ ≤ Real.sqrt m := fun n => by
    rw [← hM n, M, Real.sqrt_sq (norm_nonneg _)]
  have hl : ∀ n, ‖(w n).lap‖ ≤ Real.sqrt C := fun n => by
    rw [← Real.sqrt_sq (norm_nonneg (w n).lap)]
    exact Real.sqrt_le_sqrt (hD n)
  have hg : ∀ n i, ‖(w n).grad i‖ ≤ Real.sqrt m + Real.sqrt C := by
    intro n i
    have h1 : ‖(w n).grad i‖ ^ 2 ≤ K (w n) :=
      Finset.single_le_sum (f := fun j => ‖(w n).grad j‖ ^ 2) (fun j _ => sq_nonneg _)
        (Finset.mem_univ i)
    have h2 := K_le (w n)
    have h3 : ‖(w n).grad i‖ ^ 2 ≤ (‖(w n).val‖ + ‖(w n).lap‖) ^ 2 := by
      nlinarith [norm_nonneg (w n).val, norm_nonneg (w n).lap]
    have h4 := (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h3
    linarith [hv n, hl n]
  set R := Real.sqrt m + Real.sqrt C with hR
  have hbd : ∀ n o, ‖comp3 (w n).val (w n).lap (w n).grad o‖ ≤ R := by
    intro n o
    have h1 := Real.sqrt_nonneg m
    have h2 := Real.sqrt_nonneg C
    rcases o with _ | _ | i
    · exact (hv n).trans (by linarith)
    · exact (hl n).trans (by linarith)
    · exact hg n i
  obtain ⟨φ, hφ, Y, hY⟩ := WeakCompact.exists_weak_subseq
    (fun n => comp3 (w n).val (w n).lap (w n).grad) hbd
  obtain ⟨U, hU0, hU1, hU2⟩ := exists_weak_limit (fun n => w (φ n)) (u := Y none)
    (l := Y (some none)) (g := fun i => Y (some (some i))) (fun z => hY none z)
    (fun i z => hY (some (some i)) z) (fun z => hY (some none) z)
  refine ⟨φ, hφ, U, ?_, fun z => ?_, fun i z => ?_, fun z => ?_⟩
  · have hlim : Tendsto (fun n => ‖inner ℂ (ballInd 0 r) (w (φ n)).val‖) atTop
        (𝓝 ‖inner ℂ (ballInd 0 r) U.val‖) := by
      rw [hU0]
      exact (hY none (ballInd 0 r)).norm
    have hge : c₀ ≤ ‖inner ℂ (ballInd 0 r) U.val‖ :=
      ge_of_tendsto' hlim fun n => hball (φ n)
    rcases (M_nonneg U).lt_or_eq with h | h
    · exact h
    · exfalso
      have : U.val = 0 := by
        rw [M, eq_comm, sq_eq_zero_iff, norm_eq_zero] at h
        exact h
      rw [this, inner_zero_right, norm_zero] at hge
      linarith
  · rw [hU0]
    exact hY none z
  · rw [hU1]
    exact hY (some (some i)) z
  · rw [hU2]
    exact hY (some none) z

/-- **Conclusion of the compactness argument.**  Let `0 < m ≤ m_B`, `M(Wₙ) = m`,
`D(Wₙ) ≤ C`, `H(Wₙ) → I(m)`, and let `Wₙ ⇀ U` weakly (componentwise) with `M(U) > 0`.  Then
`M(U) = m`, `H(U) = I(m)` and `Wₙ → U` strongly in `H²`. -/
theorem conclusion (hβ : 0 < β) (hγ : 0 < γ) {m C : ℝ} (hm : 0 < m)
    (hmB : m ≤ StrictBinding.mB β γ k) {W : ℕ → H2 2} (hM : ∀ n, M (W n) = m)
    (hD : ∀ n, D (W n) ≤ C) (hE : Tendsto (fun n => energy β γ k (W n)) atTop (𝓝 (Imin β γ k m)))
    {U : H2 2} (hU : 0 < M U)
    (h0 : ∀ z, Tendsto (fun n => inner ℂ z (W n).val) atTop (𝓝 (inner ℂ z U.val)))
    (h2 : ∀ z, Tendsto (fun n => inner ℂ z (W n).lap) atTop (𝓝 (inner ℂ z U.lap))) :
    M U = m ∧ energy β γ k U = Imin β γ k m ∧
      Tendsto (fun n => distH2 (W n) U) atTop (𝓝 0) := by
  set B := C + m with hB
  have hbd : ∀ n, D (W n) + M (W n) ≤ B := fun n => by rw [hM n]; linarith [hD n]
  set V : ℕ → H2 2 := fun n => sub (W n) U with hV
  set B₂ := 2 * B + 2 * (D U + M U) with hB₂
  have hbd₂ : ∀ n, D (V n) + M (V n) ≤ B₂ := fun n =>
    (DM_sub_le (W n) U).trans (by linarith [hbd n])
  -- mass splitting
  have hMV : Tendsto (fun n => M (V n)) atTop (𝓝 (m - M U)) := by
    have := (tendsto_M_split W U h0).neg.const_add (m - M U)
    simp only [neg_zero, add_zero] at this
    refine this.congr fun n => ?_
    simp only [hV, hM n]
    ring
  have hEsplit := tendsto_energy_split β γ k W U hbd h0 h2
  -- `M(U) = m` by strict binding
  have hle : M U ≤ m := by
    have := ge_of_tendsto' hMV fun n => M_nonneg (V n)
    linarith
  have heq : M U = m := by
    by_contra hne
    have hlt : M U < m := lt_of_le_of_ne hle hne
    have hμ : 0 < m - M U := by linarith
    obtain ⟨e, he, hev⟩ := exists_energy_ge_Imin β γ k hγ V hμ hMV hbd₂
    have hIa := StrictBinding.Imin_le_energy (β := β) (k := k) hγ (rfl : M U = M U)
    have hF : Tendsto (fun n => energy β γ k (W n) -
        (energy β γ k (W n) - energy β γ k U - energy β γ k (V n)) + e n) atTop
        (𝓝 (Imin β γ k m - 0 + 0)) := (hE.sub hEsplit).add he
    rw [sub_zero, add_zero] at hF
    have hge : Imin β γ k (M U) + Imin β γ k (m - M U) ≤ Imin β γ k m := by
      refine ge_of_tendsto hF ?_
      filter_upwards [hev] with n hn
      linarith
    have := StrictBinding.strict_binding (k := k) hβ hγ hm hmB hU hlt
    linarith
  -- the remainder carries no mass
  have hMV0 : Tendsto (fun n => M (V n)) atTop (𝓝 0) := by rwa [heq, sub_self] at hMV
  have hB₂0 : 0 ≤ B₂ := (add_nonneg (D_nonneg _) (M_nonneg _)).trans (hbd₂ 0)
  have hQ0 : Tendsto (fun n => Q (V n)) atTop (𝓝 0) := by
    have := hMV0.const_mul (B₂ / 4)
    rw [mul_zero] at this
    exact squeeze_zero (fun n => Q_nonneg _) (fun n => Q_le_of_bound (hbd₂ n)) this
  have hS0 : Tendsto (fun n => S (V n)) atTop (𝓝 0) := by
    have := hMV0.const_mul ((B₂ / 4) ^ 2)
    rw [mul_zero] at this
    exact squeeze_zero (fun n => S_nonneg _) (fun n => S_le_of_bound (hbd₂ n)) this
  -- the kinetic term of the remainder
  have hTV : Tendsto (fun n => T k (V n)) atTop (𝓝 (Imin β γ k m - energy β γ k U)) := by
    have := ((hE.sub_const (energy β γ k U)).sub hEsplit).add
      ((hQ0.const_mul (β / 2)).sub (hS0.const_mul (γ / 3)))
    simp only [mul_zero, sub_zero, add_zero] at this
    refine this.congr fun n => ?_
    rw [energy_eq β γ k (V n)]
    ring
  have hIU := StrictBinding.Imin_le_energy (β := β) (k := k) hγ heq
  have hL0 : 0 ≤ Imin β γ k m - energy β γ k U := ge_of_tendsto' hTV fun n => T_nonneg k _
  have hEU : energy β γ k U = Imin β γ k m := by linarith
  have hT0 : Tendsto (fun n => T k (V n)) atTop (𝓝 0) := by
    rwa [hEU, sub_self] at hTV
  refine ⟨heq, hEU, ?_⟩
  -- strong convergence
  have hval : Tendsto (fun n => ‖(V n).val‖) atTop (𝓝 0) := by
    have := hMV0.sqrt
    rw [Real.sqrt_zero] at this
    refine this.congr fun n => ?_
    rw [M, Real.sqrt_sq (norm_nonneg _)]
  have hA : Tendsto (fun n => ‖Aop k (V n)‖) atTop (𝓝 0) := by
    have := hT0.sqrt
    rw [Real.sqrt_zero] at this
    refine this.congr fun n => ?_
    rw [show T k (V n) = ‖Aop k (V n)‖ ^ 2 from rfl, Real.sqrt_sq (norm_nonneg _)]
  have hlap : Tendsto (fun n => ‖(V n).lap‖) atTop (𝓝 0) := by
    have hup := hA.add (hval.const_mul (k ^ 2))
    rw [mul_zero, add_zero] at hup
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hup
    have e : (V n).lap = Aop k (V n) - ((k ^ 2 : ℝ) : ℂ) • (V n).val := by
      simp only [Aop, add_sub_cancel_right]
    rw [e]
    refine (norm_sub_le _ _).trans (le_of_eq ?_)
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hgrad : ∀ i, Tendsto (fun n => ‖(V n).grad i‖) atTop (𝓝 0) := by
    intro i
    have hup := hval.add hlap
    rw [add_zero] at hup
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hup
    have h1 : ‖(V n).grad i‖ ^ 2 ≤ K (V n) :=
      Finset.single_le_sum (f := fun j => ‖(V n).grad j‖ ^ 2) (fun j _ => sq_nonneg _)
        (Finset.mem_univ i)
    have h2 := K_le (V n)
    have h3 : ‖(V n).grad i‖ ^ 2 ≤ (‖(V n).val‖ + ‖(V n).lap‖) ^ 2 := by
      nlinarith [norm_nonneg (V n).val, norm_nonneg (V n).lap]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h3
  have hsum := (hval.add (tendsto_finset_sum (Finset.univ : Finset (Fin 2))
    fun i _ => hgrad i)).add hlap
  simp only [Finset.sum_const_zero, add_zero] at hsum
  exact hsum

end WholeSpace

end ReyesMath

namespace ReyesMath

namespace WholeSpace

open Sobolev Sobolev.H2

local notation "R2" => EuclideanSpace ℝ (Fin 2)

variable {β γ k : ℝ}

/-- **Theorem (iii): compactness of minimizing sequences modulo translations.**  Let
`β, γ > 0` and `0 < m ≤ m_B`.  If `M(uₙ) = m` and `H(uₙ) → I(m)`, then there are a subsequence
`φ`, translations `yₙ ∈ ℝ²` and `u ∈ H²(ℝ²)` with `uφ(n)(· + yₙ) → u` strongly in `H²`
(`distH2 → 0`), `M(u) = m` and `H(u) = I(m)`. -/
theorem compactness (hβ : 0 < β) (hγ : 0 < γ) {m : ℝ} (hm : 0 < m)
    (hmB : m ≤ StrictBinding.mB β γ k) {u : ℕ → H2 2} (hM : ∀ n, M (u n) = m)
    (hE : Tendsto (fun n => energy β γ k (u n)) atTop (𝓝 (Imin β γ k m))) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ y : ℕ → R2, ∃ U : H2 2, M U = m ∧
      energy β γ k U = Imin β γ k m ∧
      Tendsto (fun n => distH2 (translate (y n) (u (φ n))) U) atTop (𝓝 0) := by
  have hI := (NegativeEnergy.negative_constrained_energy (k := k) hβ hγ hm).2
  obtain ⟨N₀, hN₀⟩ := eventually_bounds hβ hγ hI hM hE
  set C := (Real.sqrt (0 + 3 * β ^ 2 / (16 * γ) * m) + k ^ 2 * Real.sqrt m) ^ 2 with hC
  set q₀ := -Imin β γ k m / β with hq₀
  have hq : 0 < q₀ := div_pos (by linarith) hβ
  -- shift past `N₀`
  set u' : ℕ → H2 2 := fun n => u (n + N₀) with hu'
  have hM' : ∀ n, M (u' n) = m := fun n => hM _
  have hQ' : ∀ n, q₀ ≤ Q (u' n) := fun n => (hN₀ (n + N₀) (Nat.le_add_left _ _)).1
  have hD' : ∀ n, D (u' n) ≤ C := fun n => (hN₀ (n + N₀) (Nat.le_add_left _ _)).2
  -- translate
  obtain ⟨r, -, c₀, hc₀, y, hy⟩ := exists_translations hm hq hM' hQ' hD'
  set w : ℕ → H2 2 := fun n => translate (y n) (u' n) with hw
  have hMw : ∀ n, M (w n) = m := fun n => by rw [hw, M_translate, hM']
  have hDw : ∀ n, D (w n) ≤ C := fun n => by rw [hw, D_translate]; exact hD' n
  -- extract a profile
  obtain ⟨φ, hφ, U, hU, h0, -, h2⟩ := exists_profile hc₀ hMw hDw hy
  have hφN : Tendsto (fun n => φ n + N₀) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_add_right _ _) hφ.tendsto_atTop
  have hEW : Tendsto (fun n => energy β γ k (w (φ n))) atTop (𝓝 (Imin β γ k m)) := by
    refine (hE.comp hφN).congr fun n => ?_
    simp only [Function.comp_apply, hw, hu', energy_translate]
  obtain ⟨hUm, hUE, hdist⟩ := conclusion hβ hγ hm hmB (fun n => hMw (φ n)) (fun n => hDw (φ n))
    hEW hU h0 h2
  refine ⟨fun n => φ n + N₀, fun a b hab => Nat.add_lt_add_right (hφ hab) _,
    fun n => y (φ n), U, hUm, hUE, ?_⟩
  exact hdist

/-- **Attainment:** for `0 < m ≤ m_B` the minimizing set `𝒢_m` is nonempty. -/
theorem exists_minimizer (hβ : 0 < β) (hγ : 0 < γ) {m : ℝ} (hm : 0 < m)
    (hmB : m ≤ StrictBinding.mB β γ k) :
    ∃ U : H2 2, M U = m ∧ energy β γ k U = Imin β γ k m := by
  have hU : ∀ n : ℕ, ∃ U : H2 2, M U = m ∧ energy β γ k U < Imin β γ k m + 1 / ((n : ℝ) + 1) :=
    fun n => StrictBinding.exists_energy_lt hβ hm (by positivity)
  choose u hum hult using hU
  have hlim : Tendsto (fun n : ℕ => Imin β γ k m + 1 / ((n : ℝ) + 1)) atTop
      (𝓝 (Imin β γ k m)) := by
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_add (Imin β γ k m)
  have hE : Tendsto (fun n => energy β γ k (u n)) atTop (𝓝 (Imin β γ k m)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun n => StrictBinding.Imin_le_energy hγ (hum n)) (fun n => (hult n).le)
  obtain ⟨-, -, -, U, hUm, hUE, -⟩ := compactness hβ hγ hm hmB hum hE
  exact ⟨U, hUm, hUE⟩

/-- **Sequential compactness of `𝒢_m` modulo translations:** every sequence of minimizers has a
subsequence which, after translations, converges strongly in `H²` to a minimizer. -/
theorem minimizers_seq_compact (hβ : 0 < β) (hγ : 0 < γ) {m : ℝ} (hm : 0 < m)
    (hmB : m ≤ StrictBinding.mB β γ k) {u : ℕ → H2 2} (hM : ∀ n, M (u n) = m)
    (hE : ∀ n, energy β γ k (u n) = Imin β γ k m) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ y : ℕ → R2, ∃ U : H2 2, M U = m ∧
      energy β γ k U = Imin β γ k m ∧
      Tendsto (fun n => distH2 (translate (y n) (u (φ n))) U) atTop (𝓝 0) :=
  compactness hβ hγ hm hmB hM (by simp only [hE]; exact tendsto_const_nhds)

/-- **Theorem (whole-space existence and compactness).**  For `β, γ > 0`, every `k`, and every
`0 < m ≤ m_B = 3β/(γ√(k⁴ + 3β²/(32γ)))`:
(i) `−(3β²/(16γ)) m ≤ I(m) < 0`;
(ii) `I(m) < I(μ) + I(m − μ)` for every `0 < μ < m`;
(iii) every minimizing sequence is precompact in `H²(ℝ²)` modulo translations, with limits in
`𝒢_m = {u : M(u) = m, H(u) = I(m)}`; in particular `𝒢_m ≠ ∅`. -/
theorem main (hβ : 0 < β) (hγ : 0 < γ) {m : ℝ} (hm : 0 < m)
    (hmB : m ≤ StrictBinding.mB β γ k) :
    (-(3 * β ^ 2 / (16 * γ)) * m ≤ Imin β γ k m ∧ Imin β γ k m < 0) ∧
    (∀ μ, 0 < μ → μ < m → Imin β γ k m < Imin β γ k μ + Imin β γ k (m - μ)) ∧
    (∀ u : ℕ → H2 2, (∀ n, M (u n) = m) →
      Tendsto (fun n => energy β γ k (u n)) atTop (𝓝 (Imin β γ k m)) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ y : ℕ → R2, ∃ U : H2 2, M U = m ∧
        energy β γ k U = Imin β γ k m ∧
        Tendsto (fun n => distH2 (translate (y n) (u (φ n))) U) atTop (𝓝 0)) ∧
    (∃ U : H2 2, M U = m ∧ energy β γ k U = Imin β γ k m) :=
  ⟨NegativeEnergy.negative_constrained_energy hβ hγ hm,
    fun _ hμ hμm => StrictBinding.strict_binding hβ hγ hm hmB hμ hμm,
    fun _ hM hE => compactness hβ hγ hm hmB hM hE,
    exists_minimizer hβ hγ hm hmB⟩

end WholeSpace

end ReyesMath
