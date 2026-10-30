import MathProofs.E69Curvature
import MathProofs.E68Radial
import MathProofs.M6BDimensionalField

/-!
# E69: the scope remarks

* **Spatial dimensions.** `thresholds` (`s > 5/2, 3, 7/2, 4, 9/2` for `n = 1, …, 5`); `h2_linf`
  (`H² ↪ L^∞` for `n ≤ 3` bounds `ψ`); `h2_insufficient`: for every `1 ≤ n ≤ 3` there is
  `ψ ∈ H²(ℝⁿ)`, bounded, with `Δψ ∉ L^∞` and `Θ_ε[ψ] ∉ L^∞` for every `ε > 0`, `α ∈ ℝ`, so `H²`
  regularity alone does not yield Theorem E69. The field is `ψ = (1 − Δ)⁻¹h + t·b` with the
  singular profile `h = |x|^{-1/4} 1_{|x| ≤ 1} ∈ L²` and a bump `b`, so that `Δψ = ψ − h + t·Δb`.
* **Other domains.** `theta_bound_of_linf`: on any measure space (a bounded domain `Ω`, a torus,
  …) an `L^∞` bound for `Δψ`, with an `Ω`-dependent constant, gives the bound for `Θ_ε[ψ]`. The flat
  torus is treated in full in `E69Torus`.
* **Fixed regularization.** `no_uniform_in_eps`: a Schwartz field `q` (in every `H^s`) with
  `‖Θ_ε[q]‖_∞ ≥ n / (ε(1 + e^{2|α|}))` for `0 < ε < 1`; `not_uniform_bound`: no estimate
  `‖Θ_ε[ψ]‖_∞ ≤ C‖ψ‖_{H^s}` holds uniformly in `ε ∈ (0, 1)`.
* **Choice of regularizer.** `oldDen_vanishes`: for `ε > 0` and `α ≥ 0` the older denominator
  `z + εe^{-α|z|²}` vanishes at some `z ≠ 0` (at `z = −ε` when `α = 0`), and
  `oldDen_inv_unbounded`: its reciprocal is unbounded, in contrast with `denom_pos` and
  `norm_Rε_le_Mea`.
-/

open Filter Topology Complex InnerProductSpace MeasureTheory Set Metric
open scoped ContDiff FourierTransform ENNReal

namespace ReyesMath

namespace E69

open Sobolev E26

variable {n : ℕ}

local notation "Rn" => EuclideanSpace ℝ (Fin n)

/-! ### Essential suprema and pointwise bounds on open sets -/

/-- A lower bound on a nonempty open set bounds the essential supremum from below. -/
theorem ofReal_le_eLpNorm_top {f : Rn → ℂ} {U : Set Rn} (hU : IsOpen U) (hne : U.Nonempty)
    {c : ℝ} (hc : ∀ x ∈ U, c ≤ ‖f x‖) : ENNReal.ofReal c ≤ eLpNorm f ∞ volume := by
  rw [eLpNorm_exponent_top]
  by_contra h
  push_neg at h
  have hae := enorm_ae_le_eLpNormEssSup f volume
  rw [ae_iff] at hae
  have hpos := hU.measure_pos volume hne
  refine hpos.ne' (measure_mono_null (fun x hx => ?_) hae)
  simp only [mem_setOf_eq, not_le]
  calc eLpNormEssSup f volume < ENNReal.ofReal c := h
    _ ≤ ‖f x‖ₑ := by
      rw [← ofReal_norm_eq_enorm]
      exact ENNReal.ofReal_le_ofReal (hc x hx)

/-- If `f` exceeds every level on some nonempty open set, then `f ∉ L^∞`. -/
theorem not_memLp_top_of_unbounded {f : Rn → ℂ}
    (h : ∀ K : ℝ, ∃ U : Set Rn, IsOpen U ∧ U.Nonempty ∧ ∀ x ∈ U, K ≤ ‖f x‖) :
    ¬ MemLp f ∞ volume := by
  intro hf
  have htop : eLpNorm f ∞ volume = ⊤ := by
    refine ENNReal.eq_top_of_forall_nnreal_le fun r => ?_
    obtain ⟨U, hU, hne, hK⟩ := h r
    have := ofReal_le_eLpNorm_top hU hne hK
    rwa [ENNReal.ofReal_coe_nnreal] at this
  exact hf.eLpNorm_ne_top htop

theorem exists_norm_eq (hn : 1 ≤ n) {r : ℝ} (hr : 0 ≤ r) : ∃ x : Rn, ‖x‖ = r :=
  ⟨EuclideanSpace.single ⟨0, by omega⟩ r, by
    rw [EuclideanSpace.norm_single, Real.norm_of_nonneg hr]⟩

theorem isOpen_shell (a b : ℝ) : IsOpen {x : Rn | a < ‖x‖ ∧ ‖x‖ < b} :=
  (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)

theorem shell_nonempty (hn : 1 ≤ n) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    {x : Rn | a < ‖x‖ ∧ ‖x‖ < b}.Nonempty := by
  obtain ⟨x, hx⟩ := exists_norm_eq (n := n) hn (r := (a + b) / 2) (by linarith)
  exact ⟨x, by rw [mem_setOf_eq, hx]; constructor <;> linarith⟩

/-! ### Remark (spatial dimensions) -/

/-- The thresholds `s > n/2 + 2`: `5/2, 3, 7/2, 4, 9/2` for `n = 1, …, 5`. -/
theorem thresholds :
    ((1 : ℕ) : ℝ) / 2 + 2 = 5 / 2 ∧ ((2 : ℕ) : ℝ) / 2 + 2 = 3 ∧ ((3 : ℕ) : ℝ) / 2 + 2 = 7 / 2 ∧
      ((4 : ℕ) : ℝ) / 2 + 2 = 4 ∧ ((5 : ℕ) : ℝ) / 2 + 2 = 9 / 2 := by
  norm_num

/-- `H²(ℝⁿ) ↪ L^∞(ℝⁿ)` for `n ≤ 3`: `H²` bounds `ψ`. -/
theorem h2_linf (hn : n ≤ 3) {ψ : L2 n} (hψ : MemHs 2 ψ) :
    MemLp (ψ : Rn → ℂ) ∞ volume ∧
      eLpNorm (ψ : Rn → ℂ) ∞ volume ≤ ENNReal.ofReal (Cemb n 2 * hsNorm 2 ψ) := by
  have h : (n : ℝ) / 2 < 2 := by
    have : (n : ℝ) ≤ 3 := by exact_mod_cast hn
    linarith
  obtain ⟨-, -, h1, h2⟩ := embedding h hψ
  exact ⟨h1, h2⟩

/-! #### Linearity of the Laplacian and the resolvent `(1 − Δ)⁻¹` -/

theorem lap_add {u v : L2 n} (hu : MemHs 2 u) (hv : MemHs 2 v) : lap (u + v) = lap u + lap v := by
  apply FU.injective
  apply Lp.ext
  rw [map_add]
  filter_upwards [FU_lap (hu.add hv), FU_lap hu, FU_lap hv,
    Lp.coeFn_add (FU (lap u)) (FU (lap v)), Lp.coeFn_add (FU u) (FU v)] with ξ h1 h2 h3 h4 h5
  rw [h1, h4, Pi.add_apply, h2, h3, map_add, h5, Pi.add_apply]
  ring

theorem lap_smul (c : ℂ) {u : L2 n} (hu : MemHs 2 u) : lap (c • u) = c • lap u := by
  apply FU.injective
  apply Lp.ext
  rw [map_smul]
  filter_upwards [FU_lap (hu.smul c), FU_lap hu, Lp.coeFn_smul c (FU (lap u)),
    Lp.coeFn_smul c (FU u)] with ξ h1 h2 h3 h4
  rw [h1, h3, Pi.smul_apply, h2, map_smul, h4, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
  ring

theorem memLp_resolvSym (h : L2 n) :
    MemLp (fun ξ => (((1 + ‖ξ‖ ^ 2)⁻¹ : ℝ) : ℂ) * (FU h : Rn → ℂ) ξ) 2 volume := by
  refine (Lp.memLp (FU h)).of_le
    ((Complex.continuous_ofReal.comp ((continuous_const.add (continuous_norm.pow 2)).inv₀
      fun ξ => (one_add_sq_pos ξ).ne')).aestronglyMeasurable.mul (Lp.aestronglyMeasurable _))
    (Eventually.of_forall fun ξ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 (one_add_sq_pos ξ).le)]
  exact mul_le_of_le_one_left (norm_nonneg _) (inv_le_one_of_one_le₀ (one_le_one_add_sq ξ))

/-- The resolvent `(1 − Δ)⁻¹h = 𝓕⁻¹((1 + |ξ|²)⁻¹ ĥ)`. -/
noncomputable def resolv (h : L2 n) : L2 n := FU.symm ((memLp_resolvSym h).toLp _)

theorem FU_resolv (h : L2 n) :
    (FU (resolv h) : Rn → ℂ) =ᵐ[volume]
      fun ξ => (((1 + ‖ξ‖ ^ 2)⁻¹ : ℝ) : ℂ) * (FU h : Rn → ℂ) ξ := by
  rw [resolv, LinearIsometryEquiv.apply_symm_apply]
  exact (memLp_resolvSym h).coeFn_toLp

theorem memHs_resolv (h : L2 n) : MemHs 2 (resolv h) := by
  unfold MemHs
  refine (integrable_norm_sq (FU h)).congr ?_
  filter_upwards [FU_resolv h] with ξ hξ
  rw [hξ, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (inv_nonneg.2 (one_add_sq_pos ξ).le), mul_pow, jw_two, ← mul_assoc,
    ← mul_pow, mul_inv_cancel₀ (one_add_sq_pos ξ).ne', one_pow, one_mul]

/-- `Δ(1 − Δ)⁻¹h = (1 − Δ)⁻¹h − h`. -/
theorem lap_resolv (h : L2 n) : lap (resolv h) = resolv h - h := by
  apply FU.injective
  apply Lp.ext
  rw [map_sub]
  filter_upwards [FU_lap (memHs_resolv h), FU_resolv h,
    Lp.coeFn_sub (FU (resolv h)) (FU h)] with ξ h1 h2 h3
  rw [h1, h3, Pi.sub_apply, h2]
  have hne : (1 + (‖ξ‖ : ℂ) ^ 2) ≠ 0 := by exact_mod_cast (one_add_sq_pos ξ).ne'
  push_cast
  field_simp
  ring

/-! #### The singular profile and the bump -/

/-- The singular profile `h(x) = |x|^{-1/4} 1_{|x| ≤ 1}`. -/
noncomputable def hsing (x : Rn) : ℂ :=
  (((closedBall (0 : Rn) 1).indicator (fun y => ‖y‖ ^ (-(1 / 4 : ℝ))) x : ℝ) : ℂ)

theorem memLp_hsing (hn : 1 ≤ n) : MemLp (hsing (n := n)) 2 volume := by
  have hm : AEStronglyMeasurable (hsing (n := n)) volume :=
    (Complex.measurable_ofReal.comp
      ((measurable_norm.pow_const _).indicator measurableSet_closedBall)).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq_norm hm]
  have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  refine (E68.integrable_indicator_closedBall_rpow hn (t := -(1 / 2)) (by linarith) 1).congr
    (Eventually.of_forall fun x => ?_)
  simp only [hsing, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  by_cases hx : x ∈ closedBall (0 : Rn) 1
  · rw [indicator_of_mem hx, indicator_of_mem hx, ← Real.rpow_natCast,
      ← Real.rpow_mul (norm_nonneg _)]
    norm_num
  · rw [indicator_of_notMem hx, indicator_of_notMem hx]
    norm_num

theorem norm_hsing {x : Rn} (hx : ‖x‖ ≤ 1) : ‖hsing x‖ = ‖x‖ ^ (-(1 / 4 : ℝ)) := by
  rw [hsing, indicator_of_mem (mem_closedBall_zero_iff.2 hx), Complex.norm_real,
    Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]

/-- Near the origin `h` exceeds every level. -/
theorem hsing_large {B K : ℝ} (hB : 0 ≤ B) (hK : 0 ≤ K) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hρK : ρ ≤ (K + B + 1) ^ (-(4 : ℝ))) {x : Rn} (hx0 : 0 < ‖x‖) (hxρ : ‖x‖ < ρ) :
    K + B + 1 < ‖hsing x‖ := by
  rw [norm_hsing (hxρ.le.trans hρ1)]
  have h1 : ρ ^ (-(1 / 4 : ℝ)) < ‖x‖ ^ (-(1 / 4 : ℝ)) :=
    Real.rpow_lt_rpow_of_neg hx0 hxρ (by norm_num)
  have h2 : ((K + B + 1) ^ (-(4 : ℝ))) ^ (-(1 / 4 : ℝ)) ≤ ρ ^ (-(1 / 4 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hρ0 hρK (by norm_num)
  have h3 : ((K + B + 1) ^ (-(4 : ℝ))) ^ (-(1 / 4 : ℝ)) = K + B + 1 := by
    rw [← Real.rpow_mul (by linarith)]
    norm_num
  linarith

/-- A smooth bump, `= 1` on `B̄(0, 2)` and supported in `B̄(0, 3)`. -/
noncomputable def bumpC (n : ℕ) : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) :=
  ⟨2, 3, by norm_num, by norm_num⟩

/-- The bump as a Schwartz function. -/
noncomputable def bumpS (n : ℕ) : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ :=
  schwartzOfCompact (fun x => ((bumpC n x : ℝ) : ℂ))
    (Complex.ofRealCLM.contDiff.comp ((bumpC n).contDiff (n := ⊤)))
    ((bumpC n).hasCompactSupport.comp_left Complex.ofReal_zero)

theorem bumpS_apply (x : Rn) : bumpS n x = ((bumpC n x : ℝ) : ℂ) := rfl

theorem bumpC_eq_one {x : Rn} (hx : ‖x‖ ≤ 2) : bumpC n x = 1 :=
  (bumpC n).one_of_mem_closedBall (mem_closedBall_zero_iff.2 hx)

/-! #### `H²` regularity alone does not yield Theorem E69 -/

/-- `|R_ε(z)| ≥ (1/2)/(A² + ε²e^{2|α|A²})` for `1/2 ≤ |z| ≤ A`. -/
theorem norm_Rε_ge {ε : ℝ} (hε : 0 < ε) (α : ℝ) {A : ℝ} {z : ℂ} (h1 : 1 / 2 ≤ ‖z‖)
    (h2 : ‖z‖ ≤ A) :
    (1 / 2) / (A ^ 2 + ε ^ 2 * Real.exp (2 * |α| * A ^ 2)) ≤ ‖Rε ε α z‖ := by
  rw [norm_Rε hε]
  have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
  have hD : 0 < ‖z‖ ^ 2 + ε ^ 2 * Real.exp (-2 * α * ‖z‖ ^ 2) := by positivity
  have hexp : Real.exp (-2 * α * ‖z‖ ^ 2) ≤ Real.exp (2 * |α| * A ^ 2) := by
    refine Real.exp_le_exp.2 ?_
    have hzA : ‖z‖ ^ 2 ≤ A ^ 2 := pow_le_pow_left₀ hz0 h2 2
    have ha : -α ≤ |α| := neg_le_abs α
    nlinarith [abs_nonneg α, sq_nonneg ‖z‖]
  have hDle : ‖z‖ ^ 2 + ε ^ 2 * Real.exp (-2 * α * ‖z‖ ^ 2) ≤
      A ^ 2 + ε ^ 2 * Real.exp (2 * |α| * A ^ 2) := by
    have hzA : ‖z‖ ^ 2 ≤ A ^ 2 := pow_le_pow_left₀ hz0 h2 2
    nlinarith [sq_nonneg ε]
  exact div_le_div₀ hz0 h1 hD hDle

/-- **Remark (spatial dimensions): `H²` regularity alone does not yield Theorem E69.** For every
`1 ≤ n ≤ 3` there is `ψ ∈ H²(ℝⁿ; ℂ)`, bounded (`H² ↪ L^∞`), with `Δψ ∉ L^∞` and
`Θ_ε[ψ] ∉ L^∞` for every `ε > 0` and `α ∈ ℝ`. -/
theorem h2_insufficient (hn1 : 1 ≤ n) (hn3 : n ≤ 3) :
    ∃ ψ : L2 n, MemHs 2 ψ ∧ MemLp (ψ : Rn → ℂ) ∞ volume ∧
      ¬ MemLp (lap ψ : Rn → ℂ) ∞ volume ∧
      ∀ ε : ℝ, 0 < ε → ∀ α : ℝ, ¬ MemLp (Theta ε α ψ) ∞ volume := by
  have hn2 : (n : ℝ) / 2 < 2 := by
    have : (n : ℝ) ≤ 3 := by exact_mod_cast hn3
    linarith
  obtain ⟨H, hHdef⟩ : ∃ H : L2 n, H = (memLp_hsing hn1).toLp hsing := ⟨_, rfl⟩
  have hH : (H : Rn → ℂ) =ᵐ[volume] hsing := by
    rw [hHdef]
    exact (memLp_hsing hn1).coeFn_toLp
  obtain ⟨ψ₀, hψ₀⟩ : ∃ ψ₀ : L2 n, ψ₀ = resolv H := ⟨_, rfl⟩
  have h0 : MemHs 2 ψ₀ := hψ₀ ▸ memHs_resolv H
  obtain ⟨⟨f₀, hf₀c, hf₀, hf₀b⟩, -, -, -⟩ := embedding hn2 h0
  obtain ⟨C₀, hC₀⟩ : ∃ C₀ : ℝ, C₀ = Cemb n 2 * hsNorm 2 ψ₀ := ⟨_, rfl⟩
  have hC₀0 : 0 ≤ C₀ := hC₀ ▸ mul_nonneg (Cemb_nonneg _ _) (hsNorm_nonneg _ _)
  rw [← hC₀] at hf₀b
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = ‖f₀ 0‖ + 1 := ⟨_, rfl⟩
  have ht0 : 0 < t := by rw [ht]; positivity
  obtain ⟨b, hbdef⟩ : ∃ b : SchwartzMap Rn ℂ, b = bumpS n := ⟨_, rfl⟩
  have hb0 : b 0 = 1 := by rw [hbdef, bumpS_apply, bumpC_eq_one (by simp)]; simp
  obtain ⟨ψ, hψdef⟩ : ∃ ψ : L2 n, ψ = ψ₀ + (t : ℂ) • toL2 b := ⟨_, rfl⟩
  have hb2 : MemHs 2 ((t : ℂ) • toL2 b) := (memHs_toL2 2 _).smul _
  have hψ : MemHs 2 ψ := hψdef ▸ h0.add hb2
  -- a continuous representative of `ψ`, nonzero at the origin
  obtain ⟨f, hfdef⟩ : ∃ f : Rn → ℂ, f = fun x => f₀ x + (t : ℂ) * b x := ⟨_, rfl⟩
  have hf : (ψ : Rn → ℂ) =ᵐ[volume] f := by
    rw [hψdef, hfdef]
    filter_upwards [Lp.coeFn_add ψ₀ ((t : ℂ) • toL2 b), hf₀,
      Lp.coeFn_smul (t : ℂ) (toL2 b), coeFn_toL2 b] with x h1 h2 h3 h4
    rw [h1, Pi.add_apply, h2, h3, Pi.smul_apply, h4, smul_eq_mul]
  have hfc : Continuous f := by
    rw [hfdef]
    exact hf₀c.add (continuous_const.mul b.continuous)
  have hf0 : 1 ≤ ‖f 0‖ := by
    have hre : (f 0).re = (f₀ 0).re + t := by
      rw [hfdef]
      simp [hb0]
    have h1 : -‖f₀ 0‖ ≤ (f₀ 0).re := by
      have := Complex.abs_re_le_norm (f₀ 0)
      linarith [abs_le.1 this]
    calc (1 : ℝ) ≤ (f 0).re := by rw [hre, ht]; linarith
      _ ≤ ‖f 0‖ := Complex.re_le_norm _
  -- a representative of `Δψ = ψ₀ − h + t Δb`
  obtain ⟨B₁, hB₁⟩ : ∃ B₁ : ℝ, B₁ = SchwartzMap.seminorm ℂ 0 0 (lapS b) := ⟨_, rfl⟩
  have hB₁x : ∀ x, ‖lapS b x‖ ≤ B₁ := fun x => hB₁ ▸ SchwartzMap.norm_le_seminorm ℂ _ x
  have hB₁0 : 0 ≤ B₁ := (norm_nonneg _).trans (hB₁x 0)
  obtain ⟨Lf, hLf⟩ : ∃ Lf : Rn → ℂ, Lf = fun x => f₀ x - hsing x + (t : ℂ) * lapS b x :=
    ⟨_, rfl⟩
  have hL : (lap ψ : Rn → ℂ) =ᵐ[volume] Lf := by
    have e : lap ψ = (ψ₀ - H) + (t : ℂ) • toL2 (lapS b) := by
      rw [hψdef, lap_add h0 hb2, lap_smul _ (memHs_toL2 2 _), hψ₀, lap_resolv, lap_toL2]
    rw [e, hLf]
    filter_upwards [Lp.coeFn_add (ψ₀ - H) ((t : ℂ) • toL2 (lapS b)), Lp.coeFn_sub ψ₀ H,
      hf₀, hH, Lp.coeFn_smul (t : ℂ) (toL2 (lapS b)),
      coeFn_toL2 (lapS b)] with x h1 h2 h3 h4 h5 h6
    rw [h1, Pi.add_apply, h2, Pi.sub_apply, h3, h4, h5, Pi.smul_apply, h6, smul_eq_mul]
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = C₀ + t * B₁ := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  have hB : ∀ x, ‖f₀ x + (t : ℂ) * lapS b x‖ ≤ B := fun x => by
    calc ‖f₀ x + (t : ℂ) * lapS b x‖ ≤ ‖f₀ x‖ + ‖(t : ℂ) * lapS b x‖ :=
          norm_add_le _ _
      _ ≤ C₀ + t * B₁ := by
        refine add_le_add (hf₀b x) ?_
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0.le]
        exact mul_le_mul_of_nonneg_left (hB₁x x) ht0.le
      _ = B := hBdef.symm
  -- `|Δψ| ≥ K` on a punctured ball, for every `K ≥ 0`
  have hlarge : ∀ {K : ℝ}, 0 ≤ K → ∀ {ρ : ℝ}, 0 < ρ → ρ ≤ 1 → ρ ≤ (K + B + 1) ^ (-(4 : ℝ)) →
      ∀ x : Rn, 0 < ‖x‖ → ‖x‖ < ρ → K ≤ ‖Lf x‖ := by
    intro K hK ρ hρ0 hρ1 hρK x hx0 hxρ
    have h1 := hsing_large hB0 hK hρ0 hρ1 hρK hx0 hxρ
    have h2 := norm_sub_norm_le (hsing x) (f₀ x + (t : ℂ) * lapS b x)
    have e : Lf x = -(hsing x - (f₀ x + (t : ℂ) * lapS b x)) := by
      rw [hLf]
      ring
    rw [e, norm_neg]
    linarith [hB x]
  have hpow_pos : ∀ K : ℝ, 0 ≤ K → 0 < (K + B + 1) ^ (-(4 : ℝ)) := fun K hK =>
    Real.rpow_pos_of_pos (by linarith) _
  refine ⟨ψ, hψ, ?_, ?_, ?_⟩
  · obtain ⟨-, -, h1, -⟩ := embedding hn2 hψ
    exact h1
  · rw [memLp_congr_ae hL]
    refine not_memLp_top_of_unbounded fun K => ?_
    set K' := max K 0
    have hK' : 0 ≤ K' := le_max_right _ _
    set ρ := min 1 ((K' + B + 1) ^ (-(4 : ℝ)))
    have hρ0 : 0 < ρ := lt_min one_pos (hpow_pos K' hK')
    refine ⟨{x : Rn | 0 < ‖x‖ ∧ ‖x‖ < ρ}, isOpen_shell _ _, shell_nonempty hn1 le_rfl hρ0,
      fun x hx => (le_max_left K 0).trans (hlarge hK' hρ0 (min_le_left _ _) (min_le_right _ _)
        x hx.1 hx.2)⟩
  · intro ε hε α
    have hTh : Theta ε α ψ =ᵐ[volume] fun x => -(Lf x) * Rε ε α (f x) :=
      (Theta_congr_ae ε α ψ hf.symm hL.symm).symm
    rw [memLp_congr_ae hTh]
    -- `|R_ε(f)| ≥ m` near the origin
    obtain ⟨δ, hδ, hδf⟩ := Metric.continuousAt_iff.1 hfc.continuousAt (1 / 2) (by norm_num)
    set A := ‖f 0‖ + 1 / 2 with hA
    set m := (1 / 2) / (A ^ 2 + ε ^ 2 * Real.exp (2 * |α| * A ^ 2)) with hm
    have hm0 : 0 < m := by positivity
    have hR : ∀ x : Rn, ‖x‖ < δ → m ≤ ‖Rε ε α (f x)‖ := fun x hx => by
      have hd := hδf (by rwa [dist_zero_right])
      rw [dist_eq_norm] at hd
      have hlo : 1 / 2 ≤ ‖f x‖ := by
        have := norm_sub_norm_le (f 0) (f x)
        rw [norm_sub_rev] at this
        linarith
      have hhi : ‖f x‖ ≤ A := by
        have := norm_le_insert' (f x) (f 0)
        rw [hA]
        linarith
      exact norm_Rε_ge hε α hlo hhi
    refine not_memLp_top_of_unbounded fun K => ?_
    set K' := max K 0
    have hK' : 0 ≤ K' := le_max_right _ _
    have hKm : 0 ≤ K' / m := div_nonneg hK' hm0.le
    set ρ := min (min 1 δ) ((K' / m + B + 1) ^ (-(4 : ℝ)))
    have hρ0 : 0 < ρ := lt_min (lt_min one_pos hδ) (hpow_pos _ hKm)
    refine ⟨{x : Rn | 0 < ‖x‖ ∧ ‖x‖ < ρ}, isOpen_shell _ _, shell_nonempty hn1 le_rfl hρ0,
      fun x hx => ?_⟩
    have hxδ : ‖x‖ < δ := hx.2.trans_le ((min_le_left _ _).trans (min_le_right _ _))
    have h1 := hlarge hKm hρ0 ((min_le_left _ _).trans (min_le_left _ _)) (min_le_right _ _) x
      hx.1 hx.2
    have h2 := hR x hxδ
    rw [norm_mul, norm_neg]
    calc K ≤ K' := le_max_left _ _
      _ = K' / m * m := by field_simp
      _ ≤ ‖Lf x‖ * ‖Rε ε α (f x)‖ := mul_le_mul h1 h2 hm0.le (norm_nonneg _)

/-! ### Remark (other domains) -/

/-- **Remark (other domains).** On any measure space — a bounded Lipschitz extension domain
`Ω ⊂ ℝⁿ` with Lebesgue measure, a torus, … — an available embedding bound
`‖Δψ‖_{L^∞(Ω)} ≤ C_Ω N` (with `N` the relevant Sobolev norm of `ψ`) gives
`Θ_ε[ψ] ∈ L^∞(Ω)` and `‖Θ_ε[ψ]‖_{L^∞(Ω)} ≤ C_Ω M_{ε,α} N`, the constant depending on `Ω`. -/
theorem theta_bound_of_linf {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {ε : ℝ} (hε : 0 < ε)
    (α : ℝ) {ψ F : Ω → ℂ} (hψ : AEStronglyMeasurable ψ μ) (hF : AEStronglyMeasurable F μ)
    {CΩ N : ℝ} (hemb : ∀ᵐ x ∂μ, ‖F x‖ ≤ CΩ * N) :
    MemLp (fun x => -(F x) * Rε ε α (ψ x)) ∞ μ ∧
      (∀ᵐ x ∂μ, ‖-(F x) * Rε ε α (ψ x)‖ ≤ CΩ * Mea ε α * N) ∧
      eLpNorm (fun x => -(F x) * Rε ε α (ψ x)) ∞ μ ≤ ENNReal.ofReal (CΩ * Mea ε α * N) := by
  have hb : ∀ᵐ x ∂μ, ‖-(F x) * Rε ε α (ψ x)‖ ≤ CΩ * Mea ε α * N := by
    filter_upwards [hemb] with x hx
    rw [norm_mul, norm_neg]
    calc ‖F x‖ * ‖Rε ε α (ψ x)‖ ≤ (CΩ * N) * Mea ε α :=
          mul_le_mul hx (norm_Rε_le_Mea hε α _) (norm_nonneg _) ((norm_nonneg _).trans hx)
      _ = CΩ * Mea ε α * N := by ring
  have hm : AEStronglyMeasurable (fun x => -(F x) * Rε ε α (ψ x)) μ :=
    hF.neg.mul ((continuous_Rε hε α).comp_aestronglyMeasurable hψ)
  refine ⟨memLp_top_of_bound hm _ hb, hb, ?_⟩
  rw [eLpNorm_exponent_top]
  exact eLpNormEssSup_le_of_ae_bound hb

/-! ### Remark (fixed regularization): no uniform estimate as `ε ↓ 0` -/

/-- The field `q(x) = (|x|² − 1) b(x)`, smooth and compactly supported. -/
noncomputable def qfun (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) : ℝ := (‖x‖ ^ 2 - 1) * bumpC n x

theorem contDiff_qfun : ContDiff ℝ ∞ (qfun n) :=
  (((contDiff_norm_sq ℝ).sub contDiff_const).mul ((bumpC n).contDiff (n := ⊤)))

theorem hasCompactSupport_qfun : HasCompactSupport (qfun n) := by
  have : qfun n = (fun x : Rn => ‖x‖ ^ 2 - 1) * ⇑(bumpC n) := rfl
  rw [this]
  exact (bumpC n).hasCompactSupport.mul_left

/-- `q` as a Schwartz function. -/
noncomputable def qS (n : ℕ) : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ :=
  schwartzOfCompact (fun x => ((qfun n x : ℝ) : ℂ))
    (Complex.ofRealCLM.contDiff.comp contDiff_qfun) (hasCompactSupport_qfun.comp_left
      Complex.ofReal_zero)

theorem qS_apply (x : Rn) : qS n x = ((qfun n x : ℝ) : ℂ) := rfl

theorem qfun_eq {x : Rn} (hx : ‖x‖ ≤ 2) : qfun n x = ‖x‖ ^ 2 - 1 := by
  rw [qfun, bumpC_eq_one hx, mul_one]

/-- `Δ(|x|² − 1) = 2n`. -/
theorem laplacian_norm_sq_sub (x : Rn) : Δ (fun y : Rn => ‖y‖ ^ 2 - 1) x = 2 * (n : ℝ) := by
  have e : (fun y : Rn => ‖y‖ ^ 2 - 1) = (fun y : Rn => ‖y‖ ^ 2) + fun _ => (-1 : ℝ) := by
    funext y
    simp [sub_eq_add_neg]
  have hzero : Δ (fun _ : Rn => (-1 : ℝ)) x = 0 := by
    rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
    simp [iteratedFDeriv_const_of_ne two_ne_zero]
  rw [e, ((contDiff_norm_sq ℝ).contDiffAt).laplacian_add contDiff_const.contDiffAt, hzero,
    add_zero, M6B.squared_norm_laplacian_D]

/-- `Δq = 2n` on the ball `|x| < 2`. -/
theorem lapS_qS {x : Rn} (hx : ‖x‖ < 2) : lapS (qS n) x = ((2 * n : ℝ) : ℂ) := by
  rw [lapS_apply]
  have hloc : (⇑(qS n)) =ᶠ[𝓝 x] fun y : Rn => (((‖y‖ ^ 2 - 1 : ℝ)) : ℂ) := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hx)] with y hy
    rw [qS_apply, qfun_eq (mem_ball_zero_iff.1 hy).le]
  rw [(laplacian_congr_nhds hloc).eq_of_nhds]
  have h2 : ContDiffAt ℝ 2 (fun y : Rn => ‖y‖ ^ 2 - 1) x :=
    ((contDiff_norm_sq ℝ).sub contDiff_const).contDiffAt
  have e : (fun y : Rn => (((‖y‖ ^ 2 - 1 : ℝ)) : ℂ)) =
      (⇑Complex.ofRealCLM) ∘ fun y : Rn => ‖y‖ ^ 2 - 1 := by
    funext y
    simp
  rw [e, h2.laplacian_CLM_comp_left]
  simp [laplacian_norm_sq_sub]

/-- `|R_ε(t)| ≥ (1/2)/(ε(1 + e^{2|α|}))` for real `ε/2 ≤ t ≤ ε < 1`. -/
theorem norm_Rε_real_ge {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (α : ℝ) {t : ℝ} (ht1 : ε / 2 ≤ t)
    (ht2 : t ≤ ε) :
    (1 / 2) / (ε * (1 + Real.exp (2 * |α|))) ≤ ‖Rε ε α (t : ℂ)‖ := by
  rw [norm_Rε hε, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have ht0 : 0 < t := by linarith
  have hexp : Real.exp (-2 * α * t ^ 2) ≤ Real.exp (2 * |α|) := by
    refine Real.exp_le_exp.2 ?_
    have hts : t ^ 2 ≤ 1 := by nlinarith
    have ha : -α ≤ |α| := neg_le_abs α
    nlinarith [abs_nonneg α, sq_nonneg t]
  have hD : 0 < t ^ 2 + ε ^ 2 * Real.exp (-2 * α * t ^ 2) := by positivity
  have hDle : t ^ 2 + ε ^ 2 * Real.exp (-2 * α * t ^ 2) ≤ ε ^ 2 * (1 + Real.exp (2 * |α|)) := by
    have : t ^ 2 ≤ ε ^ 2 := pow_le_pow_left₀ ht0.le ht2 2
    nlinarith [sq_nonneg ε]
  calc (1 / 2) / (ε * (1 + Real.exp (2 * |α|))) = (ε / 2) / (ε ^ 2 * (1 + Real.exp (2 * |α|))) := by
        field_simp
    _ ≤ t / (t ^ 2 + ε ^ 2 * Real.exp (-2 * α * t ^ 2)) := div_le_div₀ ht0.le ht1 hD hDle

/-- **Remark (fixed regularization).** The Schwartz field `q = (|x|² − 1) b` lies in every `H^s`,
but `‖Θ_ε[q]‖_∞ ≥ n / (ε(1 + e^{2|α|}))` for `0 < ε < 1`: the bound of Theorem E69 does not hold
uniformly as `ε ↓ 0`. -/
theorem no_uniform_in_eps (hn : 1 ≤ n) (α : ℝ) :
    (∀ s, MemHs s (toL2 (qS n))) ∧
      ∀ ε : ℝ, 0 < ε → ε < 1 →
        ENNReal.ofReal (n / (ε * (1 + Real.exp (2 * |α|)))) ≤
          eLpNorm (Theta ε α (toL2 (qS n))) ∞ volume := by
  refine ⟨fun s => memHs_toL2 s _, fun ε hε hε1 => ?_⟩
  have hTh : Theta ε α (toL2 (qS n)) =ᵐ[volume]
      fun x => -(Δ (⇑(qS n)) x) * Rε ε α (qS n x) :=
    (Theta_congr_ae ε α _ (coeFn_toL2 (qS n)).symm (lap_toL2_ae (qS n)).symm).symm
  rw [eLpNorm_congr_ae hTh]
  have ha : 0 ≤ Real.sqrt (1 + ε / 2) := Real.sqrt_nonneg _
  have hab : Real.sqrt (1 + ε / 2) < Real.sqrt (1 + ε) :=
    Real.sqrt_lt_sqrt (by linarith) (by linarith)
  refine ofReal_le_eLpNorm_top (isOpen_shell _ _) (shell_nonempty hn ha hab) fun x hx => ?_
  have hx2 : ‖x‖ < 2 := by
    have : Real.sqrt (1 + ε) < 2 := by
      rw [Real.sqrt_lt' two_pos]
      linarith
    linarith [hx.2]
  have hsq1 : 1 + ε / 2 < ‖x‖ ^ 2 := (Real.sqrt_lt' (ha.trans_lt hx.1)).1 hx.1
  have hsq2 : ‖x‖ ^ 2 < 1 + ε := (Real.lt_sqrt (norm_nonneg x)).1 hx.2
  rw [← lapS_apply, lapS_qS hx2, qS_apply, qfun_eq hx2.le, norm_mul, norm_neg,
    Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hR := norm_Rε_real_ge hε hε1 α (t := ‖x‖ ^ 2 - 1) (by linarith) (by linarith)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  calc (n : ℝ) / (ε * (1 + Real.exp (2 * |α|)))
      = (2 * n) * ((1 / 2) / (ε * (1 + Real.exp (2 * |α|)))) := by ring
    _ ≤ (2 * n) * ‖Rε ε α (((‖x‖ ^ 2 - 1 : ℝ)) : ℂ)‖ :=
        mul_le_mul_of_nonneg_left hR (by positivity)

/-- **No estimate `‖Θ_ε[ψ]‖_∞ ≤ C ‖ψ‖_{H^s}` holds uniformly in `ε ∈ (0, 1)`**, for any `n ≥ 1`,
`α`, `s` and `C`. -/
theorem not_uniform_bound (hn : 1 ≤ n) (α s : ℝ) :
    ¬ ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ ψ : L2 n, MemHs s ψ →
      eLpNorm (Theta ε α ψ) ∞ volume ≤ ENNReal.ofReal (C * hsNorm s ψ) := by
  rintro ⟨C, hC⟩
  obtain ⟨hq, hlow⟩ := no_uniform_in_eps (n := n) hn α
  set N := hsNorm s (toL2 (qS n))
  set E := 1 + Real.exp (2 * |α|)
  have hE : 0 < E := by positivity
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set Mx := max (C * N) 0
  set ε := min (1 / 2) (n / ((Mx + 1) * E))
  have hε : 0 < ε := lt_min (by norm_num) (by positivity)
  have hε1 : ε < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have h := (hlow ε hε hε1).trans (hC ε hε hε1 _ (hq s))
  rw [ENNReal.ofReal_le_ofReal_iff'] at h
  have hbig : Mx + 1 ≤ n / (ε * E) := by
    rw [le_div_iff₀ (by positivity)]
    have : ε ≤ n / ((Mx + 1) * E) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at this
    nlinarith
  rcases h with h | h
  · have : C * N ≤ Mx := le_max_left _ _
    linarith
  · have : 0 < n / (ε * E) := by positivity
    linarith

/-! ### Remark (choice of regularizer): the older denominator vanishes -/

/-- The older complex denominator `z + ε e^{−α|z|²}`. -/
noncomputable def oldDen (ε α : ℝ) (z : ℂ) : ℂ := z + (ε : ℂ) * (Real.exp (-α * ‖z‖ ^ 2) : ℂ)

theorem continuous_oldDen (ε α : ℝ) : Continuous (oldDen ε α) :=
  continuous_id.add (continuous_const.mul (Complex.continuous_ofReal.comp
    (Real.continuous_exp.comp (continuous_const.mul (continuous_norm.pow 2)))))

/-- At `α = 0` the older denominator vanishes at `z = −ε`. -/
theorem oldDen_zero_alpha (ε : ℝ) : oldDen ε 0 (-(ε : ℂ)) = 0 := by
  simp [oldDen]

/-- **The older denominator vanishes**: for `ε > 0` and `α ≥ 0` there is `z = −t`, `0 < t ≤ ε`,
with `z + ε e^{−α|z|²} = 0`. -/
theorem oldDen_vanishes {ε : ℝ} (hε : 0 < ε) {α : ℝ} (hα : 0 ≤ α) :
    ∃ t : ℝ, 0 < t ∧ t ≤ ε ∧ oldDen ε α (-(t : ℂ)) = 0 := by
  set g : ℝ → ℝ := fun t => ε * Real.exp (-α * t ^ 2) - t
  have hg : ContinuousOn g (Icc 0 ε) :=
    ((continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul
      (continuous_pow 2)))).sub continuous_id).continuousOn
  have hg0 : g 0 = ε := by simp [g]
  have hgε : g ε ≤ 0 := by
    simp only [g]
    have : Real.exp (-α * ε ^ 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg ε])
    nlinarith
  obtain ⟨t, ht, hgt⟩ := intermediate_value_Icc' hε.le hg ⟨hgε, by rw [hg0]; exact hε.le⟩
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [hg0] at hgt
    exact hε.ne' hgt
  refine ⟨t, lt_of_le_of_ne ht.1 (Ne.symm ht0), ht.2, ?_⟩
  have hnorm : ‖-(t : ℂ)‖ ^ 2 = t ^ 2 := by
    rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [oldDen, hnorm]
  have : ε * Real.exp (-α * t ^ 2) = t := by simp only [g] at hgt; linarith
  rw [← Complex.ofReal_mul, this]
  ring

/-- **Its reciprocal is unbounded**: for `ε > 0`, `α ≥ 0` and every `M`, some `z` has
`|1/(z + εe^{−α|z|²})| > M` (whereas `|R_ε| ≤ M_{ε,α}`, `norm_Rε_le_Mea`). -/
theorem oldDen_inv_unbounded {ε : ℝ} (hε : 0 < ε) {α : ℝ} (hα : 0 ≤ α) (M : ℝ) :
    ∃ z : ℂ, M < ‖(oldDen ε α z)⁻¹‖ := by
  obtain ⟨t, -, -, ht⟩ := oldDen_vanishes hε hα
  set z₀ : ℂ := -(t : ℂ)
  set η : ℝ := 1 / (|M| + 1)
  have hη : 0 < η := by positivity
  obtain ⟨δ, hδ, hδf⟩ := Metric.continuousAt_iff.1 (continuous_oldDen ε α).continuousAt η hη
  set w : ℂ := z₀ + ((δ / 2 : ℝ) : ℂ) * Complex.I
  have hw : dist w z₀ < δ := by
    rw [dist_eq_norm]
    simp only [w, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (half_pos hδ)]
    linarith
  have h1 := hδf hw
  rw [dist_eq_norm, ht, sub_zero] at h1
  have hne : oldDen ε α w ≠ 0 := by
    intro h0
    have him := congrArg Complex.im h0
    simp only [oldDen, w, z₀, Complex.add_im, Complex.neg_im, Complex.ofReal_im, neg_zero,
      Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero,
      zero_add, Complex.zero_im] at him
    linarith
  have hpos : 0 < ‖oldDen ε α w‖ := norm_pos_iff.2 hne
  refine ⟨w, ?_⟩
  rw [norm_inv]
  have : |M| + 1 < ‖oldDen ε α w‖⁻¹ := by
    rw [lt_inv_comm₀ (by positivity) hpos]
    simpa [η, one_div] using h1
  linarith [le_abs_self M]

end E69

end ReyesMath
