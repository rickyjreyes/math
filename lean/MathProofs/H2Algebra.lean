import Mathlib
import MathProofs.FreeEvolution

/-!
# The `H²(ℝ²)` algebra and the cubic–quintic nonlinearity (F01/T3, part 2)

Supporting module for `papers/orbital-stability-fourth-order-cubic-quintic/main.tex`.

* Products and conjugates of Schwartz functions (`Sobolev.mulS`, `Sobolev.conjS`) with the
  Leibniz rules for `∂ᵢ` and `Δ`.
* `Sobolev.norm_ιS_mulS_le`: `‖φψ‖_{H²} ≤ 15 ‖φ‖_{H²} ‖ψ‖_{H²}` on `𝓢(ℝ²)` (Leibniz, an `L⁴` bound
  for first derivatives by integration by parts, and `‖φ‖_∞ ≤ ‖φ‖_{H²}`); hence the bounded bilinear
  product `Sobolev.pmul` and the antilinear isometry `Sobolev.conjH` on `H²(ℝ²)`, realized a.e. by
  pointwise products (`Sobolev.vl_pmul_ae`, `Sobolev.vl_conjH_ae`).
* `Sobolev.Fnl`: `F(u) = −β|u|²u + γ|u|⁴u` on `H²(ℝ²)`, equal a.e. to `Sobolev.fnl β γ ∘ u`
  (`Sobolev.vl_Fnl_ae`), locally Lipschitz (`Sobolev.norm_Fnl_sub_le`), with
  `Im⟪u, F(u)⟫ = 0` (`Sobolev.inner_vl_Fnl_im`).
* The potential energy `Sobolev.Nsp` (`= −(β/2)Q + (γ/3)S`, `Sobolev.Nsp_eq`) and its second-order
  Taylor estimate `Sobolev.Nsp_taylor`.
-/

open Filter Topology Complex InnerProductSpace MeasureTheory Set
open scoped ContDiff FourierTransform

namespace ReyesMath

namespace Sobolev

variable {d : ℕ}

local notation "Rd" => EuclideanSpace ℝ (Fin d)

/-! ### Products and conjugates of Schwartz functions -/

theorem schwartz_hasTemperateGrowth (ψ : SchwartzMap Rd ℂ) : (⇑ψ).HasTemperateGrowth :=
  ⟨ψ.smooth ⊤, fun n => ⟨0, SchwartzMap.seminorm ℝ 0 n ψ, fun x => by
    have := ψ.le_seminorm ℝ 0 n x
    simpa using this⟩⟩

/-- The product of two Schwartz functions. -/
noncomputable def mulS (φ ψ : SchwartzMap Rd ℂ) : SchwartzMap Rd ℂ :=
  SchwartzMap.bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) (schwartz_hasTemperateGrowth ψ) φ

theorem mulS_apply (φ ψ : SchwartzMap Rd ℂ) (x : Rd) : mulS φ ψ x = φ x * ψ x := rfl

theorem coe_mulS (φ ψ : SchwartzMap Rd ℂ) : ⇑(mulS φ ψ) = fun x => φ x * ψ x := rfl

theorem mulS_add_left (φ φ' ψ : SchwartzMap Rd ℂ) :
    mulS (φ + φ') ψ = mulS φ ψ + mulS φ' ψ := by
  ext x; simp only [mulS_apply, SchwartzMap.add_apply, add_mul]

theorem mulS_add_right (φ ψ ψ' : SchwartzMap Rd ℂ) :
    mulS φ (ψ + ψ') = mulS φ ψ + mulS φ ψ' := by
  ext x; simp only [mulS_apply, SchwartzMap.add_apply, mul_add]

theorem mulS_smul_left (c : ℂ) (φ ψ : SchwartzMap Rd ℂ) : mulS (c • φ) ψ = c • mulS φ ψ := by
  ext x; simp only [mulS_apply, SchwartzMap.smul_apply, smul_eq_mul, mul_assoc]

theorem mulS_smul_right (c : ℂ) (φ ψ : SchwartzMap Rd ℂ) : mulS φ (c • ψ) = c • mulS φ ψ := by
  ext x; simp only [mulS_apply, SchwartzMap.smul_apply, smul_eq_mul]; ring

theorem mulS_comm (φ ψ : SchwartzMap Rd ℂ) : mulS φ ψ = mulS ψ φ := by
  ext x; simp only [mulS_apply, mul_comm]

/-- The complex conjugate of a Schwartz function. -/
noncomputable def conjS (φ : SchwartzMap Rd ℂ) : SchwartzMap Rd ℂ where
  toFun x := (starRingEnd ℂ) (φ x)
  smooth' := Complex.conjCLE.toContinuousLinearMap.contDiff.comp (φ.smooth ⊤)
  decay' k n := by
    obtain ⟨C, -, hC⟩ := φ.decay k n
    refine ⟨C, fun x => ?_⟩
    have h := Complex.conjLIE.norm_iteratedFDeriv_comp_left (𝕜 := ℝ) (⇑φ) x n
    have e : (fun x => (starRingEnd ℂ) (φ x)) = ⇑Complex.conjLIE ∘ ⇑φ := rfl
    rw [e, h]
    exact hC x

theorem conjS_apply (φ : SchwartzMap Rd ℂ) (x : Rd) : conjS φ x = (starRingEnd ℂ) (φ x) := rfl

theorem conjS_add (φ ψ : SchwartzMap Rd ℂ) : conjS (φ + ψ) = conjS φ + conjS ψ := by
  ext x; simp only [conjS_apply, SchwartzMap.add_apply, map_add]

theorem conjS_smul (c : ℂ) (φ : SchwartzMap Rd ℂ) :
    conjS (c • φ) = (starRingEnd ℂ) c • conjS φ := by
  ext x; simp only [conjS_apply, SchwartzMap.smul_apply, smul_eq_mul, map_mul]

theorem coe_sum_schwartz' {ι : Type*} (s : Finset ι) (f : ι → SchwartzMap Rd ℂ) (x : Rd) :
    (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, SchwartzMap.add_apply, ih]

theorem conjS_sum {ι : Type*} (s : Finset ι) (f : ι → SchwartzMap Rd ℂ) :
    conjS (∑ i ∈ s, f i) = ∑ i ∈ s, conjS (f i) := by
  ext x
  simp only [conjS_apply, coe_sum_schwartz', map_sum]

theorem dS_mulS (i : Fin d) (φ ψ : SchwartzMap Rd ℂ) :
    dS i (mulS φ ψ) = mulS (dS i φ) ψ + mulS φ (dS i ψ) := by
  ext x
  rw [dS_apply, SchwartzMap.add_apply, mulS_apply, mulS_apply, dS_apply, dS_apply, coe_mulS]
  have h := (φ.differentiableAt (x := x)).hasFDerivAt.fun_mul (ψ.differentiableAt (x := x)).hasFDerivAt
  rw [h.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem dS_conjS (i : Fin d) (φ : SchwartzMap Rd ℂ) : dS i (conjS φ) = conjS (dS i φ) := by
  ext x
  rw [dS_apply, conjS_apply, dS_apply]
  have e : ⇑(conjS φ) = ⇑(Complex.conjCLE.toContinuousLinearMap) ∘ ⇑φ := rfl
  have h := (Complex.conjCLE.toContinuousLinearMap.hasFDerivAt (x := φ x)).comp x
    (φ.differentiableAt (x := x)).hasFDerivAt
  rw [e, h.fderiv]
  rfl

theorem lapS_eq_sum (φ : SchwartzMap Rd ℂ) : lapS φ = ∑ i : Fin d, dS i (dS i φ) := by
  simp [lapS]

theorem lapS_mulS (φ ψ : SchwartzMap Rd ℂ) :
    lapS (mulS φ ψ) = mulS (lapS φ) ψ + (2 : ℂ) • ∑ i : Fin d, mulS (dS i φ) (dS i ψ) +
      mulS φ (lapS ψ) := by
  ext x
  simp only [lapS_eq_sum, dS_mulS, map_add, coe_sum_schwartz', SchwartzMap.add_apply, mulS_apply,
    SchwartzMap.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem lapS_conjS (φ : SchwartzMap Rd ℂ) : lapS (conjS φ) = conjS (lapS φ) := by
  rw [lapS_eq_sum, lapS_eq_sum, conjS_sum]
  simp only [dS_conjS]

end Sobolev

end ReyesMath

open Filter Topology Complex InnerProductSpace MeasureTheory Set
open scoped ContDiff FourierTransform

namespace ReyesMath

/-- Cauchy–Schwarz for nonnegative real functions: `(∫ fg)² ≤ ∫ f² ∫ g²`. -/
theorem sq_integral_mul_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ}
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) (hfg : Integrable (fun x => f x * g x) μ)
    (hf : Integrable (fun x => f x ^ 2) μ) (hg : Integrable (fun x => g x ^ 2) μ) :
    (∫ x, f x * g x ∂μ) ^ 2 ≤ (∫ x, f x ^ 2 ∂μ) * (∫ x, g x ^ 2 ∂μ) := by
  refine Sobolev.sq_le_of_forall_amgm (integral_nonneg fun x => mul_nonneg (hf0 x) (hg0 x))
    (integral_nonneg fun x => sq_nonneg _) (integral_nonneg fun x => sq_nonneg _) fun t ht => ?_
  have hR : Integrable (fun x => (t * (f x ^ 2 / 1) + 1 * g x ^ 2 / t) / 2) μ := by
    simp only [div_one, one_mul]
    exact ((hf.const_mul t).add (hg.div_const t)).div_const 2
  calc ∫ x, f x * g x ∂μ ≤ ∫ x, (t * (f x ^ 2 / 1) + 1 * g x ^ 2 / t) / 2 ∂μ :=
        integral_mono hfg hR fun x => Sobolev.mul_le_amgm one_pos ht
    _ = (t * ∫ x, f x ^ 2 ∂μ + (∫ x, g x ^ 2 ∂μ) / t) / 2 := by
        simp only [div_one, one_mul]
        rw [integral_div, integral_add (hf.const_mul t) (hg.div_const t), integral_const_mul,
          integral_div]

namespace Sobolev

variable {d : ℕ}

local notation "Rd" => EuclideanSpace ℝ (Fin d)

local notation "R2" => EuclideanSpace ℝ (Fin 2)

/-- `‖φ‖²_{H²} = ‖φ‖² + ‖Δφ‖² + Σᵢ‖∂ᵢφ‖²`. -/
theorem norm_ιS_sq (φ : SchwartzMap Rd ℂ) :
    ‖ιS φ‖ ^ 2 = ‖toL2 φ‖ ^ 2 + ‖toL2 (lapS φ)‖ ^ 2 + ∑ i : Fin d, ‖toL2 (dS i φ)‖ ^ 2 := by
  change ‖((ιS φ : Hsp d) : E3 d)‖ ^ 2 = _
  rw [PiLp.norm_sq_eq_of_L2, Fintype.sum_option, Fintype.sum_option]
  change ‖toL2 φ‖ ^ 2 + (‖toL2 (lapS φ)‖ ^ 2 + ∑ i : Fin d, ‖toL2 (dS i φ)‖ ^ 2) = _
  ring

theorem norm_toL2_le_ιS (φ : SchwartzMap Rd ℂ) : ‖toL2 φ‖ ≤ ‖ιS φ‖ :=
  PiLp.norm_apply_le ((ιS φ : Hsp d) : E3 d) none

theorem norm_lapS_le_ιS (φ : SchwartzMap Rd ℂ) : ‖toL2 (lapS φ)‖ ≤ ‖ιS φ‖ :=
  PiLp.norm_apply_le ((ιS φ : Hsp d) : E3 d) (some none)

theorem norm_dS_le_ιS (φ : SchwartzMap Rd ℂ) (i : Fin d) : ‖toL2 (dS i φ)‖ ≤ ‖ιS φ‖ :=
  PiLp.norm_apply_le ((ιS φ : Hsp d) : E3 d) (some (some i))

/-- The sup bound `|φ(x)| ≤ ‖φ‖_{H²}` on `𝓢(ℝ²)`. -/
theorem norm_apply_le_ιS (φ : SchwartzMap R2 ℂ) (x : R2) : ‖φ x‖ ≤ ‖ιS φ‖ := by
  have h := sup_bound_schwartz φ one_pos x
  rw [Real.sqrt_one, one_mul, mul_one] at h
  have hN := norm_ιS_sq φ
  have hs : 0 ≤ ∑ i : Fin 2, ‖toL2 (dS i φ)‖ ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have h2 : ‖φ x‖ ^ 2 ≤ ‖ιS φ‖ ^ 2 := by
    have : 0 ≤ ‖toL2 (lapS φ)‖ ^ 2 + ‖toL2 φ‖ ^ 2 := by positivity
    linarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h2

/-- `‖∂ᵢ²φ‖ ≤ ‖Δφ‖`. -/
theorem norm_dS_dS_le (i : Fin d) (φ : SchwartzMap Rd ℂ) :
    ‖toL2 (dS i (dS i φ))‖ ≤ ‖toL2 (lapS φ)‖ := by
  have h : ‖toL2 (dS i (dS i φ))‖ ^ 2 ≤ ‖toL2 (lapS φ)‖ ^ 2 := by
    rw [norm_toL2_sq_fourier, norm_toL2_sq_fourier]
    refine integral_mono (integrable_fourier_sq' _) (integrable_fourier_sq' _) fun ξ => ?_
    simp only
    rw [fourier_dS, fourier_dS, fourier_lapS]
    have hq : (2 * Real.pi * ξ i) ^ 2 ≤ qS ξ := by
      rw [qS, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
      have := Finset.single_le_sum (f := fun j => (2 * Real.pi) ^ 2 * ‖ξ j‖ ^ 2)
        (fun j _ => by positivity) (Finset.mem_univ i)
      simp only at this
      rw [Real.norm_eq_abs, sq_abs] at this
      linarith [show (2 * Real.pi * ξ i) ^ 2 = (2 * Real.pi) ^ 2 * ξ i ^ 2 by ring]
    have e1 : ‖2 * (Real.pi : ℂ) * Complex.I * (ξ i : ℂ) *
        (2 * (Real.pi : ℂ) * Complex.I * (ξ i : ℂ) * 𝓕 (⇑φ) ξ)‖ =
        (2 * Real.pi * ξ i) ^ 2 * ‖𝓕 (⇑φ) ξ‖ := by
      rw [show 2 * (Real.pi : ℂ) * Complex.I * (ξ i : ℂ) *
          (2 * (Real.pi : ℂ) * Complex.I * (ξ i : ℂ) * 𝓕 (⇑φ) ξ) =
          ((-(2 * Real.pi * ξ i) ^ 2 : ℝ) : ℂ) * 𝓕 (⇑φ) ξ by
        push_cast
        linear_combination (4 * (Real.pi : ℂ) ^ 2 * (ξ i : ℂ) ^ 2 * 𝓕 (⇑φ) ξ) *
          Complex.I_mul_I]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_nonneg (sq_nonneg _)]
    have e2 : ‖-(qS ξ : ℂ) * 𝓕 (⇑φ) ξ‖ = qS ξ * ‖𝓕 (⇑φ) ξ‖ := by
      rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (qS_nonneg ξ)]
    rw [e1, e2]
    exact pow_le_pow_left₀ (by positivity)
      (mul_le_mul_of_nonneg_right hq (norm_nonneg _)) 2
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

/-- A bounded factor: `‖ab‖₂ ≤ S‖a‖₂` when `|b| ≤ S`. -/
theorem norm_toL2_mulS_le (a b : SchwartzMap Rd ℂ) {S : ℝ} (hS : 0 ≤ S) (hb : ∀ x, ‖b x‖ ≤ S) :
    ‖toL2 (mulS a b)‖ ≤ S * ‖toL2 a‖ := by
  have h : ‖toL2 (mulS a b)‖ ^ 2 ≤ (S * ‖toL2 a‖) ^ 2 := by
    rw [norm_toL2_sq, mul_pow, norm_toL2_sq, ← integral_const_mul]
    refine integral_mono (integrable_normSq _) ((integrable_normSq a).const_mul _) fun x => ?_
    simp only [mulS_apply, norm_mul, mul_pow]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hb x) 2) (sq_nonneg _)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h

theorem norm_toL2_mulS_le' (a b : SchwartzMap Rd ℂ) {S : ℝ} (hS : 0 ≤ S) (ha : ∀ x, ‖a x‖ ≤ S) :
    ‖toL2 (mulS a b)‖ ≤ S * ‖toL2 b‖ := by
  rw [mulS_comm]
  exact norm_toL2_mulS_le b a hS ha

theorem norm_toL2_conjS (φ : SchwartzMap Rd ℂ) : ‖toL2 (conjS φ)‖ = ‖toL2 φ‖ := by
  have h : ‖toL2 (conjS φ)‖ ^ 2 = ‖toL2 φ‖ ^ 2 := by
    rw [norm_toL2_sq, norm_toL2_sq]
    simp only [conjS_apply, Complex.norm_conj]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

theorem norm_ιS_conjS (φ : SchwartzMap Rd ℂ) : ‖ιS (conjS φ)‖ = ‖ιS φ‖ := by
  have h : ‖ιS (conjS φ)‖ ^ 2 = ‖ιS φ‖ ^ 2 := by
    rw [norm_ιS_sq, norm_ιS_sq, lapS_conjS, norm_toL2_conjS, norm_toL2_conjS]
    simp only [dS_conjS, norm_toL2_conjS]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

/-- The `L⁴` bound for gradients, by one integration by parts:
`∫|∂ᵢφ|⁴ ≤ 9 S² ‖∂ᵢ²φ‖²` when `|φ| ≤ S`. -/
theorem integral_dS_pow_four_le (i : Fin d) (φ : SchwartzMap Rd ℂ) {S : ℝ}
    (hφ : ∀ x, ‖φ x‖ ≤ S) :
    ∫ x, ‖dS i φ x‖ ^ 4 ≤ 9 * S ^ 2 * ‖toL2 (dS i (dS i φ))‖ ^ 2 := by
  obtain ⟨v, hv⟩ : ∃ v, v = dS i φ := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w, w = dS i v := ⟨_, rfl⟩
  rw [← hv, ← hw]
  set χ := mulS v (mulS v (conjS v)) with hχ
  have hF4int : Integrable fun x => ‖v x‖ ^ 4 := by
    refine (integrable_normSq (mulS v v)).congr (Eventually.of_forall fun x => ?_)
    simp only [mulS_apply, norm_mul]
    ring
  have hPint : Integrable fun x => ‖v x‖ ^ 2 * ‖w x‖ := by
    refine (mulS (mulS v v) w).integrable.norm.congr (Eventually.of_forall fun x => ?_)
    simp only [mulS_apply, norm_mul]
    ring
  -- (a) `⟪χ, v⟫ = ∫ |v|⁴`
  have ha : inner ℂ (toL2 χ) (toL2 v) = ((∫ x, ‖v x‖ ^ 4 : ℝ) : ℂ) := by
    rw [inner_toL2, ← integral_complex_ofReal]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hχ, mulS_apply, conjS_apply, map_mul, Complex.conj_conj]
    have h1 : (starRingEnd ℂ) (v x) * v x = ((‖v x‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.conj_mul']; push_cast; ring
    calc (starRingEnd ℂ) (v x) * ((starRingEnd ℂ) (v x) * v x) * v x
        = ((starRingEnd ℂ) (v x) * v x) * ((starRingEnd ℂ) (v x) * v x) := by ring
      _ = ((‖v x‖ ^ 4 : ℝ) : ℂ) := by rw [h1]; push_cast; ring
  -- (b) integration by parts
  have hb : inner ℂ (toL2 χ) (toL2 v) = -inner ℂ (toL2 (dS i χ)) (toL2 φ) := by
    rw [hv]
    exact inner_toL2_dS i χ φ
  -- (c) pointwise bound on `∂ᵢχ`
  have hdχ : ∀ x, ‖dS i χ x‖ ≤ 3 * (‖v x‖ ^ 2 * ‖w x‖) := by
    intro x
    rw [hχ, dS_mulS, dS_mulS, dS_conjS, ← hw]
    simp only [SchwartzMap.add_apply, mulS_apply, conjS_apply]
    calc ‖w x * (v x * (starRingEnd ℂ) (v x)) +
          v x * (w x * (starRingEnd ℂ) (v x) + v x * (starRingEnd ℂ) (w x))‖
        ≤ ‖w x * (v x * (starRingEnd ℂ) (v x))‖ +
            (‖v x‖ * (‖w x * (starRingEnd ℂ) (v x)‖ + ‖v x * (starRingEnd ℂ) (w x)‖)) := by
          refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)
      _ = 3 * (‖v x‖ ^ 2 * ‖w x‖) := by
          simp only [norm_mul, Complex.norm_conj]
          ring
  -- (d) `|⟪∂ᵢχ, φ⟫| ≤ 3S ∫ |v|²|w|`
  have hc : ‖inner ℂ (toL2 (dS i χ)) (toL2 φ)‖ ≤ 3 * S * ∫ x, ‖v x‖ ^ 2 * ‖w x‖ := by
    rw [inner_toL2]
    refine (norm_integral_le_integral_norm _).trans ?_
    have hint1 : Integrable fun x => ‖(starRingEnd ℂ) (dS i χ x) * φ x‖ :=
      (mulS (conjS (dS i χ)) φ).integrable.norm
    have hint2 : Integrable fun x => 3 * S * (‖v x‖ ^ 2 * ‖w x‖) := hPint.const_mul _
    calc ∫ x, ‖(starRingEnd ℂ) (dS i χ x) * φ x‖ ≤ ∫ x, 3 * S * (‖v x‖ ^ 2 * ‖w x‖) := by
          refine integral_mono hint1 hint2 fun x => ?_
          simp only [norm_mul, Complex.norm_conj]
          calc ‖dS i χ x‖ * ‖φ x‖ ≤ 3 * (‖v x‖ ^ 2 * ‖w x‖) * S :=
                mul_le_mul (hdχ x) (hφ x) (norm_nonneg _) (by positivity)
            _ = 3 * S * (‖v x‖ ^ 2 * ‖w x‖) := by ring
      _ = 3 * S * ∫ x, ‖v x‖ ^ 2 * ‖w x‖ := integral_const_mul _ _
  -- (e) Cauchy–Schwarz
  have hCS : (∫ x, ‖v x‖ ^ 2 * ‖w x‖) ^ 2 ≤ (∫ x, ‖v x‖ ^ 4) * ‖toL2 w‖ ^ 2 := by
    have := sq_integral_mul_le (μ := volume) (f := fun x => ‖v x‖ ^ 2) (g := fun x => ‖w x‖)
      (fun x => sq_nonneg _) (fun x => norm_nonneg _) hPint
      (hF4int.congr (Eventually.of_forall fun x => by simp only; ring))
      (integrable_normSq w)
    rw [norm_toL2_sq]
    convert this using 2
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    ring
  -- (f) conclusion
  set F4 := ∫ x, ‖v x‖ ^ 4 with hF4
  set P := ∫ x, ‖v x‖ ^ 2 * ‖w x‖ with hP
  have hF40 : 0 ≤ F4 := integral_nonneg fun x => by positivity
  have hP0 : 0 ≤ P := integral_nonneg fun x => by positivity
  have hle : F4 ≤ 3 * S * P := by
    have h1 : ‖inner ℂ (toL2 χ) (toL2 v)‖ = F4 := by
      rw [ha, Complex.norm_real, Real.norm_of_nonneg hF40]
    rw [← h1, hb, norm_neg]
    exact hc
  have hsq : F4 ^ 2 ≤ 9 * S ^ 2 * (F4 * ‖toL2 w‖ ^ 2) := by
    calc F4 ^ 2 ≤ (3 * S * P) ^ 2 := pow_le_pow_left₀ hF40 hle 2
      _ = 9 * S ^ 2 * P ^ 2 := by ring
      _ ≤ 9 * S ^ 2 * (F4 * ‖toL2 w‖ ^ 2) := by gcongr
  rcases hF40.lt_or_eq with hpos | hzero
  · have : F4 * F4 ≤ F4 * (9 * S ^ 2 * ‖toL2 w‖ ^ 2) := by nlinarith
    exact le_of_mul_le_mul_left this hpos
  · rw [← hzero]
    positivity

theorem integrable_norm_pow_four (a : SchwartzMap Rd ℂ) : Integrable fun x => ‖a x‖ ^ 4 := by
  refine (integrable_normSq (mulS a a)).congr (Eventually.of_forall fun x => ?_)
  simp only [mulS_apply, norm_mul]
  ring

/-- The cross term `∇φ · ∇ψ`: `‖∂ᵢφ ∂ᵢψ‖² ≤ 9 S_φ S_ψ ‖∂ᵢ²φ‖ ‖∂ᵢ²ψ‖`. -/
theorem norm_toL2_mulS_dS_sq_le (i : Fin d) (φ ψ : SchwartzMap Rd ℂ) {Sφ Sψ : ℝ}
    (hSφ : 0 ≤ Sφ) (hSψ : 0 ≤ Sψ) (hφ : ∀ x, ‖φ x‖ ≤ Sφ) (hψ : ∀ x, ‖ψ x‖ ≤ Sψ) :
    ‖toL2 (mulS (dS i φ) (dS i ψ))‖ ^ 2 ≤
      9 * Sφ * Sψ * (‖toL2 (dS i (dS i φ))‖ * ‖toL2 (dS i (dS i ψ))‖) := by
  have hφ4 := integral_dS_pow_four_le i φ hφ
  have hψ4 := integral_dS_pow_four_le i ψ hψ
  have e1 : ‖toL2 (mulS (dS i φ) (dS i ψ))‖ ^ 2 = ∫ x, ‖dS i φ x‖ ^ 2 * ‖dS i ψ x‖ ^ 2 := by
    rw [norm_toL2_sq]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [mulS_apply, norm_mul, mul_pow]
  have hCS := sq_integral_mul_le (μ := volume) (f := fun x => ‖dS i φ x‖ ^ 2)
    (g := fun x => ‖dS i ψ x‖ ^ 2) (fun x => sq_nonneg _) (fun x => sq_nonneg _)
    ((integrable_normSq (mulS (dS i φ) (dS i ψ))).congr (Eventually.of_forall fun x => by
      simp only [mulS_apply, norm_mul, mul_pow]))
    ((integrable_norm_pow_four (dS i φ)).congr (Eventually.of_forall fun x => by
      simp only; ring))
    ((integrable_norm_pow_four (dS i ψ)).congr (Eventually.of_forall fun x => by
      simp only; ring))
  have e2 : ∫ x, (‖dS i φ x‖ ^ 2) ^ 2 = ∫ x, ‖dS i φ x‖ ^ 4 :=
    integral_congr_ae (Eventually.of_forall fun x => by simp only; ring)
  have e3 : ∫ x, (‖dS i ψ x‖ ^ 2) ^ 2 = ∫ x, ‖dS i ψ x‖ ^ 4 :=
    integral_congr_ae (Eventually.of_forall fun x => by simp only; ring)
  simp only at hCS
  rw [e2, e3] at hCS
  rw [e1]
  set I := ∫ x, ‖dS i φ x‖ ^ 2 * ‖dS i ψ x‖ ^ 2 with hI
  set Wφ := ‖toL2 (dS i (dS i φ))‖
  set Wψ := ‖toL2 (dS i (dS i ψ))‖
  have hI0 : 0 ≤ I := integral_nonneg fun x => by positivity
  have hF40 : 0 ≤ ∫ x, ‖dS i ψ x‖ ^ 4 := integral_nonneg fun x => by positivity
  have h1 : I ^ 2 ≤ (9 * Sφ * Sψ * (Wφ * Wψ)) ^ 2 := by
    calc I ^ 2 ≤ (∫ x, ‖dS i φ x‖ ^ 4) * ∫ x, ‖dS i ψ x‖ ^ 4 := hCS
      _ ≤ (9 * Sφ ^ 2 * Wφ ^ 2) * (9 * Sψ ^ 2 * Wψ ^ 2) :=
          mul_le_mul hφ4 hψ4 hF40 (by positivity)
      _ = (9 * Sφ * Sψ * (Wφ * Wψ)) ^ 2 := by ring
  exact (pow_le_pow_iff_left₀ hI0 (by positivity) two_ne_zero).1 h1

theorem prod_sq_arith {a b c e P : ℝ} (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hc0 : 0 ≤ c) (he0 : 0 ≤ e)
    (ha : a ≤ P) (hb : b ≤ 14 * P) (hc : c ≤ 2 * P) (he : e ≤ 2 * P) :
    a ^ 2 + b ^ 2 + (c ^ 2 + e ^ 2) ≤ (15 * P) ^ 2 := by
  have hP : 0 ≤ P := ha0.trans ha
  nlinarith [mul_le_mul ha ha ha0 hP, mul_le_mul hb hb hb0 (by linarith),
    mul_le_mul hc hc hc0 (by linarith), mul_le_mul he he he0 (by linarith)]

/-- **The `H²(ℝ²)` algebra estimate on Schwartz functions:**
`‖φψ‖_{H²} ≤ 15 ‖φ‖_{H²} ‖ψ‖_{H²}`. -/
theorem norm_ιS_mulS_le (φ ψ : SchwartzMap R2 ℂ) : ‖ιS (mulS φ ψ)‖ ≤ 15 * (‖ιS φ‖ * ‖ιS ψ‖) := by
  obtain ⟨Nφ, hNφ⟩ : ∃ N, ‖ιS φ‖ = N := ⟨_, rfl⟩
  obtain ⟨Nψ, hNψ⟩ : ∃ N, ‖ιS ψ‖ = N := ⟨_, rfl⟩
  rw [hNφ, hNψ]
  have hNφ0 : 0 ≤ Nφ := hNφ ▸ norm_nonneg _
  have hNψ0 : 0 ≤ Nψ := hNψ ▸ norm_nonneg _
  have hsφ : ∀ x, ‖φ x‖ ≤ Nφ := fun x => hNφ ▸ norm_apply_le_ιS φ x
  have hsψ : ∀ x, ‖ψ x‖ ≤ Nψ := fun x => hNψ ▸ norm_apply_le_ιS ψ x
  have hvφ : ‖toL2 φ‖ ≤ Nφ := hNφ ▸ norm_toL2_le_ιS φ
  have hlφ : ‖toL2 (lapS φ)‖ ≤ Nφ := hNφ ▸ norm_lapS_le_ιS φ
  have hlψ : ‖toL2 (lapS ψ)‖ ≤ Nψ := hNψ ▸ norm_lapS_le_ιS ψ
  have hgφ : ∀ i, ‖toL2 (dS i φ)‖ ≤ Nφ := fun i => hNφ ▸ norm_dS_le_ιS φ i
  have hgψ : ∀ i, ‖toL2 (dS i ψ)‖ ≤ Nψ := fun i => hNψ ▸ norm_dS_le_ιS ψ i
  have hval : ‖toL2 (mulS φ ψ)‖ ≤ Nφ * Nψ := by
    calc ‖toL2 (mulS φ ψ)‖ ≤ Nψ * ‖toL2 φ‖ := norm_toL2_mulS_le φ ψ hNψ0 hsψ
      _ ≤ Nψ * Nφ := mul_le_mul_of_nonneg_left hvφ hNψ0
      _ = Nφ * Nψ := mul_comm _ _
  have hgrad : ∀ i, ‖toL2 (dS i (mulS φ ψ))‖ ≤ 2 * (Nφ * Nψ) := by
    intro i
    rw [dS_mulS, map_add]
    calc ‖toL2 (mulS (dS i φ) ψ) + toL2 (mulS φ (dS i ψ))‖
        ≤ ‖toL2 (mulS (dS i φ) ψ)‖ + ‖toL2 (mulS φ (dS i ψ))‖ := norm_add_le _ _
      _ ≤ Nψ * ‖toL2 (dS i φ)‖ + Nφ * ‖toL2 (dS i ψ)‖ :=
          add_le_add (norm_toL2_mulS_le _ _ hNψ0 hsψ) (norm_toL2_mulS_le' _ _ hNφ0 hsφ)
      _ ≤ Nψ * Nφ + Nφ * Nψ := add_le_add (mul_le_mul_of_nonneg_left (hgφ i) hNψ0)
          (mul_le_mul_of_nonneg_left (hgψ i) hNφ0)
      _ = 2 * (Nφ * Nψ) := by ring
  have hcross : ∀ i, ‖toL2 (mulS (dS i φ) (dS i ψ))‖ ≤ 3 * (Nφ * Nψ) := by
    intro i
    have h := norm_toL2_mulS_dS_sq_le i φ ψ hNφ0 hNψ0 hsφ hsψ
    have hWφ : ‖toL2 (dS i (dS i φ))‖ ≤ Nφ := (norm_dS_dS_le i φ).trans hlφ
    have hWψ : ‖toL2 (dS i (dS i ψ))‖ ≤ Nψ := (norm_dS_dS_le i ψ).trans hlψ
    have h2 : ‖toL2 (mulS (dS i φ) (dS i ψ))‖ ^ 2 ≤ (3 * (Nφ * Nψ)) ^ 2 := by
      have h3 : ‖toL2 (dS i (dS i φ))‖ * ‖toL2 (dS i (dS i ψ))‖ ≤ Nφ * Nψ :=
        mul_le_mul hWφ hWψ (norm_nonneg _) hNφ0
      have h4 : 0 ≤ 9 * Nφ * Nψ := by positivity
      have h5 := mul_le_mul_of_nonneg_left h3 h4
      have h6 : 9 * Nφ * Nψ * (Nφ * Nψ) = (3 * (Nφ * Nψ)) ^ 2 := by ring
      linarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2
  have hlap : ‖toL2 (lapS (mulS φ ψ))‖ ≤ 14 * (Nφ * Nψ) := by
    rw [lapS_mulS, map_add, map_add, map_smul, map_sum, Fin.sum_univ_two]
    have h1 : ‖toL2 (mulS (lapS φ) ψ)‖ ≤ Nφ * Nψ := by
      calc ‖toL2 (mulS (lapS φ) ψ)‖ ≤ Nψ * ‖toL2 (lapS φ)‖ := norm_toL2_mulS_le _ _ hNψ0 hsψ
        _ ≤ Nψ * Nφ := mul_le_mul_of_nonneg_left hlφ hNψ0
        _ = Nφ * Nψ := mul_comm _ _
    have h3 : ‖toL2 (mulS φ (lapS ψ))‖ ≤ Nφ * Nψ :=
      (norm_toL2_mulS_le' _ _ hNφ0 hsφ).trans (mul_le_mul_of_nonneg_left hlψ hNφ0)
    have h2 : ‖(2 : ℂ) • (toL2 (mulS (dS 0 φ) (dS 0 ψ)) + toL2 (mulS (dS 1 φ) (dS 1 ψ)))‖ ≤
        12 * (Nφ * Nψ) := by
      rw [norm_smul]
      have : ‖(2 : ℂ)‖ = 2 := by norm_num
      rw [this]
      calc 2 * ‖toL2 (mulS (dS 0 φ) (dS 0 ψ)) + toL2 (mulS (dS 1 φ) (dS 1 ψ))‖
          ≤ 2 * (‖toL2 (mulS (dS 0 φ) (dS 0 ψ))‖ + ‖toL2 (mulS (dS 1 φ) (dS 1 ψ))‖) := by
            gcongr; exact norm_add_le _ _
        _ ≤ 2 * (3 * (Nφ * Nψ) + 3 * (Nφ * Nψ)) := by gcongr <;> exact hcross _
        _ = 12 * (Nφ * Nψ) := by ring
    calc ‖toL2 (mulS (lapS φ) ψ) + (2 : ℂ) • (toL2 (mulS (dS 0 φ) (dS 0 ψ)) +
          toL2 (mulS (dS 1 φ) (dS 1 ψ))) + toL2 (mulS φ (lapS ψ))‖
        ≤ ‖toL2 (mulS (lapS φ) ψ)‖ + ‖(2 : ℂ) • (toL2 (mulS (dS 0 φ) (dS 0 ψ)) +
          toL2 (mulS (dS 1 φ) (dS 1 ψ)))‖ + ‖toL2 (mulS φ (lapS ψ))‖ :=
          norm_add₃_le
      _ ≤ Nφ * Nψ + 12 * (Nφ * Nψ) + Nφ * Nψ := add_le_add (add_le_add h1 h2) h3
      _ = 14 * (Nφ * Nψ) := by ring
  have hsq : ‖ιS (mulS φ ψ)‖ ^ 2 ≤ (15 * (Nφ * Nψ)) ^ 2 := by
    rw [norm_ιS_sq, Fin.sum_univ_two]
    exact prod_sq_arith (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
      hval hlap (hgrad 0) (hgrad 1)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq

end Sobolev

end ReyesMath

open Filter Topology Complex InnerProductSpace MeasureTheory Set
open scoped ContDiff FourierTransform

namespace ReyesMath

namespace Sobolev

variable {d : ℕ}

local notation "Rd" => EuclideanSpace ℝ (Fin d)

local notation "R2" => EuclideanSpace ℝ (Fin 2)

/-! ### The Schwartz subspace of `H²` -/

/-- `ιS` as a linear map. -/
noncomputable def ιL : SchwartzMap Rd ℂ →ₗ[ℂ] Hsp d where
  toFun := ιS
  map_add' φ ψ := Hsp.ext (map_add graphS φ ψ)
  map_smul' c φ := Hsp.ext (map_smul graphS c φ)

theorem ιL_apply (φ : SchwartzMap Rd ℂ) : ιL φ = ιS φ := rfl

theorem ιS_add (φ ψ : SchwartzMap Rd ℂ) : ιS (φ + ψ) = ιS φ + ιS ψ := map_add ιL φ ψ

theorem ιS_smul (c : ℂ) (φ : SchwartzMap Rd ℂ) : ιS (c • φ) = c • ιS φ := map_smul ιL c φ

theorem ιL_injective : Function.Injective (ιL (d := d)) := by
  intro φ ψ h
  apply toL2_injective
  exact congrArg vl h

/-- The Schwartz subspace of `H²`. -/
noncomputable def Gs (d : ℕ) : Submodule ℂ (Hsp d) := LinearMap.range (ιL (d := d))

noncomputable def eG (d : ℕ) : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ ≃ₗ[ℂ] Gs d :=
  LinearEquiv.ofInjective ιL ιL_injective

theorem coe_eG_symm (g : Gs d) : ιS ((eG d).symm g) = (g : Hsp d) := by
  conv_rhs => rw [← (eG d).apply_symm_apply g]
  rfl

theorem norm_ιS_eG_symm (g : Gs d) : ‖ιS ((eG d).symm g)‖ = ‖g‖ := by
  rw [coe_eG_symm]
  rfl

theorem eG_symm_ιS (φ : SchwartzMap Rd ℂ) (h : ιS φ ∈ Gs d) : (eG d).symm ⟨ιS φ, h⟩ = φ := by
  rw [LinearEquiv.symm_apply_eq]
  rfl

theorem dense_Gs : DenseRange ((Gs d).subtypeL) := by
  have e : range ((Gs d).subtypeL) = range (ιS (d := d)) := by
    ext x
    constructor
    · rintro ⟨⟨_, ⟨φ, rfl⟩⟩, rfl⟩
      exact ⟨φ, rfl⟩
    · rintro ⟨φ, rfl⟩
      exact ⟨⟨ιS φ, ⟨φ, rfl⟩⟩, rfl⟩
  rw [DenseRange, e]
  exact denseRange_ιS

theorem uniformInducing_Gs : IsUniformInducing ((Gs d).subtypeL) :=
  (Submodule.subtypeₗᵢ (Gs d)).isometry.isUniformInducing

theorem norm_le_Gs (g : Gs d) : ‖g‖ ≤ (1 : NNReal) * ‖(Gs d).subtypeL g‖ := by
  rw [NNReal.coe_one, one_mul]
  rfl

theorem mem_Gs (φ : SchwartzMap Rd ℂ) : ιS φ ∈ Gs d := ⟨φ, rfl⟩

/-- Two continuous (semi)linear maps on `H²` agreeing on Schwartz functions are equal. -/
theorem clm_ext_ιS {σ : ℂ →+* ℂ} {f g : Hsp d →SL[σ] Hsp d}
    (h : ∀ φ : SchwartzMap Rd ℂ, f (ιS φ) = g (ιS φ)) : f = g :=
  ContinuousLinearMap.ext fun x =>
    denseRange_ιS.induction_on x (isClosed_eq f.continuous g.continuous) h

/-! ### Multiplication on `H²(ℝ²)` -/

/-- Right multiplication by a Schwartz function, as a linear map on Schwartz space. -/
noncomputable def mulRS (ψ : SchwartzMap R2 ℂ) : SchwartzMap R2 ℂ →L[ℂ] SchwartzMap R2 ℂ :=
  SchwartzMap.bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) (schwartz_hasTemperateGrowth ψ)

theorem mulRS_apply (ψ φ : SchwartzMap R2 ℂ) : mulRS ψ φ = mulS φ ψ := rfl

/-- Right multiplication by a Schwartz function, on the Schwartz subspace. -/
noncomputable def mulRG (ψ : SchwartzMap R2 ℂ) : Gs 2 →L[ℂ] Hsp 2 :=
  LinearMap.mkContinuous ((ιL.comp (mulRS ψ).toLinearMap).comp (eG 2).symm.toLinearMap)
    (15 * ‖ιS ψ‖) fun g => by
      have h := norm_ιS_mulS_le ((eG 2).symm g) ψ
      rw [norm_ιS_eG_symm] at h
      have e : ((ιL.comp (mulRS ψ).toLinearMap).comp (eG 2).symm.toLinearMap) g =
          ιS (mulS ((eG 2).symm g) ψ) := rfl
      rw [e]
      linarith [mul_comm ‖g‖ ‖ιS ψ‖]

theorem mulRG_apply (ψ φ : SchwartzMap R2 ℂ) :
    mulRG ψ ⟨ιS φ, mem_Gs φ⟩ = ιS (mulS φ ψ) := by
  have e : mulRG ψ ⟨ιS φ, mem_Gs φ⟩ = ιS (mulS ((eG 2).symm ⟨ιS φ, mem_Gs φ⟩) ψ) := rfl
  rw [e, eG_symm_ιS]

/-- Right multiplication by a Schwartz function, on `H²`. -/
noncomputable def mulR (ψ : SchwartzMap R2 ℂ) : Hsp 2 →L[ℂ] Hsp 2 :=
  (mulRG ψ).extend (Gs 2).subtypeL dense_Gs uniformInducing_Gs

theorem mulR_ιS (ψ φ : SchwartzMap R2 ℂ) : mulR ψ (ιS φ) = ιS (mulS φ ψ) := by
  have h := ContinuousLinearMap.extend_eq (mulRG ψ) (Gs 2).subtypeL dense_Gs uniformInducing_Gs
    ⟨ιS φ, mem_Gs φ⟩
  exact h.trans (mulRG_apply ψ φ)

attribute [irreducible] mulR

theorem norm_mulR_apply_le (ψ : SchwartzMap R2 ℂ) (e : Hsp 2) :
    ‖mulR ψ e‖ ≤ 15 * ‖ιS ψ‖ * ‖e‖ := by
  refine denseRange_ιS.induction_on e
    (isClosed_le (mulR ψ).continuous.norm (continuous_const.mul continuous_norm)) fun φ => ?_
  rw [mulR_ιS]
  have := norm_ιS_mulS_le φ ψ
  linarith [mul_comm ‖ιS φ‖ ‖ιS ψ‖]

theorem norm_mulR_le (ψ : SchwartzMap R2 ℂ) : ‖mulR ψ‖ ≤ 15 * ‖ιS ψ‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) (norm_mulR_apply_le ψ)

theorem mulR_add (ψ ψ' : SchwartzMap R2 ℂ) : mulR (ψ + ψ') = mulR ψ + mulR ψ' :=
  clm_ext_ιS fun φ => by
    rw [ContinuousLinearMap.add_apply, mulR_ιS, mulR_ιS, mulR_ιS, mulS_add_right, ιS_add]

theorem mulR_smul (c : ℂ) (ψ : SchwartzMap R2 ℂ) : mulR (c • ψ) = c • mulR ψ :=
  clm_ext_ιS fun φ => by
    rw [ContinuousLinearMap.smul_apply, mulR_ιS, mulR_ιS, mulS_smul_right, ιS_smul]

/-- `ψ ↦ (u ↦ uψ)`, linear in the Schwartz function `ψ`. -/
noncomputable def mulRL : SchwartzMap R2 ℂ →ₗ[ℂ] (Hsp 2 →L[ℂ] Hsp 2) where
  toFun := mulR
  map_add' := mulR_add
  map_smul' := mulR_smul

noncomputable def mulG : Gs 2 →L[ℂ] (Hsp 2 →L[ℂ] Hsp 2) :=
  LinearMap.mkContinuous (mulRL.comp (eG 2).symm.toLinearMap) 15 fun g => by
    have e : (mulRL.comp (eG 2).symm.toLinearMap) g = mulR ((eG 2).symm g) := rfl
    rw [e, ← norm_ιS_eG_symm g]
    exact norm_mulR_le _

/-- **Multiplication on `H²(ℝ²)`**, the continuous bilinear extension of the Schwartz product;
`pmul u v = u v`. -/
noncomputable def mulH : Hsp 2 →L[ℂ] (Hsp 2 →L[ℂ] Hsp 2) :=
  mulG.extend (Gs 2).subtypeL dense_Gs uniformInducing_Gs

noncomputable def pmul (e f : Hsp 2) : Hsp 2 := mulH f e

theorem mulH_ιS (ψ : SchwartzMap R2 ℂ) : mulH (ιS ψ) = mulR ψ := by
  have h := ContinuousLinearMap.extend_eq mulG (Gs 2).subtypeL dense_Gs uniformInducing_Gs
    ⟨ιS ψ, mem_Gs ψ⟩
  refine h.trans ?_
  have e : mulG ⟨ιS ψ, mem_Gs ψ⟩ = mulR ((eG 2).symm ⟨ιS ψ, mem_Gs ψ⟩) := rfl
  rw [e, eG_symm_ιS]

attribute [irreducible] mulH

theorem pmul_ιS (φ ψ : SchwartzMap R2 ℂ) : pmul (ιS φ) (ιS ψ) = ιS (mulS φ ψ) := by
  rw [pmul, mulH_ιS, mulR_ιS]

theorem norm_mulH_apply_le (f : Hsp 2) : ‖mulH f‖ ≤ 15 * ‖f‖ := by
  refine denseRange_ιS.induction_on f
    (isClosed_le mulH.continuous.norm (continuous_const.mul continuous_norm)) fun ψ => ?_
  rw [mulH_ιS]
  exact norm_mulR_le ψ

theorem norm_pmul_le (e f : Hsp 2) : ‖pmul e f‖ ≤ 15 * ‖e‖ * ‖f‖ := by
  calc ‖pmul e f‖ = ‖mulH f e‖ := rfl
    _ ≤ ‖mulH f‖ * ‖e‖ := (mulH f).le_opNorm e
    _ ≤ (15 * ‖f‖) * ‖e‖ := mul_le_mul_of_nonneg_right (norm_mulH_apply_le f) (norm_nonneg _)
    _ = 15 * ‖e‖ * ‖f‖ := by ring

theorem continuous_pmul : Continuous fun p : Hsp 2 × Hsp 2 => pmul p.1 p.2 := by
  have h := mulH.continuous₂
  have e : (fun p : Hsp 2 × Hsp 2 => pmul p.1 p.2) =
      (Function.uncurry fun x y => mulH x y) ∘ Prod.swap := by
    funext p
    rfl
  rw [e]
  exact h.comp continuous_swap

theorem pmul_add_left (e e' f : Hsp 2) : pmul (e + e') f = pmul e f + pmul e' f :=
  map_add (mulH f) e e'

theorem pmul_add_right (e f f' : Hsp 2) : pmul e (f + f') = pmul e f + pmul e f' := by
  simp only [pmul, map_add, ContinuousLinearMap.add_apply]

theorem pmul_sub_left (e e' f : Hsp 2) : pmul (e - e') f = pmul e f - pmul e' f :=
  map_sub (mulH f) e e'

theorem pmul_sub_right (e f f' : Hsp 2) : pmul e (f - f') = pmul e f - pmul e f' := by
  simp only [pmul, map_sub, ContinuousLinearMap.sub_apply]

theorem pmul_smul_left (c : ℂ) (e f : Hsp 2) : pmul (c • e) f = c • pmul e f :=
  map_smul (mulH f) c e

theorem pmul_smul_right (c : ℂ) (e f : Hsp 2) : pmul e (c • f) = c • pmul e f := by
  simp only [pmul, map_smul, ContinuousLinearMap.smul_apply]

/-! ### Conjugation on `H²(ℝ²)` -/

/-- Conjugation on Schwartz space, as a semilinear map. -/
noncomputable def conjSL : SchwartzMap R2 ℂ →ₛₗ[starRingEnd ℂ] SchwartzMap R2 ℂ where
  toFun := conjS
  map_add' := conjS_add
  map_smul' := conjS_smul

noncomputable def conjG : Gs 2 →SL[starRingEnd ℂ] Hsp 2 :=
  LinearMap.mkContinuous ((ιL.comp conjSL).comp (eG 2).symm.toLinearMap) 1 fun g => by
    have e : ((ιL.comp conjSL).comp (eG 2).symm.toLinearMap) g = ιS (conjS ((eG 2).symm g)) :=
      rfl
    rw [e, one_mul, norm_ιS_conjS, norm_ιS_eG_symm]

/-- **Complex conjugation on `H²(ℝ²)`.** -/
noncomputable def conjH : Hsp 2 →SL[starRingEnd ℂ] Hsp 2 :=
  conjG.extend (Gs 2).subtypeL dense_Gs uniformInducing_Gs

theorem conjH_ιS (φ : SchwartzMap R2 ℂ) : conjH (ιS φ) = ιS (conjS φ) := by
  have h := ContinuousLinearMap.extend_eq conjG (Gs 2).subtypeL dense_Gs uniformInducing_Gs
    ⟨ιS φ, mem_Gs φ⟩
  refine h.trans ?_
  have e : conjG ⟨ιS φ, mem_Gs φ⟩ = ιS (conjS ((eG 2).symm ⟨ιS φ, mem_Gs φ⟩)) := rfl
  rw [e, eG_symm_ιS]

attribute [irreducible] conjH

theorem norm_conjH (e : Hsp 2) : ‖conjH e‖ = ‖e‖ := by
  refine denseRange_ιS.induction_on e
    (isClosed_eq (conjH.continuous.norm) continuous_norm) fun φ => ?_
  rw [conjH_ιS, norm_ιS_conjS]

end Sobolev

end ReyesMath

open Filter Topology Complex InnerProductSpace MeasureTheory Set
open scoped ContDiff FourierTransform

namespace ReyesMath

namespace Sobolev

local notation "R2" => EuclideanSpace ℝ (Fin 2)

/-! ### Pointwise identification of products -/

/-- Limits in `L²` of pointwise relations hold pointwise a.e. -/
theorem ae_eq_of_tendsto₂ {A B C : ℕ → L2 2} {a b c : L2 2} (hA : Tendsto A atTop (𝓝 a))
    (hB : Tendsto B atTop (𝓝 b)) (hC : Tendsto C atTop (𝓝 c)) {G : ℂ → ℂ → ℂ}
    (hG : Continuous fun p : ℂ × ℂ => G p.1 p.2)
    (hrel : ∀ n, ∀ᵐ x ∂(volume : Measure R2), C n x = G (A n x) (B n x)) :
    ∀ᵐ x ∂(volume : Measure R2), c x = G (a x) (b x) := by
  obtain ⟨n1, hm1, h1⟩ := (tendstoInMeasure_of_tendsto_Lp hC).exists_seq_tendsto_ae
  obtain ⟨n2, hm2, h2⟩ :=
    (tendstoInMeasure_of_tendsto_Lp (hA.comp hm1.tendsto_atTop)).exists_seq_tendsto_ae
  obtain ⟨n3, hm3, h3⟩ := (tendstoInMeasure_of_tendsto_Lp
    (hB.comp (hm1.comp hm2).tendsto_atTop)).exists_seq_tendsto_ae
  filter_upwards [h1, h2, h3, ae_all_iff.2 hrel] with x hx1 hx2 hx3 hx
  have hc : Tendsto (fun k => C (n1 (n2 (n3 k))) x) atTop (𝓝 (c x)) :=
    hx1.comp ((hm2.comp hm3).tendsto_atTop)
  have ha : Tendsto (fun k => A (n1 (n2 (n3 k))) x) atTop (𝓝 (a x)) :=
    hx2.comp hm3.tendsto_atTop
  have hb : Tendsto (fun k => B (n1 (n2 (n3 k))) x) atTop (𝓝 (b x)) := hx3
  have hg : Tendsto (fun k => G (A (n1 (n2 (n3 k))) x) (B (n1 (n2 (n3 k))) x)) atTop
      (𝓝 (G (a x) (b x))) :=
    (hG.tendsto (a x, b x)).comp (ha.prodMk_nhds hb)
  refine tendsto_nhds_unique hc (hg.congr fun k => ?_)
  exact (hx _).symm

theorem exists_seq_ιS (e : Hsp 2) :
    ∃ φ : ℕ → SchwartzMap R2 ℂ, Tendsto (fun n => ιS (φ n)) atTop (𝓝 e) := by
  have h := fun n : ℕ => Metric.denseRange_iff.1 (denseRange_ιS (d := 2)) e (1 / ((n : ℝ) + 1))
    (by positivity)
  choose φ hφ using h
  refine ⟨φ, ?_⟩
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
  rw [dist_comm]
  exact (hφ n).le

/-- `u v` is the pointwise product. -/
theorem vl_pmul_ae (e f : Hsp 2) :
    ∀ᵐ x ∂(volume : Measure R2), vl (pmul e f) x = vl e x * vl f x := by
  obtain ⟨φ, hφ⟩ := exists_seq_ιS e
  obtain ⟨ψ, hψ⟩ := exists_seq_ιS f
  have hA : Tendsto (fun n => toL2 (φ n)) atTop (𝓝 (vl e)) :=
    (continuous_vl.tendsto e).comp hφ
  have hB : Tendsto (fun n => toL2 (ψ n)) atTop (𝓝 (vl f)) :=
    (continuous_vl.tendsto f).comp hψ
  have hC : Tendsto (fun n => toL2 (mulS (φ n) (ψ n))) atTop (𝓝 (vl (pmul e f))) := by
    have h := ((continuous_vl.comp continuous_pmul).tendsto (e, f)).comp (hφ.prodMk_nhds hψ)
    refine h.congr fun n => ?_
    simp only [Function.comp_apply]
    rw [pmul_ιS, vl_ιS]
  refine ae_eq_of_tendsto₂ hA hB hC (G := fun a b => a * b) (by fun_prop) fun n => ?_
  filter_upwards [coeFn_toL2 (mulS (φ n) (ψ n)), coeFn_toL2 (φ n), coeFn_toL2 (ψ n)]
    with x h1 h2 h3
  rw [h1, h2, h3, mulS_apply]

/-- `ū` is the pointwise conjugate. -/
theorem vl_conjH_ae (e : Hsp 2) :
    ∀ᵐ x ∂(volume : Measure R2), vl (conjH e) x = (starRingEnd ℂ) (vl e x) := by
  obtain ⟨φ, hφ⟩ := exists_seq_ιS e
  have hA : Tendsto (fun n => toL2 (φ n)) atTop (𝓝 (vl e)) :=
    (continuous_vl.tendsto e).comp hφ
  have hC : Tendsto (fun n => toL2 (conjS (φ n))) atTop (𝓝 (vl (conjH e))) := by
    have h := ((continuous_vl.comp conjH.continuous).tendsto e).comp hφ
    refine h.congr fun n => ?_
    simp only [Function.comp_apply]
    rw [conjH_ιS, vl_ιS]
  refine ae_eq_of_tendsto₂ hA hA hC (G := fun a _ => (starRingEnd ℂ) a) (Complex.continuous_conj.comp continuous_fst) fun n => ?_
  filter_upwards [coeFn_toL2 (conjS (φ n)), coeFn_toL2 (φ n)] with x h1 h2
  rw [h1, h2, conjS_apply]

/-- The a.e. sup bound `|u(x)| ≤ ‖u‖_{H²}`. -/
theorem ae_norm_vl_le (e : Hsp 2) : ∀ᵐ x ∂(volume : Measure R2), ‖vl e x‖ ≤ ‖e‖ := by
  have h := H2.ae_sup_bound (H2.ofSp e) one_pos
  have hn := H2.norm_toSp_sq (H2.ofSp e)
  rw [H2.toSp_ofSp] at hn
  filter_upwards [h] with x hx
  rw [Real.sqrt_one, mul_one, one_mul] at hx
  have hK := H2.K_nonneg (H2.ofSp e)
  have h2 : ‖vl e x‖ ^ 2 ≤ ‖e‖ ^ 2 := by
    have : (H2.ofSp e).val = vl e := rfl
    rw [this] at hx
    have hD := H2.D_nonneg (H2.ofSp e)
    have hM := H2.M_nonneg (H2.ofSp e)
    linarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h2

/-! ### The cubic–quintic nonlinearity -/

/-- `f(z) = −β|z|²z + γ|z|⁴z`, written with `z z z̄`. -/
noncomputable def fnl (β γ : ℝ) (z : ℂ) : ℂ :=
  (-(β : ℂ)) * (z * z * (starRingEnd ℂ) z) +
    (γ : ℂ) * (z * z * z * (starRingEnd ℂ) z * (starRingEnd ℂ) z)

theorem fnl_eq (β γ : ℝ) (z : ℂ) :
    fnl β γ z = ((-β * ‖z‖ ^ 2 + γ * ‖z‖ ^ 4 : ℝ) : ℂ) * z := by
  have h : z * (starRingEnd ℂ) z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj']; push_cast; ring
  unfold fnl
  have e1 : z * z * (starRingEnd ℂ) z = (z * (starRingEnd ℂ) z) * z := by ring
  have e2 : z * z * z * (starRingEnd ℂ) z * (starRingEnd ℂ) z =
      (z * (starRingEnd ℂ) z) * (z * (starRingEnd ℂ) z) * z := by ring
  rw [e1, e2, h]
  push_cast
  ring

/-- **The nonlinearity `F(u) = −β|u|²u + γ|u|⁴u` on `H²(ℝ²)`.** -/
noncomputable def Fnl (β γ : ℝ) (u : Hsp 2) : Hsp 2 :=
  (-(β : ℂ)) • pmul (pmul u u) (conjH u) +
    (γ : ℂ) • pmul (pmul (pmul (pmul u u) u) (conjH u)) (conjH u)

theorem vl_Fnl_ae (β γ : ℝ) (u : Hsp 2) :
    ∀ᵐ x ∂(volume : Measure R2), vl (Fnl β γ u) x = fnl β γ (vl u x) := by
  have h1 := vl_pmul_ae (pmul u u) (conjH u)
  have h2 := vl_pmul_ae u u
  have h3 := vl_conjH_ae u
  have h4 := vl_pmul_ae (pmul (pmul (pmul u u) u) (conjH u)) (conjH u)
  have h5 := vl_pmul_ae (pmul (pmul u u) u) (conjH u)
  have h6 := vl_pmul_ae (pmul u u) u
  have hadd := Lp.coeFn_add ((-(β : ℂ)) • vl (pmul (pmul u u) (conjH u)))
    ((γ : ℂ) • vl (pmul (pmul (pmul (pmul u u) u) (conjH u)) (conjH u)))
  have hs1 := Lp.coeFn_smul (-(β : ℂ)) (vl (pmul (pmul u u) (conjH u)))
  have hs2 := Lp.coeFn_smul (γ : ℂ) (vl (pmul (pmul (pmul (pmul u u) u) (conjH u)) (conjH u)))
  filter_upwards [h1, h2, h3, h4, h5, h6, hadd, hs1, hs2] with x a1 a2 a3 a4 a5 a6 ad b1 b2
  have e : vl (Fnl β γ u) = (-(β : ℂ)) • vl (pmul (pmul u u) (conjH u)) +
      (γ : ℂ) • vl (pmul (pmul (pmul (pmul u u) u) (conjH u)) (conjH u)) := rfl
  rw [e, ad, Pi.add_apply, b1, b2, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
    a1, a4, a5, a6, a2, a3, fnl]

/-- `⟪u, F(u)⟫ = ∫(−β|u|⁴ + γ|u|⁶)` is real. -/
theorem inner_vl_Fnl_im (β γ : ℝ) (u : Hsp 2) : (inner ℂ (vl u) (vl (Fnl β γ u))).im = 0 := by
  rw [L2.inner_def]
  have h : ∫ x, inner ℂ (vl u x) (vl (Fnl β γ u) x) =
      ∫ x, (((-β * ‖vl u x‖ ^ 2 + γ * ‖vl u x‖ ^ 4) * ‖vl u x‖ ^ 2 : ℝ) : ℂ) := by
    refine integral_congr_ae ?_
    filter_upwards [vl_Fnl_ae β γ u] with x hx
    rw [hx, fnl_eq]
    simp only [RCLike.inner_apply]
    rw [mul_assoc, Complex.mul_conj']
    push_cast
    ring
  rw [h, integral_complex_ofReal, Complex.ofReal_im]

/-! ### Lipschitz bounds -/

theorem norm_pmul_sub_le (a b a' b' : Hsp 2) :
    ‖pmul a b - pmul a' b'‖ ≤ 15 * (‖a - a'‖ * ‖b‖ + ‖a'‖ * ‖b - b'‖) := by
  have e : pmul a b - pmul a' b' = pmul (a - a') b + pmul a' (b - b') := by
    rw [pmul_sub_left, pmul_sub_right]
    abel
  rw [e]
  calc ‖pmul (a - a') b + pmul a' (b - b')‖ ≤ ‖pmul (a - a') b‖ + ‖pmul a' (b - b')‖ :=
        norm_add_le _ _
    _ ≤ 15 * ‖a - a'‖ * ‖b‖ + 15 * ‖a'‖ * ‖b - b'‖ :=
        add_le_add (norm_pmul_le _ _) (norm_pmul_le _ _)
    _ = 15 * (‖a - a'‖ * ‖b‖ + ‖a'‖ * ‖b - b'‖) := by ring

/-- Lipschitz composition through a product. -/
theorem lip_pmul {X Y : Hsp 2 → Hsp 2} {u v : Hsp 2} {LX LY BX BY : ℝ}
    (hX : ‖X u - X v‖ ≤ LX * ‖u - v‖) (hY : ‖Y u - Y v‖ ≤ LY * ‖u - v‖)
    (hBX : ‖X v‖ ≤ BX) (hBY : ‖Y u‖ ≤ BY) (hLX : 0 ≤ LX) (hBX0 : 0 ≤ BX) :
    ‖pmul (X u) (Y u) - pmul (X v) (Y v)‖ ≤ 15 * (LX * BY + BX * LY) * ‖u - v‖ := by
  have h := norm_pmul_sub_le (X u) (Y u) (X v) (Y v)
  have hd := norm_nonneg (u - v)
  have h1 : ‖X u - X v‖ * ‖Y u‖ ≤ LX * ‖u - v‖ * BY :=
    mul_le_mul hX hBY (norm_nonneg _) (by positivity)
  have h2 : ‖X v‖ * ‖Y u - Y v‖ ≤ BX * (LY * ‖u - v‖) :=
    mul_le_mul hBX hY (norm_nonneg _) hBX0
  nlinarith

theorem norm_conjH_sub (u v : Hsp 2) : ‖conjH u - conjH v‖ = ‖u - v‖ := by
  rw [← map_sub, norm_conjH]

/-- The Lipschitz constant of `F` on the ball of radius `R`. -/
noncomputable def LF (β γ R : ℝ) : ℝ := |β| * (675 * R ^ 2) + |γ| * (253125 * R ^ 4)

theorem LF_nonneg (β γ : ℝ) {R : ℝ} : 0 ≤ LF β γ R := by unfold LF; positivity

/-- **`F` is Lipschitz on balls of `H²(ℝ²)`.** -/
theorem norm_Fnl_sub_le (β γ : ℝ) {u v : Hsp 2} {R : ℝ} (hu : ‖u‖ ≤ R) (hv : ‖v‖ ≤ R) :
    ‖Fnl β γ u - Fnl β γ v‖ ≤ LF β γ R * ‖u - v‖ := by
  have hR : 0 ≤ R := (norm_nonneg u).trans hu
  have hid : ‖u - v‖ ≤ 1 * ‖u - v‖ := by rw [one_mul]
  have hcj : ‖conjH u - conjH v‖ ≤ 1 * ‖u - v‖ := by rw [norm_conjH_sub, one_mul]
  have hcu : ‖conjH u‖ ≤ R := by rw [norm_conjH]; exact hu
  -- p2 = u u
  have p2L : ‖pmul u u - pmul v v‖ ≤ 15 * (1 * R + R * 1) * ‖u - v‖ :=
    lip_pmul (X := id) (Y := id) hid hid hv hu zero_le_one hR
  have p2B : ∀ w : Hsp 2, ‖w‖ ≤ R → ‖pmul w w‖ ≤ 15 * R * R := fun w hw =>
    (norm_pmul_le w w).trans (by gcongr)
  -- cubic
  have cL : ‖pmul (pmul u u) (conjH u) - pmul (pmul v v) (conjH v)‖ ≤
      15 * (15 * (1 * R + R * 1) * R + 15 * R * R * 1) * ‖u - v‖ :=
    lip_pmul (X := fun w => pmul w w) (Y := conjH) p2L hcj (p2B v hv) hcu (by positivity)
      (by positivity)
  -- p3 = (u u) u
  have p3L : ‖pmul (pmul u u) u - pmul (pmul v v) v‖ ≤
      15 * (15 * (1 * R + R * 1) * R + 15 * R * R * 1) * ‖u - v‖ :=
    lip_pmul (X := fun w => pmul w w) (Y := id) p2L hid (p2B v hv) hu (by positivity)
      (by positivity)
  have p3B : ∀ w : Hsp 2, ‖w‖ ≤ R → ‖pmul (pmul w w) w‖ ≤ 15 * (15 * R * R) * R := fun w hw =>
    (norm_pmul_le _ w).trans (by gcongr; exact p2B w hw)
  -- p4 = ((u u) u) ū
  have p4L : ‖pmul (pmul (pmul u u) u) (conjH u) - pmul (pmul (pmul v v) v) (conjH v)‖ ≤
      15 * (15 * (15 * (1 * R + R * 1) * R + 15 * R * R * 1) * R +
        15 * (15 * R * R) * R * 1) * ‖u - v‖ :=
    lip_pmul (X := fun w => pmul (pmul w w) w) (Y := conjH) p3L hcj (p3B v hv) hcu
      (by positivity) (by positivity)
  have p4B : ∀ w : Hsp 2, ‖w‖ ≤ R →
      ‖pmul (pmul (pmul w w) w) (conjH w)‖ ≤ 15 * (15 * (15 * R * R) * R) * R := fun w hw =>
    (norm_pmul_le _ _).trans (by
      gcongr
      · exact p3B w hw
      · rw [norm_conjH]; exact hw)
  -- quintic
  have qL : ‖pmul (pmul (pmul (pmul u u) u) (conjH u)) (conjH u) -
      pmul (pmul (pmul (pmul v v) v) (conjH v)) (conjH v)‖ ≤
      15 * (15 * (15 * (15 * (1 * R + R * 1) * R + 15 * R * R * 1) * R +
        15 * (15 * R * R) * R * 1) * R + 15 * (15 * (15 * R * R) * R) * R * 1) * ‖u - v‖ :=
    lip_pmul (X := fun w => pmul (pmul (pmul w w) w) (conjH w)) (Y := conjH) p4L hcj (p4B v hv)
      hcu (by positivity) (by positivity)
  have e : Fnl β γ u - Fnl β γ v =
      (-(β : ℂ)) • (pmul (pmul u u) (conjH u) - pmul (pmul v v) (conjH v)) +
      (γ : ℂ) • (pmul (pmul (pmul (pmul u u) u) (conjH u)) (conjH u) -
        pmul (pmul (pmul (pmul v v) v) (conjH v)) (conjH v)) := by
    simp only [Fnl, smul_sub]
    abel
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, norm_neg, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs]
  have hb := abs_nonneg β
  have hg := abs_nonneg γ
  have c1 : |β| * ‖pmul (pmul u u) (conjH u) - pmul (pmul v v) (conjH v)‖ ≤
      |β| * (675 * R ^ 2) * ‖u - v‖ := by
    have : 15 * (15 * (1 * R + R * 1) * R + 15 * R * R * 1) = 675 * R ^ 2 := by ring
    rw [this] at cL
    calc _ ≤ |β| * (675 * R ^ 2 * ‖u - v‖) := mul_le_mul_of_nonneg_left cL hb
      _ = _ := by ring
  have c2 : |γ| * ‖pmul (pmul (pmul (pmul u u) u) (conjH u)) (conjH u) -
      pmul (pmul (pmul (pmul v v) v) (conjH v)) (conjH v)‖ ≤ |γ| * (253125 * R ^ 4) * ‖u - v‖ := by
    have : 15 * (15 * (15 * (15 * (1 * R + R * 1) * R + 15 * R * R * 1) * R +
        15 * (15 * R * R) * R * 1) * R + 15 * (15 * (15 * R * R) * R) * R * 1) =
        253125 * R ^ 4 := by ring
    rw [this] at qL
    calc _ ≤ |γ| * (253125 * R ^ 4 * ‖u - v‖) := mul_le_mul_of_nonneg_left qL hg
      _ = _ := by ring
  calc |β| * ‖pmul (pmul u u) (conjH u) - pmul (pmul v v) (conjH v)‖ +
        |γ| * ‖pmul (pmul (pmul (pmul u u) u) (conjH u)) (conjH u) -
          pmul (pmul (pmul (pmul v v) v) (conjH v)) (conjH v)‖
      ≤ |β| * (675 * R ^ 2) * ‖u - v‖ + |γ| * (253125 * R ^ 4) * ‖u - v‖ := add_le_add c1 c2
    _ = LF β γ R * ‖u - v‖ := by unfold LF; ring

theorem Fnl_zero (β γ : ℝ) : Fnl β γ 0 = 0 := by
  simp [Fnl, pmul]

theorem norm_Fnl_le (β γ : ℝ) (u : Hsp 2) : ‖Fnl β γ u‖ ≤ LF β γ ‖u‖ * ‖u‖ := by
  have h := norm_Fnl_sub_le β γ (u := u) (v := 0) le_rfl (by rw [norm_zero]; exact norm_nonneg u)
  rwa [Fnl_zero, sub_zero, sub_zero] at h

theorem continuous_Fnl (β γ : ℝ) : Continuous (Fnl β γ) := by
  have hp : ∀ {X Y : Hsp 2 → Hsp 2}, Continuous X → Continuous Y →
      Continuous fun w => pmul (X w) (Y w) := fun hX hY =>
    continuous_pmul.comp (hX.prodMk hY)
  have hc : Continuous (fun w : Hsp 2 => conjH w) := conjH.continuous
  unfold Fnl
  exact ((hp (hp continuous_id continuous_id) hc).const_smul _).add
    ((hp (hp (hp (hp continuous_id continuous_id) continuous_id) hc) hc).const_smul _)

end Sobolev

end ReyesMath

open Filter Topology Complex InnerProductSpace MeasureTheory Set
open scoped ContDiff FourierTransform

namespace ReyesMath

namespace Sobolev

local notation "R2" => EuclideanSpace ℝ (Fin 2)

/-! ### The potential energy and its Taylor estimate -/

/-- The potential density `n(z) = −(β/2)|z|⁴ + (γ/3)|z|⁶`. -/
noncomputable def nfun (β γ : ℝ) (z : ℂ) : ℝ := -β / 2 * ‖z‖ ^ 4 + γ / 3 * ‖z‖ ^ 6

/-- `2 Re⟪z, δ⟫ = |z + δ|² − |z|² − |δ|²`. -/
theorem two_re_conj_mul (z δ : ℂ) :
    2 * ((starRingEnd ℂ) z * δ).re = ‖z + δ‖ ^ 2 - ‖z‖ ^ 2 - ‖δ‖ ^ 2 := by
  have h := @norm_add_sq ℂ ℂ _ _ _ z δ
  simp only [RCLike.inner_apply, RCLike.re_to_complex] at h
  rw [h, mul_comm ((starRingEnd ℂ) z) δ]
  ring

/-- **Pointwise Taylor estimate** for `n`: with `f(z) = −β|z|²z + γ|z|⁴z`,
`|n(w) − n(z) − 2Re(f(z)‾ (w − z))| ≤ (3|β|R² + 5|γ|R⁴)|w − z|²` for `|z|, |w| ≤ R`. -/
theorem nfun_taylor (β γ : ℝ) {z w : ℂ} {R : ℝ} (hz : ‖z‖ ≤ R) (hw : ‖w‖ ≤ R) :
    |nfun β γ w - nfun β γ z - 2 * ((starRingEnd ℂ) (fnl β γ z) * (w - z)).re| ≤
      (3 * |β| * R ^ 2 + 5 * |γ| * R ^ 4) * ‖w - z‖ ^ 2 := by
  have hR : 0 ≤ R := (norm_nonneg z).trans hz
  set s := ‖z‖ ^ 2 with hs
  set t := ‖w‖ ^ 2 with ht
  set b := ‖w - z‖ ^ 2 with hb
  have hs0 : 0 ≤ s := sq_nonneg _
  have ht0 : 0 ≤ t := sq_nonneg _
  have hb0 : 0 ≤ b := sq_nonneg _
  have hsR : s ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hz 2
  have htR : t ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hw 2
  -- the linear term
  have hlin : 2 * ((starRingEnd ℂ) (fnl β γ z) * (w - z)).re = (-β * s + γ * s ^ 2) * (t - s - b) := by
    rw [fnl_eq, map_mul, Complex.conj_ofReal, mul_assoc, Complex.re_ofReal_mul]
    have h := two_re_conj_mul z (w - z)
    rw [add_sub_cancel, ← hs, ← ht, ← hb] at h
    rw [show ‖z‖ ^ 4 = s ^ 2 by rw [hs]; ring, ← hs]
    rw [show 2 * ((-β * s + γ * s ^ 2) * ((starRingEnd ℂ) z * (w - z)).re) =
      (-β * s + γ * s ^ 2) * (2 * ((starRingEnd ℂ) z * (w - z)).re) by ring, h]
  -- `(t − s)² ≤ 4R²b`
  have hts : (t - s) ^ 2 ≤ 4 * R ^ 2 * b := by
    have h1 : |‖w‖ - ‖z‖| ≤ ‖w - z‖ := abs_norm_sub_norm_le w z
    have h2 : t - s = (‖w‖ - ‖z‖) * (‖w‖ + ‖z‖) := by rw [ht, hs]; ring
    have h3 : (‖w‖ + ‖z‖) ^ 2 ≤ (2 * R) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 2
    rw [h2, mul_pow]
    have h4 : (‖w‖ - ‖z‖) ^ 2 ≤ b := by
      rw [hb, ← sq_abs (‖w‖ - ‖z‖)]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    nlinarith [sq_nonneg (‖w‖ - ‖z‖), sq_nonneg (‖w‖ + ‖z‖)]
  have hn : nfun β γ w - nfun β γ z - 2 * ((starRingEnd ℂ) (fnl β γ z) * (w - z)).re =
      -β / 2 * ((t - s) ^ 2 + 2 * s * b) + γ / 3 * ((t - s) ^ 2 * (t + 2 * s) + 3 * s ^ 2 * b) := by
    rw [hlin, nfun, nfun, show ‖w‖ ^ 4 = t ^ 2 by rw [ht]; ring,
      show ‖w‖ ^ 6 = t ^ 3 by rw [ht]; ring, show ‖z‖ ^ 4 = s ^ 2 by rw [hs]; ring,
      show ‖z‖ ^ 6 = s ^ 3 by rw [hs]; ring]
    ring
  rw [hn]
  have q1 : 0 ≤ (t - s) ^ 2 + 2 * s * b := by positivity
  have q2 : (t - s) ^ 2 + 2 * s * b ≤ 6 * R ^ 2 * b := by nlinarith
  have q3 : 0 ≤ (t - s) ^ 2 * (t + 2 * s) + 3 * s ^ 2 * b := by positivity
  have q4 : (t - s) ^ 2 * (t + 2 * s) + 3 * s ^ 2 * b ≤ 15 * R ^ 4 * b := by
    have h5 : t + 2 * s ≤ 3 * R ^ 2 := by linarith
    have h6 : (t - s) ^ 2 * (t + 2 * s) ≤ 4 * R ^ 2 * b * (3 * R ^ 2) :=
      mul_le_mul hts h5 (by positivity) (by positivity)
    have h7 : s ^ 2 ≤ R ^ 4 := by
      calc s ^ 2 ≤ (R ^ 2) ^ 2 := pow_le_pow_left₀ hs0 hsR 2
        _ = R ^ 4 := by ring
    nlinarith
  calc |-β / 2 * ((t - s) ^ 2 + 2 * s * b) + γ / 3 * ((t - s) ^ 2 * (t + 2 * s) + 3 * s ^ 2 * b)|
      ≤ |-β / 2 * ((t - s) ^ 2 + 2 * s * b)| + |γ / 3 * ((t - s) ^ 2 * (t + 2 * s) + 3 * s ^ 2 * b)| :=
        abs_add_le _ _
    _ = |β| / 2 * ((t - s) ^ 2 + 2 * s * b) + |γ| / 3 * ((t - s) ^ 2 * (t + 2 * s) + 3 * s ^ 2 * b) := by
        rw [abs_mul, abs_mul, abs_of_nonneg q1, abs_of_nonneg q3, abs_div, abs_div, abs_neg,
          abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    _ ≤ |β| / 2 * (6 * R ^ 2 * b) + |γ| / 3 * (15 * R ^ 4 * b) := by
        gcongr
    _ = (3 * |β| * R ^ 2 + 5 * |γ| * R ^ 4) * b := by ring

/-- `‖h‖² = ∫ |h|²` in `L²`. -/
theorem norm_sq_L2 (h : L2 2) : ‖h‖ ^ 2 = ∫ x, ‖h x‖ ^ 2 := by
  rw [@norm_sq_eq_re_inner ℂ, L2.inner_def]
  simp_rw [inner_self_complex]
  rw [integral_complex_ofReal]
  simp

theorem integrable_sq_L2' (h : L2 2) : Integrable fun x => ‖h x‖ ^ 2 :=
  (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable h)).1 (Lp.memLp h)

/-- The potential energy `N(u) = ∫ n(u)` on `H²(ℝ²)`. -/
noncomputable def Nsp (β γ : ℝ) (e : Hsp 2) : ℝ := ∫ x, nfun β γ (vl e x)

theorem integrable_nfun (β γ : ℝ) (e : Hsp 2) : Integrable fun x => nfun β γ (vl e x) := by
  have h4 := H2.integrable_Q (H2.ofSp e)
  have h6 := H2.integrable_S (H2.ofSp e)
  exact (h4.const_mul _).add (h6.const_mul _)

theorem Nsp_eq (β γ : ℝ) (e : Hsp 2) :
    Nsp β γ e = -β / 2 * H2.Q (H2.ofSp e) + γ / 3 * H2.S (H2.ofSp e) := by
  have h4 := H2.integrable_Q (H2.ofSp e)
  have h6 := H2.integrable_S (H2.ofSp e)
  rw [Nsp, H2.Q, H2.S, ← integral_const_mul, ← integral_const_mul, ← integral_add
    (h4.const_mul _) (h6.const_mul _)]
  rfl

theorem integrable_conj_mul_L2 (f g : L2 2) :
    Integrable fun x => (starRingEnd ℂ) (f x) * g x := by
  have := L2.integrable_inner (𝕜 := ℂ) f g
  refine this.congr (Eventually.of_forall fun x => ?_)
  simp only [RCLike.inner_apply]
  ring

/-- **Integrated Taylor estimate for the potential energy** on `H²(ℝ²)`. -/
theorem Nsp_taylor (β γ : ℝ) {e f : Hsp 2} {R : ℝ} (he : ‖e‖ ≤ R) (hf : ‖f‖ ≤ R) :
    |Nsp β γ f - Nsp β γ e - 2 * (inner ℂ (vl (Fnl β γ e)) (vl f - vl e)).re| ≤
      (3 * |β| * R ^ 2 + 5 * |γ| * R ^ 4) * ‖vl f - vl e‖ ^ 2 := by
  set C := 3 * |β| * R ^ 2 + 5 * |γ| * R ^ 4 with hC
  have hint1 := integrable_nfun β γ e
  have hint2 := integrable_nfun β γ f
  have hint3 := integrable_conj_mul_L2 (vl (Fnl β γ e)) (vl f - vl e)
  have hinner : (inner ℂ (vl (Fnl β γ e)) (vl f - vl e)).re =
      ∫ x, ((starRingEnd ℂ) (vl (Fnl β γ e) x) * (vl f - vl e) x).re := by
    rw [L2.inner_def, ← RCLike.re_to_complex, ← integral_re (L2.integrable_inner _ _)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [RCLike.inner_apply, RCLike.re_to_complex]
    ring_nf
  have hre : Integrable fun x => ((starRingEnd ℂ) (vl (Fnl β γ e) x) * (vl f - vl e) x).re :=
    hint3.re
  have heq : Nsp β γ f - Nsp β γ e - 2 * (inner ℂ (vl (Fnl β γ e)) (vl f - vl e)).re =
      ∫ x, (nfun β γ (vl f x) - nfun β γ (vl e x) -
        2 * ((starRingEnd ℂ) (vl (Fnl β γ e) x) * (vl f - vl e) x).re) := by
    rw [hinner, Nsp, Nsp, ← integral_sub hint2 hint1, ← integral_const_mul,
      ← integral_sub (f := fun x => nfun β γ (vl f x) - nfun β γ (vl e x))
        (g := fun x => 2 * ((starRingEnd ℂ) (vl (Fnl β γ e) x) * (vl f - vl e) x).re)
        (hint2.sub hint1) (hre.const_mul 2)]
  rw [heq, norm_sq_L2, ← integral_const_mul]
  refine (abs_integral_le_integral_abs).trans (integral_mono_ae
    (((hint2.sub hint1).sub (hre.const_mul 2)).abs) ((integrable_sq_L2' _).const_mul C) ?_)
  filter_upwards [ae_norm_vl_le e, ae_norm_vl_le f, vl_Fnl_ae β γ e,
    Lp.coeFn_sub (vl f) (vl e)] with x h1 h2 h3 h4
  rw [h3, h4, Pi.sub_apply]
  exact nfun_taylor β γ (h1.trans he) (h2.trans hf)

end Sobolev

end ReyesMath
