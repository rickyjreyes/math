import Mathlib
import MathProofs.WholeSpaceMinimizers

/-!
# The free fourth-order group `e^{-it(Δ+k²)²}` on `𝓢`, `L²` and `H²(ℝ^d)` (F01/T3, part 1)

Supporting module for `papers/orbital-stability-fourth-order-cubic-quintic/main.tex`.

* `TemperateGrowth`: closure properties of `Function.HasTemperateGrowth` (products, sums and
  `θ ↦ e^{iθ}` composed with a temperate-growth phase, via Faà di Bruno).
* `Sobolev.symb k ξ = (k² − 4π²|ξ|²)²`, the multiplier `Sobolev.gt k t = e^{-it·symb}` and the free
  group `Sobolev.US` on Schwartz space (Fourier multiplier): group law, commutation with `∂ᵢ` and
  `Δ`, unitarity in `L²` and the strong-continuity estimates.
* `Sobolev.U2`: the unitary extension to `L²(ℝ^d)` (from the dense range of `𝓢 → L²`);
  `Sobolev.U3` on `L² × L² × (L²)^d`; the state space `Sobolev.Hsp d` (the closed Schwartz graph,
  i.e. `H²(ℝ^d)` as a Hilbert space) with the unitary, strongly continuous group `Sobolev.Usp`; the
  bridge `Sobolev.H2.toSp` / `Sobolev.H2.ofSp` with `H2.norm_toSp_sq`, `H2.distH2_le`,
  `H2.norm_le_distH2`.
* The weak generator: `Sobolev.tendsto_Qh` (`h⁻¹⟪f, U(h)u − u⟫ → −i⟪Af, Au⟫` for `f, u ∈ H²`,
  `A = Δ + k²`) and `Sobolev.tendsto_norm_vl_Usp_sub_sq_div` (`‖U(h)u − u‖²_{L²}/|h| → 0`).
-/

open Filter Topology Complex InnerProductSpace MeasureTheory Set
open scoped ContDiff FourierTransform

namespace ReyesMath

namespace TemperateGrowth

open scoped Nat

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem le_infty (n : ℕ) : ((n : ℕ∞) : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.2 le_top

/-- Products of functions of temperate growth have temperate growth. -/
theorem mul {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] {f g : E → A}
    (hf : f.HasTemperateGrowth) (hg : g.HasTemperateGrowth) :
    (fun x => f x * g x).HasTemperateGrowth := by
  refine ⟨hf.1.mul hg.1, fun n => ?_⟩
  obtain ⟨k₁, C₁, hC₁, h₁⟩ := hf.norm_iteratedFDeriv_le_uniform_aux n
  obtain ⟨k₂, C₂, hC₂, h₂⟩ := hg.norm_iteratedFDeriv_le_uniform_aux n
  refine ⟨k₁ + k₂, 2 ^ n * (C₁ * C₂), fun x => ?_⟩
  have hb := norm_iteratedFDeriv_mul_le hf.1 hg.1 x (n := n) (le_infty n)
  refine hb.trans ?_
  have hx : 0 ≤ ‖x‖ := norm_nonneg x
  calc ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ *
        ‖iteratedFDeriv ℝ (n - i) g x‖
      ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (C₁ * (1 + ‖x‖) ^ k₁) *
          (C₂ * (1 + ‖x‖) ^ k₂) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
        gcongr
        · exact h₁ i hi' x
        · exact h₂ (n - i) (Nat.sub_le n i) x
    _ = (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) * (C₁ * C₂) * (1 + ‖x‖) ^ (k₁ + k₂) := by
        rw [Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
    _ = 2 ^ n * (C₁ * C₂) * (1 + ‖x‖) ^ (k₁ + k₂) := by
        congr 2
        exact_mod_cast Nat.sum_range_choose n

/-- Sums of functions of temperate growth have temperate growth. -/
theorem add {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f g : E → F}
    (hf : f.HasTemperateGrowth) (hg : g.HasTemperateGrowth) :
    (fun x => f x + g x).HasTemperateGrowth := by
  refine ⟨hf.1.add hg.1, fun n => ?_⟩
  obtain ⟨k₁, C₁, hC₁, h₁⟩ := hf.norm_iteratedFDeriv_le_uniform_aux n
  obtain ⟨k₂, C₂, hC₂, h₂⟩ := hg.norm_iteratedFDeriv_le_uniform_aux n
  refine ⟨k₁ + k₂, C₁ + C₂, fun x => ?_⟩
  have hx1 : 1 ≤ 1 + ‖x‖ := le_add_of_nonneg_right (norm_nonneg x)
  have e : iteratedFDeriv ℝ n (fun x => f x + g x) x =
      iteratedFDeriv ℝ n f x + iteratedFDeriv ℝ n g x :=
    iteratedFDeriv_add_apply (hf.1.contDiffAt.of_le (le_infty n))
      (hg.1.contDiffAt.of_le (le_infty n))
  rw [e]
  calc ‖iteratedFDeriv ℝ n f x + iteratedFDeriv ℝ n g x‖
      ≤ ‖iteratedFDeriv ℝ n f x‖ + ‖iteratedFDeriv ℝ n g x‖ := norm_add_le _ _
    _ ≤ C₁ * (1 + ‖x‖) ^ k₁ + C₂ * (1 + ‖x‖) ^ k₂ := add_le_add (h₁ n le_rfl x) (h₂ n le_rfl x)
    _ ≤ C₁ * (1 + ‖x‖) ^ (k₁ + k₂) + C₂ * (1 + ‖x‖) ^ (k₁ + k₂) := by
        gcongr
        · exact hx1
        · omega
        · exact hx1
        · omega
    _ = (C₁ + C₂) * (1 + ‖x‖) ^ (k₁ + k₂) := by ring

theorem sum {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type*} (s : Finset ι)
    {f : ι → E → F} (hf : ∀ i ∈ s, (f i).HasTemperateGrowth) :
    (fun x => ∑ i ∈ s, f i x).HasTemperateGrowth := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Function.HasTemperateGrowth.zero
  | insert a s ha ih =>
    simp_rw [Finset.sum_insert ha]
    exact add (hf a (Finset.mem_insert_self a s)) (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem const_mul {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] (c : A) {f : E → A}
    (hf : f.HasTemperateGrowth) : (fun x => c * f x).HasTemperateGrowth :=
  mul (Function.HasTemperateGrowth.const c) hf

/-- The derivatives of `θ ↦ e^{iθ}`. -/
theorem iteratedDeriv_exp_mul_I (n : ℕ) :
    iteratedDeriv n (fun θ : ℝ => Complex.exp (θ * Complex.I)) =
      fun θ : ℝ => Complex.I ^ n * Complex.exp ((θ : ℂ) * Complex.I) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext θ
    have h1 : HasDerivAt (fun θ : ℝ => (θ : ℂ) * Complex.I) (1 * Complex.I) θ :=
      ((hasDerivAt_id θ).ofReal_comp).mul_const Complex.I
    have h2 := (h1.cexp).const_mul (Complex.I ^ n)
    rw [h2.deriv]
    ring

theorem contDiff_exp_mul_I : ContDiff ℝ ∞ fun θ : ℝ => Complex.exp (θ * Complex.I) :=
  Complex.contDiff_exp.comp (Complex.ofRealCLM.contDiff.mul contDiff_const)

theorem norm_iteratedFDeriv_exp_mul_I (n : ℕ) (θ : ℝ) :
    ‖iteratedFDeriv ℝ n (fun θ : ℝ => Complex.exp (θ * Complex.I)) θ‖ = 1 := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_exp_mul_I, norm_mul, norm_pow,
    Complex.norm_I, one_pow, one_mul, Complex.norm_exp_ofReal_mul_I]

/-- `e^{iq}` has temperate growth when the real phase `q` does. -/
theorem exp_mul_I {q : E → ℝ} (hq : q.HasTemperateGrowth) :
    (fun x => Complex.exp (q x * Complex.I)).HasTemperateGrowth := by
  refine ⟨contDiff_exp_mul_I.comp hq.1, fun n => ?_⟩
  obtain ⟨k, C, hC, h⟩ := hq.norm_iteratedFDeriv_le_uniform_aux n
  refine ⟨k * n, n ! * (C + 1) ^ n, fun x => ?_⟩
  have hx1 : 1 ≤ 1 + ‖x‖ := le_add_of_nonneg_right (norm_nonneg x)
  set D := C * (1 + ‖x‖) ^ k + 1 with hD
  have hD1 : 1 ≤ D := by
    have : 0 ≤ C * (1 + ‖x‖) ^ k := by positivity
    rw [hD]
    linarith
  have hb := norm_iteratedFDeriv_comp_le (g := fun θ : ℝ => Complex.exp (θ * Complex.I)) (f := q)
    contDiff_exp_mul_I hq.1 (le_infty n) x (C := 1) (D := D)
    (fun i _ => (norm_iteratedFDeriv_exp_mul_I i (q x)).le)
    (fun i hi hin => by
      calc ‖iteratedFDeriv ℝ i q x‖ ≤ C * (1 + ‖x‖) ^ k := h i hin x
        _ ≤ D := by rw [hD]; linarith
        _ ≤ D ^ i := le_self_pow₀ hD1 (by omega))
  have hcomp : (fun x => Complex.exp (q x * Complex.I)) =
      (fun θ : ℝ => Complex.exp (θ * Complex.I)) ∘ q := rfl
  rw [hcomp]
  refine hb.trans ?_
  rw [mul_one]
  have hD2 : D ≤ (C + 1) * (1 + ‖x‖) ^ k := by
    have : 1 ≤ (1 + ‖x‖) ^ k := one_le_pow₀ hx1
    rw [hD]
    nlinarith
  calc (n ! : ℝ) * D ^ n ≤ n ! * ((C + 1) * (1 + ‖x‖) ^ k) ^ n := by
        gcongr
    _ = n ! * (C + 1) ^ n * (1 + ‖x‖) ^ (k * n) := by rw [mul_pow, ← pow_mul]; ring

end TemperateGrowth

namespace Sobolev

variable {d : ℕ}

local notation "Rd" => EuclideanSpace ℝ (Fin d)

/-! ### The free group `e^{−itA²}` on Schwartz space -/

/-- The symbol `p(ξ) = (k² − |2πξ|²)²` of `A² = (Δ + k²)²`. -/
noncomputable def symb (k : ℝ) (ξ : Rd) : ℝ := (k ^ 2 - qS ξ) ^ 2

theorem symb_nonneg (k : ℝ) (ξ : Rd) : 0 ≤ symb k ξ := sq_nonneg _

theorem hasTemperateGrowth_qS : (qS (d := d)).HasTemperateGrowth := by
  have hc : ∀ i : Fin d, (fun ξ : Rd => ξ i).HasTemperateGrowth := fun i =>
    (EuclideanSpace.proj (𝕜 := ℝ) i : Rd →L[ℝ] ℝ).hasTemperateGrowth
  have hs : (fun ξ : Rd => ∑ i : Fin d, ξ i * ξ i).HasTemperateGrowth :=
    TemperateGrowth.sum _ fun i _ => TemperateGrowth.mul (hc i) (hc i)
  have := TemperateGrowth.const_mul ((2 * Real.pi) ^ 2) hs
  convert this using 1
  funext ξ
  rw [qS, EuclideanSpace.norm_sq_eq]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.norm_eq_abs, sq_abs, sq]

theorem hasTemperateGrowth_symb (k : ℝ) : (symb (d := d) k).HasTemperateGrowth := by
  have h1 : (fun ξ : Rd => k ^ 2 - qS ξ).HasTemperateGrowth := by
    have := TemperateGrowth.add (Function.HasTemperateGrowth.const (k ^ 2))
      (TemperateGrowth.const_mul (-1 : ℝ) (hasTemperateGrowth_qS (d := d)))
    convert this using 1
    funext ξ
    ring
  have := TemperateGrowth.mul h1 h1
  convert this using 1
  funext ξ
  rw [symb, sq]

/-- The multiplier `e^{−itp(ξ)}`. -/
noncomputable def gt (k t : ℝ) (ξ : Rd) : ℂ := Complex.exp ((-(t * symb k ξ) : ℝ) * Complex.I)

theorem hasTemperateGrowth_gt (k t : ℝ) : (gt (d := d) k t).HasTemperateGrowth := by
  have h := TemperateGrowth.exp_mul_I (TemperateGrowth.const_mul (-t)
    (hasTemperateGrowth_symb (d := d) k))
  convert h using 1
  funext ξ
  simp only [gt, neg_mul]

end Sobolev

end ReyesMath

open Filter Topology Complex InnerProductSpace MeasureTheory Set
open scoped ContDiff FourierTransform

namespace ReyesMath

namespace Sobolev

variable {d : ℕ}

local notation "Rd" => EuclideanSpace ℝ (Fin d)

theorem norm_gt (k t : ℝ) (ξ : Rd) : ‖gt k t ξ‖ = 1 := Complex.norm_exp_ofReal_mul_I _

theorem gt_zero (k : ℝ) (ξ : Rd) : gt k 0 ξ = 1 := by simp [gt]

theorem gt_add (k s t : ℝ) (ξ : Rd) : gt k (s + t) ξ = gt k s ξ * gt k t ξ := by
  simp only [gt, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem conj_gt (k t : ℝ) (ξ : Rd) : (starRingEnd ℂ) (gt k t ξ) = gt k (-t) ξ := by
  simp only [gt, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  push_cast
  ring

/-- Multiplication by `e^{−itp}` on Schwartz space. -/
noncomputable def mulGt (k t : ℝ) : SchwartzMap Rd ℂ →L[ℂ] SchwartzMap Rd ℂ :=
  SchwartzMap.bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) (hasTemperateGrowth_gt k t)

theorem mulGt_apply (k t : ℝ) (φ : SchwartzMap Rd ℂ) (ξ : Rd) :
    mulGt k t φ ξ = φ ξ * gt k t ξ := rfl

/-- The free propagator `U(t) = e^{−itA²} = 𝓕⁻¹ e^{−itp(ξ)} 𝓕` on Schwartz space,
`p(ξ) = (k² − |2πξ|²)²`. -/
noncomputable def US (k t : ℝ) : SchwartzMap Rd ℂ →L[ℂ] SchwartzMap Rd ℂ :=
  (SchwartzMap.fourierTransformCLE ℂ (V := Rd) (E := ℂ)).symm.toContinuousLinearMap.comp
    ((mulGt k t).comp (SchwartzMap.fourierTransformCLE ℂ (V := Rd) (E := ℂ)).toContinuousLinearMap)

theorem fourierCLE_US (k t : ℝ) (φ : SchwartzMap Rd ℂ) :
    SchwartzMap.fourierTransformCLE ℂ (US k t φ) =
      mulGt k t (SchwartzMap.fourierTransformCLE ℂ φ) := by
  simp only [US, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]

theorem fourier_US (k t : ℝ) (φ : SchwartzMap Rd ℂ) (ξ : Rd) :
    𝓕 (⇑(US k t φ)) ξ = gt k t ξ * 𝓕 (⇑φ) ξ := by
  have h := congrArg (fun f : SchwartzMap Rd ℂ => f ξ) (fourierCLE_US k t φ)
  simp only [SchwartzMap.fourierTransformCLE_apply, mulGt_apply] at h
  rw [h, mul_comm]

/-- Schwartz functions with equal Fourier transforms are equal. -/
theorem schwartz_ext_fourier {φ ψ : SchwartzMap Rd ℂ} (h : ∀ ξ, 𝓕 (⇑φ) ξ = 𝓕 (⇑ψ) ξ) :
    φ = ψ := by
  apply (SchwartzMap.fourierTransformCLE ℂ).injective
  ext ξ
  exact h ξ

theorem US_zero (k : ℝ) (φ : SchwartzMap Rd ℂ) : US k 0 φ = φ :=
  schwartz_ext_fourier fun ξ => by rw [fourier_US, gt_zero, one_mul]

theorem US_add (k s t : ℝ) (φ : SchwartzMap Rd ℂ) : US k (s + t) φ = US k s (US k t φ) :=
  schwartz_ext_fourier fun ξ => by rw [fourier_US, fourier_US, fourier_US, gt_add, mul_assoc]

theorem dS_US (k t : ℝ) (i : Fin d) (φ : SchwartzMap Rd ℂ) :
    dS i (US k t φ) = US k t (dS i φ) :=
  schwartz_ext_fourier fun ξ => by
    rw [fourier_dS, fourier_US, fourier_US, fourier_dS]
    ring

theorem lapS_US (k t : ℝ) (φ : SchwartzMap Rd ℂ) : lapS (US k t φ) = US k t (lapS φ) :=
  schwartz_ext_fourier fun ξ => by
    rw [fourier_lapS, fourier_US, fourier_US, fourier_lapS]
    ring

/-- `A = Δ + k²` on Schwartz space. -/
noncomputable def AS (k : ℝ) (φ : SchwartzMap Rd ℂ) : SchwartzMap Rd ℂ :=
  lapS φ + ((k ^ 2 : ℝ) : ℂ) • φ

theorem fourier_AS (k : ℝ) (φ : SchwartzMap Rd ℂ) (ξ : Rd) :
    𝓕 (⇑(AS k φ)) ξ = ((k ^ 2 - qS ξ : ℝ) : ℂ) * 𝓕 (⇑φ) ξ := by
  have h := congrArg (fun f : SchwartzMap Rd ℂ => f ξ)
    (map_add (SchwartzMap.fourierTransformCLM ℂ) (lapS φ) (((k ^ 2 : ℝ) : ℂ) • φ))
  have h2 := congrArg (fun f : SchwartzMap Rd ℂ => f ξ)
    (map_smul (SchwartzMap.fourierTransformCLM ℂ) (((k ^ 2 : ℝ) : ℂ)) φ)
  simp only [SchwartzMap.fourierTransformCLM_apply, SchwartzMap.add_apply,
    SchwartzMap.smul_apply, smul_eq_mul] at h h2
  rw [AS, h, h2, fourier_lapS]
  push_cast
  ring

theorem norm_fourier_AS_sq (k : ℝ) (φ : SchwartzMap Rd ℂ) (ξ : Rd) :
    ‖𝓕 (⇑(AS k φ)) ξ‖ ^ 2 = symb k ξ * ‖𝓕 (⇑φ) ξ‖ ^ 2 := by
  rw [fourier_AS, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, symb]

theorem integrable_fourier_sq' (φ : SchwartzMap Rd ℂ) :
    Integrable fun ξ => ‖𝓕 (⇑φ) ξ‖ ^ 2 := by
  rw [← coe_fS]
  exact integrable_normSq (fS φ)

theorem integrable_symb_fourier (k : ℝ) (φ : SchwartzMap Rd ℂ) :
    Integrable fun ξ => symb k ξ * ‖𝓕 (⇑φ) ξ‖ ^ 2 :=
  (integrable_fourier_sq' (AS k φ)).congr (Eventually.of_forall fun ξ => norm_fourier_AS_sq k φ ξ)

theorem norm_toL2_AS_sq (k : ℝ) (φ : SchwartzMap Rd ℂ) :
    ‖toL2 (AS k φ)‖ ^ 2 = ∫ ξ, symb k ξ * ‖𝓕 (⇑φ) ξ‖ ^ 2 := by
  rw [norm_toL2_sq_fourier]
  exact integral_congr_ae (Eventually.of_forall fun ξ => norm_fourier_AS_sq k φ ξ)

theorem inner_toL2_US (k t : ℝ) (φ ψ : SchwartzMap Rd ℂ) :
    inner ℂ (toL2 (US k t φ)) (toL2 ψ) = inner ℂ (toL2 φ) (toL2 (US k (-t) ψ)) := by
  rw [inner_toL2_fourier, inner_toL2_fourier]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only
  rw [fourier_US, fourier_US, map_mul, conj_gt]
  ring

theorem norm_toL2_US (k t : ℝ) (φ : SchwartzMap Rd ℂ) : ‖toL2 (US k t φ)‖ = ‖toL2 φ‖ := by
  have h : ‖toL2 (US k t φ)‖ ^ 2 = ‖toL2 φ‖ ^ 2 := by
    rw [norm_toL2_sq_fourier, norm_toL2_sq_fourier]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp only
    rw [fourier_US, norm_mul, norm_gt, one_mul]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

/-- `|e^{iθ} − 1|² ≤ 2|θ|`. -/
theorem norm_exp_mul_I_sub_one_sq_le (θ : ℝ) :
    ‖Complex.exp (θ * Complex.I) - 1‖ ^ 2 ≤ 2 * |θ| := by
  have h : ‖Complex.exp (θ * Complex.I) - 1‖ ^ 2 = 2 - 2 * Real.cos θ := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im, Complex.one_re, Complex.one_im, sub_zero]
    nlinarith [Real.sin_sq_add_cos_sq θ]
  rw [h]
  rcases le_or_gt |θ| 2 with h2 | h2
  · have hc := Real.one_sub_sq_div_two_le_cos (x := θ)
    have : θ ^ 2 ≤ 2 * |θ| := by
      rw [← sq_abs]
      nlinarith [abs_nonneg θ]
    linarith
  · have := Real.neg_one_le_cos θ
    linarith

/-- `‖(U(h) − 1)φ‖² ≤ 2|h| ‖Aφ‖²`. -/
theorem norm_toL2_US_sub_sq_le (k h : ℝ) (φ : SchwartzMap Rd ℂ) :
    ‖toL2 (US k h φ) - toL2 φ‖ ^ 2 ≤ 2 * |h| * ‖toL2 (AS k φ)‖ ^ 2 := by
  rw [← map_sub, norm_toL2_sq_fourier, norm_toL2_AS_sq, ← integral_const_mul]
  have hF : ∀ ξ, 𝓕 (⇑(US k h φ - φ)) ξ = (gt k h ξ - 1) * 𝓕 (⇑φ) ξ := by
    intro ξ
    have e := congrArg (fun f : SchwartzMap Rd ℂ => f ξ)
      (map_sub (SchwartzMap.fourierTransformCLM ℂ) (US k h φ) φ)
    simp only [SchwartzMap.fourierTransformCLM_apply, SchwartzMap.sub_apply] at e
    rw [e, fourier_US]
    ring
  refine integral_mono (integrable_fourier_sq' _) ((integrable_symb_fourier k φ).const_mul _)
    fun ξ => ?_
  simp only
  rw [hF, norm_mul, mul_pow]
  have hb : ‖gt k h ξ - 1‖ ^ 2 ≤ 2 * |h| * symb k ξ := by
    have := norm_exp_mul_I_sub_one_sq_le (-(h * symb k ξ))
    rw [abs_neg, abs_mul, abs_of_nonneg (symb_nonneg k ξ)] at this
    simpa [gt, mul_assoc] using this
  calc ‖gt k h ξ - 1‖ ^ 2 * ‖𝓕 (⇑φ) ξ‖ ^ 2 ≤ 2 * |h| * symb k ξ * ‖𝓕 (⇑φ) ξ‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hb (sq_nonneg _)
    _ = 2 * |h| * (symb k ξ * ‖𝓕 (⇑φ) ξ‖ ^ 2) := by ring

end Sobolev

end ReyesMath

open Filter Topology Complex InnerProductSpace MeasureTheory Set
open scoped ContDiff FourierTransform

namespace ReyesMath

namespace Sobolev

variable {d : ℕ}

local notation "Rd" => EuclideanSpace ℝ (Fin d)

theorem norm_gt_sub_one_le (k h : ℝ) (ξ : Rd) : ‖gt k h ξ - 1‖ ≤ |h| * symb k ξ := by
  have := norm_exp_mul_I_sub_one_le (-(h * symb k ξ))
  rwa [abs_neg, abs_mul, abs_of_nonneg (symb_nonneg k ξ)] at this

theorem fourier_US_sub (k h : ℝ) (φ : SchwartzMap Rd ℂ) (ξ : Rd) :
    𝓕 (⇑(US k h φ - φ)) ξ = (gt k h ξ - 1) * 𝓕 (⇑φ) ξ := by
  have e := congrArg (fun f : SchwartzMap Rd ℂ => f ξ)
    (map_sub (SchwartzMap.fourierTransformCLM ℂ) (US k h φ) φ)
  simp only [SchwartzMap.fourierTransformCLM_apply, SchwartzMap.sub_apply] at e
  rw [e, fourier_US]
  ring

/-- Continuity of `t ↦ U(t)φ` in `L²`. -/
theorem tendsto_toL2_US (k : ℝ) (φ : SchwartzMap Rd ℂ) (t₀ : ℝ) :
    Tendsto (fun t => toL2 (US k t φ)) (𝓝 t₀) (𝓝 (toL2 (US k t₀ φ))) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hb : ∀ t, ‖toL2 (US k t φ) - toL2 (US k t₀ φ)‖ ≤
      Real.sqrt (2 * |t - t₀|) * ‖toL2 (AS k φ)‖ := by
    intro t
    have e : US k t φ = US k t₀ (US k (t - t₀) φ) := by
      rw [← US_add]
      congr 1
      ring_nf
    rw [e, ← map_sub, ← map_sub, norm_toL2_US, map_sub]
    have := norm_toL2_US_sub_sq_le k (t - t₀) φ
    rw [← Real.sqrt_sq (norm_nonneg _), ← Real.sqrt_sq (norm_nonneg (toL2 (AS k φ))),
      ← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt (by linarith)
  have hlim : Tendsto (fun t => Real.sqrt (2 * |t - t₀|) * ‖toL2 (AS k φ)‖) (𝓝 t₀) (𝓝 0) := by
    have hc : Continuous fun t => Real.sqrt (2 * |t - t₀|) * ‖toL2 (AS k φ)‖ := by fun_prop
    simpa using hc.tendsto t₀
  exact squeeze_zero (fun t => norm_nonneg _) hb hlim

theorem integrable_mul_fourier (φ ψ : SchwartzMap Rd ℂ) :
    Integrable fun ξ => ‖𝓕 (⇑ψ) ξ‖ * ‖𝓕 (⇑φ) ξ‖ := by
  refine (((integrable_fourier_sq' ψ).add (integrable_fourier_sq' φ)).div_const 2).mono'
    ((continuous_fourier ψ).norm.mul (continuous_fourier φ).norm).aestronglyMeasurable
    (Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (‖𝓕 (⇑ψ) ξ‖ - ‖𝓕 (⇑φ) ξ‖)]

theorem integrable_conj_mul_fourier (φ ψ : SchwartzMap Rd ℂ) :
    Integrable fun ξ => (starRingEnd ℂ) (𝓕 (⇑ψ) ξ) * 𝓕 (⇑φ) ξ :=
  (integrable_mul_fourier φ ψ).mono'
    (((continuous_fourier ψ).star).mul (continuous_fourier φ)).aestronglyMeasurable
    (Eventually.of_forall fun ξ => by rw [norm_mul, Complex.norm_conj])

/-- `∫ |F||G| ≤ ‖F‖₂ ‖G‖₂` for the Fourier transforms of Schwartz functions. -/
theorem integral_mul_fourier_le (φ ψ : SchwartzMap Rd ℂ) :
    ∫ ξ, ‖𝓕 (⇑ψ) ξ‖ * ‖𝓕 (⇑φ) ξ‖ ≤ ‖toL2 ψ‖ * ‖toL2 φ‖ := by
  have h := sq_le_of_forall_amgm (x := ∫ ξ, ‖𝓕 (⇑ψ) ξ‖ * ‖𝓕 (⇑φ) ξ‖)
    (integral_nonneg fun ξ => by positivity) (sq_nonneg ‖toL2 ψ‖) (sq_nonneg ‖toL2 φ‖)
    fun t ht => by
      rw [norm_toL2_sq_fourier, norm_toL2_sq_fourier, ← integral_const_mul,
        ← integral_div, ← integral_add ((integrable_fourier_sq' ψ).const_mul t)
          ((integrable_fourier_sq' φ).div_const t), ← integral_div]
      refine integral_mono (integrable_mul_fourier φ ψ)
        ((((integrable_fourier_sq' ψ).const_mul t).add
          ((integrable_fourier_sq' φ).div_const t)).div_const 2) fun ξ => ?_
      have := mul_le_amgm (a := ‖𝓕 (⇑ψ) ξ‖) (b := ‖𝓕 (⇑φ) ξ‖) one_pos ht
      simp only [div_one, one_mul] at this
      exact this
  have h0 : 0 ≤ ‖toL2 ψ‖ * ‖toL2 φ‖ := by positivity
  have := Real.sqrt_le_sqrt h
  rwa [Real.sqrt_sq (integral_nonneg fun ξ => by positivity), ← mul_pow,
    Real.sqrt_sq h0] at this

/-- **Bound on the weak difference quotient:** `|⟪ψ, (U(h) − 1)φ⟫| ≤ |h| ‖Aψ‖ ‖Aφ‖`. -/
theorem norm_inner_US_sub_le (k h : ℝ) (ψ φ : SchwartzMap Rd ℂ) :
    ‖inner ℂ (toL2 ψ) (toL2 (US k h φ) - toL2 φ)‖ ≤
      |h| * (‖toL2 (AS k ψ)‖ * ‖toL2 (AS k φ)‖) := by
  rw [← map_sub, inner_toL2_fourier]
  refine (norm_integral_le_integral_norm _).trans ?_
  have hpt : ∀ ξ, ‖(starRingEnd ℂ) (𝓕 (⇑ψ) ξ) * 𝓕 (⇑(US k h φ - φ)) ξ‖ ≤
      |h| * (‖𝓕 (⇑(AS k ψ)) ξ‖ * ‖𝓕 (⇑(AS k φ)) ξ‖) := by
    intro ξ
    rw [fourier_US_sub, norm_mul, norm_mul, Complex.norm_conj, fourier_AS, fourier_AS,
      norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hb := norm_gt_sub_one_le k h ξ
    have hs : symb k ξ = |k ^ 2 - qS ξ| * |k ^ 2 - qS ξ| := by
      rw [symb, ← abs_mul, abs_of_nonneg (mul_self_nonneg _), sq]
    calc ‖𝓕 (⇑ψ) ξ‖ * (‖gt k h ξ - 1‖ * ‖𝓕 (⇑φ) ξ‖)
        ≤ ‖𝓕 (⇑ψ) ξ‖ * (|h| * symb k ξ * ‖𝓕 (⇑φ) ξ‖) := by gcongr
      _ = |h| * (|k ^ 2 - qS ξ| * ‖𝓕 (⇑ψ) ξ‖ * (|k ^ 2 - qS ξ| * ‖𝓕 (⇑φ) ξ‖)) := by
          rw [hs]; ring
  calc ∫ ξ, ‖(starRingEnd ℂ) (𝓕 (⇑ψ) ξ) * 𝓕 (⇑(US k h φ - φ)) ξ‖
      ≤ ∫ ξ, |h| * (‖𝓕 (⇑(AS k ψ)) ξ‖ * ‖𝓕 (⇑(AS k φ)) ξ‖) :=
        integral_mono_of_nonneg (Eventually.of_forall fun ξ => norm_nonneg _)
          ((integrable_mul_fourier (AS k φ) (AS k ψ)).const_mul _)
          (Eventually.of_forall hpt)
    _ ≤ |h| * (‖toL2 (AS k ψ)‖ * ‖toL2 (AS k φ)‖) := by
        rw [integral_const_mul]
        exact mul_le_mul_of_nonneg_left (integral_mul_fourier_le _ _) (abs_nonneg h)

theorem hasDerivAt_gt (k : ℝ) (ξ : Rd) :
    HasDerivAt (fun h : ℝ => gt k h ξ) (-(symb k ξ : ℂ) * Complex.I) 0 := by
  have h1 : HasDerivAt (fun h : ℝ => ((-(h * symb k ξ) : ℝ) : ℂ) * Complex.I)
      (((-(1 * symb k ξ)) : ℝ) * Complex.I) 0 :=
    ((((hasDerivAt_id (0 : ℝ)).mul_const (symb k ξ)).neg).ofReal_comp).mul_const Complex.I
  have h2 := h1.cexp
  simp only [zero_mul, neg_zero, Complex.ofReal_zero, Complex.exp_zero, one_mul] at h2
  convert h2 using 1
  push_cast
  ring

/-- **Weak derivative of the free group on Schwartz functions:**
`h⁻¹ ⟪ψ, (U(h) − 1)φ⟫ → −i ⟪Aψ, Aφ⟫`. -/
theorem tendsto_inner_US (k : ℝ) (ψ φ : SchwartzMap Rd ℂ) :
    Tendsto (fun h : ℝ => (h : ℂ)⁻¹ * inner ℂ (toL2 ψ) (toL2 (US k h φ) - toL2 φ))
      (𝓝[≠] 0) (𝓝 (-Complex.I * inner ℂ (toL2 (AS k ψ)) (toL2 (AS k φ)))) := by
  have heq : ∀ h : ℝ, (h : ℂ)⁻¹ * inner ℂ (toL2 ψ) (toL2 (US k h φ) - toL2 φ) =
      ∫ ξ, (starRingEnd ℂ) (𝓕 (⇑ψ) ξ) * ((h : ℂ)⁻¹ * (gt k h ξ - 1)) * 𝓕 (⇑φ) ξ := by
    intro h
    rw [← map_sub, inner_toL2_fourier, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp only
    rw [fourier_US_sub]
    ring
  simp_rw [heq]
  have hlimint : -Complex.I * inner ℂ (toL2 (AS k ψ)) (toL2 (AS k φ)) =
      ∫ ξ, (starRingEnd ℂ) (𝓕 (⇑ψ) ξ) * (-(symb k ξ : ℂ) * Complex.I) * 𝓕 (⇑φ) ξ := by
    rw [inner_toL2_fourier, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp only
    rw [fourier_AS, fourier_AS, map_mul, Complex.conj_ofReal, symb]
    push_cast
    ring
  rw [hlimint]
  refine tendsto_integral_filter_of_dominated_convergence
    (fun ξ => ‖𝓕 (⇑(AS k ψ)) ξ‖ * ‖𝓕 (⇑(AS k φ)) ξ‖) ?_ ?_
    (integrable_mul_fourier (AS k φ) (AS k ψ)) ?_
  · refine Eventually.of_forall fun h => Continuous.aestronglyMeasurable ?_
    have hg : Continuous fun ξ : Rd => gt k h ξ := by
      unfold gt symb qS
      fun_prop
    exact (((continuous_fourier ψ).star).mul (continuous_const.mul (hg.sub continuous_const))).mul
      (continuous_fourier φ)
  · filter_upwards [self_mem_nhdsWithin] with h hh
    refine Eventually.of_forall fun ξ => ?_
    have hh' : (h : ℝ) ≠ 0 := hh
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_conj, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, fourier_AS, fourier_AS, norm_mul, norm_mul, Complex.norm_real,
      Real.norm_eq_abs]
    have hb := norm_gt_sub_one_le k h ξ
    have hs : symb k ξ = |k ^ 2 - qS ξ| * |k ^ 2 - qS ξ| := by
      rw [symb, ← abs_mul, abs_of_nonneg (mul_self_nonneg _), sq]
    have habs : 0 < |h| := abs_pos.2 hh'
    have hq : |h|⁻¹ * ‖gt k h ξ - 1‖ ≤ symb k ξ := by
      rw [inv_mul_le_iff₀ habs]
      exact hb
    calc ‖𝓕 (⇑ψ) ξ‖ * (|h|⁻¹ * ‖gt k h ξ - 1‖) * ‖𝓕 (⇑φ) ξ‖
        ≤ ‖𝓕 (⇑ψ) ξ‖ * symb k ξ * ‖𝓕 (⇑φ) ξ‖ := by gcongr
      _ = |k ^ 2 - qS ξ| * ‖𝓕 (⇑ψ) ξ‖ * (|k ^ 2 - qS ξ| * ‖𝓕 (⇑φ) ξ‖) := by rw [hs]; ring
  · refine Eventually.of_forall fun ξ => ?_
    have hd := (hasDerivAt_iff_tendsto_slope.1 (hasDerivAt_gt k ξ))
    have hd' : Tendsto (fun h : ℝ => (h : ℂ)⁻¹ * (gt k h ξ - 1)) (𝓝[≠] 0)
        (𝓝 (-(symb k ξ : ℂ) * Complex.I)) := by
      refine hd.congr fun h => ?_
      rw [slope_def_module, sub_zero, gt_zero, Complex.real_smul, Complex.ofReal_inv]
    exact (tendsto_const_nhds.mul hd').mul tendsto_const_nhds

/-- `‖(U(h) − 1)φ‖² = o(h)`. -/
theorem tendsto_norm_US_sub_sq_div (k : ℝ) (φ : SchwartzMap Rd ℂ) :
    Tendsto (fun h : ℝ => ‖toL2 (US k h φ) - toL2 φ‖ ^ 2 / |h|) (𝓝[≠] 0) (𝓝 0) := by
  have heq : ∀ h : ℝ, ‖toL2 (US k h φ) - toL2 φ‖ ^ 2 / |h| =
      ∫ ξ, ‖gt k h ξ - 1‖ ^ 2 / |h| * ‖𝓕 (⇑φ) ξ‖ ^ 2 := by
    intro h
    rw [← map_sub, norm_toL2_sq_fourier, ← integral_div]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp only
    rw [fourier_US_sub, norm_mul, mul_pow]
    ring
  simp_rw [heq]
  have key : Tendsto (fun h : ℝ => ∫ ξ, ‖gt k h ξ - 1‖ ^ 2 / |h| * ‖𝓕 (⇑φ) ξ‖ ^ 2) (𝓝[≠] 0)
      (𝓝 (∫ ξ : Rd, (0 : ℝ))) := ?_
  · simpa using key
  refine tendsto_integral_filter_of_dominated_convergence
    (fun ξ => 2 * (symb k ξ * ‖𝓕 (⇑φ) ξ‖ ^ 2)) ?_ ?_
    ((integrable_symb_fourier k φ).const_mul 2) ?_
  · refine Eventually.of_forall fun h => Continuous.aestronglyMeasurable ?_
    have hg : Continuous fun ξ : Rd => gt k h ξ := by
      unfold gt symb qS
      fun_prop
    exact ((hg.sub continuous_const).norm.pow 2).div_const _ |>.mul ((continuous_fourier φ).norm.pow 2)
  · filter_upwards [self_mem_nhdsWithin] with h hh
    refine Eventually.of_forall fun ξ => ?_
    have hh' : (h : ℝ) ≠ 0 := hh
    have habs : 0 < |h| := abs_pos.2 hh'
    rw [Real.norm_of_nonneg (by positivity)]
    have hb : ‖gt k h ξ - 1‖ ^ 2 ≤ 2 * |h| * symb k ξ := by
      have := norm_exp_mul_I_sub_one_sq_le (-(h * symb k ξ))
      rw [abs_neg, abs_mul, abs_of_nonneg (symb_nonneg k ξ)] at this
      simpa [gt, mul_assoc] using this
    have : ‖gt k h ξ - 1‖ ^ 2 / |h| ≤ 2 * symb k ξ := by
      rw [div_le_iff₀ habs]
      linarith
    calc ‖gt k h ξ - 1‖ ^ 2 / |h| * ‖𝓕 (⇑φ) ξ‖ ^ 2 ≤ 2 * symb k ξ * ‖𝓕 (⇑φ) ξ‖ ^ 2 :=
          mul_le_mul_of_nonneg_right this (sq_nonneg _)
      _ = 2 * (symb k ξ * ‖𝓕 (⇑φ) ξ‖ ^ 2) := by ring
  · refine Eventually.of_forall fun ξ => ?_
    have hup : Tendsto (fun h : ℝ => |h| * symb k ξ ^ 2 * ‖𝓕 (⇑φ) ξ‖ ^ 2) (𝓝[≠] 0) (𝓝 0) := by
      have hc : Continuous fun h : ℝ => |h| * symb k ξ ^ 2 * ‖𝓕 (⇑φ) ξ‖ ^ 2 := by fun_prop
      have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := {(0 : ℝ)}ᶜ))
      simpa using this
    refine squeeze_zero' (Eventually.of_forall fun h => by positivity) ?_ hup
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hh' : (h : ℝ) ≠ 0 := hh
    have habs : 0 < |h| := abs_pos.2 hh'
    have hb := norm_gt_sub_one_le k h ξ
    have hb2 : ‖gt k h ξ - 1‖ ^ 2 ≤ (|h| * symb k ξ) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hb 2
    have : ‖gt k h ξ - 1‖ ^ 2 / |h| ≤ |h| * symb k ξ ^ 2 := by
      rw [div_le_iff₀ habs]
      nlinarith
    exact mul_le_mul_of_nonneg_right this (sq_nonneg _)

end Sobolev

end ReyesMath

open Filter Topology Complex InnerProductSpace MeasureTheory Set
open scoped ContDiff FourierTransform

namespace ReyesMath

namespace Sobolev

variable {d : ℕ}

local notation "Rd" => EuclideanSpace ℝ (Fin d)

/-! ### The free group on `L²` -/

theorem toL2_injective : Function.Injective (toL2 : SchwartzMap Rd ℂ → L2 d) := by
  intro φ ψ h
  apply SchwartzMap.injective_toLp (E := Rd) (F := ℂ) 2 volume
  simpa [toL2] using h

/-- Schwartz functions as a subspace of `L²`. -/
noncomputable def S2 (d : ℕ) : Submodule ℂ (L2 d) :=
  LinearMap.range (toL2 (d := d) : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ →L[ℂ] L2 d)

theorem mem_S2 (φ : SchwartzMap Rd ℂ) : toL2 φ ∈ S2 d := LinearMap.mem_range.2 ⟨φ, rfl⟩

theorem S2_closure : (S2 d).topologicalClosure = ⊤ := by
  rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro w hw
  apply eq_zero_of_inner_schwartz
  intro χ
  exact Submodule.inner_right_of_mem_orthogonal (mem_S2 χ) hw

theorem denseRange_toL2 : DenseRange (toL2 : SchwartzMap Rd ℂ → L2 d) := by
  have h : Dense ((S2 d : Submodule ℂ (L2 d)) : Set (L2 d)) :=
    Submodule.dense_iff_topologicalClosure_eq_top.2 S2_closure
  have e : range (toL2 : SchwartzMap Rd ℂ → L2 d) = (S2 d : Set (L2 d)) := by
    ext f
    simp only [mem_range, SetLike.mem_coe, S2, LinearMap.mem_range]
  rw [DenseRange, e]
  exact h

theorem denseRange_subtypeL_S2 : DenseRange ((S2 d).subtypeL) := by
  have h : Dense ((S2 d : Submodule ℂ (L2 d)) : Set (L2 d)) :=
    Submodule.dense_iff_topologicalClosure_eq_top.2 S2_closure
  simpa [DenseRange, Submodule.coe_subtypeL', Subtype.range_coe] using h

/-- `𝓢 ≃ S2`. -/
noncomputable def eS (d : ℕ) : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ ≃ₗ[ℂ] S2 d :=
  LinearEquiv.ofInjective
    (toL2 (d := d) : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ →L[ℂ] L2 d).toLinearMap
    toL2_injective

theorem coe_eS (φ : SchwartzMap Rd ℂ) : ((eS d φ : S2 d) : L2 d) = toL2 φ := rfl

theorem eS_symm_toL2 (φ : SchwartzMap Rd ℂ) (h : toL2 φ ∈ S2 d) :
    (eS d).symm ⟨toL2 φ, h⟩ = φ := by
  rw [LinearEquiv.symm_apply_eq]
  rfl

theorem toL2_eS_symm (v : S2 d) : toL2 ((eS d).symm v) = (v : L2 d) := by
  conv_rhs => rw [← (eS d).apply_symm_apply v]
  rfl

/-- `U(t)` on the Schwartz subspace of `L²`. -/
noncomputable def V2 (k t : ℝ) : S2 d →ₗ[ℂ] L2 d :=
  ((toL2 (d := d) : SchwartzMap Rd ℂ →L[ℂ] L2 d).toLinearMap ∘ₗ (US k t).toLinearMap) ∘ₗ
    (eS d).symm.toLinearMap

theorem norm_V2 (k t : ℝ) (v : S2 d) : ‖V2 k t v‖ = ‖v‖ := by
  simp only [V2, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    ContinuousLinearMap.coe_coe]
  rw [norm_toL2_US, toL2_eS_symm]
  rfl

noncomputable def W2 (k t : ℝ) : S2 d →L[ℂ] L2 d :=
  LinearMap.mkContinuous (V2 k t) 1 fun v => by rw [norm_V2, one_mul]

/-- **The free Schrödinger group `U(t) = e^{−itA²}` on `L²(ℝ^d)`**, the continuous extension of
the Schwartz-space propagator `US`. -/
noncomputable def U2 (k t : ℝ) : L2 d →L[ℂ] L2 d :=
  (W2 k t).extend (S2 d).subtypeL denseRange_subtypeL_S2
    (Submodule.subtypeₗᵢ (S2 d)).isometry.isUniformInducing

theorem U2_toL2 (k t : ℝ) (φ : SchwartzMap Rd ℂ) : U2 k t (toL2 φ) = toL2 (US k t φ) := by
  have hmem : toL2 φ ∈ S2 d := mem_S2 φ
  have h := ContinuousLinearMap.extend_eq (W2 k t) (S2 d).subtypeL denseRange_subtypeL_S2
    (Submodule.subtypeₗᵢ (S2 d)).isometry.isUniformInducing ⟨toL2 φ, hmem⟩
  have e : (S2 d).subtypeL ⟨toL2 φ, hmem⟩ = toL2 φ := rfl
  rw [e] at h
  rw [U2, h]
  simp only [W2, LinearMap.mkContinuous_apply, V2, LinearMap.coe_comp, Function.comp_apply,
    LinearEquiv.coe_coe, ContinuousLinearMap.coe_coe]
  rw [eS_symm_toL2]

attribute [irreducible] U2

theorem norm_U2 (k t : ℝ) (f : L2 d) : ‖U2 k t f‖ = ‖f‖ := by
  refine denseRange_toL2.induction_on f
    (isClosed_eq ((U2 k t).continuous.norm) continuous_norm) fun φ => ?_
  rw [U2_toL2, norm_toL2_US]

theorem inner_U2 (k t : ℝ) (f g : L2 d) :
    inner ℂ (U2 k t f) g = inner ℂ f (U2 k (-t) g) := by
  refine denseRange_toL2.induction_on₂ (p := fun f g => inner ℂ (U2 k t f) g =
    inner ℂ f (U2 k (-t) g)) ?_ (fun φ ψ => ?_) f g
  · exact isClosed_eq (((U2 k t).continuous.comp continuous_fst).inner continuous_snd)
      (continuous_fst.inner ((U2 k (-t)).continuous.comp continuous_snd))
  · dsimp only
    rw [U2_toL2, U2_toL2, inner_toL2_US]

theorem inner_U2_U2 (k t : ℝ) (f g : L2 d) : inner ℂ (U2 k t f) (U2 k t g) = inner ℂ f g := by
  rw [inner_U2]
  refine denseRange_toL2.induction_on₂ (p := fun f g => inner ℂ f (U2 k (-t) (U2 k t g)) =
    inner ℂ f g) ?_ (fun φ ψ => ?_) f g
  · exact isClosed_eq (continuous_fst.inner (((U2 k (-t)).continuous.comp
      (U2 k t).continuous).comp continuous_snd)) (continuous_fst.inner continuous_snd)
  · dsimp only
    rw [U2_toL2, U2_toL2, ← US_add, neg_add_cancel, US_zero]

theorem U2_add (k s t : ℝ) (f : L2 d) : U2 k (s + t) f = U2 k s (U2 k t f) := by
  refine denseRange_toL2.induction_on f
    (isClosed_eq (U2 k (s + t)).continuous ((U2 k s).continuous.comp (U2 k t).continuous))
    fun φ => ?_
  rw [U2_toL2, U2_toL2, U2_toL2, US_add]

theorem U2_zero (k : ℝ) (f : L2 d) : U2 k 0 f = f := by
  refine denseRange_toL2.induction_on f (isClosed_eq (U2 k 0).continuous continuous_id)
    fun φ => ?_
  rw [U2_toL2, US_zero]

/-- **Strong continuity** of `t ↦ U(t)f` in `L²`. -/
theorem continuous_U2 (k : ℝ) (f : L2 d) : Continuous fun t => U2 k t f := by
  rw [continuous_iff_continuousAt]
  intro t₀
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨φ, hφ⟩ := denseRange_toL2.exists_dist_lt f (show 0 < ε / 3 by positivity)
  have hs := Metric.tendsto_nhds.1 (tendsto_toL2_US k φ t₀) (ε / 3) (by positivity)
  filter_upwards [hs] with t ht
  have e1 : dist (U2 k t f) (U2 k t (toL2 φ)) = dist f (toL2 φ) := by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub, norm_U2]
  have e2 : dist (U2 k t₀ (toL2 φ)) (U2 k t₀ f) = dist (toL2 φ) f := by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub, norm_U2]
  calc dist (U2 k t f) (U2 k t₀ f) ≤ dist (U2 k t f) (U2 k t (toL2 φ)) +
        dist (U2 k t (toL2 φ)) (U2 k t₀ (toL2 φ)) + dist (U2 k t₀ (toL2 φ)) (U2 k t₀ f) :=
        dist_triangle4 _ _ _ _
    _ < ε / 3 + ε / 3 + ε / 3 := by
        rw [e1, e2, U2_toL2, U2_toL2, dist_comm (toL2 φ) f]
        gcongr
    _ = ε := by ring

end Sobolev

end ReyesMath

open Filter Topology Complex InnerProductSpace MeasureTheory Set
open scoped ContDiff FourierTransform

namespace ReyesMath

namespace Sobolev

variable {d : ℕ}

local notation "Rd" => EuclideanSpace ℝ (Fin d)

/-! ### The free group on `E3 = L² × L² × (L²)^d` and on `H²` -/

/-- `U(t)` acting componentwise on `E3`. -/
noncomputable def U3 (k t : ℝ) : E3 d →L[ℂ] E3 d :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Option (Option (Fin d)) => L2 d)).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.pi fun o => (U2 k t).comp (ContinuousLinearMap.proj o)).comp
      (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Option (Option (Fin d)) => L2 d)).toContinuousLinearMap)

theorem U3_apply (k t : ℝ) (e : E3 d) (o : Option (Option (Fin d))) :
    U3 k t e o = U2 k t (e o) := rfl

theorem norm_U3 (k t : ℝ) (e : E3 d) : ‖U3 k t e‖ = ‖e‖ := by
  have h : ‖U3 k t e‖ ^ 2 = ‖e‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    refine Finset.sum_congr rfl fun o _ => ?_
    rw [U3_apply, norm_U2]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

theorem U3_graphS (k t : ℝ) (φ : SchwartzMap Rd ℂ) : U3 k t (graphS φ) = graphS (US k t φ) := by
  refine PiLp.ext fun o => ?_
  rcases o with _ | _ | i
  · exact U2_toL2 k t φ
  · change U2 k t (toL2 (lapS φ)) = toL2 (lapS (US k t φ))
    rw [U2_toL2, lapS_US]
  · change U2 k t (toL2 (dS i φ)) = toL2 (dS i (US k t φ))
    rw [U2_toL2, dS_US]

theorem continuous_U3 (k : ℝ) (e : E3 d) : Continuous fun t => U3 k t e := by
  have : Continuous fun t => WithLp.ofLp (U3 k t e) :=
    continuous_pi fun o => continuous_U2 k (e o)
  exact (PiLp.continuous_toLp 2 _).comp this

/-- `H²(ℝ^d)` as the closed subspace `cl{(φ, Δφ, ∇φ)}` of the Hilbert space `E3`, as a type of
its own carrying one canonical Hilbert-space structure. -/
def Hsp (d : ℕ) : Type := ↥(graphSub d).topologicalClosure

namespace Hsp

noncomputable instance instNormedAddCommGroup : NormedAddCommGroup (Hsp d) :=
  inferInstanceAs (NormedAddCommGroup ↥(graphSub d).topologicalClosure)

noncomputable instance instInnerProductSpace : InnerProductSpace ℂ (Hsp d) :=
  inferInstanceAs (InnerProductSpace ℂ ↥(graphSub d).topologicalClosure)

instance instCompleteSpace : CompleteSpace (Hsp d) :=
  show CompleteSpace ↥(graphSub d).topologicalClosure from
    (Submodule.isClosed_topologicalClosure (graphSub d)).completeSpace_coe

/-- The underlying element `(u, Δu, ∇u)` of `E3`. -/
def val (e : Hsp d) : E3 d := Subtype.val (show ↥(graphSub d).topologicalClosure from e)

instance : CoeOut (Hsp d) (E3 d) := ⟨val⟩

theorem mem (e : Hsp d) : (e : E3 d) ∈ (graphSub d).topologicalClosure :=
  Subtype.property (show ↥(graphSub d).topologicalClosure from e)

/-- Build an element of `H²` from an element of the closure. -/
def mk (x : E3 d) (hx : x ∈ (graphSub d).topologicalClosure) : Hsp d :=
  show ↥(graphSub d).topologicalClosure from ⟨x, hx⟩

@[simp] theorem val_mk (x : E3 d) (hx : x ∈ (graphSub d).topologicalClosure) :
    ((mk x hx : Hsp d) : E3 d) = x := rfl

theorem ext {e f : Hsp d} (h : (e : E3 d) = f) : e = f :=
  Subtype.ext (p := fun x => x ∈ (graphSub d).topologicalClosure) h

theorem norm_val (e : Hsp d) : ‖(e : E3 d)‖ = ‖e‖ := rfl

theorem val_add (e f : Hsp d) : ((e + f : Hsp d) : E3 d) = e + f := rfl

theorem val_sub (e f : Hsp d) : ((e - f : Hsp d) : E3 d) = e - f := rfl

theorem val_smul (c : ℂ) (e : Hsp d) : ((c • e : Hsp d) : E3 d) = c • (e : E3 d) := rfl

theorem val_zero : ((0 : Hsp d) : E3 d) = 0 := rfl

theorem continuous_val : Continuous (val (d := d)) := continuous_subtype_val

theorem continuous_iff {X : Type*} [TopologicalSpace X] {f : X → Hsp d} :
    Continuous f ↔ Continuous fun x => (f x : E3 d) :=
  continuous_induced_rng

end Hsp

theorem U3_mem (k t : ℝ) {e : E3 d} (he : e ∈ (graphSub d).topologicalClosure) :
    U3 k t e ∈ (graphSub d).topologicalClosure := by
  have hle : (graphSub d).topologicalClosure ≤
      ((graphSub d).topologicalClosure).comap (U3 (d := d) k t).toLinearMap := by
    refine Submodule.topologicalClosure_minimal _ ?_ ?_
    · rintro _ ⟨φ, rfl⟩
      rw [Submodule.mem_comap]
      change U3 k t (graphS φ) ∈ (graphSub d).topologicalClosure
      rw [U3_graphS]
      exact Submodule.le_topologicalClosure _ ⟨US k t φ, rfl⟩
    · exact (Submodule.isClosed_topologicalClosure _).preimage (U3 (d := d) k t).continuous
  exact hle he

/-- **The free group `U(t) = e^{−itA²}` on `H²`.** -/
noncomputable def Usp (k t : ℝ) : Hsp d →L[ℂ] Hsp d :=
  (((U3 k t).comp (graphSub d).topologicalClosure.subtypeL).codRestrict _
    fun e => U3_mem k t e.2 :
      ↥(graphSub d).topologicalClosure →L[ℂ] ↥(graphSub d).topologicalClosure)

theorem coe_Usp (k t : ℝ) (e : Hsp d) : ((Usp k t e : Hsp d) : E3 d) = U3 k t e := rfl

theorem Usp_apply (k t : ℝ) (e : Hsp d) (o : Option (Option (Fin d))) :
    ((Usp k t e : Hsp d) : E3 d) o = U2 k t ((e : E3 d) o) := rfl

theorem norm_Usp (k t : ℝ) (e : Hsp d) : ‖Usp k t e‖ = ‖e‖ := by
  change ‖((Usp k t e : Hsp d) : E3 d)‖ = ‖(e : E3 d)‖
  rw [coe_Usp, norm_U3]

theorem Usp_add (k s t : ℝ) (e : Hsp d) : Usp k (s + t) e = Usp k s (Usp k t e) := by
  apply Hsp.ext
  refine PiLp.ext fun o => ?_
  simp only [Usp_apply, U2_add]

theorem Usp_zero (k : ℝ) (e : Hsp d) : Usp k 0 e = e := by
  apply Hsp.ext
  refine PiLp.ext fun o => ?_
  simp only [Usp_apply, U2_zero]

theorem Usp_neg_Usp (k t : ℝ) (e : Hsp d) : Usp k (-t) (Usp k t e) = e := by
  rw [← Usp_add, neg_add_cancel, Usp_zero]

theorem Usp_Usp_neg (k t : ℝ) (e : Hsp d) : Usp k t (Usp k (-t) e) = e := by
  rw [← Usp_add, add_neg_cancel, Usp_zero]

theorem continuous_Usp (k : ℝ) (e : Hsp d) : Continuous fun t => Usp k t e :=
  Hsp.continuous_iff.2 (continuous_U3 k (e : E3 d))

/-- Joint continuity of `(t, e) ↦ U(t)e` on `H²`. -/
theorem continuous_Usp_uncurry (k : ℝ) :
    Continuous fun p : ℝ × Hsp d => Usp k p.1 p.2 := by
  rw [continuous_iff_continuousAt]
  rintro ⟨t₀, e₀⟩
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  have h1 := Metric.tendsto_nhds.1 ((continuous_Usp k e₀).tendsto t₀) (ε / 2) (by positivity)
  have h1' : ∀ᶠ p : ℝ × Hsp d in 𝓝 (t₀, e₀), dist (Usp k p.1 e₀) (Usp k t₀ e₀) < ε / 2 :=
    (continuous_fst.tendsto (t₀, e₀)).eventually h1
  have h2 : ∀ᶠ p : ℝ × Hsp d in 𝓝 (t₀, e₀), dist p.2 e₀ < ε / 2 :=
    (continuous_snd.tendsto (t₀, e₀)).eventually (Metric.ball_mem_nhds e₀ (by positivity))
  filter_upwards [h1', h2] with p hp1 hp2
  calc dist (Usp k p.1 p.2) (Usp k t₀ e₀) ≤ dist (Usp k p.1 p.2) (Usp k p.1 e₀) +
        dist (Usp k p.1 e₀) (Usp k t₀ e₀) := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := by
        rw [dist_eq_norm, ← map_sub, norm_Usp, ← dist_eq_norm]
        gcongr
    _ = ε := by ring

/-! ### Between `H2 d` and `Hsp d` -/

namespace H2

/-- `H2 d → Hsp d`. -/
noncomputable def toSp (U : H2 d) : Hsp d := Hsp.mk (emb U) (emb_mem_closure U)

theorem approx_of_mem_closure {e : E3 d} (he : e ∈ (graphSub d).topologicalClosure) :
    ∃ φ : ℕ → SchwartzMap Rd ℂ,
      Tendsto (fun n => toL2 (φ n)) atTop (𝓝 (e none)) ∧
      (∀ i, Tendsto (fun n => toL2 (dS i (φ n))) atTop (𝓝 (e (some (some i))))) ∧
      Tendsto (fun n => toL2 (lapS (φ n))) atTop (𝓝 (e (some none))) := by
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at he
  obtain ⟨g, hg, hlim⟩ := mem_closure_iff_seq_limit.1 he
  choose φ hφ using fun n => (hg n : g n ∈ LinearMap.range (graphS (d := d)))
  have hc : ∀ o, Tendsto (fun n => g n o) atTop (𝓝 (e o)) := fun o =>
    ((PiLp.continuous_apply 2 _ o).tendsto e).comp hlim
  refine ⟨φ, ?_, fun i => ?_, ?_⟩
  · simpa only [← hφ] using hc none
  · simpa only [← hφ] using hc (some (some i))
  · simpa only [← hφ] using hc (some none)

/-- `Hsp d → H2 d`. -/
noncomputable def ofSp (e : Hsp d) : H2 d :=
  ⟨(e : E3 d) none, fun i => (e : E3 d) (some (some i)), (e : E3 d) (some none),
    approx_of_mem_closure (Hsp.mem e)⟩

theorem toSp_ofSp (e : Hsp d) : toSp (ofSp e) = e := by
  apply Hsp.ext
  refine PiLp.ext fun o => ?_
  rcases o with _ | _ | i <;> rfl

theorem ofSp_toSp (U : H2 d) : ofSp (toSp U) = U := ext_of_val rfl

theorem toSp_injective : Function.Injective (toSp (d := d)) := fun U V h => by
  rw [← ofSp_toSp U, h, ofSp_toSp]

theorem ofSp_val (e : Hsp d) : (ofSp e).val = (e : E3 d) none := rfl

theorem toSp_val (U : H2 d) : ((toSp U : Hsp d) : E3 d) none = U.val := rfl

theorem toSp_lap (U : H2 d) : ((toSp U : Hsp d) : E3 d) (some none) = U.lap := rfl

theorem toSp_grad (U : H2 d) (i : Fin d) :
    ((toSp U : Hsp d) : E3 d) (some (some i)) = U.grad i := rfl

/-- `‖u‖²_{H²} = M(u) + D(u) + K(u)`. -/
theorem norm_toSp_sq (U : H2 d) : ‖toSp U‖ ^ 2 = M U + D U + K U := by
  change ‖((toSp U : Hsp d) : E3 d)‖ ^ 2 = _
  rw [PiLp.norm_sq_eq_of_L2, Fintype.sum_option, Fintype.sum_option]
  simp only [toSp_val, toSp_lap, toSp_grad, M, D, K]
  ring

theorem M_le_norm_sq (U : H2 d) : M U ≤ ‖toSp U‖ ^ 2 := by
  rw [norm_toSp_sq]; linarith [D_nonneg U, K_nonneg U]

theorem D_le_norm_sq (U : H2 d) : D U ≤ ‖toSp U‖ ^ 2 := by
  rw [norm_toSp_sq]; linarith [M_nonneg U, K_nonneg U]

/-- The `H²` distance is controlled by the `Hsp` norm. -/
theorem distH2_le (U V : H2 d) :
    distH2 U V ≤ (d + 2) * ‖toSp U - toSp V‖ := by
  have hc : ∀ o, ‖((toSp U - toSp V : Hsp d) : E3 d) o‖ ≤ ‖toSp U - toSp V‖ := fun o =>
    PiLp.norm_apply_le _ o
  unfold distH2
  have h0 := hc none
  have h1 := hc (some none)
  have h2 : ∑ i : Fin d, ‖U.grad i - V.grad i‖ ≤ d * ‖toSp U - toSp V‖ := by
    calc ∑ i : Fin d, ‖U.grad i - V.grad i‖ ≤ ∑ _i : Fin d, ‖toSp U - toSp V‖ :=
          Finset.sum_le_sum fun i _ => hc (some (some i))
      _ = d * ‖toSp U - toSp V‖ := by simp
  have e0 : ((toSp U - toSp V : Hsp d) : E3 d) none = U.val - V.val := rfl
  have e1 : ((toSp U - toSp V : Hsp d) : E3 d) (some none) = U.lap - V.lap := rfl
  rw [e0] at h0
  rw [e1] at h1
  linarith

/-- And conversely. -/
theorem norm_le_distH2 (U V : H2 d) : ‖toSp U - toSp V‖ ≤ distH2 U V := by
  have hsq : ‖toSp U - toSp V‖ ^ 2 = ‖U.val - V.val‖ ^ 2 + ‖U.lap - V.lap‖ ^ 2 +
      ∑ i : Fin d, ‖U.grad i - V.grad i‖ ^ 2 := by
    change ‖((toSp U - toSp V : Hsp d) : E3 d)‖ ^ 2 = _
    rw [PiLp.norm_sq_eq_of_L2, Fintype.sum_option, Fintype.sum_option]
    have e0 : ((toSp U - toSp V : Hsp d) : E3 d) none = U.val - V.val := rfl
    have e1 : ((toSp U - toSp V : Hsp d) : E3 d) (some none) = U.lap - V.lap := rfl
    have e2 : ∀ i, ((toSp U - toSp V : Hsp d) : E3 d) (some (some i)) = U.grad i - V.grad i :=
      fun i => rfl
    simp only [e0, e1, e2]
    ring
  have hD := distH2_nonneg U V
  have hsum : ∑ i : Fin d, ‖U.grad i - V.grad i‖ ^ 2 ≤ (∑ i : Fin d, ‖U.grad i - V.grad i‖) ^ 2 :=
    Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => norm_nonneg _
  have : ‖toSp U - toSp V‖ ^ 2 ≤ distH2 U V ^ 2 := by
    rw [hsq]
    unfold distH2
    have a := norm_nonneg (U.val - V.val)
    have b := norm_nonneg (U.lap - V.lap)
    have c : 0 ≤ ∑ i : Fin d, ‖U.grad i - V.grad i‖ := Finset.sum_nonneg fun i _ => norm_nonneg _
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hD two_ne_zero).1 this

end H2

end Sobolev

end ReyesMath

open Filter Topology Complex InnerProductSpace MeasureTheory Set
open scoped ContDiff FourierTransform

namespace ReyesMath

/-- A family of additive maps, uniformly bounded, converging on a dense set, converges
everywhere. -/
theorem tendsto_of_dense_of_bound {X Y ι : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y]
    {l : Filter ι} {T : ι → X → Y} {L : X → Y} {C : ℝ} (hC : 0 ≤ C)
    (hT : ∀ i x y, T i (x - y) = T i x - T i y) (hL : ∀ x y, L (x - y) = L x - L y)
    (hTb : ∀ᶠ i in l, ∀ x, ‖T i x‖ ≤ C * ‖x‖) (hLb : ∀ x, ‖L x‖ ≤ C * ‖x‖)
    {D : Set X} (hD : Dense D) (hconv : ∀ y ∈ D, Tendsto (fun i => T i y) l (𝓝 (L y)))
    (x : X) : Tendsto (fun i => T i x) l (𝓝 (L x)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨y, hyD, hy⟩ := hD.exists_dist_lt x (show 0 < ε / (3 * (C + 1)) by positivity)
  have hev := Metric.tendsto_nhds.1 (hconv y hyD) (ε / 3) (by positivity)
  filter_upwards [hev, hTb] with i hi hbi
  have hxy : C * ‖x - y‖ < ε / 3 := by
    rw [← dist_eq_norm]
    calc C * dist x y ≤ (C + 1) * dist x y := by nlinarith [dist_nonneg (x := x) (y := y)]
      _ < (C + 1) * (ε / (3 * (C + 1))) := by gcongr
      _ = ε / 3 := by field_simp
  have e1 : T i x - L x = T i (x - y) + (T i y - L y) - L (x - y) := by
    rw [hT, hL]
    abel
  rw [dist_eq_norm, e1]
  calc ‖T i (x - y) + (T i y - L y) - L (x - y)‖
      ≤ ‖T i (x - y)‖ + ‖T i y - L y‖ + ‖L (x - y)‖ := norm_sub_le_of_le (norm_add_le _ _) le_rfl
    _ < ε / 3 + ε / 3 + ε / 3 := by
        rw [← dist_eq_norm (T i y)]
        have h1 := hbi (x - y)
        have h2 := hLb (x - y)
        gcongr
        · linarith
        · linarith
    _ = ε := by ring

namespace Sobolev

variable {d : ℕ}

local notation "Rd" => EuclideanSpace ℝ (Fin d)

/-- Schwartz functions inside `H²`. -/
noncomputable def ιS (φ : SchwartzMap Rd ℂ) : Hsp d :=
  Hsp.mk (graphS φ) (Submodule.le_topologicalClosure _ ⟨φ, rfl⟩)

theorem denseRange_ιS : DenseRange (ιS (d := d)) := by
  rw [Metric.denseRange_iff]
  intro x ε hε
  have hx := Hsp.mem x
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe, Metric.mem_closure_iff] at hx
  obtain ⟨b, ⟨φ, rfl⟩, hb⟩ := hx ε hε
  exact ⟨φ, hb⟩

/-- The `L²` component `u` of `(u, Δu, ∇u) ∈ H²`. -/
noncomputable def vl (e : Hsp d) : L2 d := (e : E3 d) none

/-- `A u = Δu + k²u ∈ L²` for `u ∈ H²`. -/
noncomputable def Asp (k : ℝ) (e : Hsp d) : L2 d :=
  (e : E3 d) (some none) + ((k ^ 2 : ℝ) : ℂ) • (e : E3 d) none

theorem continuous_vl : Continuous (vl (d := d)) :=
  (PiLp.continuous_apply 2 _ none).comp Hsp.continuous_val

theorem continuous_Asp (k : ℝ) : Continuous (Asp (d := d) k) :=
  ((PiLp.continuous_apply 2 _ (some none)).comp Hsp.continuous_val).add
    (((PiLp.continuous_apply 2 _ none).comp Hsp.continuous_val).const_smul _)

theorem vl_sub (e f : Hsp d) : vl (e - f) = vl e - vl f := rfl

theorem vl_add (e f : Hsp d) : vl (e + f) = vl e + vl f := rfl

theorem vl_smul (c : ℂ) (e : Hsp d) : vl (c • e) = c • vl e := rfl

theorem Asp_sub (k : ℝ) (e f : Hsp d) : Asp k (e - f) = Asp k e - Asp k f := by
  simp only [Asp]
  change (e : E3 d) (some none) - (f : E3 d) (some none) +
    ((k ^ 2 : ℝ) : ℂ) • ((e : E3 d) none - (f : E3 d) none) = _
  rw [smul_sub]
  abel

theorem Asp_add (k : ℝ) (e f : Hsp d) : Asp k (e + f) = Asp k e + Asp k f := by
  simp only [Asp]
  change (e : E3 d) (some none) + (f : E3 d) (some none) +
    ((k ^ 2 : ℝ) : ℂ) • ((e : E3 d) none + (f : E3 d) none) = _
  rw [smul_add]
  abel

theorem Asp_smul (k : ℝ) (c : ℂ) (e : Hsp d) : Asp k (c • e) = c • Asp k e := by
  simp only [Asp]
  change c • (e : E3 d) (some none) + ((k ^ 2 : ℝ) : ℂ) • (c • (e : E3 d) none) = _
  rw [smul_add, smul_comm]

theorem norm_vl_le (e : Hsp d) : ‖vl e‖ ≤ ‖e‖ := PiLp.norm_apply_le (e : E3 d) none

theorem norm_Asp_le (k : ℝ) (e : Hsp d) : ‖Asp k e‖ ≤ (1 + k ^ 2) * ‖e‖ := by
  have h1 : ‖(e : E3 d) (some none)‖ ≤ ‖e‖ := PiLp.norm_apply_le (e : E3 d) (some none)
  have h2 : ‖(e : E3 d) none‖ ≤ ‖e‖ := PiLp.norm_apply_le (e : E3 d) none
  calc ‖Asp k e‖ ≤ ‖(e : E3 d) (some none)‖ + ‖((k ^ 2 : ℝ) : ℂ) • (e : E3 d) none‖ :=
        norm_add_le _ _
    _ = ‖(e : E3 d) (some none)‖ + k ^ 2 * ‖(e : E3 d) none‖ := by
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    _ ≤ ‖e‖ + k ^ 2 * ‖e‖ := by gcongr
    _ = (1 + k ^ 2) * ‖e‖ := by ring

theorem vl_ιS (φ : SchwartzMap Rd ℂ) : vl (ιS φ) = toL2 φ := rfl

theorem Asp_ιS (k : ℝ) (φ : SchwartzMap Rd ℂ) : Asp k (ιS φ) = toL2 (AS k φ) := by
  simp only [Asp, AS, map_add, map_smul]
  rfl

theorem Usp_ιS (k t : ℝ) (φ : SchwartzMap Rd ℂ) : Usp k t (ιS φ) = ιS (US k t φ) :=
  Hsp.ext (U3_graphS k t φ)

theorem vl_Usp (k t : ℝ) (e : Hsp d) : vl (Usp k t e) = U2 k t (vl e) := rfl

theorem Asp_Usp (k t : ℝ) (e : Hsp d) : Asp k (Usp k t e) = U2 k t (Asp k e) := by
  simp only [Asp, map_add, map_smul]
  rfl

theorem norm_vl_Usp (k t : ℝ) (e : Hsp d) : ‖vl (Usp k t e)‖ = ‖vl e‖ := by
  rw [vl_Usp, norm_U2]

theorem norm_Asp_Usp (k t : ℝ) (e : Hsp d) : ‖Asp k (Usp k t e)‖ = ‖Asp k e‖ := by
  rw [Asp_Usp, norm_U2]

/-- `‖(U(h) − 1)u‖² ≤ 2|h| ‖Au‖²` on `H²`. -/
theorem norm_vl_Usp_sub_sq_le (k h : ℝ) (e : Hsp d) :
    ‖vl (Usp k h e) - vl e‖ ^ 2 ≤ 2 * |h| * ‖Asp k e‖ ^ 2 := by
  refine denseRange_ιS.induction_on e
    (isClosed_le (((continuous_vl.comp (Usp k h).continuous).sub continuous_vl).norm.pow 2)
      (continuous_const.mul ((continuous_Asp k).norm.pow 2))) fun φ => ?_
  rw [Usp_ιS, vl_ιS, vl_ιS, Asp_ιS]
  exact norm_toL2_US_sub_sq_le k h φ

/-- `|⟪f, (U(h) − 1)u⟫| ≤ |h| ‖Af‖ ‖Au‖` on `H²`. -/
theorem norm_inner_vl_Usp_sub_le (k h : ℝ) (f e : Hsp d) :
    ‖inner ℂ (vl f) (vl (Usp k h e) - vl e)‖ ≤ |h| * (‖Asp k f‖ * ‖Asp k e‖) := by
  refine denseRange_ιS.induction_on₂ (p := fun f e => ‖inner ℂ (vl f) (vl (Usp k h e) - vl e)‖ ≤
    |h| * (‖Asp k f‖ * ‖Asp k e‖)) ?_ (fun φ ψ => ?_) f e
  · refine isClosed_le ?_ ?_
    · exact ((continuous_vl.comp continuous_fst).inner
        ((continuous_vl.comp ((Usp k h).continuous.comp continuous_snd)).sub
          (continuous_vl.comp continuous_snd))).norm
    · exact continuous_const.mul (((continuous_Asp k).comp continuous_fst).norm.mul
        ((continuous_Asp k).comp continuous_snd).norm)
  · dsimp only
    rw [Usp_ιS, vl_ιS, vl_ιS, vl_ιS, Asp_ιS, Asp_ιS]
    exact norm_inner_US_sub_le k h φ ψ

/-- The weak difference quotient `Q_h(f, u) = h⁻¹ ⟪f, (U(h) − 1)u⟫`. -/
noncomputable def Qh (k h : ℝ) (f e : Hsp d) : ℂ :=
  (h : ℂ)⁻¹ * inner ℂ (vl f) (vl (Usp k h e) - vl e)

theorem Qh_sub_left (k h : ℝ) (f f' e : Hsp d) : Qh k h (f - f') e = Qh k h f e - Qh k h f' e := by
  simp only [Qh, vl_sub, inner_sub_left, mul_sub]

theorem Qh_sub_right (k h : ℝ) (f e e' : Hsp d) :
    Qh k h f (e - e') = Qh k h f e - Qh k h f e' := by
  simp only [Qh, map_sub, vl_sub]
  rw [← mul_sub, ← inner_sub_right]
  congr 2
  abel

theorem norm_Qh_le (k h : ℝ) (hh : h ≠ 0) (f e : Hsp d) :
    ‖Qh k h f e‖ ≤ ‖Asp k f‖ * ‖Asp k e‖ := by
  rw [Qh, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    inv_mul_le_iff₀ (abs_pos.2 hh)]
  exact norm_inner_vl_Usp_sub_le k h f e

/-- The limit form `L(f, u) = −i ⟪Af, Au⟫`. -/
noncomputable def Lw (k : ℝ) (f e : Hsp d) : ℂ := -Complex.I * inner ℂ (Asp k f) (Asp k e)

theorem norm_Lw_le (k : ℝ) (f e : Hsp d) : ‖Lw k f e‖ ≤ ‖Asp k f‖ * ‖Asp k e‖ := by
  rw [Lw, norm_mul, norm_neg, Complex.norm_I, one_mul]
  exact norm_inner_le_norm _ _

theorem tendsto_Qh_schwartz (k : ℝ) (φ : SchwartzMap Rd ℂ) (e : Hsp d) :
    Tendsto (fun h : ℝ => Qh k h (ιS φ) e) (𝓝[≠] 0) (𝓝 (Lw k (ιS φ) e)) := by
  have hC : 0 ≤ ‖Asp k (ιS φ)‖ * (1 + k ^ 2) := by positivity
  refine tendsto_of_dense_of_bound (X := Hsp d) (Y := ℂ) (T := fun h x => Qh k h (ιS φ) x)
    (L := fun x => Lw k (ιS φ) x) hC (fun h x y => Qh_sub_right k h _ x y)
    (fun x y => by simp only [Lw, Asp_sub, inner_sub_right, mul_sub]) ?_ (fun x => ?_)
    (denseRange_ιS (d := d)) ?_ e
  · filter_upwards [self_mem_nhdsWithin] with h hh x
    refine (norm_Qh_le k h hh _ x).trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (norm_Asp_le k x) (norm_nonneg _)
  · refine (norm_Lw_le k _ x).trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (norm_Asp_le k x) (norm_nonneg _)
  · rintro _ ⟨ψ, rfl⟩
    have := tendsto_inner_US k φ ψ
    simp only [Qh, Lw, Usp_ιS, vl_ιS, Asp_ιS]
    exact this

/-- **Weak derivative of the free group on `H²`:**
`h⁻¹ ⟪f, (U(h) − 1)u⟫ → −i ⟪Af, Au⟫`. -/
theorem tendsto_Qh (k : ℝ) (f e : Hsp d) :
    Tendsto (fun h : ℝ => Qh k h f e) (𝓝[≠] 0) (𝓝 (Lw k f e)) := by
  have hC : 0 ≤ ‖Asp k e‖ * (1 + k ^ 2) := by positivity
  refine tendsto_of_dense_of_bound (X := Hsp d) (Y := ℂ) (T := fun h x => Qh k h x e)
    (L := fun x => Lw k x e) hC (fun h x y => Qh_sub_left k h x y e)
    (fun x y => by simp only [Lw, Asp_sub, inner_sub_left, mul_sub]) ?_ (fun x => ?_)
    (denseRange_ιS (d := d)) ?_ f
  · filter_upwards [self_mem_nhdsWithin] with h hh x
    refine (norm_Qh_le k h hh x e).trans ?_
    calc ‖Asp k x‖ * ‖Asp k e‖ ≤ ((1 + k ^ 2) * ‖x‖) * ‖Asp k e‖ :=
          mul_le_mul_of_nonneg_right (norm_Asp_le k x) (norm_nonneg _)
      _ = ‖Asp k e‖ * (1 + k ^ 2) * ‖x‖ := by ring
  · refine (norm_Lw_le k x e).trans ?_
    calc ‖Asp k x‖ * ‖Asp k e‖ ≤ ((1 + k ^ 2) * ‖x‖) * ‖Asp k e‖ :=
          mul_le_mul_of_nonneg_right (norm_Asp_le k x) (norm_nonneg _)
      _ = ‖Asp k e‖ * (1 + k ^ 2) * ‖x‖ := by ring
  · rintro _ ⟨φ, rfl⟩
    exact tendsto_Qh_schwartz k φ e

theorem oh_arith {N A B Ax ε h : ℝ} (hN : N ≤ A + B) (hN0 : 0 ≤ N)
    (hh : A ^ 2 / |h| < ε / 4) (hb : B ^ 2 ≤ 2 * |h| * Ax ^ 2) (hAx : Ax ^ 2 < ε / 8)
    (habs : 0 < |h|) : N ^ 2 / |h| < ε := by
  rw [div_lt_iff₀ habs]
  rw [div_lt_iff₀ habs] at hh
  have hN2 : N ^ 2 ≤ 2 * A ^ 2 + 2 * B ^ 2 := by nlinarith [sq_nonneg (A - B)]
  nlinarith

/-- `‖(U(h) − 1)u‖² = o(h)` on `H²`. -/
theorem tendsto_norm_vl_Usp_sub_sq_div (k : ℝ) (e : Hsp d) :
    Tendsto (fun h : ℝ => ‖vl (Usp k h e) - vl e‖ ^ 2 / |h|) (𝓝[≠] 0) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hk : 0 < 1 + k ^ 2 := by positivity
  obtain ⟨φ, hφ⟩ := (denseRange_ιS (d := d)).exists_dist_lt e
    (show 0 < Real.sqrt (ε / 8) / (1 + k ^ 2) by
      have : 0 < Real.sqrt (ε / 8) := Real.sqrt_pos.2 (by positivity)
      positivity)
  obtain ⟨x, hx⟩ : ∃ x : Hsp d, x = e - ιS φ := ⟨_, rfl⟩
  have hAx : ‖Asp k x‖ ^ 2 < ε / 8 := by
    have h1 : ‖Asp k x‖ < Real.sqrt (ε / 8) := by
      calc ‖Asp k x‖ ≤ (1 + k ^ 2) * ‖x‖ := norm_Asp_le k x
        _ < (1 + k ^ 2) * (Real.sqrt (ε / 8) / (1 + k ^ 2)) := by
            rw [hx, ← dist_eq_norm]
            gcongr
        _ = Real.sqrt (ε / 8) := by field_simp
    have := pow_lt_pow_left₀ h1 (norm_nonneg _) two_ne_zero
    rwa [Real.sq_sqrt (by positivity)] at this
  have hS := Metric.tendsto_nhds.1 (tendsto_norm_US_sub_sq_div k φ) (ε / 4) (by positivity)
  filter_upwards [hS, self_mem_nhdsWithin] with h hh hne
  have hne' : (h : ℝ) ≠ 0 := hne
  have habs : 0 < |h| := abs_pos.2 hne'
  rw [dist_zero_right, Real.norm_of_nonneg (div_nonneg (sq_nonneg _) (abs_nonneg _))] at hh
  rw [dist_zero_right, Real.norm_of_nonneg (div_nonneg (sq_nonneg _) (abs_nonneg _))]
  have hsplit : vl (Usp k h e) - vl e = (toL2 (US k h φ) - toL2 φ) + (vl (Usp k h x) - vl x) := by
    have : e = ιS φ + x := by rw [hx]; abel
    rw [this, map_add, vl_add, vl_add, Usp_ιS, vl_ιS, vl_ιS]
    abel
  have key : ‖vl (Usp k h e) - vl e‖ ≤
      ‖toL2 (US k h φ) - toL2 φ‖ + ‖vl (Usp k h x) - vl x‖ :=
    (congrArg (fun v : L2 d => ‖v‖) hsplit).le.trans (norm_add_le _ _)
  exact oh_arith key (norm_nonneg _) hh
    (norm_vl_Usp_sub_sq_le k h x) hAx habs

end Sobolev

end ReyesMath
