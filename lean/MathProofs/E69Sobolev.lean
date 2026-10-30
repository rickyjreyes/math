import Mathlib
import MathProofs.FourierShellL2
import MathProofs.RegularizedCurvatureL2

/-!
# E69: Fourier-defined Sobolev spaces `H^s(ℝⁿ; ℂ)` of real order

For every dimension `n` and every real `s`, `u ∈ L²(ℝⁿ; ℂ)` lies in `H^s(ℝⁿ; ℂ)` when
`‖u‖²_{H^s} = ∫ (1 + |ξ|²)^s |û(ξ)|² dξ < ∞`, where `û = Sobolev.FU u` is the unitary Fourier
transform `û(ξ) = (2π)^{-n/2} ∫ u(x) e^{-ix·ξ} dx` (the Plancherel extension, `Sobolev.FU_ae_eq`).
For `s ≥ 0` this is the Bessel-potential space `H^s(ℝⁿ)`.

* `MemHs`, `hsNorm`, `Hs`: the space, its norm, the subspace of `L²`. The norm is a norm
  (`hsNorm_add_le`, `hsNorm_smul`, `hsNorm_eq_zero_iff`), equals the `L²` norm at `s = 0`
  (`hsNorm_zero`), is monotone in `s` (`hsNorm_mono`), and Schwartz functions lie in every `H^s`
  (`memHs_toL2`).
* `lap`: the Laplacian `Δu = 𝓕⁻¹(−|ξ|² û)` on `H²`. It is the classical Laplacian on Schwartz
  functions (`lap_toL2`, `lap_toL2_ae`) and the weak Laplacian of `u` (`inner_toL2_lap`,
  `isWeakLaplacian_lap`), uniquely (`eq_lap_of_weak`).
* `hsNorm_lap_le`: `‖Δu‖_{H^{s-2}} ≤ ‖u‖_{H^s}`.
* `ae_eq_fourierUinv`: Fourier inversion, `u(x) = (2π)^{-n/2} ∫ û(ξ) e^{ix·ξ} dξ` a.e. when
  `û ∈ L¹`.
* `embedding`: `H^r(ℝⁿ) ↪ L^∞(ℝⁿ)` for `r > n/2`, with `‖u‖_∞ ≤ Cemb n r · ‖u‖_{H^r}`,
  `Cemb n r = (2π)^{-n/2} (∫ (1 + |ξ|²)^{-r} dξ)^{1/2}`, and a bounded continuous representative.
-/

open Filter Topology Complex InnerProductSpace MeasureTheory Set
open scoped ContDiff FourierTransform ENNReal

namespace ReyesMath

namespace E69

open Sobolev

variable {n : ℕ}

local notation "Rn" => EuclideanSpace ℝ (Fin n)

/-! ### The weight `(1 + |ξ|²)^s` -/

/-- The Sobolev weight `(1 + |ξ|²)^s`. -/
noncomputable def jw (s : ℝ) (ξ : Rn) : ℝ := (1 + ‖ξ‖ ^ 2) ^ s

theorem one_le_one_add_sq (ξ : Rn) : 1 ≤ 1 + ‖ξ‖ ^ 2 := by nlinarith [sq_nonneg ‖ξ‖]

theorem one_add_sq_pos (ξ : Rn) : 0 < 1 + ‖ξ‖ ^ 2 := by positivity

theorem jw_pos (s : ℝ) (ξ : Rn) : 0 < jw s ξ := Real.rpow_pos_of_pos (one_add_sq_pos ξ) s

theorem jw_nonneg (s : ℝ) (ξ : Rn) : 0 ≤ jw s ξ := (jw_pos s ξ).le

theorem jw_add (s t : ℝ) (ξ : Rn) : jw (s + t) ξ = jw s ξ * jw t ξ :=
  Real.rpow_add (one_add_sq_pos ξ) s t

theorem jw_zero (ξ : Rn) : jw 0 ξ = 1 := Real.rpow_zero _

theorem jw_two (ξ : Rn) : jw 2 ξ = (1 + ‖ξ‖ ^ 2) ^ 2 := Real.rpow_two _

theorem jw_mono {s t : ℝ} (h : s ≤ t) (ξ : Rn) : jw s ξ ≤ jw t ξ :=
  Real.rpow_le_rpow_of_exponent_le (one_le_one_add_sq ξ) h

theorem jw_half_sq (s : ℝ) (ξ : Rn) : jw (s / 2) ξ ^ 2 = jw s ξ := by
  rw [jw, jw, ← Real.rpow_natCast, ← Real.rpow_mul (one_add_sq_pos ξ).le]
  norm_num

theorem jw_neg_half_mul (r : ℝ) (ξ : Rn) : jw (-r / 2) ξ * jw (r / 2) ξ = 1 := by
  rw [← jw_add, show -r / 2 + r / 2 = 0 by ring, jw_zero]

theorem continuous_jw (s : ℝ) : Continuous (jw (n := n) s) :=
  (continuous_const.add (continuous_norm.pow 2)).rpow_const fun ξ =>
    Or.inl (one_add_sq_pos ξ).ne'

/-- `∫ (1 + |ξ|²)^{-r} dξ < ∞` for `r > n/2`. -/
theorem integrable_jw_neg {r : ℝ} (hr : (n : ℝ) / 2 < r) : Integrable (jw (n := n) (-r)) := by
  have h := integrable_rpow_neg_one_add_norm_sq (E := Rn) (μ := volume) (r := 2 * r)
    (by rw [finrank_euclideanSpace_fin]; linarith)
  refine h.congr (Eventually.of_forall fun ξ => ?_)
  simp only [jw]
  congr 1
  ring

/-! ### `L²` norms as integrals -/

theorem integral_norm_sq (f : L2 n) : ∫ x, ‖(f : Rn → ℂ) x‖ ^ 2 = ‖f‖ ^ 2 := by
  rw [@norm_sq_eq_re_inner ℂ, L2.inner_def]
  have hB : (fun x => inner ℂ ((f : Rn → ℂ) x) ((f : Rn → ℂ) x)) =
      fun x => (((‖(f : Rn → ℂ) x‖ ^ 2 : ℝ)) : ℂ) := by
    funext x
    rw [inner_self_complex]
  rw [hB, integral_complex_ofReal]
  simp

theorem integrable_norm_sq (f : L2 n) : Integrable fun x => ‖(f : Rn → ℂ) x‖ ^ 2 :=
  (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).1 (Lp.memLp f)

theorem inner_toL2_eq_integral (χ : SchwartzMap Rn ℂ) (w : L2 n) :
    inner ℂ (toL2 χ) w = ∫ x, (starRingEnd ℂ) (χ x) * (w : Rn → ℂ) x := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_toL2 χ] with x hx
  rw [hx, RCLike.inner_apply, mul_comm]

/-! ### The space `H^s(ℝⁿ; ℂ)` -/

/-- **`u ∈ H^s(ℝⁿ; ℂ)`**: `(1 + |ξ|²)^s |û(ξ)|²` is integrable, `û = FU u`. -/
def MemHs (s : ℝ) (u : L2 n) : Prop :=
  Integrable fun ξ => jw s ξ * ‖(FU u : Rn → ℂ) ξ‖ ^ 2

/-- `‖u‖_{H^s} = (∫ (1 + |ξ|²)^s |û(ξ)|² dξ)^{1/2}`. -/
noncomputable def hsNorm (s : ℝ) (u : L2 n) : ℝ :=
  Real.sqrt (∫ ξ, jw s ξ * ‖(FU u : Rn → ℂ) ξ‖ ^ 2)

theorem hsNorm_nonneg (s : ℝ) (u : L2 n) : 0 ≤ hsNorm s u := Real.sqrt_nonneg _

theorem integral_hs_nonneg (s : ℝ) (u : L2 n) :
    0 ≤ ∫ ξ, jw s ξ * ‖(FU u : Rn → ℂ) ξ‖ ^ 2 :=
  integral_nonneg fun ξ => mul_nonneg (jw_nonneg s ξ) (sq_nonneg _)

theorem hsNorm_sq (s : ℝ) (u : L2 n) :
    hsNorm s u ^ 2 = ∫ ξ, jw s ξ * ‖(FU u : Rn → ℂ) ξ‖ ^ 2 :=
  Real.sq_sqrt (integral_hs_nonneg s u)

theorem aestronglyMeasurable_hs (s : ℝ) (u : L2 n) :
    AEStronglyMeasurable (fun ξ => jw s ξ * ‖(FU u : Rn → ℂ) ξ‖ ^ 2) volume :=
  (continuous_jw s).aestronglyMeasurable.mul ((Lp.aestronglyMeasurable (FU u)).norm.pow 2)

/-- `H⁰ = L²`. -/
theorem memHs_zero (u : L2 n) : MemHs 0 u := by
  unfold MemHs
  simp_rw [jw_zero, one_mul]
  exact integrable_norm_sq (FU u)

/-- **Plancherel:** `‖u‖_{H⁰} = ‖u‖_{L²}`. -/
theorem hsNorm_zero (u : L2 n) : hsNorm 0 u = ‖u‖ := by
  rw [hsNorm]
  simp_rw [jw_zero, one_mul]
  rw [integral_norm_sq, norm_FU, Real.sqrt_sq (norm_nonneg _)]

theorem MemHs.mono {s t : ℝ} {u : L2 n} (hu : MemHs s u) (h : t ≤ s) : MemHs t u := by
  refine hu.mono' (aestronglyMeasurable_hs t u) (Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_of_nonneg (mul_nonneg (jw_nonneg _ _) (sq_nonneg _))]
  exact mul_le_mul_of_nonneg_right (jw_mono h ξ) (sq_nonneg _)

theorem hsNorm_mono {s t : ℝ} {u : L2 n} (hu : MemHs s u) (h : t ≤ s) :
    hsNorm t u ≤ hsNorm s u :=
  Real.sqrt_le_sqrt (integral_mono (hu.mono h) hu fun ξ =>
    mul_le_mul_of_nonneg_right (jw_mono h ξ) (sq_nonneg _))

/-- `‖u‖_{L²} ≤ ‖u‖_{H^s}` for `s ≥ 0`. -/
theorem norm_le_hsNorm {s : ℝ} {u : L2 n} (hu : MemHs s u) (hs : 0 ≤ s) : ‖u‖ ≤ hsNorm s u := by
  rw [← hsNorm_zero]
  exact hsNorm_mono hu hs

/-! ### The norm axioms -/

/-- The weighted transform `(1 + |ξ|²)^{s/2} û(ξ)`. -/
noncomputable def wFU (s : ℝ) (u : L2 n) (ξ : Rn) : ℂ := (jw (s / 2) ξ : ℂ) * (FU u : Rn → ℂ) ξ

theorem norm_wFU_sq (s : ℝ) (u : L2 n) (ξ : Rn) :
    ‖wFU s u ξ‖ ^ 2 = jw s ξ * ‖(FU u : Rn → ℂ) ξ‖ ^ 2 := by
  rw [wFU, norm_mul, Complex.norm_real, Real.norm_of_nonneg (jw_nonneg _ _), mul_pow, jw_half_sq]

theorem aestronglyMeasurable_wFU (s : ℝ) (u : L2 n) : AEStronglyMeasurable (wFU s u) volume :=
  (Complex.continuous_ofReal.comp (continuous_jw (s / 2))).aestronglyMeasurable.mul
    (Lp.aestronglyMeasurable (FU u))

theorem memHs_iff_memLp (s : ℝ) (u : L2 n) : MemHs s u ↔ MemLp (wFU s u) 2 := by
  rw [memLp_two_iff_integrable_sq_norm (aestronglyMeasurable_wFU s u), MemHs]
  simp_rw [norm_wFU_sq]

theorem wFU_add (s : ℝ) (u v : L2 n) : wFU s (u + v) =ᵐ[volume] wFU s u + wFU s v := by
  filter_upwards [Lp.coeFn_add (FU u) (FU v)] with ξ hξ
  simp only [wFU, map_add, Pi.add_apply, hξ, mul_add]

theorem wFU_smul (s : ℝ) (c : ℂ) (u : L2 n) : wFU s (c • u) =ᵐ[volume] c • wFU s u := by
  filter_upwards [Lp.coeFn_smul c (FU u)] with ξ hξ
  simp only [wFU, map_smul, Pi.smul_apply, hξ, smul_eq_mul]
  ring

theorem wFU_zero (s : ℝ) : wFU s (0 : L2 n) =ᵐ[volume] 0 := by
  filter_upwards [Lp.coeFn_zero ℂ 2 (volume : Measure Rn)] with ξ hξ
  simp only [wFU, map_zero, hξ, Pi.zero_apply, mul_zero]

/-- `‖u‖_{H^s}` is the `L²` norm of `(1 + |ξ|²)^{s/2} û`. -/
theorem hsNorm_eq_norm_toLp {s : ℝ} {u : L2 n} (hu : MemHs s u) :
    hsNorm s u = ‖((memHs_iff_memLp s u).1 hu).toLp (wFU s u)‖ := by
  have h := integral_norm_sq (((memHs_iff_memLp s u).1 hu).toLp (wFU s u))
  have h2 : ∫ x, ‖((((memHs_iff_memLp s u).1 hu).toLp (wFU s u) : L2 n) : Rn → ℂ) x‖ ^ 2 =
      ∫ ξ, jw s ξ * ‖(FU u : Rn → ℂ) ξ‖ ^ 2 := by
    have h3 : ∫ x, ‖wFU s u x‖ ^ 2 = ∫ ξ, jw s ξ * ‖(FU u : Rn → ℂ) ξ‖ ^ 2 := by
      simp_rw [norm_wFU_sq]
    refine (integral_congr_ae ?_).trans h3
    filter_upwards [((memHs_iff_memLp s u).1 hu).coeFn_toLp] with x hx
    rw [hx]
  rw [hsNorm, ← h2, h, Real.sqrt_sq (norm_nonneg _)]

theorem MemHs.add {s : ℝ} {u v : L2 n} (hu : MemHs s u) (hv : MemHs s v) : MemHs s (u + v) := by
  rw [memHs_iff_memLp] at *
  exact (hu.add hv).ae_eq (wFU_add s u v).symm

theorem MemHs.smul {s : ℝ} (c : ℂ) {u : L2 n} (hu : MemHs s u) : MemHs s (c • u) := by
  rw [memHs_iff_memLp] at *
  exact (hu.const_smul c).ae_eq (wFU_smul s c u).symm

theorem memHs_zero_fun (s : ℝ) : MemHs s (0 : L2 n) := by
  rw [memHs_iff_memLp]
  exact (MemLp.zero : MemLp (0 : Rn → ℂ) 2 volume).ae_eq (wFU_zero s).symm

/-- **The Sobolev space `H^s(ℝⁿ; ℂ)`**, a subspace of `L²(ℝⁿ; ℂ)`. -/
noncomputable def Hs (n : ℕ) (s : ℝ) : Submodule ℂ (L2 n) where
  carrier := {u | MemHs s u}
  add_mem' := MemHs.add
  zero_mem' := memHs_zero_fun s
  smul_mem' c _ hu := MemHs.smul c hu

theorem mem_Hs {s : ℝ} {u : L2 n} : u ∈ Hs n s ↔ MemHs s u := Iff.rfl

/-- The triangle inequality. -/
theorem hsNorm_add_le {s : ℝ} {u v : L2 n} (hu : MemHs s u) (hv : MemHs s v) :
    hsNorm s (u + v) ≤ hsNorm s u + hsNorm s v := by
  rw [hsNorm_eq_norm_toLp hu, hsNorm_eq_norm_toLp hv, hsNorm_eq_norm_toLp (hu.add hv)]
  have e : ((memHs_iff_memLp s (u + v)).1 (hu.add hv)).toLp (wFU s (u + v)) =
      ((memHs_iff_memLp s u).1 hu).toLp (wFU s u) + ((memHs_iff_memLp s v).1 hv).toLp (wFU s v) := by
    apply Lp.ext
    filter_upwards [((memHs_iff_memLp s (u + v)).1 (hu.add hv)).coeFn_toLp,
      Lp.coeFn_add (((memHs_iff_memLp s u).1 hu).toLp (wFU s u))
        (((memHs_iff_memLp s v).1 hv).toLp (wFU s v)),
      ((memHs_iff_memLp s u).1 hu).coeFn_toLp, ((memHs_iff_memLp s v).1 hv).coeFn_toLp,
      wFU_add s u v] with ξ h1 h2 h3 h4 h5
    rw [h1, h2, Pi.add_apply, h3, h4, h5, Pi.add_apply]
  rw [e]
  exact norm_add_le _ _

/-- Homogeneity. -/
theorem hsNorm_smul (s : ℝ) (c : ℂ) (u : L2 n) : hsNorm s (c • u) = ‖c‖ * hsNorm s u := by
  have h : ∫ ξ, jw s ξ * ‖(FU (c • u) : Rn → ℂ) ξ‖ ^ 2 =
      ‖c‖ ^ 2 * ∫ ξ, jw s ξ * ‖(FU u : Rn → ℂ) ξ‖ ^ 2 := by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_smul c (FU u)] with ξ hξ
    rw [map_smul, hξ, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]
    ring
  rw [hsNorm, hsNorm, h, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

/-- Definiteness. -/
theorem hsNorm_eq_zero_iff {s : ℝ} {u : L2 n} (hu : MemHs s u) : hsNorm s u = 0 ↔ u = 0 := by
  constructor
  · intro h
    have h0 : ∫ ξ, jw s ξ * ‖(FU u : Rn → ℂ) ξ‖ ^ 2 = 0 := by
      rw [← hsNorm_sq, h]
      ring
    rw [integral_eq_zero_iff_of_nonneg (fun ξ => mul_nonneg (jw_nonneg s ξ) (sq_nonneg _)) hu]
      at h0
    have hF : FU u = 0 := by
      rw [Lp.eq_zero_iff_ae_eq_zero]
      filter_upwards [h0] with ξ hξ
      have := (mul_eq_zero.1 hξ).resolve_left (jw_pos s ξ).ne'
      simpa using this
    simpa using hF
  · rintro rfl
    have h0 : ∫ ξ, jw s ξ * ‖(FU (0 : L2 n) : Rn → ℂ) ξ‖ ^ 2 = 0 := by
      refine (integral_congr_ae ?_).trans (integral_zero _ _)
      filter_upwards [Lp.coeFn_zero ℂ 2 (volume : Measure Rn)] with ξ hξ
      rw [map_zero, hξ]
      simp
    rw [hsNorm, h0, Real.sqrt_zero]

/-! ### Schwartz functions lie in every `H^s` -/

/-- The unitary Fourier transform of a Schwartz function, `ξ ↦ (2π)^{-n/2} 𝓕φ(ξ/2π)`. -/
noncomputable def FUS (φ : SchwartzMap Rn ℂ) : SchwartzMap Rn ℂ :=
  dilS (inv_pos.2 two_pi_pos') (fS φ)

theorem FU_toL2 (φ : SchwartzMap Rn ℂ) : FU (toL2 φ) = toL2 (FUS φ) := by
  rw [FU_apply, fourierL2_toL2, FUS, toL2_dilS]

theorem FUS_apply (φ : SchwartzMap Rn ℂ) (ξ : Rn) :
    FUS φ ξ = (((2 * Real.pi)⁻¹ ^ ((n : ℝ) / 2) : ℝ) : ℂ) * 𝓕 (⇑φ) ((2 * Real.pi)⁻¹ • ξ) := by
  rw [FUS, dilS_apply, dilF, coe_fS]

/-- `(Δφ)^(ξ) = −|ξ|² φ̂(ξ)` for the unitary transform. -/
theorem FUS_lapS (φ : SchwartzMap Rn ℂ) (ξ : Rn) :
    FUS (lapS φ) ξ = -((‖ξ‖ ^ 2 : ℝ) : ℂ) * FUS φ ξ := by
  rw [FUS_apply, FUS_apply, fourier_lapS]
  have h : qS ((2 * Real.pi)⁻¹ • ξ) = ‖ξ‖ ^ 2 := by
    rw [qS, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 two_pi_pos'),
      mul_pow ((2 * Real.pi)⁻¹) ‖ξ‖ 2, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ two_pi_pos'.ne',
      one_pow, one_mul]
  rw [h]
  ring

theorem integrable_jw_mul_schwartz (s : ℝ) (χ : SchwartzMap Rn ℂ) :
    Integrable fun ξ => jw s ξ * ‖χ ξ‖ ^ 2 := by
  set m : ℕ := ⌈s⌉₊
  set B := SchwartzMap.seminorm ℂ 0 0 χ
  have hB : ∀ ξ, ‖χ ξ‖ ≤ B := fun ξ => SchwartzMap.norm_le_seminorm ℂ χ ξ
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have h1 : Integrable fun ξ => (2 : ℝ) ^ m * B * (‖χ ξ‖ + ‖ξ‖ ^ (2 * m) * ‖χ ξ‖) :=
    ((χ.integrable (μ := volume)).norm.add (χ.integrable_pow_mul volume (2 * m))).const_mul _
  refine h1.mono' ((continuous_jw s).mul (χ.continuous.norm.pow 2)).aestronglyMeasurable
    (Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_of_nonneg (mul_nonneg (jw_nonneg _ _) (sq_nonneg _))]
  have hjw : jw s ξ ≤ (1 + ‖ξ‖ ^ 2) ^ m :=
    calc jw s ξ ≤ jw (m : ℝ) ξ := jw_mono (Nat.le_ceil s) ξ
      _ = (1 + ‖ξ‖ ^ 2) ^ m := Real.rpow_natCast _ _
  have h2m : (0 : ℝ) < 2 ^ m := by positivity
  have hpm : 0 ≤ ‖ξ‖ ^ (2 * m) := by positivity
  have hpow : (1 + ‖ξ‖ ^ 2) ^ m ≤ 2 ^ m * (1 + ‖ξ‖ ^ (2 * m)) := by
    rcases le_total 1 (‖ξ‖ ^ 2) with h | h
    · calc (1 + ‖ξ‖ ^ 2) ^ m ≤ (2 * ‖ξ‖ ^ 2) ^ m :=
            pow_le_pow_left₀ (by positivity) (by linarith) m
        _ = 2 ^ m * ‖ξ‖ ^ (2 * m) := by rw [mul_pow, pow_mul]
        _ ≤ 2 ^ m * (1 + ‖ξ‖ ^ (2 * m)) := by nlinarith
    · calc (1 + ‖ξ‖ ^ 2) ^ m ≤ (2 : ℝ) ^ m := pow_le_pow_left₀ (by positivity) (by linarith) m
        _ ≤ 2 ^ m * (1 + ‖ξ‖ ^ (2 * m)) := by nlinarith
  have hsq : ‖χ ξ‖ ^ 2 ≤ B * ‖χ ξ‖ := by
    rw [sq]
    exact mul_le_mul_of_nonneg_right (hB ξ) (norm_nonneg _)
  calc jw s ξ * ‖χ ξ‖ ^ 2 ≤ (2 ^ m * (1 + ‖ξ‖ ^ (2 * m))) * (B * ‖χ ξ‖) :=
        mul_le_mul (hjw.trans hpow) hsq (sq_nonneg _) (by positivity)
    _ = 2 ^ m * B * (‖χ ξ‖ + ‖ξ‖ ^ (2 * m) * ‖χ ξ‖) := by ring

/-- `𝓢(ℝⁿ) ⊂ H^s(ℝⁿ)` for every real `s`. -/
theorem memHs_toL2 (s : ℝ) (φ : SchwartzMap Rn ℂ) : MemHs s (toL2 φ) := by
  unfold MemHs
  rw [FU_toL2]
  refine (integrable_jw_mul_schwartz s (FUS φ)).congr ?_
  filter_upwards [coeFn_toL2 (FUS φ)] with ξ hξ
  rw [hξ]

/-! ### The Laplacian `Δu = 𝓕⁻¹(−|ξ|² û)` -/

theorem memLp_lapSym {u : L2 n} (hu : MemHs 2 u) :
    MemLp (fun ξ => -((‖ξ‖ ^ 2 : ℝ) : ℂ) * (FU u : Rn → ℂ) ξ) 2 volume := by
  have hm : AEStronglyMeasurable (fun ξ => -((‖ξ‖ ^ 2 : ℝ) : ℂ) * (FU u : Rn → ℂ) ξ) volume :=
    ((Complex.continuous_ofReal.comp (continuous_norm.pow 2)).neg.aestronglyMeasurable).mul
      (Lp.aestronglyMeasurable (FU u))
  rw [memLp_two_iff_integrable_sq_norm hm]
  refine hu.mono' (hm.norm.pow 2) (Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _), norm_mul, norm_neg, Complex.norm_real,
    Real.norm_of_nonneg (sq_nonneg _), mul_pow, jw_two]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (sq_nonneg _) (by linarith) 2) (sq_nonneg _)

open Classical in
/-- **The Laplacian on `H²(ℝⁿ)`**: `Δu = 𝓕⁻¹(−|ξ|² û)`, extended by `0` outside `H²`. -/
noncomputable def lap (u : L2 n) : L2 n :=
  if hu : MemHs 2 u then FU.symm ((memLp_lapSym hu).toLp _) else 0

/-- `(Δu)^(ξ) = −|ξ|² û(ξ)` a.e. -/
theorem FU_lap {u : L2 n} (hu : MemHs 2 u) :
    (FU (lap u) : Rn → ℂ) =ᵐ[volume] fun ξ => -((‖ξ‖ ^ 2 : ℝ) : ℂ) * (FU u : Rn → ℂ) ξ := by
  rw [lap, dif_pos hu, LinearIsometryEquiv.apply_symm_apply]
  exact (memLp_lapSym hu).coeFn_toLp

theorem lap_weight_le (s : ℝ) (ξ : Rn) (z : ℂ) :
    jw (s - 2) ξ * ‖-((‖ξ‖ ^ 2 : ℝ) : ℂ) * z‖ ^ 2 ≤ jw s ξ * ‖z‖ ^ 2 := by
  rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _), mul_pow]
  have h1 : (‖ξ‖ ^ 2) ^ 2 ≤ jw 2 ξ := by
    rw [jw_two]
    exact pow_le_pow_left₀ (sq_nonneg _) (by linarith) 2
  have h2 : jw s ξ = jw (s - 2) ξ * jw 2 ξ := by rw [← jw_add, sub_add_cancel]
  rw [h2, mul_assoc]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 (sq_nonneg _)) (jw_nonneg _ _)

/-- `Δ : H^s → H^{s-2}` for `s ≥ 2`. -/
theorem memHs_lap {s : ℝ} {u : L2 n} (hu : MemHs s u) (hs : 2 ≤ s) : MemHs (s - 2) (lap u) := by
  refine hu.mono' (aestronglyMeasurable_hs _ _) ?_
  filter_upwards [FU_lap (hu.mono hs)] with ξ hξ
  rw [hξ, Real.norm_of_nonneg (mul_nonneg (jw_nonneg _ _) (sq_nonneg _))]
  exact lap_weight_le s ξ _

/-- **`‖Δu‖_{H^{s-2}} ≤ ‖u‖_{H^s}`** for `s ≥ 2`. -/
theorem hsNorm_lap_le {s : ℝ} {u : L2 n} (hu : MemHs s u) (hs : 2 ≤ s) :
    hsNorm (s - 2) (lap u) ≤ hsNorm s u := by
  refine Real.sqrt_le_sqrt (integral_mono_ae (memHs_lap hu hs) hu ?_)
  filter_upwards [FU_lap (hu.mono hs)] with ξ hξ
  rw [hξ]
  exact lap_weight_le s ξ _

/-- On Schwartz functions, `lap` is the classical Laplacian. -/
theorem lap_toL2 (φ : SchwartzMap Rn ℂ) : lap (toL2 φ) = toL2 (lapS φ) := by
  apply FU.injective
  apply Lp.ext
  have h3 : (FU (toL2 φ) : Rn → ℂ) =ᵐ[volume] FUS φ := by
    rw [FU_toL2]
    exact coeFn_toL2 (FUS φ)
  rw [FU_toL2 (lapS φ)]
  filter_upwards [FU_lap (memHs_toL2 2 φ), coeFn_toL2 (FUS (lapS φ)), h3] with ξ h1 h2 h3
  rw [h1, h2, h3, FUS_lapS]

/-- `lap (toL2 φ) = Δφ` a.e., with Mathlib's Laplacian `Δ`. -/
theorem lap_toL2_ae (φ : SchwartzMap Rn ℂ) :
    (lap (toL2 φ) : Rn → ℂ) =ᵐ[volume] fun x => Δ (⇑φ) x := by
  rw [lap_toL2]
  filter_upwards [coeFn_toL2 (lapS φ)] with x hx
  rw [hx, lapS_apply]

/-- **`lap u` is the weak Laplacian of `u`**: `⟨χ, Δu⟩ = ⟨Δχ, u⟩` for every Schwartz `χ`. -/
theorem inner_toL2_lap {u : L2 n} (hu : MemHs 2 u) (χ : SchwartzMap Rn ℂ) :
    inner ℂ (toL2 χ) (lap u) = inner ℂ (toL2 (lapS χ)) u := by
  rw [← FU.inner_map_map (toL2 χ), ← FU.inner_map_map (toL2 (lapS χ)), FU_toL2, FU_toL2,
    L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [FU_lap hu, coeFn_toL2 (FUS χ), coeFn_toL2 (FUS (lapS χ))] with ξ h1 h2 h3
  rw [h1, h2, h3, FUS_lapS, RCLike.inner_apply, RCLike.inner_apply, map_mul, map_neg,
    Complex.conj_ofReal]
  ring

/-- The weak Laplacian in `L²` is unique: it is `lap u`. -/
theorem eq_lap_of_weak {u v : L2 n} (hu : MemHs 2 u)
    (h : ∀ χ : SchwartzMap Rn ℂ, inner ℂ (toL2 χ) v = inner ℂ (toL2 (lapS χ)) u) : v = lap u := by
  have : v - lap u = 0 := eq_zero_of_inner_schwartz fun χ => by
    rw [inner_sub_right, h χ, inner_toL2_lap hu χ, sub_self]
  exact sub_eq_zero.1 this

/-- **Compatibility with `E26.IsWeakLaplacian`** (real test functions): for `u ∈ H²(ℝⁿ)`,
`∫ (Δφ) u = ∫ φ (lap u)` for every `φ ∈ C_c^∞(ℝⁿ; ℝ)`. -/
theorem isWeakLaplacian_lap {u : L2 n} (hu : MemHs 2 u) :
    E26.IsWeakLaplacian univ (u : Rn → ℂ) (lap u : Rn → ℂ) := by
  refine ⟨((Lp.memLp (lap u)).locallyIntegrable (by norm_num)).locallyIntegrableOn _,
    fun φ hφ => ?_⟩
  simp only [Measure.restrict_univ]
  obtain ⟨χ, hχ⟩ : ∃ χ : SchwartzMap Rn ℂ, ⇑χ = fun x => ((φ x : ℝ) : ℂ) :=
    ⟨schwartzOfCompact (fun x => ((φ x : ℝ) : ℂ)) (Complex.ofRealCLM.contDiff.comp hφ.1)
      (hφ.2.1.comp_left Complex.ofReal_zero), by
        ext x
        rfl⟩
  have hlap : ∀ x, lapS χ x = ((Δ φ x : ℝ) : ℂ) := fun x => by
    have h2 : ContDiffAt ℝ 2 φ x :=
      hφ.1.contDiffAt.of_le (WithTop.coe_le_coe.2 le_top)
    have e : (fun x => ((φ x : ℝ) : ℂ)) = (⇑Complex.ofRealCLM) ∘ φ := by
      funext y
      simp
    rw [lapS_apply, hχ, e, h2.laplacian_CLM_comp_left]
    simp
  have h1 := inner_toL2_lap hu χ
  rw [inner_toL2_eq_integral, inner_toL2_eq_integral] at h1
  have l1 : ∫ x, (starRingEnd ℂ) (χ x) * (lap u : Rn → ℂ) x = ∫ x, φ x • (lap u : Rn → ℂ) x := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hχ, Complex.conj_ofReal, Complex.real_smul]
  have l2 : ∫ x, (starRingEnd ℂ) (lapS χ x) * (u : Rn → ℂ) x = ∫ x, Δ φ x • (u : Rn → ℂ) x := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hlap, Complex.conj_ofReal, Complex.real_smul]
  rw [l1, l2] at h1
  exact h1.symm

/-! ### Fourier inversion -/

/-- The reflection `f ↦ f(−·)`, a unitary operator on `L²(ℝⁿ)`. -/
noncomputable def refl : L2 n →ₗᵢ[ℂ] L2 n :=
  Lp.compMeasurePreservingₗᵢ ℂ (Neg.neg : Rn → Rn) (Measure.measurePreserving_neg volume)

theorem coeFn_refl (f : L2 n) : (refl f : Rn → ℂ) =ᵐ[volume] fun x => (f : Rn → ℂ) (-x) :=
  Lp.coeFn_compMeasurePreserving f (Measure.measurePreserving_neg volume)

theorem neg_ae_eq {f g : Rn → ℂ} (h : f =ᵐ[volume] g) :
    (fun x => f (-x)) =ᵐ[volume] fun x => g (-x) :=
  (Measure.measurePreserving_neg (volume : Measure Rn)).quasiMeasurePreserving.ae_eq h

/-- `𝓕⁻¹ = R ∘ 𝓕` on `L²`. -/
theorem fourierL2_symm_eq (f : L2 n) : fourierL2.symm f = refl (fourierL2 f) := by
  refine denseRange_toL2.induction_on f
    (isClosed_eq fourierL2.symm.continuous (refl.continuous.comp fourierL2.continuous))
    fun φ => ?_
  rw [fourierL2_symm_toL2, fourierL2_toL2]
  apply Lp.ext
  filter_upwards [coeFn_toL2 (fSi φ), coeFn_refl (toL2 (fS φ)),
    neg_ae_eq (coeFn_toL2 (fS φ))] with x h1 h2 h3
  rw [h1, h2, h3, fSi_eq_fS_neg]

theorem fourier_congr_ae {f g : Rn → ℂ} (h : f =ᵐ[volume] g) : 𝓕 f = 𝓕 g := by
  funext ξ
  rw [Real.fourierIntegral_eq', Real.fourierIntegral_eq']
  exact integral_congr_ae (h.mono fun x hx => by simp only [hx])

/-- The scaling law `𝓕(g(λ·))(ξ) = λ^{-n} 𝓕g(ξ/λ)`, with the factor `λ^{n/2}` of `dilF`. -/
theorem fourier_dilF {lam : ℝ} (hlam : 0 < lam) (g : Rn → ℂ) (ξ : Rn) :
    𝓕 (dilF lam g) ξ =
      (((lam ^ ((n : ℝ) / 2)) * (lam ^ n)⁻¹ : ℝ) : ℂ) * 𝓕 g (lam⁻¹ • ξ) := by
  rw [Real.fourierIntegral_eq', Real.fourierIntegral_eq']
  have hin : ∀ v : Rn, inner ℝ (lam • v) (lam⁻¹ • ξ) = inner ℝ v ξ := fun v => by
    rw [real_inner_smul_left, real_inner_smul_right, ← mul_assoc, mul_inv_cancel₀ hlam.ne',
      one_mul]
  set F : Rn → ℂ := fun y => Complex.exp (↑(-2 * Real.pi * inner ℝ y (lam⁻¹ • ξ)) * Complex.I) •
    g y with hF
  have hcv := Measure.integral_comp_smul (volume : Measure Rn) F lam
  rw [finrank_euclideanSpace_fin, abs_of_pos (by positivity)] at hcv
  have e : (fun v : Rn => Complex.exp (↑(-2 * Real.pi * inner ℝ v ξ) * Complex.I) • dilF lam g v) =
      fun v => ((lam ^ ((n : ℝ) / 2) : ℝ) : ℂ) • F (lam • v) := by
    funext v
    simp only [hF, dilF, smul_eq_mul, hin]
    ring
  rw [e, integral_smul, hcv, Complex.real_smul, smul_eq_mul]
  push_cast
  ring

theorem two_pi_coef :
    (2 * Real.pi) ^ ((n : ℝ) / 2) * ((2 * Real.pi) ^ n)⁻¹ = (2 * Real.pi)⁻¹ ^ ((n : ℝ) / 2) := by
  have h := two_pi_pos'
  rw [Real.inv_rpow h.le, ← Real.rpow_natCast, ← Real.rpow_neg h.le, ← Real.rpow_neg h.le,
    ← Real.rpow_add h]
  congr 1
  ring

theorem FU_symm_apply (g : L2 n) :
    FU.symm g = fourierL2.symm (dilL2 (inv_pos.2 (inv_pos.2 two_pi_pos')) g) := rfl

/-- On `L¹ ∩ L²`, `FU⁻¹ g (x) = ĝ(−x)`. -/
theorem FU_symm_ae_eq (g : L2 n) (hg : Integrable (g : Rn → ℂ)) :
    (FU.symm g : Rn → ℂ) =ᵐ[volume] fun x => fourierU (g : Rn → ℂ) (-x) := by
  have hl : (0 : ℝ) < ((2 * Real.pi)⁻¹)⁻¹ := inv_pos.2 (inv_pos.2 two_pi_pos')
  have hw : (dilL2 hl g : Rn → ℂ) =ᵐ[volume] dilF ((2 * Real.pi)⁻¹)⁻¹ g := coeFn_dilL2 hl g
  have hwi : Integrable (dilL2 hl g : Rn → ℂ) := by
    refine Integrable.congr ?_ hw.symm
    exact ((integrable_comp_smul_iff volume (g : Rn → ℂ) hl.ne').2 hg).const_mul _
  rw [FU_symm_apply, fourierL2_symm_eq]
  filter_upwards [coeFn_refl (fourierL2 (dilL2 hl g)),
    neg_ae_eq (fourierL2_ae_eq_fourier (dilL2 hl g) hwi)] with x h1 h2
  rw [h1]
  refine h2.trans ?_
  rw [fourier_congr_ae hw, fourier_dilF hl, fourierU_eq, dilF, inv_inv, two_pi_coef]

/-- The inverse unitary Fourier transform `ǧ(x) = (2π)^{-n/2} ∫ g(ξ) e^{ix·ξ} dξ`. -/
noncomputable def fourierUinv (g : Rn → ℂ) (x : Rn) : ℂ :=
  (((2 * Real.pi) ^ (-((n : ℝ) / 2)) : ℝ) : ℂ) *
    ∫ ξ, g ξ * Complex.exp (((inner ℝ ξ x : ℝ) : ℂ) * Complex.I)

theorem fourierUinv_eq (g : Rn → ℂ) (x : Rn) : fourierUinv g x = fourierU g (-x) := by
  rw [fourierUinv, fourierU]
  congr 2
  funext ξ
  rw [inner_neg_right, Complex.ofReal_neg, neg_neg]

/-- **Fourier inversion.** If `û ∈ L¹`, then `u(x) = (2π)^{-n/2} ∫ û(ξ) e^{ix·ξ} dξ` for a.e.
`x`. -/
theorem ae_eq_fourierUinv (u : L2 n) (hu : Integrable (FU u : Rn → ℂ)) :
    (u : Rn → ℂ) =ᵐ[volume] fourierUinv (FU u : Rn → ℂ) := by
  have h := FU_symm_ae_eq (FU u) hu
  rw [LinearIsometryEquiv.symm_apply_apply] at h
  filter_upwards [h] with x hx
  rw [hx, fourierUinv_eq]

theorem norm_fourierUinv_le (g : Rn → ℂ) (x : Rn) :
    ‖fourierUinv g x‖ ≤ (2 * Real.pi) ^ (-((n : ℝ) / 2)) * ∫ ξ, ‖g ξ‖ := by
  rw [fourierUinv, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  refine mul_le_mul_of_nonneg_left ((norm_integral_le_integral_norm _).trans (le_of_eq ?_))
    (by positivity)
  congr 1
  funext ξ
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

theorem continuous_fourierUinv {g : Rn → ℂ} (hg : Integrable g) : Continuous (fourierUinv g) := by
  have h : fourierUinv g = fun x => dilF (2 * Real.pi)⁻¹ (𝓕 g) (-x) := by
    funext x
    rw [fourierUinv_eq, fourierU_eq]
  rw [h]
  have hc : Continuous (𝓕 g) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner hg
  simp only [dilF]
  exact continuous_const.mul (hc.comp (continuous_const.smul continuous_neg))

/-! ### The Sobolev embedding `H^r(ℝⁿ) ↪ L^∞(ℝⁿ)`, `r > n/2` -/

/-- The embedding constant `C(n, r) = (2π)^{-n/2} (∫ (1 + |ξ|²)^{-r} dξ)^{1/2}`. -/
noncomputable def Cemb (n : ℕ) (r : ℝ) : ℝ :=
  (2 * Real.pi) ^ (-((n : ℝ) / 2)) *
    Real.sqrt (∫ ξ : EuclideanSpace ℝ (Fin n), jw (-r) ξ)

theorem Cemb_nonneg (n : ℕ) (r : ℝ) : 0 ≤ Cemb n r := by
  unfold Cemb
  positivity

theorem Cemb_pos {r : ℝ} (hr : (n : ℝ) / 2 < r) : 0 < Cemb n r := by
  unfold Cemb
  have hpos : 0 < ∫ ξ : Rn, jw (-r) ξ := by
    rw [integral_pos_iff_support_of_nonneg (fun ξ => jw_nonneg _ ξ) (integrable_jw_neg hr)]
    have hs : Function.support (jw (n := n) (-r)) = univ :=
      eq_univ_of_forall fun ξ => (jw_pos _ ξ).ne'
    rw [hs]
    exact Measure.measure_univ_pos.2 (NeZero.ne _)
  have := Real.sqrt_pos.2 hpos
  positivity

/-- `t ≤ ((1 + |ξ|²)^{-r} + (1 + |ξ|²)^r t²)/2`. -/
theorem le_jw_amgm (r : ℝ) (ξ : Rn) (t : ℝ) : t ≤ (jw (-r) ξ + jw r ξ * t ^ 2) / 2 := by
  have ha := jw_neg_half_mul r ξ
  rw [← jw_half_sq (-r) ξ, ← jw_half_sq r ξ]
  set a := jw (-r / 2) ξ
  set b := jw (r / 2) ξ
  have e : t = a * (b * t) := by rw [← mul_assoc, ha, one_mul]
  nlinarith [sq_nonneg (a - b * t)]

/-- **Cauchy–Schwarz:** for `r > n/2`, `û ∈ L¹`. -/
theorem integrable_FU {r : ℝ} (hr : (n : ℝ) / 2 < r) {u : L2 n} (hu : MemHs r u) :
    Integrable (FU u : Rn → ℂ) := by
  refine (((integrable_jw_neg hr).add hu).div_const 2).mono' (Lp.aestronglyMeasurable _)
    (Eventually.of_forall fun ξ => ?_)
  simp only [Pi.add_apply]
  exact le_jw_amgm r ξ _

/-- **Cauchy–Schwarz:** `‖û‖_{L¹} ≤ (∫ (1 + |ξ|²)^{-r})^{1/2} ‖u‖_{H^r}`. -/
theorem integral_norm_FU_le {r : ℝ} (hr : (n : ℝ) / 2 < r) {u : L2 n} (hu : MemHs r u) :
    ∫ ξ, ‖(FU u : Rn → ℂ) ξ‖ ≤ Real.sqrt (∫ ξ : Rn, jw (-r) ξ) * hsNorm r u := by
  have hf : MemLp (fun ξ => jw (-r / 2) ξ) (ENNReal.ofReal 2) (volume : Measure Rn) := by
    rw [ENNReal.ofReal_ofNat,
      memLp_two_iff_integrable_sq_norm (continuous_jw _).aestronglyMeasurable]
    refine (integrable_jw_neg hr).congr (Eventually.of_forall fun ξ => ?_)
    dsimp only
    rw [Real.norm_of_nonneg (jw_nonneg _ _), jw_half_sq]
  have hgm : AEStronglyMeasurable (fun ξ => jw (r / 2) ξ * ‖(FU u : Rn → ℂ) ξ‖) volume :=
    (continuous_jw _).aestronglyMeasurable.mul (Lp.aestronglyMeasurable _).norm
  have hg : MemLp (fun ξ => jw (r / 2) ξ * ‖(FU u : Rn → ℂ) ξ‖) (ENNReal.ofReal 2)
      (volume : Measure Rn) := by
    rw [ENNReal.ofReal_ofNat, memLp_two_iff_integrable_sq_norm hgm]
    refine hu.congr (Eventually.of_forall fun ξ => ?_)
    dsimp only
    rw [Real.norm_of_nonneg (mul_nonneg (jw_nonneg _ _) (norm_nonneg _)), mul_pow, jw_half_sq]
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Eventually.of_forall fun ξ => jw_nonneg (-r / 2) ξ)
    (Eventually.of_forall fun ξ => mul_nonneg (jw_nonneg (r / 2) ξ) (norm_nonneg _)) hf hg
  have e1 : ∫ ξ, jw (-r / 2) ξ * (jw (r / 2) ξ * ‖(FU u : Rn → ℂ) ξ‖) =
      ∫ ξ, ‖(FU u : Rn → ℂ) ξ‖ := by
    congr 1
    funext ξ
    rw [← mul_assoc, jw_neg_half_mul, one_mul]
  have e2 : ∫ ξ : Rn, jw (-r / 2) ξ ^ (2 : ℝ) = ∫ ξ : Rn, jw (-r) ξ := by
    congr 1
    funext ξ
    rw [Real.rpow_two, jw_half_sq]
  have e3 : ∫ ξ, (jw (r / 2) ξ * ‖(FU u : Rn → ℂ) ξ‖) ^ (2 : ℝ) =
      ∫ ξ, jw r ξ * ‖(FU u : Rn → ℂ) ξ‖ ^ 2 := by
    congr 1
    funext ξ
    rw [Real.rpow_two, mul_pow, jw_half_sq]
  rw [e1, e2, e3] at h
  rw [hsNorm, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  exact h

/-- **Sobolev embedding `H^r(ℝⁿ) ↪ L^∞(ℝⁿ)` for `r > n/2`.** Every `u ∈ H^r` has a continuous
representative bounded by `C(n, r)‖u‖_{H^r}`; in particular `u ∈ L^∞` and
`‖u‖_∞ ≤ C(n, r)‖u‖_{H^r}`. -/
theorem embedding {r : ℝ} (hr : (n : ℝ) / 2 < r) {u : L2 n} (hu : MemHs r u) :
    (∃ f : Rn → ℂ, Continuous f ∧ (u : Rn → ℂ) =ᵐ[volume] f ∧
      ∀ x, ‖f x‖ ≤ Cemb n r * hsNorm r u) ∧
    (∀ᵐ x ∂volume, ‖(u : Rn → ℂ) x‖ ≤ Cemb n r * hsNorm r u) ∧
    MemLp (u : Rn → ℂ) ∞ volume ∧
    eLpNorm (u : Rn → ℂ) ∞ volume ≤ ENNReal.ofReal (Cemb n r * hsNorm r u) := by
  have hi := integrable_FU hr hu
  have hb : ∀ x, ‖fourierUinv (FU u : Rn → ℂ) x‖ ≤ Cemb n r * hsNorm r u := fun x =>
    (norm_fourierUinv_le _ x).trans (by
      rw [Cemb, mul_assoc]
      exact mul_le_mul_of_nonneg_left (integral_norm_FU_le hr hu) (by positivity))
  have hae := ae_eq_fourierUinv u hi
  have hbd : ∀ᵐ x ∂volume, ‖(u : Rn → ℂ) x‖ ≤ Cemb n r * hsNorm r u := by
    filter_upwards [hae] with x hx
    rw [hx]
    exact hb x
  refine ⟨⟨_, continuous_fourierUinv hi, hae, hb⟩, hbd,
    memLp_top_of_bound (Lp.aestronglyMeasurable u) _ hbd, ?_⟩
  rw [eLpNorm_exponent_top]
  exact eLpNormEssSup_le_of_ae_bound hbd

end E69

end ReyesMath
