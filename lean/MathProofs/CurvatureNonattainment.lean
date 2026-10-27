import Mathlib
import MathProofs.StrictBinding

/-!
# Whole-space nonattainment and strict spreading for a positive curvature functional (F05/T8)

Formalization of `papers/positive-curvature-whole-space-nonattainment/main.tex` on the Sobolev
space `H²(ℝ^d; ℂ)` of `MathProofs.SobolevH2`, for every finite `d`.

* The weight `Curvature.F ε α s = s/(s + ε²e^{−2αs})²`: `F_nonneg`, `F_pos`, the uniform bound
  `F_le` (`F ≤ M_F = 1 + e^{2α}/(4ε²)`), the derivative `hasDerivAt_F`
  (`F' = (A − s + 4αsA)/(s + A)³`), `abs_mul_F'_le` (`|sF'(s)| ≤ M_F + 4α`), the virial weight
  identity `virial_weight` (`4F + dsF' = F(4 − d + 2dA(1 + 2αs)/(s + A))`) and its sign
  `virial_nonneg`, `virial_pos` for `d ≤ 4`.
* `Curvature.Ec`: `E(ψ) = c₁∫|∇ψ|² + c₂∫F(|ψ|²)|Δψ|²`; `Curvature.Id`: `I_d(m)`.
* `Sobolev.H2.val_eq_zero_of_K_eq_zero`: for `d ≥ 1`, `∇ψ = 0` in `L²` forces `ψ = 0` (proved by
  Parseval and a weighted Cauchy–Schwarz estimate, with dominated convergence as `η ↓ 0`); hence
  `Curvature.Ec_eq_zero_iff` (`E(ψ) = 0 ⟺ ψ = 0`).
* `Curvature.Ec_dil` (exact scaling formula `E(ψ_λ) = c₁λ²‖∇ψ‖² + c₂λ⁴∫F(λ^d|ψ|²)|Δψ|²`).
* Theorem (positive-mass whole-space nonattainment): `Curvature.global_nonattainment` — for every
  `d ≥ 1` and `m > 0`, `E` is finite and nonnegative on `H²`, positive at every `ψ ≠ 0`,
  `I_d(m) = 0`, and the set of constrained minimizers is empty.
* Theorem (strict spreading, `1 ≤ d ≤ 4`): `Curvature.strict_spreading` — for `ψ ≠ 0`,
  `λ ↦ E(ψ_λ)` is `C¹` and strictly increasing on `(0, ∞)`, so `E(ψ_λ) < E(ψ)` for `0 < λ < 1`;
  with the derivative `Curvature.hasDerivAt_eDil` (differentiation under the integral sign) and
  the bound `Curvature.log_deriv_ge` (`d/d log λ E(ψ_λ) ≥ 2c₁λ²‖∇ψ‖² > 0`).
* `Sobolev.H2.tendsto_distH2_dilR`: strong continuity of the dilation group on `H²`;
  `Curvature.no_local_minimizer`: `E|𝒜_m` has no local minimizer in the `H²` topology.  The
  distance `H2.distH2` is `‖u − v‖ + Σᵢ‖∂ᵢ(u − v)‖ + ‖Δ(u − v)‖`; since `‖∂ᵢ∂ⱼw‖ ≤ ‖Δw‖` on
  `ℝ^d`, every ball of the standard `H²` norm contains a `distH2`-ball, so the statement holds
  for the standard `H²` topology as well.
-/

open Filter Topology Complex InnerProductSpace MeasureTheory Set
open scoped ContDiff FourierTransform

namespace ReyesMath

namespace Curvature

/-- `A(s) = ε² e^{−2αs}`. -/
noncomputable def Aw (ε α s : ℝ) : ℝ := ε ^ 2 * Real.exp (-2 * α * s)

/-- The bounded nonlinear weight `F(s) = s/(s + ε² e^{−2αs})²`. -/
noncomputable def F (ε α s : ℝ) : ℝ := s / (s + Aw ε α s) ^ 2

/-- `F'(s) = (A(s) − s + 4αsA(s))/(s + A(s))³`. -/
noncomputable def F' (ε α s : ℝ) : ℝ :=
  (Aw ε α s - s + 4 * α * s * Aw ε α s) / (s + Aw ε α s) ^ 3

/-- The uniform bound `M_F = 1 + e^{2α}/(4ε²)`. -/
noncomputable def MF (ε α : ℝ) : ℝ := 1 + Real.exp (2 * α) / (4 * ε ^ 2)

variable {ε α s : ℝ}

theorem Aw_pos (hε : 0 < ε) : 0 < Aw ε α s := by
  unfold Aw
  positivity

theorem den_pos (hε : 0 < ε) (hs : 0 ≤ s) : 0 < s + Aw ε α s := by
  have := Aw_pos (α := α) (s := s) hε
  linarith

theorem F_nonneg (hs : 0 ≤ s) : 0 ≤ F ε α s := by
  unfold F
  positivity

theorem F_pos (hε : 0 < ε) (hs : 0 < s) : 0 < F ε α s := by
  unfold F
  have := den_pos (α := α) hε hs.le
  positivity

theorem F_zero : F ε α 0 = 0 := by simp [F]

theorem MF_pos : 0 < MF ε α := by
  unfold MF
  positivity

/-- `F ≤ M_F` on `[0, ∞)`. -/
theorem F_le (hε : 0 < ε) (hα : 0 ≤ α) (hs : 0 ≤ s) : F ε α s ≤ MF ε α := by
  have hA := Aw_pos (α := α) (s := s) hε
  have hD := den_pos (α := α) hε hs
  have hE : 0 ≤ Real.exp (2 * α) / (4 * ε ^ 2) := by positivity
  unfold MF
  rcases le_total s 1 with h1 | h1
  · -- `F ≤ 1/(4A) ≤ e^{2α}/(4ε²)`
    have hF : F ε α s ≤ 1 / (4 * Aw ε α s) := by
      unfold F
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [sq_nonneg (s - Aw ε α s)]
    have hA' : ε ^ 2 * Real.exp (-2 * α) ≤ Aw ε α s := by
      unfold Aw
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith)) (by positivity)
    have h2 : 1 / (4 * Aw ε α s) ≤ Real.exp (2 * α) / (4 * ε ^ 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : Real.exp (2 * α) * (ε ^ 2 * Real.exp (-2 * α)) = ε ^ 2 := by
        rw [mul_left_comm, ← Real.exp_add]
        simp
      nlinarith [Real.exp_pos (2 * α)]
    linarith
  · -- `F ≤ 1/s ≤ 1`
    have hF : F ε α s ≤ 1 := by
      unfold F
      rw [div_le_one (by positivity)]
      nlinarith
    linarith

theorem hasDerivAt_Aw (s : ℝ) : HasDerivAt (Aw ε α) (-2 * α * Aw ε α s) s := by
  unfold Aw
  have h := ((hasDerivAt_id s).const_mul (-2 * α)).exp.const_mul (ε ^ 2)
  convert h using 1
  simp only [id]
  ring

theorem hasDerivAt_F (hε : 0 < ε) (hs : 0 ≤ s) : HasDerivAt (F ε α) (F' ε α s) s := by
  have hD := den_pos (α := α) hε hs
  have h1 : HasDerivAt (fun x => x + Aw ε α x) (1 + -2 * α * Aw ε α s) s :=
    (hasDerivAt_id s).add (hasDerivAt_Aw s)
  have h2 := h1.fun_pow 2
  have h3 := (hasDerivAt_id' s).div h2 (by positivity)
  unfold F
  convert h3 using 1
  unfold F'
  simp only [Nat.cast_ofNat]
  field_simp
  ring

theorem continuousAt_F' (hε : 0 < ε) (hs : 0 ≤ s) : ContinuousAt (F' ε α) s := by
  have hD := den_pos (α := α) hε hs
  have hA : Continuous (Aw ε α) := by unfold Aw; fun_prop
  unfold F'
  exact ((hA.sub continuous_id).add ((continuous_const.mul continuous_id).mul hA)).continuousAt.div
    ((continuous_id.add hA).pow 3).continuousAt (by positivity)

theorem measurable_F : Measurable (F ε α) := by
  unfold F Aw
  fun_prop

theorem measurable_F' : Measurable (F' ε α) := by
  unfold F' Aw
  fun_prop

/-- `|s F'(s)| ≤ M_F + 4α` on `[0, ∞)`. -/
theorem abs_mul_F'_le (hε : 0 < ε) (hα : 0 ≤ α) (hs : 0 ≤ s) :
    |s * F' ε α s| ≤ MF ε α + 4 * α := by
  have hA := Aw_pos (α := α) (s := s) hε
  have hD := den_pos (α := α) hε hs
  set A := Aw ε α s with hAdef
  have hF := F_le (α := α) hε hα hs
  have hsplit : s * F' ε α s = s * (A - s) / (s + A) ^ 3 + 4 * α * (s ^ 2 * A / (s + A) ^ 3) := by
    unfold F'
    rw [← hAdef]
    field_simp
  have hFs : F ε α s = s * (s + A) / (s + A) ^ 3 := by
    unfold F
    rw [← hAdef]
    field_simp
  have h1 : |s * (A - s) / (s + A) ^ 3| ≤ F ε α s := by
    rw [hFs, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (s + A) ^ 3)]
    apply div_le_div_of_nonneg_right _ (by positivity)
    rw [abs_mul, abs_of_nonneg hs]
    apply mul_le_mul_of_nonneg_left _ hs
    rw [abs_le]
    constructor <;> linarith
  have h2 : s ^ 2 * A / (s + A) ^ 3 ≤ 1 := by
    rw [div_le_one (by positivity)]
    have : s ^ 2 ≤ (s + A) ^ 2 := by nlinarith
    calc s ^ 2 * A ≤ (s + A) ^ 2 * (s + A) := by
          apply mul_le_mul this (by linarith) hA.le (by positivity)
      _ = (s + A) ^ 3 := by ring
  have h3 : 0 ≤ s ^ 2 * A / (s + A) ^ 3 := by positivity
  rw [hsplit]
  calc |s * (A - s) / (s + A) ^ 3 + 4 * α * (s ^ 2 * A / (s + A) ^ 3)|
      ≤ |s * (A - s) / (s + A) ^ 3| + |4 * α * (s ^ 2 * A / (s + A) ^ 3)| := abs_add _ _
    _ ≤ F ε α s + 4 * α := by
        rw [abs_of_nonneg (by positivity : 0 ≤ 4 * α * (s ^ 2 * A / (s + A) ^ 3))]
        nlinarith
    _ ≤ MF ε α + 4 * α := by linarith

/-- **The virial weight:** `4F + d s F' = F (4 − d + 2dA(1 + 2αs)/(s + A))`. -/
theorem virial_weight (hε : 0 < ε) (d : ℕ) (hs : 0 ≤ s) :
    4 * F ε α s + d * s * F' ε α s =
      F ε α s * (4 - d + 2 * d * Aw ε α s * (1 + 2 * α * s) / (s + Aw ε α s)) := by
  have hD := den_pos (α := α) hε hs
  unfold F F'
  field_simp
  ring

/-- For `d ≤ 4`, `4F(s) + d s F'(s) ≥ 0` on `[0, ∞)`. -/
theorem virial_nonneg (hε : 0 < ε) (hα : 0 ≤ α) {d : ℕ} (hd : d ≤ 4) (hs : 0 ≤ s) :
    0 ≤ 4 * F ε α s + d * s * F' ε α s := by
  rw [virial_weight hε d hs]
  have hD := den_pos (α := α) hε hs
  have hA := Aw_pos (α := α) (s := s) hε
  have hd' : (d : ℝ) ≤ 4 := by exact_mod_cast hd
  have : 0 ≤ 4 - (d : ℝ) + 2 * d * Aw ε α s * (1 + 2 * α * s) / (s + Aw ε α s) := by
    have : 0 ≤ 2 * d * Aw ε α s * (1 + 2 * α * s) / (s + Aw ε α s) := by positivity
    linarith
  exact mul_nonneg (F_nonneg hs) this

/-- For `1 ≤ d ≤ 4` and `s > 0`, `4F(s) + d s F'(s) > 0`. -/
theorem virial_pos (hε : 0 < ε) (hα : 0 ≤ α) {d : ℕ} (hd : d ≤ 4) (hs : 0 < s) :
    0 < 4 * F ε α s + d * s * F' ε α s := by
  rw [virial_weight hε d hs.le]
  have hD := den_pos (α := α) hε hs.le
  have hA := Aw_pos (α := α) (s := s) hε
  have hd' : (d : ℝ) ≤ 4 := by exact_mod_cast hd
  have h1 : 0 < 4 - (d : ℝ) + 2 * d * Aw ε α s * (1 + 2 * α * s) / (s + Aw ε α s) ∨ d = 0 := by
    rcases Nat.eq_zero_or_pos d with h | h
    · right; exact h
    · left
      have hd0 : (0 : ℝ) < d := by exact_mod_cast h
      have : 0 < 2 * d * Aw ε α s * (1 + 2 * α * s) / (s + Aw ε α s) := by positivity
      linarith
  rcases h1 with h1 | h1
  · exact mul_pos (F_pos hε hs) h1
  · subst h1
    simp only [Nat.cast_zero, sub_zero, mul_zero, zero_mul, zero_div, add_zero]
    have := F_pos (α := α) hε hs
    linarith

end Curvature

end ReyesMath

namespace ReyesMath

namespace Sobolev

variable {d : ℕ}

local notation "Rd" => EuclideanSpace ℝ (Fin d)

theorem integrable_sq_L2 (f : L2 d) : Integrable fun x => ‖f x‖ ^ 2 :=
  (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).1 (Lp.memLp f)

theorem normSq_eq_integral (f : L2 d) : ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
  rw [@norm_sq_eq_re_inner ℂ, L2.inner_def]
  simp_rw [inner_self_complex]
  rw [integral_complex_ofReal]
  simp

theorem norm_fourier_dS_sq (i : Fin d) (φ : SchwartzMap Rd ℂ) (ξ : Rd) :
    ‖𝓕 (⇑(dS i φ)) ξ‖ ^ 2 = (2 * Real.pi * ξ i) ^ 2 * ‖𝓕 (⇑φ) ξ‖ ^ 2 := by
  rw [fourier_dS, norm_mul]
  simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_I, mul_one]
  rw [abs_of_pos Real.pi_pos]
  ring_nf
  rw [sq_abs]
  ring

theorem integrable_fourier_sq (φ : SchwartzMap Rd ℂ) : Integrable fun ξ => ‖𝓕 (⇑φ) ξ‖ ^ 2 := by
  have := integrable_normSq (fS φ)
  simpa only [coe_fS] using this

theorem integrable_qS_fourier (φ : SchwartzMap Rd ℂ) :
    Integrable fun ξ => qS ξ * ‖𝓕 (⇑φ) ξ‖ ^ 2 := by
  have h : (fun ξ => qS ξ * ‖𝓕 (⇑φ) ξ‖ ^ 2) = fun ξ => ∑ i : Fin d, ‖𝓕 (⇑(dS i φ)) ξ‖ ^ 2 := by
    funext ξ
    simp_rw [norm_fourier_dS_sq]
    rw [← Finset.sum_mul]
    congr 1
    rw [qS, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Real.norm_eq_abs, sq_abs]
    ring
  rw [h]
  exact integrable_finset_sum _ fun i _ => integrable_fourier_sq (dS i φ)

theorem continuous_qS : Continuous (qS (d := d)) := by
  unfold qS
  fun_prop

theorem continuous_fourier (φ : SchwartzMap Rd ℂ) : Continuous (𝓕 (⇑φ)) := by
  rw [← coe_fS]
  exact (fS φ).continuous

/-- `J_η(χ) = ∫ |𝓕χ|²/(|2πξ|² + η)`. -/
noncomputable def Jw (η : ℝ) (χ : SchwartzMap Rd ℂ) : ℝ := ∫ ξ, ‖𝓕 (⇑χ) ξ‖ ^ 2 / (qS ξ + η)

theorem integrable_Jw {η : ℝ} (hη : 0 < η) (χ : SchwartzMap Rd ℂ) :
    Integrable fun ξ => ‖𝓕 (⇑χ) ξ‖ ^ 2 / (qS ξ + η) := by
  refine ((integrable_fourier_sq χ).div_const η).mono'
    ((((continuous_fourier χ).norm.pow 2).div (continuous_qS.add continuous_const)
      fun ξ => (by have := qS_nonneg ξ; positivity)).aestronglyMeasurable)
    (Eventually.of_forall fun ξ => ?_)
  have hq := qS_nonneg ξ
  rw [Real.norm_of_nonneg (by positivity)]
  exact div_le_div_of_nonneg_left (by positivity) hη (by linarith)

theorem Jw_nonneg (η : ℝ) (χ : SchwartzMap Rd ℂ) (hη : 0 < η) : 0 ≤ Jw η χ :=
  integral_nonneg fun ξ => by have := qS_nonneg ξ; positivity

/-- Pointwise AM–GM `ab ≤ (t a²/w + w b²/t)/2`. -/
theorem mul_le_amgm {a b w t : ℝ} (hw : 0 < w) (ht : 0 < t) :
    a * b ≤ (t * (a ^ 2 / w) + w * b ^ 2 / t) / 2 := by
  have hid : t * (a ^ 2 / w) + w * b ^ 2 / t - 2 * (a * b) = (t * a - w * b) ^ 2 / (w * t) := by
    field_simp
    ring
  have : 0 ≤ (t * a - w * b) ^ 2 / (w * t) := by positivity
  linarith

/-- If `x ≤ (ta + b/t)/2` for all `t > 0`, then `x² ≤ ab`. -/
theorem sq_le_of_forall_amgm {x a b : ℝ} (hx : 0 ≤ x) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : ∀ t : ℝ, 0 < t → x ≤ (t * a + b / t) / 2) : x ^ 2 ≤ a * b := by
  rcases hx.lt_or_eq with hx' | hx'
  · rcases ha.lt_or_eq with ha' | ha'
    · have h1 := h (x / a) (div_pos hx' ha')
      have e : (x / a * a + b / (x / a)) / 2 = (x + a * b / x) / 2 := by
        field_simp
      rw [e] at h1
      have h2 : x ≤ a * b / x := by linarith
      rw [le_div_iff₀ hx'] at h2
      nlinarith
    · exfalso
      have h1 := h ((b + 1) / x) (by positivity)
      rw [← ha', mul_zero, zero_add] at h1
      have h2 : b / ((b + 1) / x) < x := by
        rw [div_div_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith
      linarith
  · rw [← hx']
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    positivity

/-- **Weighted Parseval–Cauchy–Schwarz on `𝓢`:**
`|⟪χ, φ⟫| ≤ (t J_η(χ) + (Σ‖∂ᵢφ‖² + η‖φ‖²)/t)/2`. -/
theorem norm_inner_le (χ φ : SchwartzMap Rd ℂ) {η t : ℝ} (hη : 0 < η) (ht : 0 < t) :
    ‖inner ℂ (toL2 χ) (toL2 φ)‖ ≤
      (t * Jw η χ + (∑ i : Fin d, ‖toL2 (dS i φ)‖ ^ 2 + η * ‖toL2 φ‖ ^ 2) / t) / 2 := by
  rw [inner_toL2_fourier]
  have hW : Integrable fun ξ : Rd => (qS ξ + η) * ‖𝓕 (⇑φ) ξ‖ ^ 2 := by
    simp_rw [add_mul]
    exact (integrable_qS_fourier φ).add ((integrable_fourier_sq φ).const_mul η)
  have hR : Integrable fun ξ : Rd =>
      (t * (‖𝓕 (⇑χ) ξ‖ ^ 2 / (qS ξ + η)) + (qS ξ + η) * ‖𝓕 (⇑φ) ξ‖ ^ 2 / t) / 2 :=
    (((integrable_Jw hη χ).const_mul t).add (hW.div_const t)).div_const 2
  calc ‖∫ ξ, (starRingEnd ℂ) (𝓕 (⇑χ) ξ) * 𝓕 (⇑φ) ξ‖
      ≤ ∫ ξ, ‖(starRingEnd ℂ) (𝓕 (⇑χ) ξ) * 𝓕 (⇑φ) ξ‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ ξ, (t * (‖𝓕 (⇑χ) ξ‖ ^ 2 / (qS ξ + η)) + (qS ξ + η) * ‖𝓕 (⇑φ) ξ‖ ^ 2 / t) / 2 := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun ξ => norm_nonneg _) hR
          (Eventually.of_forall fun ξ => ?_)
        have hq := qS_nonneg ξ
        simp only [norm_mul, Complex.norm_conj]
        exact mul_le_amgm (by positivity) ht
    _ = (t * Jw η χ + (∑ i : Fin d, ‖toL2 (dS i φ)‖ ^ 2 + η * ‖toL2 φ‖ ^ 2) / t) / 2 := by
        rw [integral_div, integral_add ((integrable_Jw hη χ).const_mul t) (hW.div_const t),
          integral_const_mul, integral_div]
        congr 3
        simp_rw [add_mul]
        rw [integral_add (integrable_qS_fourier φ) ((integrable_fourier_sq φ).const_mul η),
          integral_const_mul, sum_normSq_dS, norm_toL2_sq_fourier]

/-- `η J_η(χ) → 0` as `η ↓ 0` (dominated convergence; `{0}` is null for `d ≥ 1`). -/
theorem tendsto_mul_Jw [NeZero d] (χ : SchwartzMap Rd ℂ) :
    Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1)) * Jw (1 / ((n : ℝ) + 1)) χ) atTop (𝓝 0) := by
  have hη : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have heq : ∀ n : ℕ, (1 / ((n : ℝ) + 1)) * Jw (1 / ((n : ℝ) + 1)) χ =
      ∫ ξ, (1 / ((n : ℝ) + 1)) * (‖𝓕 (⇑χ) ξ‖ ^ 2 / (qS ξ + 1 / ((n : ℝ) + 1))) := fun n => by
    rw [Jw, integral_const_mul]
  simp_rw [heq]
  have h0 : (0 : ℝ) = ∫ ξ : Rd, (0 : ℝ) := by simp
  rw [h0]
  refine tendsto_integral_of_dominated_convergence (fun ξ => ‖𝓕 (⇑χ) ξ‖ ^ 2)
    (fun n => ((integrable_Jw (hη n) χ).const_mul _).aestronglyMeasurable)
    (integrable_fourier_sq χ) (fun n => Eventually.of_forall fun ξ => ?_) ?_
  · have hq := qS_nonneg ξ
    have hn := hη n
    rw [Real.norm_of_nonneg (by positivity)]
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg ‖𝓕 (⇑χ) ξ‖]
  · have hne : ∀ᵐ ξ ∂(volume : Measure Rd), ξ ≠ 0 := by
      have := measure_singleton (μ := (volume : Measure Rd)) 0
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 this] with ξ hξ
      simpa using hξ
    filter_upwards [hne] with ξ hξ
    have hq : 0 < qS ξ := by
      unfold qS
      have : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
      positivity
    have hc : ContinuousAt (fun η : ℝ => η * (‖𝓕 (⇑χ) ξ‖ ^ 2 / (qS ξ + η))) 0 :=
      continuousAt_id.mul (continuousAt_const.div (continuousAt_const.add continuousAt_id)
        (by simp only [add_zero]; exact hq.ne'))
    have := hc.tendsto.comp tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using this

namespace H2

/-- **Vanishing Dirichlet energy forces `u = 0`** (`d ≥ 1`): if `∇u = 0` in `L²(ℝ^d)` then
`u = 0`. -/
theorem val_eq_zero_of_K_eq_zero [NeZero d] (U : H2 d) (hK : K U = 0) : U.val = 0 := by
  apply eq_zero_of_inner_schwartz
  intro χ
  obtain ⟨φ, h0, h1, -⟩ := U.approx
  have hbound : ∀ η : ℝ, 0 < η → ‖inner ℂ (toL2 χ) U.val‖ ^ 2 ≤ M U * (η * Jw η χ) := by
    intro η hη
    have ht : ∀ t : ℝ, 0 < t → ‖inner ℂ (toL2 χ) U.val‖ ≤ (t * Jw η χ + (η * M U) / t) / 2 := by
      intro t ht
      have hA : Tendsto (fun n => ‖inner ℂ (toL2 χ) (toL2 (φ n))‖) atTop
          (𝓝 ‖inner ℂ (toL2 χ) U.val‖) :=
        ((tendsto_const_nhds (x := toL2 χ)).inner (𝕜 := ℂ) h0).norm
      have hK' : Tendsto (fun n => ∑ i : Fin d, ‖toL2 (dS i (φ n))‖ ^ 2) atTop (𝓝 (K U)) :=
        tendsto_finset_sum _ fun i _ => ((h1 i).norm).pow 2
      have hM' : Tendsto (fun n => ‖toL2 (φ n)‖ ^ 2) atTop (𝓝 (M U)) := (h0.norm).pow 2
      have hB : Tendsto (fun n => (t * Jw η χ + (∑ i : Fin d, ‖toL2 (dS i (φ n))‖ ^ 2 +
          η * ‖toL2 (φ n)‖ ^ 2) / t) / 2) atTop (𝓝 ((t * Jw η χ + (K U + η * M U) / t) / 2)) :=
        (tendsto_const_nhds.add ((hK'.add (hM'.const_mul η)).div_const t)).div_const 2
      have := le_of_tendsto_of_tendsto' hA hB fun n => norm_inner_le χ (φ n) hη ht
      rwa [hK, zero_add] at this
    have := sq_le_of_forall_amgm (norm_nonneg _) (Jw_nonneg η χ hη)
      (mul_nonneg hη.le (M_nonneg U)) ht
    linarith [show Jw η χ * (η * M U) = M U * (η * Jw η χ) by ring]
  have hlim : Tendsto (fun n : ℕ => M U * ((1 / ((n : ℝ) + 1)) * Jw (1 / ((n : ℝ) + 1)) χ))
      atTop (𝓝 0) := by
    simpa using (tendsto_mul_Jw χ).const_mul (M U)
  have hle : ‖inner ℂ (toL2 χ) U.val‖ ^ 2 ≤ 0 :=
    ge_of_tendsto' hlim fun n => hbound _ (by positivity)
  have : ‖inner ℂ (toL2 χ) U.val‖ = 0 := by
    have := sq_nonneg ‖inner ℂ (toL2 χ) U.val‖
    have h2 : ‖inner ℂ (toL2 χ) U.val‖ ^ 2 = 0 := le_antisymm hle this
    exact pow_eq_zero_iff two_ne_zero |>.1 h2
  exact norm_eq_zero.1 this

theorem M_eq_zero_of_K_eq_zero [NeZero d] (U : H2 d) (hK : K U = 0) : M U = 0 := by
  rw [M, val_eq_zero_of_K_eq_zero U hK, norm_zero]
  simp

theorem K_pos [NeZero d] (U : H2 d) (hM : M U ≠ 0) : 0 < K U :=
  (K_nonneg U).lt_of_ne fun h => hM (M_eq_zero_of_K_eq_zero U h.symm)

end H2

end Sobolev

end ReyesMath

namespace ReyesMath

namespace Sobolev

namespace H2

variable {d : ℕ}

local notation "Rd" => EuclideanSpace ℝ (Fin d)

/-- `H²(ℝ^d)` contains states of every mass `m ≥ 0`. -/
theorem exists_M_eq {m : ℝ} (hm : 0 ≤ m) : ∃ U : H2 d, M U = m := by
  let b : ContDiffBump (0 : Rd) := ⟨1, 2, one_pos, one_lt_two⟩
  have hC : ContDiff ℝ ∞ fun x : Rd => ((b x : ℝ) : ℂ) := Complex.ofRealCLM.contDiff.comp b.contDiff
  have hc : HasCompactSupport fun x : Rd => ((b x : ℝ) : ℂ) :=
    b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  set U₀ := ofSchwartz (schwartzOfCompact _ hC hc) with hU₀
  have hM₀ : 0 < M U₀ := by
    rw [hU₀, M, ofSchwartz]
    simp only
    rw [norm_toL2_sq]
    simp only [coe_schwartzOfCompact, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have hcont : Continuous fun x : Rd => b x ^ 2 := b.continuous.pow 2
    have hcs : HasCompactSupport fun x : Rd => b x ^ 2 :=
      b.hasCompactSupport.comp_left (g := fun r : ℝ => r ^ 2) (by simp)
    refine hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero hcs (fun x => sq_nonneg _)
      (x := 0) ?_
    have : b 0 = 1 := b.one_of_mem_closedBall (by simp [b])
    simp [this]
  refine ⟨smul ((Real.sqrt (m / M U₀) : ℝ) : ℂ) U₀, ?_⟩
  rw [M_smul, Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (by positivity)]
  field_simp

end H2

end Sobolev

namespace Sobolev

variable {d : ℕ}

local notation "Rd" => EuclideanSpace ℝ (Fin d)

/-! ### Strong continuity of the dilation group -/

/-- The dilation `f ↦ f_λ` on `L²` for real `λ` (the identity for `λ ≤ 0`). -/
noncomputable def dilR (lam : ℝ) (f : L2 d) : L2 d := if h : 0 < lam then dilL2 h f else f

theorem dilR_of_pos {lam : ℝ} (h : 0 < lam) (f : L2 d) : dilR lam f = dilL2 h f := by
  simp [dilR, h]

/-- For Schwartz `φ`: `∫ \overline{φ_λ} φ → ∫ \overline{φ} φ` as `λ → 1`. -/
theorem tendsto_inner_dilF (φ : SchwartzMap Rd ℂ) :
    Tendsto (fun lam : ℝ => ∫ x, (starRingEnd ℂ) (dilF lam (⇑φ) x) * φ x) (𝓝 1)
      (𝓝 (∫ x, (starRingEnd ℂ) (φ x) * φ x)) := by
  obtain ⟨C, hC⟩ : ∃ C, ∀ x, ‖φ x‖ ≤ C := by
    obtain ⟨C, -, hC⟩ := φ.decay 0 0
    exact ⟨C, fun x => by simpa using hC x⟩
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  refine tendsto_integral_filter_of_dominated_convergence
    (fun x => (2 : ℝ) ^ ((d : ℝ) / 2) * C * ‖φ x‖) ?_ ?_ ?_ ?_
  · refine Eventually.of_forall fun lam => ?_
    have : Continuous fun x : Rd => (starRingEnd ℂ) (dilF lam (⇑φ) x) * φ x := by
      unfold dilF
      exact (Complex.continuous_conj.comp (continuous_const.mul
        (φ.continuous.comp (continuous_const.smul continuous_id)))).mul φ.continuous
    exact this.aestronglyMeasurable
  · filter_upwards [Ioo_mem_nhds (show (0 : ℝ) < 1 by norm_num) (show (1 : ℝ) < 2 by norm_num)]
      with lam hlam
    refine Eventually.of_forall fun x => ?_
    rw [norm_mul, Complex.norm_conj, dilF, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hlam.1.le _)]
    have h1 : lam ^ ((d : ℝ) / 2) ≤ 2 ^ ((d : ℝ) / 2) :=
      Real.rpow_le_rpow hlam.1.le hlam.2.le (by positivity)
    have h2 := hC (lam • x)
    have h4 : lam ^ ((d : ℝ) / 2) * ‖φ (lam • x)‖ ≤ 2 ^ ((d : ℝ) / 2) * C :=
      mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    exact mul_le_mul_of_nonneg_right h4 (norm_nonneg _)
  · exact φ.integrable.norm.const_mul _
  · refine Eventually.of_forall fun x => ?_
    have h1 : Tendsto (fun lam : ℝ => (((lam ^ ((d : ℝ) / 2) : ℝ)) : ℂ)) (𝓝 1) (𝓝 1) := by
      have := (Real.continuousAt_rpow_const 1 ((d : ℝ) / 2) (Or.inl one_ne_zero)).tendsto
      simpa using (Complex.continuous_ofReal.tendsto _).comp this
    have h2 : Tendsto (fun lam : ℝ => φ (lam • x)) (𝓝 1) (𝓝 (φ x)) := by
      have := (φ.continuous.tendsto ((1 : ℝ) • x)).comp
        ((continuous_id.smul continuous_const).tendsto (1 : ℝ))
      simpa using this
    have h3 : Tendsto (fun lam : ℝ => dilF lam (⇑φ) x) (𝓝 1) (𝓝 (φ x)) := by
      unfold dilF
      simpa using h1.mul h2
    exact ((Complex.continuous_conj.tendsto _).comp h3).mul_const (φ x)

theorem tendsto_dilR_schwartz (φ : SchwartzMap Rd ℂ) :
    Tendsto (fun lam => ‖dilR lam (toL2 φ) - toL2 φ‖) (𝓝 1) (𝓝 0) := by
  have hI := tendsto_inner_dilF φ
  have hre : Tendsto (fun lam : ℝ => 2 * ‖toL2 φ‖ ^ 2 -
      2 * (∫ x, (starRingEnd ℂ) (dilF lam (⇑φ) x) * φ x).re) (𝓝 1) (𝓝 0) := by
    have := (((Complex.continuous_re.tendsto _).comp hI).const_mul 2).const_sub
      (2 * ‖toL2 φ‖ ^ 2)
    have e : (∫ x, (starRingEnd ℂ) (φ x) * φ x).re = ‖toL2 φ‖ ^ 2 := by
      rw [← inner_toL2, @norm_sq_eq_re_inner ℂ]
      rfl
    rw [e, sub_self] at this
    exact this
  have heq : ∀ᶠ lam in 𝓝 (1 : ℝ), Real.sqrt (2 * ‖toL2 φ‖ ^ 2 -
      2 * (∫ x, (starRingEnd ℂ) (dilF lam (⇑φ) x) * φ x).re) = ‖dilR lam (toL2 φ) - toL2 φ‖ := by
    filter_upwards [Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with lam hlam
    have hlam' : (0 : ℝ) < lam := hlam
    rw [dilR_of_pos hlam', ← toL2_dilS hlam']
    have h1 := @norm_sub_sq ℂ _ _ _ _ (toL2 (dilS hlam' φ)) (toL2 φ)
    have h2 : ‖toL2 (dilS hlam' φ)‖ = ‖toL2 φ‖ := by rw [toL2_dilS, norm_dilL2]
    have h3 : inner ℂ (toL2 (dilS hlam' φ)) (toL2 φ) =
        ∫ x, (starRingEnd ℂ) (dilF lam (⇑φ) x) * φ x := by
      rw [inner_toL2]
      simp_rw [dilS_apply]
    rw [h2, h3, RCLike.re_to_complex] at h1
    rw [show 2 * ‖toL2 φ‖ ^ 2 - 2 * (∫ x, (starRingEnd ℂ) (dilF lam (⇑φ) x) * φ x).re =
      ‖toL2 (dilS hlam' φ) - toL2 φ‖ ^ 2 by rw [h1]; ring, Real.sqrt_sq (norm_nonneg _)]
  have := (Real.continuous_sqrt.tendsto 0).comp hre
  rw [Real.sqrt_zero] at this
  exact this.congr' heq

/-- `f_λ → f` in `L²` as `λ → 1`, for every `f` that is an `L²` limit of Schwartz functions. -/
theorem tendsto_dilR {f : L2 d} {φ : ℕ → SchwartzMap Rd ℂ}
    (hf : Tendsto (fun n => toL2 (φ n)) atTop (𝓝 f)) :
    Tendsto (fun lam => ‖dilR lam f - f‖) (𝓝 1) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro δ hδ
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hf) (δ / 3) (by positivity)
  have hN' := hN N le_rfl
  rw [dist_eq_norm] at hN'
  have hA := (Metric.tendsto_nhds.1 (tendsto_dilR_schwartz (φ N))) (δ / 3) (by positivity)
  filter_upwards [hA, Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with lam hlam hpos
  have hpos' : (0 : ℝ) < lam := hpos
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at hlam ⊢
  rw [dilR_of_pos hpos'] at hlam ⊢
  have h1 : dilL2 hpos' f - f = dilL2 hpos' (f - toL2 (φ N)) + (dilL2 hpos' (toL2 (φ N)) -
      toL2 (φ N)) + (toL2 (φ N) - f) := by
    rw [dilL2_sub]
    abel
  calc ‖dilL2 hpos' f - f‖ ≤ ‖dilL2 hpos' (f - toL2 (φ N))‖ + ‖dilL2 hpos' (toL2 (φ N)) -
        toL2 (φ N)‖ + ‖toL2 (φ N) - f‖ := by
          rw [h1]
          exact norm_add₃_le
    _ = ‖toL2 (φ N) - f‖ + ‖dilL2 hpos' (toL2 (φ N)) - toL2 (φ N)‖ + ‖toL2 (φ N) - f‖ := by
          rw [norm_dilL2, norm_sub_rev f]
    _ < δ := by linarith

theorem norm_smul_dil_sub_le {lam : ℝ} (hlam : 0 < lam) (r : ℝ) (g : L2 d) :
    ‖((r : ℝ) : ℂ) • dilL2 hlam g - g‖ ≤ |r - 1| * ‖g‖ + ‖dilL2 hlam g - g‖ := by
  have e : ((r : ℝ) : ℂ) • dilL2 hlam g - g =
      (((r - 1 : ℝ)) : ℂ) • dilL2 hlam g + (dilL2 hlam g - g) := by
    rw [Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul]
    abel
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, norm_dilL2]

namespace H2

/-- The `H²` distance `‖u − v‖₂ + Σᵢ‖∂ᵢu − ∂ᵢv‖₂ + ‖Δu − Δv‖₂` (equivalent to the `H²` norm of
`u − v`). -/
noncomputable def distH2 (U V : H2 d) : ℝ :=
  ‖U.val - V.val‖ + ∑ i, ‖U.grad i - V.grad i‖ + ‖U.lap - V.lap‖

theorem distH2_nonneg (U V : H2 d) : 0 ≤ distH2 U V := by
  unfold distH2
  positivity

/-- The dilation `ψ ↦ ψ_λ` on `H²` for real `λ` (the identity for `λ ≤ 0`). -/
noncomputable def dilR (lam : ℝ) (U : H2 d) : H2 d := if h : 0 < lam then dil h U else U

theorem dilR_of_pos {lam : ℝ} (h : 0 < lam) (U : H2 d) : dilR lam U = dil h U := by
  simp [dilR, h]

/-- **Strong continuity of the dilation group on `H²(ℝ^d)`:** `‖ψ_λ − ψ‖_{H²} → 0` as
`λ → 1`. -/
theorem tendsto_distH2_dilR (U : H2 d) :
    Tendsto (fun lam => distH2 (dilR lam U) U) (𝓝 1) (𝓝 0) := by
  obtain ⟨φ, h0, h1, h2⟩ := U.approx
  have hv := Sobolev.tendsto_dilR h0
  have hg := fun i => Sobolev.tendsto_dilR (h1 i)
  have hl := Sobolev.tendsto_dilR h2
  have ha1 : Tendsto (fun lam : ℝ => |lam - 1|) (𝓝 1) (𝓝 0) := by
    have hc : Continuous fun lam : ℝ => |lam - 1| := by fun_prop
    simpa using hc.tendsto 1
  have ha2 : Tendsto (fun lam : ℝ => |lam ^ 2 - 1|) (𝓝 1) (𝓝 0) := by
    have hc : Continuous fun lam : ℝ => |lam ^ 2 - 1| := by fun_prop
    simpa using hc.tendsto 1
  have hb : Tendsto (fun lam : ℝ => ‖Sobolev.dilR lam U.val - U.val‖ +
      ∑ i, (|lam - 1| * ‖U.grad i‖ + ‖Sobolev.dilR lam (U.grad i) - U.grad i‖) +
      (|lam ^ 2 - 1| * ‖U.lap‖ + ‖Sobolev.dilR lam U.lap - U.lap‖)) (𝓝 1) (𝓝 0) := by
    have := (hv.add (tendsto_finset_sum (Finset.univ : Finset (Fin d))
      fun i _ => (ha1.mul_const ‖U.grad i‖).add (hg i))).add ((ha2.mul_const ‖U.lap‖).add hl)
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hb
    (Eventually.of_forall fun lam => distH2_nonneg _ _) ?_
  filter_upwards [Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with lam hlam
  have hlam' : (0 : ℝ) < lam := hlam
  rw [dilR_of_pos hlam']
  simp only [Sobolev.dilR_of_pos hlam']
  unfold distH2
  simp only [dil]
  refine add_le_add (add_le_add le_rfl (Finset.sum_le_sum fun i _ => ?_)) ?_
  · exact norm_smul_dil_sub_le hlam' lam _
  · exact norm_smul_dil_sub_le hlam' (lam ^ 2) _

end H2

end Sobolev

namespace Curvature

open Sobolev

variable {d : ℕ} {c₁ c₂ ε α : ℝ}

local notation "Rd" => EuclideanSpace ℝ (Fin d)

/-- The curvature term `∫ F(|ψ|²)|Δψ|²`. -/
noncomputable def Wc (ε α : ℝ) (U : H2 d) : ℝ := ∫ x, F ε α (‖U.val x‖ ^ 2) * ‖U.lap x‖ ^ 2

/-- The energy `E(ψ) = c₁ ∫|∇ψ|² + c₂ ∫ F(|ψ|²)|Δψ|²` on `H²(ℝ^d; ℂ)`. -/
noncomputable def Ec (c₁ c₂ ε α : ℝ) (U : H2 d) : ℝ := c₁ * U.K + c₂ * Wc ε α U

/-- `I_d(m) = inf {E(ψ) : ψ ∈ H²(ℝ^d; ℂ), ‖ψ‖²₂ = m}`. -/
noncomputable def Id (c₁ c₂ ε α : ℝ) (d : ℕ) (m : ℝ) : ℝ :=
  sInf (Ec c₁ c₂ ε α '' {U : H2 d | U.M = m})

theorem aestronglyMeasurable_curv (U : H2 d) (G : ℝ → ℝ) (hG : Measurable G) :
    AEStronglyMeasurable (fun x => G (‖U.val x‖ ^ 2) * ‖U.lap x‖ ^ 2) volume :=
  (hG.comp_aemeasurable ((Lp.aestronglyMeasurable U.val).aemeasurable.norm.pow_const 2)
    ).aestronglyMeasurable.mul ((Lp.aestronglyMeasurable U.lap).norm.pow 2)

/-- The curvature integrand is integrable: the energy is finite on `H²(ℝ^d)`. -/
theorem integrable_curv (hε : 0 < ε) (hα : 0 ≤ α) (U : H2 d) :
    Integrable fun x => F ε α (‖U.val x‖ ^ 2) * ‖U.lap x‖ ^ 2 := by
  refine ((integrable_sq_L2 U.lap).const_mul (MF ε α)).mono'
    (aestronglyMeasurable_curv U _ measurable_F) (Eventually.of_forall fun x => ?_)
  rw [Real.norm_of_nonneg (mul_nonneg (F_nonneg (sq_nonneg _)) (sq_nonneg _))]
  exact mul_le_mul_of_nonneg_right (F_le hε hα (sq_nonneg _)) (sq_nonneg _)

theorem Wc_nonneg (U : H2 d) : 0 ≤ Wc ε α U :=
  integral_nonneg fun _ => mul_nonneg (F_nonneg (sq_nonneg _)) (sq_nonneg _)

/-- `∫ F(|ψ|²)|Δψ|² ≤ M_F ‖Δψ‖²`. -/
theorem Wc_le (hε : 0 < ε) (hα : 0 ≤ α) (U : H2 d) : Wc ε α U ≤ MF ε α * U.D := by
  rw [H2.D, normSq_eq_integral, ← integral_const_mul]
  exact integral_mono (integrable_curv hε hα U) ((integrable_sq_L2 U.lap).const_mul _)
    fun x => mul_le_mul_of_nonneg_right (F_le hε hα (sq_nonneg _)) (sq_nonneg _)

theorem Ec_nonneg (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (U : H2 d) : 0 ≤ Ec c₁ c₂ ε α U := by
  unfold Ec
  have := H2.K_nonneg U
  have := Wc_nonneg (ε := ε) (α := α) U
  positivity

theorem Ec_ge (hc₂ : 0 ≤ c₂) (U : H2 d) : c₁ * U.K ≤ Ec c₁ c₂ ε α U := by
  unfold Ec
  have := Wc_nonneg (ε := ε) (α := α) U
  nlinarith

/-- **Positivity:** `E(ψ) > 0` for every nonzero `ψ ∈ H²(ℝ^d)`, `d ≥ 1`. -/
theorem Ec_pos [NeZero d] (hc₁ : 0 < c₁) (hc₂ : 0 ≤ c₂) {U : H2 d} (hU : U.val ≠ 0) :
    0 < Ec c₁ c₂ ε α U := by
  have hM : U.M ≠ 0 := by
    rw [H2.M]
    exact pow_ne_zero 2 (norm_ne_zero_iff.2 hU)
  have hK := H2.K_pos U hM
  have := Ec_ge (c₁ := c₁) (ε := ε) (α := α) hc₂ U
  nlinarith

/-- `E(ψ) = 0 ⟺ ψ = 0` (`d ≥ 1`). -/
theorem Ec_eq_zero_iff [NeZero d] (hc₁ : 0 < c₁) (hc₂ : 0 ≤ c₂) (U : H2 d) :
    Ec c₁ c₂ ε α U = 0 ↔ U.val = 0 := by
  constructor
  · intro h
    by_contra hU
    have := Ec_pos (ε := ε) (α := α) hc₁ hc₂ hU
    linarith
  · intro h
    have hK : U.K = 0 := by
      have := H2.K_le U
      rw [h, norm_zero, zero_mul] at this
      exact le_antisymm this (H2.K_nonneg U)
    have hW : Wc ε α U = 0 := by
      unfold Wc
      refine integral_eq_zero_of_ae ?_
      have h0 : (U.val : Rd → ℂ) =ᵐ[volume] 0 := by rw [h]; exact Lp.coeFn_zero ℂ 2 volume
      filter_upwards [h0] with x hx
      simp [hx, F_zero]
    unfold Ec
    rw [hK, hW]
    ring

/-- `Φ_ψ(λ) = ∫ F(λ^d|ψ|²)|Δψ|²`. -/
noncomputable def Phi (ε α : ℝ) (U : H2 d) (lam : ℝ) : ℝ :=
  ∫ y, F ε α (lam ^ d * ‖U.val y‖ ^ 2) * ‖U.lap y‖ ^ 2

/-- The energy along the dilation orbit, `e_ψ(λ) = c₁λ²‖∇ψ‖² + c₂λ⁴Φ_ψ(λ)`. -/
noncomputable def eDil (c₁ c₂ ε α : ℝ) (U : H2 d) (lam : ℝ) : ℝ :=
  c₁ * lam ^ 2 * U.K + c₂ * lam ^ 4 * Phi ε α U lam

/-- Exact scaling of the curvature term: `∫ F(|ψ_λ|²)|Δψ_λ|² = λ⁴ ∫ F(λ^d|ψ|²)|Δψ|²`. -/
theorem Wc_dil {lam : ℝ} (hlam : 0 < lam) (U : H2 d) :
    Wc ε α (H2.dil hlam U) = lam ^ 4 * Phi ε α U lam := by
  unfold Wc Phi
  have h : (fun x => F ε α (‖(H2.dil hlam U).val x‖ ^ 2) * ‖(H2.dil hlam U).lap x‖ ^ 2) =ᵐ[volume]
      fun x => lam ^ 4 * lam ^ d * (F ε α (lam ^ d * ‖(U.val : Rd → ℂ) (lam • x)‖ ^ 2) *
        ‖(U.lap : Rd → ℂ) (lam • x)‖ ^ 2) := by
    filter_upwards [coeFn_dilL2 hlam U.val, coeFn_dilL2 hlam U.lap,
      Lp.coeFn_smul (((lam ^ 2 : ℝ)) : ℂ) (dilL2 hlam U.lap)] with x h1 h2 h3
    simp only [H2.dil]
    rw [h1, h3, Pi.smul_apply, h2, norm_smul, mul_pow, norm_dilF_sq hlam, norm_dilF_sq hlam,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < lam ^ 2)]
    ring
  rw [integral_congr_ae h, integral_const_mul, integral_comp_dil hlam
    (fun y => F ε α (lam ^ d * ‖(U.val : Rd → ℂ) y‖ ^ 2) * ‖(U.lap : Rd → ℂ) y‖ ^ 2)]
  field_simp

/-- **Exact scaling formula:** `E(ψ_λ) = c₁λ²‖∇ψ‖² + c₂λ⁴∫F(λ^d|ψ|²)|Δψ|²`. -/
theorem Ec_dil {lam : ℝ} (hlam : 0 < lam) (U : H2 d) :
    Ec c₁ c₂ ε α (H2.dil hlam U) = eDil c₁ c₂ ε α U lam := by
  unfold Ec eDil
  rw [H2.K_dil, Wc_dil]
  ring

theorem eDil_one (U : H2 d) : eDil c₁ c₂ ε α U 1 = Ec c₁ c₂ ε α U := by
  unfold eDil Ec Phi Wc
  simp

theorem bddBelow_Ec (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (m : ℝ) :
    BddBelow (Ec c₁ c₂ ε α '' {U : H2 d | U.M = m}) :=
  ⟨0, by rintro _ ⟨U, -, rfl⟩; exact Ec_nonneg hc₁ hc₂ U⟩

/-- `I_d(m) = 0` for every `m > 0` and `d ≥ 1`. -/
theorem Id_eq_zero (hc₁ : 0 < c₁) (hc₂ : 0 ≤ c₂) (hε : 0 < ε) (hα : 0 ≤ α)
    {m : ℝ} (hm : 0 < m) : Id c₁ c₂ ε α d m = 0 := by
  obtain ⟨U, hU⟩ := H2.exists_M_eq (d := d) hm.le
  have hne : (Ec c₁ c₂ ε α '' {U : H2 d | U.M = m}).Nonempty := ⟨_, U, hU, rfl⟩
  apply le_antisymm
  · have hle : ∀ n : ℕ, Id c₁ c₂ ε α d m ≤
        c₁ * (1 / ((n : ℝ) + 1)) ^ 2 * U.K + c₂ * (MF ε α * ((1 / ((n : ℝ) + 1)) ^ 4 * U.D)) := by
      intro n
      have hlam : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      have h1 : Id c₁ c₂ ε α d m ≤ Ec c₁ c₂ ε α (H2.dil hlam U) :=
        csInf_le (bddBelow_Ec hc₁.le hc₂ m) ⟨_, (H2.M_dil hlam U).trans hU, rfl⟩
      have h2 : Ec c₁ c₂ ε α (H2.dil hlam U) ≤
          c₁ * (1 / ((n : ℝ) + 1)) ^ 2 * U.K + c₂ * (MF ε α * ((1 / ((n : ℝ) + 1)) ^ 4 * U.D)) := by
        unfold Ec
        rw [H2.K_dil]
        have h3 := Wc_le (ε := ε) (α := α) hε hα (H2.dil hlam U)
        rw [H2.D_dil] at h3
        have := mul_le_mul_of_nonneg_left h3 hc₂
        linarith
      exact h1.trans h2
    have hlim : Tendsto (fun n : ℕ => c₁ * (1 / ((n : ℝ) + 1)) ^ 2 * U.K +
        c₂ * (MF ε α * ((1 / ((n : ℝ) + 1)) ^ 4 * U.D))) atTop (𝓝 0) := by
      have h := tendsto_one_div_add_atTop_nhds_zero_nat
      have := (((h.pow 2).const_mul c₁).mul_const U.K).add
        ((((h.pow 4).mul_const U.D).const_mul (MF ε α)).const_mul c₂)
      simpa using this
    exact ge_of_tendsto' hlim hle
  · exact le_csInf hne (by rintro _ ⟨V, -, rfl⟩; exact Ec_nonneg hc₁.le hc₂ V)

theorem val_ne_zero_of_M {U : H2 d} {m : ℝ} (hm : 0 < m) (hU : U.M = m) : U.val ≠ 0 := by
  intro h
  rw [H2.M, h, norm_zero] at hU
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hU
  linarith

/-- **Theorem (positive-mass whole-space nonattainment).**  For every `d ≥ 1` and `m > 0`: the
energy is finite (the curvature integrand is integrable) and nonnegative on `H²(ℝ^d; ℂ)`,
strictly positive at every nonzero `ψ`, `I_d(m) = 0`, and the set of constrained minimizers is
empty. -/
theorem global_nonattainment (hd : 1 ≤ d) (hc₁ : 0 < c₁) (hc₂ : 0 ≤ c₂) (hε : 0 < ε)
    (hα : 0 ≤ α) {m : ℝ} (hm : 0 < m) :
    (∀ U : H2 d, Integrable (fun x => F ε α (‖U.val x‖ ^ 2) * ‖U.lap x‖ ^ 2) ∧
      0 ≤ Ec c₁ c₂ ε α U) ∧
    (∀ U : H2 d, U.val ≠ 0 → 0 < Ec c₁ c₂ ε α U) ∧
    Id c₁ c₂ ε α d m = 0 ∧
    {U : H2 d | U.M = m ∧ ∀ V : H2 d, V.M = m → Ec c₁ c₂ ε α U ≤ Ec c₁ c₂ ε α V} = ∅ := by
  haveI : NeZero d := ⟨by omega⟩
  have hI := Id_eq_zero hc₁ hc₂ hε hα (ε := ε) (α := α) (d := d) hm
  refine ⟨fun U => ⟨integrable_curv hε hα U, Ec_nonneg hc₁.le hc₂ U⟩,
    fun U hU => Ec_pos hc₁ hc₂ hU, hI, ?_⟩
  refine Set.eq_empty_iff_forall_notMem.2 fun U ⟨hUm, hUmin⟩ => ?_
  obtain ⟨V, hV⟩ := H2.exists_M_eq (d := d) hm.le
  have hle : Ec c₁ c₂ ε α U ≤ Id c₁ c₂ ε α d m :=
    le_csInf ⟨_, V, hV, rfl⟩ (by rintro _ ⟨W, hW, rfl⟩; exact hUmin W hW)
  have hpos := Ec_pos (ε := ε) (α := α) hc₁ hc₂ (val_ne_zero_of_M hm hUm)
  linarith

/-! ### Strict spreading for `1 ≤ d ≤ 4` -/

/-- The virial weight `G(s) = 4F(s) + d s F'(s)`. -/
noncomputable def Gv (ε α : ℝ) (d : ℕ) (s : ℝ) : ℝ := 4 * F ε α s + d * s * F' ε α s

/-- `e_ψ'(λ) = 2c₁λ‖∇ψ‖² + c₂λ³∫(4F(s) + d s F'(s))|Δψ|²`, `s = λ^d|ψ|²`. -/
noncomputable def eDil' (c₁ c₂ ε α : ℝ) (U : H2 d) (lam : ℝ) : ℝ :=
  2 * c₁ * lam * U.K + c₂ * lam ^ 3 * ∫ y, Gv ε α d (lam ^ d * ‖U.val y‖ ^ 2) * ‖U.lap y‖ ^ 2

theorem measurable_Gv : Measurable (Gv ε α d) := by
  unfold Gv
  exact (measurable_const.mul measurable_F).add
    ((measurable_const.mul measurable_id).mul measurable_F')

theorem abs_Gv_le (hε : 0 < ε) (hα : 0 ≤ α) {s : ℝ} (hs : 0 ≤ s) :
    |Gv ε α d s| ≤ 4 * MF ε α + d * (MF ε α + 4 * α) := by
  unfold Gv
  have h1 := F_le (α := α) hε hα hs
  have h2 := abs_mul_F'_le (α := α) hε hα hs
  have h0 := F_nonneg (ε := ε) (α := α) hs
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  calc |4 * F ε α s + d * s * F' ε α s| ≤ |4 * F ε α s| + |d * s * F' ε α s| := abs_add _ _
    _ = 4 * F ε α s + d * |s * F' ε α s| := by
        rw [abs_of_nonneg (by positivity), mul_assoc, abs_mul, abs_of_nonneg hd]
    _ ≤ 4 * MF ε α + d * (MF ε α + 4 * α) := by gcongr

theorem continuousAt_Gv (hε : 0 < ε) {s : ℝ} (hs : 0 ≤ s) : ContinuousAt (Gv ε α d) s := by
  unfold Gv
  exact (continuousAt_const.mul (hasDerivAt_F (α := α) hε hs).continuousAt).add
    ((continuousAt_const.mul continuousAt_id).mul (continuousAt_F' hε hs))

theorem integrable_curv_scaled (hε : 0 < ε) (hα : 0 ≤ α) (U : H2 d) {c : ℝ} (hc : 0 ≤ c) :
    Integrable fun y => F ε α (c * ‖U.val y‖ ^ 2) * ‖U.lap y‖ ^ 2 := by
  refine ((integrable_sq_L2 U.lap).const_mul (MF ε α)).mono'
    (aestronglyMeasurable_curv U (fun s => F ε α (c * s))
      (measurable_F.comp (measurable_const.mul measurable_id))) (Eventually.of_forall fun x => ?_)
  have hs : 0 ≤ c * ‖U.val x‖ ^ 2 := by positivity
  rw [Real.norm_of_nonneg (mul_nonneg (F_nonneg hs) (sq_nonneg _))]
  exact mul_le_mul_of_nonneg_right (F_le hε hα hs) (sq_nonneg _)

/-- `|F'(λ^dρ) · dλ^{d−1}ρ| ≤ d(M_F + 4α)/λ`. -/
theorem abs_deriv_term_le (hε : 0 < ε) (hα : 0 ≤ α) (hd : 1 ≤ d) {lam ρ : ℝ} (hlam : 0 < lam)
    (hρ : 0 ≤ ρ) :
    |F' ε α (lam ^ d * ρ) * (d * lam ^ (d - 1) * ρ)| ≤ d * (MF ε α + 4 * α) / lam := by
  have hpow : lam ^ d = lam ^ (d - 1) * lam := by
    rw [← pow_succ, Nat.sub_add_cancel hd]
  have key : F' ε α (lam ^ d * ρ) * (d * lam ^ (d - 1) * ρ) =
      d * ((lam ^ d * ρ) * F' ε α (lam ^ d * ρ)) / lam := by
    rw [hpow]
    field_simp
  have hs : 0 ≤ lam ^ d * ρ := by positivity
  have h2 := abs_mul_F'_le (α := α) hε hα hs
  rw [key, abs_div, abs_mul, abs_of_nonneg (Nat.cast_nonneg d), abs_of_pos hlam]
  gcongr

/-- Differentiation under the integral sign: `Φ_ψ'(λ) = ∫ F'(λ^dρ) dλ^{d−1}ρ |Δψ|²`. -/
theorem hasDerivAt_Phi (hε : 0 < ε) (hα : 0 ≤ α) (hd : 1 ≤ d) (U : H2 d) {lam₀ : ℝ}
    (hlam₀ : 0 < lam₀) :
    Integrable (fun y => F' ε α (lam₀ ^ d * ‖U.val y‖ ^ 2) *
        (d * lam₀ ^ (d - 1) * ‖U.val y‖ ^ 2) * ‖U.lap y‖ ^ 2) ∧
      HasDerivAt (Phi ε α U) (∫ y, F' ε α (lam₀ ^ d * ‖U.val y‖ ^ 2) *
        (d * lam₀ ^ (d - 1) * ‖U.val y‖ ^ 2) * ‖U.lap y‖ ^ 2) lam₀ := by
  have hball : ∀ lam ∈ Metric.ball lam₀ (lam₀ / 2), lam₀ / 2 < lam := by
    intro lam hl
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hl
    linarith
  have hmeasG : Measurable fun s => F' ε α (lam₀ ^ d * s) * (d * lam₀ ^ (d - 1) * s) :=
    (measurable_F'.comp (measurable_const.mul measurable_id)).mul
      (measurable_const.mul measurable_id)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (x₀ := lam₀)
    (F := fun lam y => F ε α (lam ^ d * ‖U.val y‖ ^ 2) * ‖U.lap y‖ ^ 2)
    (F' := fun lam y => F' ε α (lam ^ d * ‖U.val y‖ ^ 2) * (d * lam ^ (d - 1) * ‖U.val y‖ ^ 2) *
      ‖U.lap y‖ ^ 2)
    (bound := fun y => 2 * d * (MF ε α + 4 * α) / lam₀ * ‖U.lap y‖ ^ 2)
    (half_pos hlam₀)
    (Eventually.of_forall fun lam => aestronglyMeasurable_curv U (fun s => F ε α (lam ^ d * s))
      (measurable_F.comp (measurable_const.mul measurable_id)))
    (integrable_curv_scaled hε hα U (by positivity))
    (aestronglyMeasurable_curv U _ hmeasG)
    (Eventually.of_forall fun y lam hl => ?_)
    ((integrable_sq_L2 U.lap).const_mul _)
    (Eventually.of_forall fun y lam hl => ?_)
  · exact h
  · have hlam := hball lam hl
    have hlpos : 0 < lam := by linarith
    have h1 := abs_deriv_term_le (α := α) hε hα hd hlpos (sq_nonneg ‖U.val y‖)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg ‖U.lap y‖)]
    refine mul_le_mul_of_nonneg_right (h1.trans ?_) (sq_nonneg _)
    rw [div_le_div_iff₀ hlpos hlam₀]
    have : (0 : ℝ) ≤ d * (MF ε α + 4 * α) := by
      have := MF_pos (ε := ε) (α := α)
      positivity
    nlinarith
  · have hlpos : 0 < lam := by linarith [hball lam hl]
    have hσ : 0 ≤ lam ^ d * ‖U.val y‖ ^ 2 := by positivity
    have h1 : HasDerivAt (fun l : ℝ => l ^ d * ‖U.val y‖ ^ 2) (d * lam ^ (d - 1) * ‖U.val y‖ ^ 2)
        lam := (hasDerivAt_pow d lam).mul_const _
    exact ((hasDerivAt_F hε hσ).comp lam h1).mul_const _

/-- `∫ G(λ^dρ)|Δψ|² = 4Φ_ψ(λ) + λΦ_ψ'(λ)`. -/
theorem integral_Gv_eq (hε : 0 < ε) (hα : 0 ≤ α) (hd : 1 ≤ d) (U : H2 d) {lam : ℝ}
    (hlam : 0 < lam) :
    ∫ y, Gv ε α d (lam ^ d * ‖U.val y‖ ^ 2) * ‖U.lap y‖ ^ 2 =
      4 * Phi ε α U lam + lam * ∫ y, F' ε α (lam ^ d * ‖U.val y‖ ^ 2) *
        (d * lam ^ (d - 1) * ‖U.val y‖ ^ 2) * ‖U.lap y‖ ^ 2 := by
  have hint := (hasDerivAt_Phi hε hα hd U hlam).1
  have hpow : lam ^ d = lam ^ (d - 1) * lam := by
    rw [← pow_succ, Nat.sub_add_cancel hd]
  have hpt : (fun y => Gv ε α d (lam ^ d * ‖U.val y‖ ^ 2) * ‖U.lap y‖ ^ 2) =
      fun y => 4 * (F ε α (lam ^ d * ‖U.val y‖ ^ 2) * ‖U.lap y‖ ^ 2) +
        lam * (F' ε α (lam ^ d * ‖U.val y‖ ^ 2) * (d * lam ^ (d - 1) * ‖U.val y‖ ^ 2) *
          ‖U.lap y‖ ^ 2) := by
    funext y
    unfold Gv
    rw [hpow]
    ring
  rw [hpt, integral_add ((integrable_curv_scaled hε hα U (by positivity)).const_mul 4)
    (hint.const_mul lam), integral_const_mul, integral_const_mul]
  rfl

/-- **Derivative along the dilation orbit.** -/
theorem hasDerivAt_eDil (hε : 0 < ε) (hα : 0 ≤ α) (hd : 1 ≤ d) (U : H2 d) {lam : ℝ}
    (hlam : 0 < lam) : HasDerivAt (eDil c₁ c₂ ε α U) (eDil' c₁ c₂ ε α U lam) lam := by
  have hP := (hasDerivAt_Phi hε hα hd U hlam).2
  have h1 : HasDerivAt (fun l : ℝ => c₁ * l ^ 2 * U.K) (c₁ * (2 * lam) * U.K) lam := by
    have := ((hasDerivAt_pow 2 lam).const_mul c₁).mul_const U.K
    simpa using this
  have h2 : HasDerivAt (fun l : ℝ => c₂ * l ^ 4 * Phi ε α U l)
      (c₂ * (4 * lam ^ 3) * Phi ε α U lam + c₂ * lam ^ 4 * ∫ y, F' ε α (lam ^ d * ‖U.val y‖ ^ 2) *
        (d * lam ^ (d - 1) * ‖U.val y‖ ^ 2) * ‖U.lap y‖ ^ 2) lam := by
    have := (((hasDerivAt_pow 4 lam).const_mul c₂)).mul hP
    simpa using this
  have := h1.add h2
  unfold eDil eDil'
  convert this using 1
  rw [integral_Gv_eq hε hα hd U hlam]
  ring

theorem continuousOn_eDil' (hε : 0 < ε) (hα : 0 ≤ α) (U : H2 d) :
    ContinuousOn (eDil' c₁ c₂ ε α U) (Ioi 0) := by
  have hI : ContinuousOn (fun lam : ℝ => ∫ y, Gv ε α d (lam ^ d * ‖U.val y‖ ^ 2) * ‖U.lap y‖ ^ 2)
      (Ioi 0) := by
    refine continuousOn_of_dominated (bound := fun y =>
      (4 * MF ε α + d * (MF ε α + 4 * α)) * ‖U.lap y‖ ^ 2)
      (fun lam _ => aestronglyMeasurable_curv U (fun s => Gv ε α d (lam ^ d * s))
        (measurable_Gv.comp (measurable_const.mul measurable_id)))
      (fun lam hlam => Eventually.of_forall fun y => ?_)
      ((integrable_sq_L2 U.lap).const_mul _) (Eventually.of_forall fun y => ?_)
    · have hlam' : (0 : ℝ) < lam := hlam
      have hs : 0 ≤ lam ^ d * ‖U.val y‖ ^ 2 := by positivity
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg ‖U.lap y‖)]
      exact mul_le_mul_of_nonneg_right (abs_Gv_le hε hα hs) (sq_nonneg _)
    · intro lam hlam
      have hlam' : (0 : ℝ) < lam := hlam
      have hs : 0 ≤ lam ^ d * ‖U.val y‖ ^ 2 := by positivity
      have hc : ContinuousAt (fun l : ℝ => l ^ d * ‖U.val y‖ ^ 2) lam :=
        ((continuous_pow d).mul continuous_const).continuousAt
      exact ((ContinuousAt.comp (f := fun l : ℝ => l ^ d * ‖U.val y‖ ^ 2)
        (continuousAt_Gv (α := α) (d := d) hε hs) hc).mul continuousAt_const).continuousWithinAt
  unfold eDil'
  exact ((continuousOn_const.mul continuousOn_id).mul continuousOn_const).add
    ((continuousOn_const.mul (continuousOn_id.pow 3)).mul hI)

/-- **Log-derivative bound:** `λ e_ψ'(λ) ≥ 2c₁λ²‖∇ψ‖²`. -/
theorem log_deriv_ge (hε : 0 < ε) (hα : 0 ≤ α) (hd4 : d ≤ 4) (hc₂ : 0 ≤ c₂) (U : H2 d)
    {lam : ℝ} (hlam : 0 < lam) :
    2 * c₁ * lam ^ 2 * U.K ≤ lam * eDil' c₁ c₂ ε α U lam := by
  have hI : 0 ≤ ∫ y, Gv ε α d (lam ^ d * ‖U.val y‖ ^ 2) * ‖U.lap y‖ ^ 2 :=
    integral_nonneg fun y => mul_nonneg (virial_nonneg hε hα hd4 (by positivity)) (sq_nonneg _)
  unfold eDil'
  have : 0 ≤ lam * (c₂ * lam ^ 3 * ∫ y, Gv ε α d (lam ^ d * ‖U.val y‖ ^ 2) * ‖U.lap y‖ ^ 2) := by
    positivity
  nlinarith

theorem eDil'_pos (hd1 : 1 ≤ d) (hd4 : d ≤ 4) (hc₁ : 0 < c₁) (hc₂ : 0 ≤ c₂) (hε : 0 < ε)
    (hα : 0 ≤ α) {U : H2 d} (hU : U.val ≠ 0) {lam : ℝ} (hlam : 0 < lam) :
    0 < eDil' c₁ c₂ ε α U lam := by
  haveI : NeZero d := ⟨by omega⟩
  have hM : U.M ≠ 0 := by
    rw [H2.M]
    exact pow_ne_zero 2 (norm_ne_zero_iff.2 hU)
  have hK := H2.K_pos U hM
  have h := log_deriv_ge (c₁ := c₁) hε hα hd4 hc₂ U hlam
  have : 0 < 2 * c₁ * lam ^ 2 * U.K := by positivity
  have h2 : 0 < lam * eDil' c₁ c₂ ε α U lam := by linarith
  exact pos_of_mul_pos_right h2 hlam.le

/-- **Theorem (strict spreading, `1 ≤ d ≤ 4`).**  For nonzero `ψ ∈ H²(ℝ^d; ℂ)`, the energy along
the mass-preserving dilation orbit, `λ ↦ E(ψ_λ)` (`= e_ψ(λ)` for `λ > 0`), is continuously
differentiable and strictly increasing on `(0, ∞)`; in particular `E(ψ_λ) < E(ψ)` for
`0 < λ < 1`. -/
theorem strict_spreading (hd1 : 1 ≤ d) (hd4 : d ≤ 4) (hc₁ : 0 < c₁) (hc₂ : 0 ≤ c₂) (hε : 0 < ε)
    (hα : 0 ≤ α) {U : H2 d} (hU : U.val ≠ 0) :
    (∀ lam (hlam : 0 < lam), Ec c₁ c₂ ε α (H2.dil hlam U) = eDil c₁ c₂ ε α U lam) ∧
    ContDiffOn ℝ 1 (eDil c₁ c₂ ε α U) (Ioi 0) ∧
    StrictMonoOn (eDil c₁ c₂ ε α U) (Ioi 0) ∧
    ∀ lam (hlam : 0 < lam), lam < 1 → Ec c₁ c₂ ε α (H2.dil hlam U) < Ec c₁ c₂ ε α U := by
  have hderiv : ∀ lam ∈ Ioi (0 : ℝ), HasDerivAt (eDil c₁ c₂ ε α U) (eDil' c₁ c₂ ε α U lam) lam :=
    fun lam hlam => hasDerivAt_eDil hε hα hd1 U hlam
  have hcont : ContinuousOn (eDil c₁ c₂ ε α U) (Ioi 0) :=
    fun lam hlam => (hderiv lam hlam).continuousAt.continuousWithinAt
  have hmono : StrictMonoOn (eDil c₁ c₂ ε α U) (Ioi 0) := by
    refine strictMonoOn_of_deriv_pos (convex_Ioi 0) hcont fun lam hlam => ?_
    rw [interior_Ioi] at hlam
    rw [(hderiv lam hlam).deriv]
    exact eDil'_pos hd1 hd4 hc₁ hc₂ hε hα hU hlam
  refine ⟨fun lam hlam => Ec_dil hlam U, ?_, hmono, fun lam hlam hlt => ?_⟩
  · rw [show (1 : WithTop ℕ∞) = 0 + 1 by norm_num, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
    refine ⟨fun lam hlam => (hderiv lam hlam).differentiableAt.differentiableWithinAt,
      by simp, ?_⟩
    rw [contDiffOn_zero]
    exact (continuousOn_eDil' hε hα U).congr fun lam hlam => (hderiv lam hlam).deriv
  · rw [Ec_dil hlam U, ← eDil_one]
    exact hmono hlam (Set.mem_Ioi.2 (one_pos : (0 : ℝ) < 1)) hlt

/-- **Corollary (no local constrained minimizer, `1 ≤ d ≤ 4`).**  For every `m > 0`, every
`ψ ∈ 𝒜_m` and every `δ > 0` there is `φ ∈ 𝒜_m` with `‖φ − ψ‖_{H²} < δ` and `E(φ) < E(ψ)`: `E`
restricted to `𝒜_m` has no local minimizer in the `H²` topology. -/
theorem no_local_minimizer (hd1 : 1 ≤ d) (hd4 : d ≤ 4) (hc₁ : 0 < c₁) (hc₂ : 0 ≤ c₂)
    (hε : 0 < ε) (hα : 0 ≤ α) {m : ℝ} (hm : 0 < m) {U : H2 d} (hU : U.M = m) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ V : H2 d, V.M = m ∧ H2.distH2 V U < δ ∧ Ec c₁ c₂ ε α V < Ec c₁ c₂ ε α U := by
  have h1 : ∀ᶠ lam in 𝓝[<] (1 : ℝ), H2.distH2 (H2.dilR lam U) U < δ :=
    nhdsWithin_le_nhds ((tendsto_order.1 (H2.tendsto_distH2_dilR U)).2 δ hδ)
  have h2 : ∀ᶠ lam in 𝓝[<] (1 : ℝ), lam ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsLT (by norm_num)
  obtain ⟨lam, hl1, hl2⟩ := (h1.and h2).exists
  have hlam : 0 < lam := hl2.1
  refine ⟨H2.dil hlam U, (H2.M_dil hlam U).trans hU, ?_, ?_⟩
  · rwa [H2.dilR_of_pos hlam] at hl1
  · exact (strict_spreading hd1 hd4 hc₁ hc₂ hε hα (val_ne_zero_of_M hm hU)).2.2.2 lam hlam hl2.2

end Curvature

end ReyesMath
