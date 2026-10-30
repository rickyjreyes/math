import Mathlib
import MathProofs.E68Sobolev
import MathProofs.E68Singular

/-!
# E68: the Sobolev embedding `H¹(ℝⁿ) ⊂ L^{p*}` for weak `H¹` fields

For `n ≥ 1` and `1/p* = 1/2 - 1/n`, every `ψ ∈ H¹(ℝⁿ)` (weak gradient `g`) satisfies
`‖ψ‖_{L^{p*}} ≤ C_n ‖g‖_{L²}`. In particular `H¹(ℝ³) ⊂ L⁶` and `H¹(ℝ⁴) ⊂ L⁴`. The proof
extends Mathlib's Gagliardo–Nirenberg–Sobolev inequality for `C¹` compactly supported
functions (`eLpNorm_le_eLpNorm_fderiv_of_eq_inner`) to the weak Sobolev space:

* **mollification** (`gradVec_conv_apply`, `eLpNorm_gradVec_conv_le`): for a smooth
  compactly supported kernel `ρ ≥ 0` with `∫ ρ = 1`, the classical gradient of `ρ ⋆ v` is
  `ρ ⋆ ∇v`, where `∇v` is the *weak* gradient. The weak derivative identity is tested
  against `t ↦ ρ(x - t)`. Also `‖ρ ⋆ ∇v‖_{L²} ≤ ‖∇v‖_{L²}`, from a pointwise Cauchy–Schwarz
  inequality and `∫ (ρ ⋆ h) = ∫ h`;
* **compact support** (`sobolev_of_hasCompactSupport`): GNS for `ρ_k ⋆ v`, then Fatou's
  lemma along the a.e. convergence `ρ_k ⋆ v → v`;
* **cutoff** (`sobolev_H1`): `χ_R ψ` has weak gradient `χ_R g + ψ ∇χ_R` with
  `|∇χ_R| ≤ 4K/R`, and Fatou's lemma as `R → ∞`.
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric ContinuousLinearMap
open scoped ContDiff ENNReal NNReal Convolution

namespace ReyesMath.E68

variable {n : ℕ}

local notation "Rn" => EuclideanSpace ℝ (Fin n)

/-! ### Convolution with a real kernel -/

/-- `(ρ ⋆ v)(x) = ∫ ρ(t) v(x - t) dt = ∫ ρ(x - t) v(t) dt`. -/
abbrev conv (ρ : Rn → ℝ) (v : Rn → ℂ) : Rn → ℂ := ρ ⋆[lsmul ℝ ℝ, volume] v

theorem conv_apply (ρ : Rn → ℝ) (v : Rn → ℂ) (x : Rn) :
    conv ρ v x = ∫ t, ρ (x - t) • v t :=
  convolution_lsmul_swap

theorem integrable_kernel_smul {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ρ : Rn → ℝ} (hρ : Continuous ρ) (hρc : HasCompactSupport ρ) {f : Rn → F}
    (hf : LocallyIntegrable f volume) (x : Rn) :
    Integrable (fun t => ρ (x - t) • f t) volume :=
  hf.integrable_smul_left_of_hasCompactSupport (hρ.comp (continuous_const.sub continuous_id))
    (hρc.comp_homeomorph (Homeomorph.subLeft x))

/-- The classical directional derivative of `ρ ⋆ v` is `(∂ᵢρ) ⋆ v`. -/
theorem fderiv_conv_apply {ρ : Rn → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ)
    {v : Rn → ℂ} (hv : LocallyIntegrable v volume) (x : Rn) (i : Fin n) :
    fderiv ℝ (conv ρ v) x (ev i) = ∫ t, fderiv ℝ ρ (x - t) (ev i) • v t := by
  have hρ1 : ContDiff ℝ 1 ρ := hρ.of_le (by exact_mod_cast le_top)
  have hint : Integrable (fun t => (ContinuousLinearMap.precompL Rn
      (lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ)) (fderiv ℝ ρ t) (v (x - t))) volume :=
    (hρc.fderiv ℝ).convolutionExists_left _ (hρ1.continuous_fderiv le_rfl) hv x
  rw [(hρc.hasFDerivAt_convolution_left (lsmul ℝ ℝ) hρ1 hv x).fderiv, convolution_def,
    ContinuousLinearMap.integral_apply hint]
  have h := convolution_lsmul_swap (μ := volume) (x := x)
    (f := fun t => fderiv ℝ ρ t (ev i)) (g := v)
  rw [convolution_lsmul] at h
  simpa [ContinuousLinearMap.precompL, ContinuousLinearMap.precompR] using h

/-- **The weak derivative commutes with mollification.** For an `H¹` field `v` with weak
gradient `G`, `∫ (∂ᵢρ)(x - t) v(t) dt = ∫ ρ(x - t) Gᵢ(t) dt`. This is the weak derivative
identity tested against `t ↦ ρ(x - t)`. -/
theorem integral_fderiv_kernel_eq {v : Rn → ℂ} {G : Rn → EuclideanSpace ℂ (Fin n)}
    (h : IsH1 v G) {ρ : Rn → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ) (x : Rn)
    (i : Fin n) :
    ∫ t, fderiv ℝ ρ (x - t) (ev i) • v t = ∫ t, ρ (x - t) • G t i := by
  have hφ : ContDiff ℝ ∞ (fun t : Rn => ρ (x - t)) := hρ.comp (contDiff_const.sub contDiff_id)
  have hφc : HasCompactSupport (fun t : Rn => ρ (x - t)) :=
    hρc.comp_homeomorph (Homeomorph.subLeft x)
  have hd : ∀ t, fderiv ℝ (fun t : Rn => ρ (x - t)) t (ev i) = -fderiv ℝ ρ (x - t) (ev i) := by
    intro t
    have h1 : HasFDerivAt (fun t : Rn => x - t) (-ContinuousLinearMap.id ℝ Rn) t :=
      (hasFDerivAt_id t).const_sub x
    have h2 := ((hρ.differentiable (by simp)) (x - t)).hasFDerivAt.comp t h1
    rw [show (fun t : Rn => ρ (x - t)) = ρ ∘ fun t => x - t from rfl, h2.fderiv]
    simp
  have hw := h.weak i (fun t => ρ (x - t)) hφ hφc
  simp_rw [hd] at hw
  have e1 : ∫ t, fderiv ℝ ρ (x - t) (ev i) • v t =
      -∫ t, v t * ((-fderiv ℝ ρ (x - t) (ev i) : ℝ) : ℂ) := by
    rw [← integral_neg]
    congr 1
    funext t
    rw [Complex.real_smul]
    push_cast
    ring
  have e2 : ∫ t, ρ (x - t) • G t i = ∫ t, G t i * ((ρ (x - t) : ℝ) : ℂ) := by
    congr 1
    funext t
    rw [Complex.real_smul, mul_comm]
  rw [e1, hw, e2, neg_neg]

/-- The classical gradient of `ρ ⋆ v`, componentwise: `∂ᵢ(ρ ⋆ v) = ρ ⋆ Gᵢ`. -/
theorem gradVec_conv_apply {v : Rn → ℂ} {G : Rn → EuclideanSpace ℂ (Fin n)} (h : IsH1 v G)
    {ρ : Rn → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ) (x : Rn) (i : Fin n) :
    gradVec (conv ρ v) x i = ∫ t, ρ (x - t) • G t i := by
  rw [gradVec_apply, fderiv_conv_apply hρ hρc h.locallyIntegrable x i,
    integral_fderiv_kernel_eq h hρ hρc x i]

/-- The classical gradient of `ρ ⋆ v` is the vector `∫ ρ(x - t) G(t) dt`. -/
theorem gradVec_conv {v : Rn → ℂ} {G : Rn → EuclideanSpace ℂ (Fin n)} (h : IsH1 v G)
    {ρ : Rn → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ) (x : Rn) :
    gradVec (conv ρ v) x = ∫ t, ρ (x - t) • G t := by
  have hint := integrable_kernel_smul hρ.continuous hρc
    (h.memLp_grad.locallyIntegrable (by norm_num)) x
  ext i
  rw [gradVec_conv_apply h hρ hρc x i]
  have := (EuclideanSpace.proj (𝕜 := ℂ) i).restrictScalars ℝ |>.integral_comp_comm hint
  simpa using this

/-! ### The `L²` bound for the mollified gradient -/

/-- **Pointwise Cauchy–Schwarz.** For a kernel `ρ ≥ 0` with `∫ ρ = 1`,
`(∫ ρ(x - t) a(t) dt)² ≤ ∫ ρ(x - t) a(t)² dt`. -/
theorem sq_integral_kernel_le {ρ : Rn → ℝ} (hρ0 : ∀ x, 0 ≤ ρ x) (hρ1 : ∫ x, ρ x = 1)
    (hρ : Continuous ρ) (hρc : HasCompactSupport ρ) {a : Rn → ℝ}
    (ha : LocallyIntegrable a volume) (ha2 : LocallyIntegrable (fun t => a t ^ 2) volume)
    (x : Rn) : (∫ t, ρ (x - t) * a t) ^ 2 ≤ ∫ t, ρ (x - t) * a t ^ 2 := by
  set m := ∫ t, ρ (x - t) * a t with hm
  have i0 : Integrable (fun t => ρ (x - t)) volume :=
    (hρ.integrable_of_hasCompactSupport hρc).comp_sub_left x
  have i1 : Integrable (fun t => ρ (x - t) * a t) volume := by
    simpa [smul_eq_mul] using integrable_kernel_smul hρ hρc ha x
  have i2 : Integrable (fun t => ρ (x - t) * a t ^ 2) volume := by
    simpa [smul_eq_mul] using integrable_kernel_smul hρ hρc ha2 x
  have hw : ∫ t, ρ (x - t) = 1 := by
    rw [integral_sub_left_eq_self (fun t => ρ t) volume x, hρ1]
  have key : 0 ≤ ∫ t, ρ (x - t) * (a t - m) ^ 2 :=
    integral_nonneg fun t => mul_nonneg (hρ0 _) (sq_nonneg _)
  have expand : ∫ t, ρ (x - t) * (a t - m) ^ 2 =
      (∫ t, ρ (x - t) * a t ^ 2) - 2 * m * (∫ t, ρ (x - t) * a t) + m ^ 2 * ∫ t, ρ (x - t) := by
    have e : (fun t => ρ (x - t) * (a t - m) ^ 2) =
        fun t => ρ (x - t) * a t ^ 2 - 2 * m * (ρ (x - t) * a t) + m ^ 2 * ρ (x - t) := by
      funext t
      ring
    have i3 : Integrable (fun t => ρ (x - t) * a t ^ 2 - 2 * m * (ρ (x - t) * a t)) volume :=
      i2.sub (i1.const_mul _)
    rw [e, integral_add i3 (i0.const_mul _), integral_sub i2 (i1.const_mul _),
      integral_const_mul, integral_const_mul]
  rw [expand, hw, ← hm] at key
  nlinarith [key]

/-- Two `L²` functions whose squared norms have ordered integrals have ordered `L²`
seminorms. -/
theorem eLpNorm_two_le_of_integral_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F F' : Type*} [NormedAddCommGroup F] [NormedAddCommGroup F'] {f : α → F} {g : α → F'}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (h : ∫ x, ‖f x‖ ^ 2 ∂μ ≤ ∫ x, ‖g x‖ ^ 2 ∂μ) : eLpNorm f 2 μ ≤ eLpNorm g 2 μ := by
  rw [hf.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top,
    hg.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  exact ENNReal.ofReal_le_ofReal
    (Real.rpow_le_rpow (integral_nonneg fun x => by positivity) h (by norm_num))

/-- **The `L²` bound for the mollified gradient.** For an `H¹` field `v` with compact support
and a smooth compactly supported kernel `ρ ≥ 0` with `∫ ρ = 1`, the classical gradient of
`ρ ⋆ v` satisfies `‖∇(ρ ⋆ v)‖_{L²} ≤ ‖∇v‖_{L²}` (weak gradient on the right). -/
theorem eLpNorm_gradVec_conv_le {v : Rn → ℂ} {G : Rn → EuclideanSpace ℂ (Fin n)}
    (h : IsH1 v G) (hvc : HasCompactSupport v) {ρ : Rn → ℝ} (hρ : ContDiff ℝ ∞ ρ)
    (hρc : HasCompactSupport ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρ1 : ∫ x, ρ x = 1) :
    eLpNorm (gradVec (conv ρ v)) 2 volume ≤ eLpNorm G 2 volume := by
  have hloc := h.locallyIntegrable
  have hc : ContDiff ℝ 1 (conv ρ v) :=
    hρc.contDiff_convolution_left (lsmul ℝ ℝ) (n := 1) (hρ.of_le (by exact_mod_cast le_top))
      hloc
  have hcc : HasCompactSupport (conv ρ v) := hρc.convolution (lsmul ℝ ℝ) hvc
  have hm1 : MemLp (gradVec (conv ρ v)) 2 volume :=
    (continuous_gradVec hc).memLp_of_hasCompactSupport (hasCompactSupport_gradVec hcc)
  refine eLpNorm_two_le_of_integral_le hm1 h.memLp_grad ?_
  set a : Rn → ℝ := fun t => ‖G t‖ with ha
  have hGa : LocallyIntegrable a volume :=
    (h.memLp_grad.norm.locallyIntegrable (by norm_num))
  have hGa2 : Integrable (fun t => a t ^ 2) volume := h.integrable_grad_sq
  have hρi : Integrable ρ volume := hρ.continuous.integrable_of_hasCompactSupport hρc
  -- the pointwise bound `‖∇(ρ ⋆ v)(x)‖² ≤ (ρ ⋆ a²)(x)`
  have hpt : ∀ x, ‖gradVec (conv ρ v) x‖ ^ 2 ≤
      (ρ ⋆[lsmul ℝ ℝ, volume] fun t => a t ^ 2) x := by
    intro x
    rw [convolution_lsmul_swap, gradVec_conv h hρ hρc x]
    have h1 : ‖∫ t, ρ (x - t) • G t‖ ≤ ∫ t, ρ (x - t) * a t := by
      refine (norm_integral_le_integral_norm _).trans_eq ?_
      congr 1
      funext t
      rw [norm_smul, Real.norm_of_nonneg (hρ0 _)]
    have h2 := sq_integral_kernel_le hρ0 hρ1 hρ.continuous hρc hGa hGa2.locallyIntegrable x
    calc ‖∫ t, ρ (x - t) • G t‖ ^ 2 ≤ (∫ t, ρ (x - t) * a t) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ ∫ t, ρ (x - t) * a t ^ 2 := h2
      _ = ∫ t, ρ (x - t) • a t ^ 2 := by simp only [smul_eq_mul]
  -- integrating: `∫ (ρ ⋆ a²) = (∫ ρ)(∫ a²) = ∫ a²`
  have hint : ∫ x, (ρ ⋆[lsmul ℝ ℝ, volume] fun t => a t ^ 2) x = ∫ t, a t ^ 2 := by
    rw [integral_convolution (lsmul ℝ ℝ) hρi hGa2, hρ1]
    simp
  calc (∫ x, ‖gradVec (conv ρ v) x‖ ^ 2) ≤
        ∫ x, (ρ ⋆[lsmul ℝ ℝ, volume] fun t => a t ^ 2) x :=
        integral_mono_of_nonneg (Eventually.of_forall fun x => by positivity)
          (hρi.integrable_convolution (lsmul ℝ ℝ) hGa2) (Eventually.of_forall hpt)
    _ = ∫ t, ‖G t‖ ^ 2 := hint

/-! ### The Gagliardo–Nirenberg–Sobolev inequality for mollified fields -/

/-- The constant of Mathlib's Gagliardo–Nirenberg–Sobolev inequality for `p = 2` on `ℝⁿ`. -/
def sobolevConst (n : ℕ) : ℝ≥0 :=
  eLpNormLESNormFDerivOfEqInnerConst (volume : Measure (EuclideanSpace ℝ (Fin n)))
    ((2 : ℝ≥0) : ℝ)

/-- **GNS for `C¹` compactly supported complex fields**, stated with the Euclidean norm of
the gradient vector: `‖w‖_{L^{p*}} ≤ C_n ‖∇w‖_{L²}` for `1/p* = 1/2 - 1/n`. -/
theorem gns_gradVec (hn : 0 < n) {p' : ℝ≥0} (hp' : (p' : ℝ)⁻¹ = 2⁻¹ - (n : ℝ)⁻¹) {w : Rn → ℂ}
    (hw : ContDiff ℝ 1 w) (hwc : HasCompactSupport w) :
    eLpNorm w p' volume ≤ sobolevConst n * eLpNorm (gradVec w) 2 volume := by
  have hfin : Module.finrank ℝ Rn = n := finrank_euclidean n
  have h := eLpNorm_le_eLpNorm_fderiv_of_eq_inner (μ := volume) hw hwc (p := 2) (p' := p')
    (by norm_num) (by rw [hfin]; exact hn) (by rw [hfin]; push_cast; exact hp')
  have h2 : ((2 : ℝ≥0) : ℝ≥0∞) = 2 := by norm_num
  rw [h2] at h
  exact h.trans (mul_le_mul_left' (eLpNorm_mono fun x => norm_le_norm_coordVec _) _)

/-- The mollifier bumps, supported in `B(0, 1/(k+1))` and equal to one on
`B(0, 1/(2(k+1)))`. -/
def molBump (n k : ℕ) : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) where
  rIn := 1 / (2 * ((k : ℝ) + 1))
  rOut := 1 / ((k : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := one_div_lt_one_div_of_lt (by positivity) (by linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)])

/-- **The Sobolev inequality for compactly supported `H¹` fields.** -/
theorem sobolev_of_hasCompactSupport (hn : 0 < n) {p' : ℝ≥0}
    (hp' : (p' : ℝ)⁻¹ = 2⁻¹ - (n : ℝ)⁻¹) {v : Rn → ℂ} {G : Rn → EuclideanSpace ℂ (Fin n)}
    (h : IsH1 v G) (hvc : HasCompactSupport v) :
    eLpNorm v p' volume ≤ sobolevConst n * eLpNorm G 2 volume := by
  have hloc := h.locallyIntegrable
  have hc : ∀ k, ContDiff ℝ 1 (conv ((molBump n k).normed volume) v) := fun k =>
    (molBump n k).hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ) (n := 1)
      (molBump n k).contDiff_normed hloc
  have hcc : ∀ k, HasCompactSupport (conv ((molBump n k).normed volume) v) := fun k =>
    (molBump n k).hasCompactSupport_normed.convolution (lsmul ℝ ℝ) hvc
  have hrOut : Tendsto (fun k => (molBump n k).rOut) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hratio : ∀ᶠ k in atTop, (molBump n k).rOut ≤ 2 * (molBump n k).rIn :=
    Eventually.of_forall fun k => by
      show 1 / ((k : ℝ) + 1) ≤ 2 * (1 / (2 * ((k : ℝ) + 1)))
      have : (2 : ℝ) * (1 / (2 * ((k : ℝ) + 1))) = 1 / ((k : ℝ) + 1) := by field_simp
      rw [this]
  -- `ρ_k ⋆ v → v` almost everywhere
  have hae := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable (μ := volume)
    hrOut hratio hloc
  -- Fatou's lemma for the `L^{p*}` seminorm
  have hF := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := p')
    (fun k => (hc k).continuous.aestronglyMeasurable) v hae
  refine hF.trans (liminf_le_of_frequently_le' (Frequently.of_forall fun k => ?_))
  calc eLpNorm (conv ((molBump n k).normed volume) v) p' volume ≤
      sobolevConst n * eLpNorm (gradVec (conv ((molBump n k).normed volume) v)) 2 volume :=
        gns_gradVec hn hp' (hc k) (hcc k)
    _ ≤ sobolevConst n * eLpNorm G 2 volume :=
        mul_le_mul_left' (eLpNorm_gradVec_conv_le h hvc (molBump n k).contDiff_normed
          (molBump n k).hasCompactSupport_normed (molBump n k).nonneg_normed
          (molBump n k).integral_normed) _

/-! ### Cutoffs `χ_R(x) = cut(|x|²/R²)` -/

/-- The cutoff `χ_R(x) = cut(|x|²/R²)`: `χ_R = 1` on `B̄_R`, `χ_R = 0` outside `B̄_{2R}`. -/
def cutoff (R : ℝ) (x : Rn) : ℝ := Singular.cut ((R ^ 2)⁻¹ * ‖x‖ ^ 2)

theorem contDiff_cutoff (R : ℝ) : ContDiff ℝ ∞ (cutoff R : Rn → ℝ) :=
  Singular.contDiff_cut.comp (contDiff_const.mul (contDiff_norm_sq ℝ))

theorem cutoff_eq_zero {R : ℝ} (hR : 0 < R) {x : Rn} (hx : 2 * R < ‖x‖) : cutoff R x = 0 := by
  apply Singular.cut_eq_zero
  rw [inv_mul_eq_div, le_div_iff₀ (by positivity)]
  nlinarith

theorem cutoff_eq_one {R : ℝ} (hR : 0 < R) {x : Rn} (hx : ‖x‖ ≤ R) : cutoff R x = 1 := by
  apply Singular.cut_eq_one
  rw [inv_mul_eq_div, div_le_one (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg x) hx 2

theorem hasCompactSupport_cutoff {R : ℝ} (hR : 0 < R) :
    HasCompactSupport (cutoff R : Rn → ℝ) :=
  HasCompactSupport.intro (isCompact_closedBall 0 (2 * R)) fun x hx =>
    cutoff_eq_zero hR (by simpa [mem_closedBall, dist_zero_right] using hx)

theorem abs_cutoff_le_one (R : ℝ) (x : Rn) : |cutoff R x| ≤ 1 := by
  rw [cutoff, abs_of_nonneg (Singular.cut_nonneg _)]
  exact Singular.cut_le_one _

/-- `|∇χ_R| ≤ 4K/R`, where `K` bounds `|cut'|`. -/
theorem norm_fderiv_cutoff_le {R : ℝ} (hR : 0 < R) {K : ℝ}
    (hK : ∀ s, |deriv Singular.cut s| ≤ K) (x : Rn) :
    ‖fderiv ℝ (cutoff R) x‖ ≤ 4 * K / R := by
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0)
  have h1 := ((hasStrictFDerivAt_norm_sq x).hasFDerivAt).const_mul ((R ^ 2)⁻¹)
  have h2 := (((Singular.contDiff_cut.differentiable (by simp))
    ((R ^ 2)⁻¹ * ‖x‖ ^ 2)).hasDerivAt).comp_hasFDerivAt x h1
  rw [show (cutoff R : Rn → ℝ) = Singular.cut ∘ fun x => (R ^ 2)⁻¹ * ‖x‖ ^ 2 from rfl,
    h2.fderiv]
  have hnorm : ‖deriv Singular.cut ((R ^ 2)⁻¹ * ‖x‖ ^ 2) • ((R ^ 2)⁻¹ • (2 • innerSL ℝ x))‖ ≤
      |deriv Singular.cut ((R ^ 2)⁻¹ * ‖x‖ ^ 2)| * ((R ^ 2)⁻¹ * (2 * ‖x‖)) := by
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_of_nonneg (by positivity)]
    gcongr
    calc ‖(2 : ℕ) • innerSL ℝ x‖ ≤ (2 : ℕ) * ‖innerSL ℝ x‖ := norm_nsmul_le
      _ = 2 * ‖x‖ := by rw [innerSL_apply_norm]; norm_num
  refine hnorm.trans ?_
  by_cases hx : ‖x‖ ≤ 2 * R
  · calc |deriv Singular.cut ((R ^ 2)⁻¹ * ‖x‖ ^ 2)| * ((R ^ 2)⁻¹ * (2 * ‖x‖)) ≤
        K * ((R ^ 2)⁻¹ * (2 * (2 * R))) := by gcongr; exact hK _
      _ = 4 * K / R := by field_simp; ring
  · have hs : 4 < (R ^ 2)⁻¹ * ‖x‖ ^ 2 := by
      rw [inv_mul_eq_div, lt_div_iff₀ (by positivity)]
      nlinarith [not_le.1 hx]
    rw [Singular.deriv_cut_of_four_lt hs, abs_zero, zero_mul]
    positivity

/-! ### The Sobolev embedding for weak `H¹` fields -/

/-- **The Sobolev inequality for weak `H¹(ℝⁿ)`.** For `n ≥ 1` and `1/p* = 1/2 - 1/n`, every
`ψ ∈ H¹(ℝⁿ)` with weak gradient `g` satisfies `‖ψ‖_{L^{p*}} ≤ C_n ‖g‖_{L²}`, with `C_n`
Mathlib's Gagliardo–Nirenberg–Sobolev constant. -/
theorem sobolev_H1 (hn : 0 < n) {p' : ℝ≥0} (hp' : (p' : ℝ)⁻¹ = 2⁻¹ - (n : ℝ)⁻¹)
    {u : Rn → ℂ} {G : Rn → EuclideanSpace ℂ (Fin n)} (h : IsH1 u G) :
    eLpNorm u p' volume ≤ sobolevConst n * eLpNorm G 2 volume := by
  obtain ⟨K, hK0, hK⟩ := Singular.exists_bound_deriv_cut
  have hR : ∀ k : ℕ, (0 : ℝ) < (k : ℝ) + 1 := fun k => by positivity
  -- the truncations `χ_{k+1} u`, with weak gradients `χ_{k+1} G + u ∇χ_{k+1}`
  have hv : ∀ k : ℕ, IsH1 (fun x => ((cutoff ((k : ℝ) + 1) x : ℝ) : ℂ) * u x)
      (fun x => ((cutoff ((k : ℝ) + 1) x : ℝ) : ℂ) • G x +
        u x • gradVec (ofRealFn (cutoff ((k : ℝ) + 1))) x) := fun k =>
    h.smul_test (contDiff_cutoff _) (hasCompactSupport_cutoff (hR k))
  have hvc : ∀ k : ℕ, HasCompactSupport (fun x => ((cutoff ((k : ℝ) + 1) x : ℝ) : ℂ) * u x) :=
    fun k => ((hasCompactSupport_cutoff (hR k)).comp_left Complex.ofReal_zero).mul_right
  -- the bound for each truncation
  have hk : ∀ k : ℕ, eLpNorm (fun x => ((cutoff ((k : ℝ) + 1) x : ℝ) : ℂ) * u x) p' volume ≤
      sobolevConst n * (eLpNorm G 2 volume +
        ENNReal.ofReal (4 * K * (1 / ((k : ℝ) + 1))) * eLpNorm u 2 volume) := by
    intro k
    refine (sobolev_of_hasCompactSupport hn hp' (hv k) (hvc k)).trans (mul_le_mul_left' ?_ _)
    have hχ := contDiff_cutoff (n := n) ((k : ℝ) + 1)
    have hχ1 : ContDiff ℝ 1 (cutoff ((k : ℝ) + 1) : Rn → ℝ) := hχ.of_le (by exact_mod_cast le_top)
    have m1 : AEStronglyMeasurable (fun x => ((cutoff ((k : ℝ) + 1) x : ℝ) : ℂ) • G x) volume :=
      (Complex.continuous_ofReal.comp hχ.continuous).aestronglyMeasurable.smul h.memLp_grad.1
    have m2 : AEStronglyMeasurable
        (fun x => u x • gradVec (ofRealFn (cutoff ((k : ℝ) + 1))) x) volume :=
      h.memLp.1.smul (continuous_gradVec (Complex.ofRealCLM.contDiff.comp hχ1)).aestronglyMeasurable
    have hadd := eLpNorm_add_le m1 m2 (p := 2) (by norm_num)
    refine hadd.trans (add_le_add ?_ ?_)
    · refine eLpNorm_mono fun x => ?_
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg _) (abs_cutoff_le_one _ x)
    · refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul (Eventually.of_forall fun x => ?_) 2
      rw [norm_smul, norm_gradVec_ofRealFn ((hχ1.differentiable le_rfl) x), mul_comm]
      gcongr
      rw [← div_eq_mul_one_div]
      exact norm_fderiv_cutoff_le (hR k) hK x
  -- `χ_{k+1} u → u` pointwise
  have hlim : ∀ x, Tendsto (fun k : ℕ => ((cutoff ((k : ℝ) + 1) x : ℝ) : ℂ) * u x) atTop
      (𝓝 (u x)) := by
    intro x
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop ⌈‖x‖⌉₊] with k hk
    have hxk : ‖x‖ ≤ (k : ℝ) + 1 := by
      have := (Nat.ceil_le.1 hk)
      linarith
    rw [cutoff_eq_one (hR k) hxk]
    simp
  have hF := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := p')
    (fun k => (hv k).memLp.1) u (Eventually.of_forall hlim)
  -- the bounds converge to `C ‖G‖₂`
  have hB : Tendsto (fun k : ℕ => (sobolevConst n : ℝ≥0∞) * (eLpNorm G 2 volume +
      ENNReal.ofReal (4 * K * (1 / ((k : ℝ) + 1))) * eLpNorm u 2 volume)) atTop
      (𝓝 (sobolevConst n * eLpNorm G 2 volume)) := by
    have h0 : Tendsto (fun k : ℕ => ENNReal.ofReal (4 * K * (1 / ((k : ℝ) + 1)))) atTop (𝓝 0) := by
      have := ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (4 * K))
      rwa [mul_zero, ENNReal.ofReal_zero] at this
    have h1 := (ENNReal.Tendsto.mul_const h0 (Or.inr h.memLp.eLpNorm_ne_top)).const_add
      (eLpNorm G 2 volume)
    rw [zero_mul, add_zero] at h1
    exact ENNReal.Tendsto.const_mul h1 (Or.inr ENNReal.coe_ne_top)
  calc eLpNorm u p' volume ≤ liminf (fun k : ℕ =>
        eLpNorm (fun x => ((cutoff ((k : ℝ) + 1) x : ℝ) : ℂ) * u x) p' volume) atTop := hF
    _ ≤ liminf (fun k : ℕ => (sobolevConst n : ℝ≥0∞) * (eLpNorm G 2 volume +
        ENNReal.ofReal (4 * K * (1 / ((k : ℝ) + 1))) * eLpNorm u 2 volume)) atTop :=
        liminf_le_liminf (Eventually.of_forall hk)
    _ = sobolevConst n * eLpNorm G 2 volume := hB.liminf_eq

/-- `H¹(ℝⁿ) ⊂ L^{p*}`: the field is in `L^{p*}`. -/
theorem memLp_of_isH1 (hn : 0 < n) {p' : ℝ≥0} (hp' : (p' : ℝ)⁻¹ = 2⁻¹ - (n : ℝ)⁻¹)
    {u : Rn → ℂ} {G : Rn → EuclideanSpace ℂ (Fin n)} (h : IsH1 u G) : MemLp u p' volume :=
  ⟨h.memLp.1, (sobolev_H1 hn hp' h).trans_lt
    (ENNReal.mul_lt_top ENNReal.coe_lt_top h.memLp_grad.eLpNorm_lt_top)⟩

end ReyesMath.E68
