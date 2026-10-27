import Mathlib
import MathProofs.H2Algebra
import MathProofs.SphereNull

/-!
# The Plancherel transform and the isolated Fourier shell (F10)

Formalization of `papers/isolated-fourier-shell-no-l2-bound-state/main.tex`.

* Plancherel's theorem: `Sobolev.fourierL2 : L²(ℝ^d) ≃ₗᵢ[ℂ] L²(ℝ^d)`, the unitary extension of the
  Schwartz-space Fourier transform (`Sobolev.fourierL2_toL2`), which equals the Fourier integral
  on `L¹ ∩ L²` (`Sobolev.fourierL2_ae_eq_fourier`) and satisfies the multiplication formula
  `Sobolev.integral_mul_fourierL2`. In the manuscript's normalization
  `û(ξ) = (2π)^{-d/2} ∫ u(x) e^{-ix·ξ} dx` (`Sobolev.fourierU` on integrable functions) the
  unitary transform is `Sobolev.FU`, with `Sobolev.FU_ae_eq` on `L¹ ∩ L²`.
* Theorem (zero `L²` state on an isolated Fourier shell): `FourierShell.shell_theorem`
  (essential support) and `FourierShell.shell_theorem_distrib` (distributional support).
* Corollary (free-space Helmholtz equation): `FourierShell.helmholtz`, for solutions in the sense
  of distributions (smooth compactly supported test functions), via the cutoff approximation
  `Sobolev.exists_cutoff_seq` in the graph norm of `Δ`.
* Corollary (nonconstant polynomial dispersion): `FourierShell.poly_dispersion`, with `P(−Δ)` the
  operator `Sobolev.polyLapS P` of Fourier symbol `P(4π²|ξ|²)` (`Sobolev.fS_polyLapS`); the
  zero set is a finite union of spheres (`Sobolev.polyZero_null`).
* Remark (general Fourier multipliers): `FourierShell.multiplier`.
* Proposition (fixed carrier, freely varying envelope): `FourierShell.packets` for the packets
  `Sobolev.packet`.
-/

open Filter Topology Complex InnerProductSpace MeasureTheory Set
open scoped ContDiff FourierTransform

namespace ReyesMath

namespace Sobolev

variable {d : ℕ}

local notation "Rd" => EuclideanSpace ℝ (Fin d)

/-! ### The inverse Fourier transform on Schwartz space -/

/-- `𝓕⁻` on Schwartz space. -/
noncomputable def fSi (φ : SchwartzMap Rd ℂ) : SchwartzMap Rd ℂ :=
  (SchwartzMap.fourierTransformCLE ℂ (V := Rd) (E := ℂ)).symm φ

theorem coe_fSi (φ : SchwartzMap Rd ℂ) : ⇑(fSi φ) = 𝓕⁻ (⇑φ) := by
  rw [fSi, SchwartzMap.fourierTransformCLE_symm_apply]

theorem fS_fSi (φ : SchwartzMap Rd ℂ) : fS (fSi φ) = φ :=
  (SchwartzMap.fourierTransformCLE ℂ (V := Rd) (E := ℂ)).apply_symm_apply φ

theorem fSi_fS (φ : SchwartzMap Rd ℂ) : fSi (fS φ) = φ :=
  (SchwartzMap.fourierTransformCLE ℂ (V := Rd) (E := ℂ)).symm_apply_apply φ

/-- Plancherel on Schwartz space. -/
theorem norm_toL2_fS (φ : SchwartzMap Rd ℂ) : ‖toL2 (fS φ)‖ = ‖toL2 φ‖ := by
  have h1 := norm_toL2_sq (fS φ)
  rw [coe_fS, ← norm_toL2_sq_fourier] at h1
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h1

theorem norm_toL2_fSi (φ : SchwartzMap Rd ℂ) : ‖toL2 (fSi φ)‖ = ‖toL2 φ‖ := by
  have h := norm_toL2_fS (fSi φ)
  rw [fS_fSi] at h
  exact h.symm

/-! ### Isometric extension from the Schwartz subspace -/

/-- An `L²`-isometric operator on `𝓢`, restricted to the Schwartz subspace of `L²`. -/
noncomputable def extV (T : SchwartzMap Rd ℂ →L[ℂ] SchwartzMap Rd ℂ) : S2 d →ₗ[ℂ] L2 d :=
  ((toL2 (d := d)).toLinearMap ∘ₗ T.toLinearMap) ∘ₗ (eS d).symm.toLinearMap

theorem extV_apply (T : SchwartzMap Rd ℂ →L[ℂ] SchwartzMap Rd ℂ) (v : S2 d) :
    extV T v = toL2 (T ((eS d).symm v)) := rfl

theorem norm_extV {T : SchwartzMap Rd ℂ →L[ℂ] SchwartzMap Rd ℂ}
    (hT : ∀ φ, ‖toL2 (T φ)‖ = ‖toL2 φ‖) (v : S2 d) : ‖extV T v‖ = ‖v‖ := by
  rw [extV_apply, hT, toL2_eS_symm]
  rfl

noncomputable def extW {T : SchwartzMap Rd ℂ →L[ℂ] SchwartzMap Rd ℂ}
    (hT : ∀ φ, ‖toL2 (T φ)‖ = ‖toL2 φ‖) : S2 d →L[ℂ] L2 d :=
  LinearMap.mkContinuous (extV T) 1 fun v => by rw [norm_extV hT, one_mul]

/-- The isometric extension of `T` to `L²(ℝ^d)`. -/
noncomputable def extL2 {T : SchwartzMap Rd ℂ →L[ℂ] SchwartzMap Rd ℂ}
    (hT : ∀ φ, ‖toL2 (T φ)‖ = ‖toL2 φ‖) : L2 d →L[ℂ] L2 d :=
  (extW hT).extend (S2 d).subtypeL denseRange_subtypeL_S2
    (Submodule.subtypeₗᵢ (S2 d)).isometry.isUniformInducing

theorem extL2_toL2 {T : SchwartzMap Rd ℂ →L[ℂ] SchwartzMap Rd ℂ}
    (hT : ∀ φ, ‖toL2 (T φ)‖ = ‖toL2 φ‖) (φ : SchwartzMap Rd ℂ) :
    extL2 hT (toL2 φ) = toL2 (T φ) := by
  have hmem : toL2 φ ∈ S2 d := mem_S2 φ
  have h := ContinuousLinearMap.extend_eq (extW hT) (S2 d).subtypeL denseRange_subtypeL_S2
    (Submodule.subtypeₗᵢ (S2 d)).isometry.isUniformInducing ⟨toL2 φ, hmem⟩
  have e : (S2 d).subtypeL ⟨toL2 φ, hmem⟩ = toL2 φ := rfl
  rw [e] at h
  rw [extL2, h]
  simp only [extW, LinearMap.mkContinuous_apply, extV_apply]
  rw [eS_symm_toL2]

theorem norm_extL2 {T : SchwartzMap Rd ℂ →L[ℂ] SchwartzMap Rd ℂ}
    (hT : ∀ φ, ‖toL2 (T φ)‖ = ‖toL2 φ‖) (f : L2 d) : ‖extL2 hT f‖ = ‖f‖ := by
  refine denseRange_toL2.induction_on f
    (isClosed_eq ((extL2 hT).continuous.norm) continuous_norm) fun φ => ?_
  rw [extL2_toL2, hT]

/-! ### The Plancherel transform -/

theorem norm_toL2_fourierCLM (φ : SchwartzMap Rd ℂ) :
    ‖toL2 (SchwartzMap.fourierTransformCLM ℂ φ)‖ = ‖toL2 φ‖ :=
  norm_toL2_fS φ

theorem norm_toL2_fourierCLE_symm (φ : SchwartzMap Rd ℂ) :
    ‖toL2 ((SchwartzMap.fourierTransformCLE ℂ (V := Rd) (E := ℂ)).symm.toContinuousLinearMap φ)‖ =
      ‖toL2 φ‖ :=
  norm_toL2_fSi φ

/-- The Plancherel extension of `𝓕` to `L²(ℝ^d)` (Mathlib normalization `e^{-2πi⟨x, ξ⟩}`). -/
noncomputable def FL : L2 d →L[ℂ] L2 d := extL2 (T := SchwartzMap.fourierTransformCLM ℂ)
  norm_toL2_fourierCLM

/-- The Plancherel extension of `𝓕⁻`. -/
noncomputable def FLi : L2 d →L[ℂ] L2 d :=
  extL2 (T := (SchwartzMap.fourierTransformCLE ℂ (V := Rd) (E := ℂ)).symm.toContinuousLinearMap)
    norm_toL2_fourierCLE_symm

theorem FL_toL2 (φ : SchwartzMap Rd ℂ) : FL (toL2 φ) = toL2 (fS φ) :=
  extL2_toL2 _ φ

theorem FLi_toL2 (φ : SchwartzMap Rd ℂ) : FLi (toL2 φ) = toL2 (fSi φ) :=
  extL2_toL2 _ φ

theorem norm_FL (f : L2 d) : ‖FL f‖ = ‖f‖ := norm_extL2 _ f

theorem norm_FLi (f : L2 d) : ‖FLi f‖ = ‖f‖ := norm_extL2 _ f

theorem FL_FLi (f : L2 d) : FL (FLi f) = f := by
  refine denseRange_toL2.induction_on f
    (isClosed_eq (FL.continuous.comp FLi.continuous) continuous_id) fun φ => ?_
  rw [FLi_toL2, FL_toL2, fS_fSi]

theorem FLi_FL (f : L2 d) : FLi (FL f) = f := by
  refine denseRange_toL2.induction_on f
    (isClosed_eq (FLi.continuous.comp FL.continuous) continuous_id) fun φ => ?_
  rw [FL_toL2, FLi_toL2, fSi_fS]

attribute [irreducible] FL FLi

/-- **Plancherel's theorem**: the Fourier transform extends from `𝓢(ℝ^d)` to a unitary operator
on `L²(ℝ^d)`. -/
noncomputable def fourierL2 : L2 d ≃ₗᵢ[ℂ] L2 d where
  toLinearEquiv := LinearEquiv.ofLinear FL.toLinearMap FLi.toLinearMap
    (LinearMap.ext fun f => FL_FLi f) (LinearMap.ext fun f => FLi_FL f)
  norm_map' := norm_FL

theorem fourierL2_apply (f : L2 d) : fourierL2 f = FL f := rfl

theorem fourierL2_toL2 (φ : SchwartzMap Rd ℂ) : fourierL2 (toL2 φ) = toL2 (fS φ) :=
  FL_toL2 φ

theorem fourierL2_symm_toL2 (φ : SchwartzMap Rd ℂ) : fourierL2.symm (toL2 φ) = toL2 (fSi φ) :=
  FLi_toL2 φ

/-! ### The multiplication formula and the identification on `L¹ ∩ L²` -/

/-- `∫ 𝓕f · g = ∫ f · 𝓕g` for integrable `f, g`. -/
theorem integral_fourier_mul_eq {f g : Rd → ℂ} (hf : Integrable f) (hg : Integrable g) :
    ∫ ξ, 𝓕 f ξ * g ξ = ∫ x, f x * 𝓕 g x := by
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ Rd)
    (μ := volume) (ν := volume) Real.continuous_fourierChar continuous_inner hf hg
  have e1 : ∀ ξ, VectorFourier.fourierIntegral 𝐞 volume (innerₗ Rd) f ξ = 𝓕 f ξ :=
    fun ξ => rfl
  have e2 : ∀ x, VectorFourier.fourierIntegral 𝐞 volume (innerₗ Rd).flip g x = 𝓕 g x := by
    intro x
    simp [Real.fourierIntegral, VectorFourier.fourierIntegral, real_inner_comm]
  simp_rw [e1, e2, smul_eq_mul] at h
  exact h

/-- Pairing with a Schwartz function as an `L²` inner product. -/
theorem integral_schwartz_mul_eq_inner (ψ : SchwartzMap Rd ℂ) (f : L2 d) :
    ∫ x, ψ x * f x = inner ℂ (toL2 (conjS ψ)) f := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_toL2 (conjS ψ)] with x hx
  rw [hx, conjS_apply, RCLike.inner_apply, Complex.conj_conj, mul_comm]

theorem integrable_schwartz_mul (ψ : SchwartzMap Rd ℂ) (f : L2 d) :
    Integrable fun x => ψ x * f x := by
  have h := L2.integrable_inner (𝕜 := ℂ) (toL2 (conjS ψ)) f
  refine h.congr ?_
  filter_upwards [coeFn_toL2 (conjS ψ)] with x hx
  rw [hx, conjS_apply, RCLike.inner_apply, Complex.conj_conj, mul_comm]

/-- **The multiplication formula on `L²`:** `∫ ψ · 𝓕f = ∫ 𝓕ψ · f` for `ψ ∈ 𝓢`, `f ∈ L²`. -/
theorem integral_mul_fourierL2 (ψ : SchwartzMap Rd ℂ) (f : L2 d) :
    ∫ ξ, ψ ξ * fourierL2 f ξ = ∫ x, fS ψ x * f x := by
  rw [integral_schwartz_mul_eq_inner, integral_schwartz_mul_eq_inner]
  refine denseRange_toL2.induction_on f
    (isClosed_eq (continuous_const.inner fourierL2.continuous)
      (continuous_const.inner continuous_id)) fun φ => ?_
  rw [fourierL2_toL2, ← integral_schwartz_mul_eq_inner, ← integral_schwartz_mul_eq_inner]
  have h1 : ∫ ξ, ψ ξ * (toL2 (fS φ) : Rd → ℂ) ξ = ∫ ξ, ψ ξ * 𝓕 (⇑φ) ξ := by
    refine integral_congr_ae ?_
    filter_upwards [coeFn_toL2 (fS φ)] with ξ hξ
    rw [hξ, coe_fS]
  have h2 : ∫ x, fS ψ x * (toL2 φ : Rd → ℂ) x = ∫ x, 𝓕 (⇑ψ) x * φ x := by
    refine integral_congr_ae ?_
    filter_upwards [coeFn_toL2 φ] with x hx
    rw [hx, coe_fS]
  rw [h1, h2, integral_fourier_mul_eq ψ.integrable φ.integrable]

/-- **The Plancherel transform is the Fourier integral on `L¹ ∩ L²`.** -/
theorem fourierL2_ae_eq_fourier (f : L2 d) (hf : Integrable (f : Rd → ℂ)) :
    (fourierL2 f : Rd → ℂ) =ᵐ[volume] 𝓕 (f : Rd → ℂ) := by
  have hc : Continuous (𝓕 (f : Rd → ℂ)) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner hf
  have hloc : LocallyIntegrable (fun ξ => (fourierL2 f : Rd → ℂ) ξ - 𝓕 (f : Rd → ℂ) ξ) volume :=
    ((Lp.memLp (fourierL2 f)).locallyIntegrable (by norm_num)).sub hc.locallyIntegrable
  have hbd : ∀ ξ, ‖𝓕 (f : Rd → ℂ) ξ‖ ≤ ∫ x, ‖(f : Rd → ℂ) x‖ := fun ξ =>
    VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
  have h := ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc fun g hg hgc => by
    obtain ⟨ψ, hψ⟩ : ∃ ψ : SchwartzMap Rd ℂ, ⇑ψ = fun x => ((g x : ℝ) : ℂ) :=
      ⟨schwartzOfCompact (fun x => ((g x : ℝ) : ℂ)) (Complex.ofRealCLM.contDiff.comp hg)
        (hgc.comp_left Complex.ofReal_zero), by
          ext x
          rfl⟩
    have hψx : ∀ x, ((g x : ℝ) : ℂ) = ψ x := fun x => by rw [hψ]
    have hi1 : Integrable fun ξ => ψ ξ * (fourierL2 f : Rd → ℂ) ξ :=
      integrable_schwartz_mul ψ (fourierL2 f)
    have hi2 : Integrable fun ξ => ψ ξ * 𝓕 (f : Rd → ℂ) ξ := by
      have := (ψ.integrable (μ := volume)).bdd_mul' (c := ∫ x, ‖(f : Rd → ℂ) x‖)
        hc.aestronglyMeasurable (Eventually.of_forall hbd)
      refine this.congr (Eventually.of_forall fun ξ => ?_)
      simp only
      rw [mul_comm]
    have e : (fun ξ => g ξ • ((fourierL2 f : Rd → ℂ) ξ - 𝓕 (f : Rd → ℂ) ξ)) =
        fun ξ => ψ ξ * (fourierL2 f : Rd → ℂ) ξ - ψ ξ * 𝓕 (f : Rd → ℂ) ξ := by
      funext ξ
      rw [Complex.real_smul, hψx, mul_sub]
    rw [e, integral_sub hi1 hi2, integral_mul_fourierL2]
    have h3 : ∫ ξ, ψ ξ * 𝓕 (f : Rd → ℂ) ξ = ∫ x, fS ψ x * (f : Rd → ℂ) x := by
      rw [← integral_fourier_mul_eq ψ.integrable hf]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only
      rw [coe_fS]
    rw [h3, sub_self]
  filter_upwards [h] with ξ hξ
  exact sub_eq_zero.1 hξ

end Sobolev

end ReyesMath

open Filter Topology Complex InnerProductSpace MeasureTheory Set
open scoped ContDiff FourierTransform

namespace ReyesMath

namespace Sobolev

variable {d : ℕ} {lam : ℝ}

local notation "Rd" => EuclideanSpace ℝ (Fin d)

/-! ### The dilation as a unitary operator -/

theorem dilL2_add (hlam : 0 < lam) (f g : L2 d) :
    dilL2 hlam (f + g) = dilL2 hlam f + dilL2 hlam g := by
  have h := dilL2_sub hlam (f + g) g
  rw [add_sub_cancel_right] at h
  rw [h, sub_add_cancel]

theorem dilL2_congr {a b : ℝ} (h : a = b) (ha : 0 < a) (hb : 0 < b) (f : L2 d) :
    dilL2 ha f = dilL2 hb f := by
  subst h
  rfl

theorem dilL2_inv (hlam : 0 < lam) (f : L2 d) : dilL2 (inv_pos.2 hlam) (dilL2 hlam f) = f := by
  apply Lp.ext
  filter_upwards [coeFn_dilL2 (inv_pos.2 hlam) (dilL2 hlam f),
    dilF_congr_ae (inv_pos.2 hlam) (coeFn_dilL2 hlam f)] with x h1 h2
  rw [h1, h2]
  simp only [dilF]
  rw [smul_smul, mul_inv_cancel₀ hlam.ne', one_smul, ← mul_assoc, ← Complex.ofReal_mul,
    ← Real.mul_rpow (inv_nonneg.2 hlam.le) hlam.le, inv_mul_cancel₀ hlam.ne', Real.one_rpow,
    Complex.ofReal_one, one_mul]

/-- The `L²`-unitary dilation `f ↦ λ^{d/2} f(λ ·)`. -/
noncomputable def dilLIE (hlam : 0 < lam) : L2 d ≃ₗᵢ[ℂ] L2 d where
  toFun := dilL2 hlam
  invFun := dilL2 (inv_pos.2 hlam)
  map_add' := dilL2_add hlam
  map_smul' := dilL2_smul hlam
  left_inv := dilL2_inv hlam
  right_inv f := by
    have h := dilL2_inv (inv_pos.2 hlam) f
    rwa [dilL2_congr (inv_inv lam) _ hlam] at h
  norm_map' := norm_dilL2 hlam

theorem dilLIE_apply (hlam : 0 < lam) (f : L2 d) : dilLIE hlam f = dilL2 hlam f := rfl

/-! ### The unitary Fourier transform of the manuscript -/

theorem two_pi_pos' : (0 : ℝ) < 2 * Real.pi := by positivity

/-- The unitary Fourier transform `û(ξ) = (2π)^{-d/2} ∫ u(x) e^{-ix·ξ} dx` on integrable
functions. -/
noncomputable def fourierU (u : Rd → ℂ) (ξ : Rd) : ℂ :=
  (((2 * Real.pi) ^ (-((d : ℝ) / 2)) : ℝ) : ℂ) *
    ∫ x, u x * Complex.exp (-((inner ℝ x ξ : ℝ) : ℂ) * Complex.I)

theorem fourierU_eq (u : Rd → ℂ) (ξ : Rd) :
    fourierU u ξ = dilF (2 * Real.pi)⁻¹ (𝓕 u) ξ := by
  rw [fourierU, dilF, Real.fourierIntegral_eq']
  congr 1
  · rw [Real.inv_rpow two_pi_pos'.le, Real.rpow_neg two_pi_pos'.le]
  · congr 1
    funext x
    rw [real_inner_smul_right, smul_eq_mul, mul_comm (u x)]
    have hπ : (2 * Real.pi) ≠ 0 := two_pi_pos'.ne'
    have e : -2 * Real.pi * ((2 * Real.pi)⁻¹ * inner ℝ x ξ) = -inner ℝ x ξ := by
      field_simp
    rw [e, Complex.ofReal_neg]

/-- **The unitary Fourier transform on `L²(ℝ^d)`**: the Plancherel extension of `fourierU`
(`FU_ae_eq`), a unitary operator. -/
noncomputable def FU : L2 d ≃ₗᵢ[ℂ] L2 d := fourierL2.trans (dilLIE (inv_pos.2 two_pi_pos'))

theorem FU_apply (u : L2 d) : FU u = dilL2 (inv_pos.2 two_pi_pos') (fourierL2 u) := rfl

/-- On `L¹ ∩ L²`, `FU` is the integral transform `fourierU`. -/
theorem FU_ae_eq (u : L2 d) (hu : Integrable (u : Rd → ℂ)) :
    (FU u : Rd → ℂ) =ᵐ[volume] fourierU (u : Rd → ℂ) := by
  have h1 : (FU u : Rd → ℂ) =ᵐ[volume] dilF (2 * Real.pi)⁻¹ (fourierL2 u : Rd → ℂ) :=
    coeFn_dilL2 (inv_pos.2 two_pi_pos') (fourierL2 u)
  have h2 := dilF_congr_ae (inv_pos.2 two_pi_pos') (fourierL2_ae_eq_fourier u hu)
  filter_upwards [h1, h2] with ξ e1 e2
  rw [e1, e2, fourierU_eq]

/-- `FU` is unitary (Plancherel). -/
theorem norm_FU (u : L2 d) : ‖FU u‖ = ‖u‖ := FU.norm_map u

/-! ### The isolated-shell theorem -/

/-- **Theorem (zero `L²` state on an isolated Fourier shell).**  For `d ≥ 1`, if the Fourier
transform of `u ∈ L²(ℝ^d)` vanishes almost everywhere off the shell `|ξ| = k₀`, then `u = 0`. -/
theorem shell_theorem (hd : 1 ≤ d) (k₀ : ℝ) (u : L2 d)
    (hsupp : ∀ᵐ ξ ∂volume, ξ ∉ Metric.sphere (0 : Rd) k₀ → (FU u : Rd → ℂ) ξ = 0) :
    u = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := Nat.exists_eq_add_of_le' hd
  have hS : ∀ᵐ ξ ∂(volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))),
      ξ ∉ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) k₀ :=
    measure_eq_zero_iff_ae_notMem.1 (euclidean_frequency_shell_measure_zero n k₀)
  have hae : (FU u : EuclideanSpace ℝ (Fin (n + 1)) → ℂ) =ᵐ[volume] 0 := by
    filter_upwards [hS, hsupp] with ξ h1 h2
    exact h2 h1
  have h0 : FU u = 0 := Lp.eq_zero_iff_ae_eq_zero.2 hae
  exact (LinearIsometryEquiv.map_eq_zero_iff FU).1 h0

theorem tsupport_ofReal_comp (g : Rd → ℝ) :
    tsupport (fun x => ((g x : ℝ) : ℂ)) = tsupport g := by
  unfold tsupport
  congr 1
  ext x
  simp [Function.mem_support]

/-- **Theorem**, distributional form: if `û` vanishes as a distribution off the shell, `u = 0`. -/
theorem shell_theorem_distrib (hd : 1 ≤ d) (k₀ : ℝ) (u : L2 d)
    (hsupp : ∀ ψ : Rd → ℂ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ (Metric.sphere (0 : Rd) k₀)ᶜ → ∫ ξ, ψ ξ * (FU u : Rd → ℂ) ξ = 0) :
    u = 0 := by
  refine shell_theorem hd k₀ u ?_
  have hU : IsOpen (Metric.sphere (0 : Rd) k₀)ᶜ := Metric.isClosed_sphere.isOpen_compl
  have hloc : LocallyIntegrableOn (FU u : Rd → ℂ) (Metric.sphere (0 : Rd) k₀)ᶜ volume :=
    ((Lp.memLp (FU u)).locallyIntegrable (by norm_num)).locallyIntegrableOn _
  have h := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc fun g hg hgc hgs => by
    have h1 := hsupp (fun x => ((g x : ℝ) : ℂ)) (Complex.ofRealCLM.contDiff.comp hg)
      (hgc.comp_left Complex.ofReal_zero) (by rw [tsupport_ofReal_comp]; exact hgs)
    simpa only [Complex.real_smul] using h1
  filter_upwards [h] with ξ hξ
  exact hξ

end Sobolev

end ReyesMath

open Filter Topology Complex InnerProductSpace MeasureTheory Set Polynomial
open scoped ContDiff FourierTransform

namespace ReyesMath

namespace Sobolev

variable {d : ℕ}

local notation "Rd" => EuclideanSpace ℝ (Fin d)

/-! ### `P(−Δ)` on Schwartz space and its Fourier symbol -/

/-- `P(−Δ)` on Schwartz space, for a real polynomial `P`. -/
noncomputable def polyLapS (P : Polynomial ℝ) : SchwartzMap Rd ℂ →L[ℂ] SchwartzMap Rd ℂ :=
  Polynomial.aeval (-(lapS (d := d))) P

theorem fS_add (φ ψ : SchwartzMap Rd ℂ) : fS (φ + ψ) = fS φ + fS ψ :=
  map_add (SchwartzMap.fourierTransformCLM ℂ) φ ψ

theorem fS_sub (φ ψ : SchwartzMap Rd ℂ) : fS (φ - ψ) = fS φ - fS ψ :=
  map_sub (SchwartzMap.fourierTransformCLM ℂ) φ ψ

theorem fS_smul (c : ℂ) (φ : SchwartzMap Rd ℂ) : fS (c • φ) = c • fS φ :=
  map_smul (SchwartzMap.fourierTransformCLM ℂ) c φ

theorem fS_neg_lapS (φ : SchwartzMap Rd ℂ) (ξ : Rd) :
    fS ((-(lapS (d := d))) φ) ξ = (qS ξ : ℂ) * fS φ ξ := by
  have e : fS ((-(lapS (d := d))) φ) = -fS (lapS φ) := by
    rw [ContinuousLinearMap.neg_apply]
    exact map_neg (SchwartzMap.fourierTransformCLM ℂ) (lapS φ)
  rw [e]
  show -(fS (lapS φ) ξ) = _
  rw [coe_fS, coe_fS, fourier_lapS]
  ring

theorem algebraMap_apply_schwartz (a : ℝ) (φ : SchwartzMap Rd ℂ) :
    (algebraMap ℝ (SchwartzMap Rd ℂ →L[ℂ] SchwartzMap Rd ℂ) a) φ = (a : ℂ) • φ := by
  rw [Algebra.algebraMap_eq_smul_one]
  rfl

/-- `𝓕(P(−Δ)φ)(ξ) = P(4π²|ξ|²) 𝓕φ(ξ)`. -/
theorem fS_polyLapS (P : Polynomial ℝ) (φ : SchwartzMap Rd ℂ) (ξ : Rd) :
    fS (polyLapS P φ) ξ = ((P.eval (qS ξ) : ℝ) : ℂ) * fS φ ξ := by
  induction P using Polynomial.induction_on generalizing φ with
  | C a =>
    rw [polyLapS, Polynomial.aeval_C, algebraMap_apply_schwartz, fS_smul, SchwartzMap.smul_apply,
      eval_C, smul_eq_mul]
  | add p q hp hq =>
    rw [polyLapS, Polynomial.aeval_add, ContinuousLinearMap.add_apply, fS_add,
      SchwartzMap.add_apply]
    rw [← polyLapS, ← polyLapS, hp, hq, eval_add, Complex.ofReal_add]
    ring
  | monomial n a h =>
    have e : polyLapS (C a * X ^ (n + 1)) φ = polyLapS (C a * X ^ n) ((-(lapS (d := d))) φ) := by
      rw [polyLapS, polyLapS, pow_succ, ← mul_assoc, Polynomial.aeval_mul, Polynomial.aeval_X,
        ContinuousLinearMap.mul_apply]
    rw [e, h, fS_neg_lapS]
    simp only [eval_mul, eval_C, eval_pow, eval_X, Complex.ofReal_mul, Complex.ofReal_pow]
    ring

theorem fSi_eq_fS_neg (g : SchwartzMap Rd ℂ) (ξ : Rd) : fSi g ξ = fS g (-ξ) := by
  rw [coe_fSi, coe_fS, Real.fourierIntegralInv_eq_fourierIntegral_neg]

theorem qS_neg (ξ : Rd) : qS (-ξ) = qS ξ := by
  simp only [qS, norm_neg]

/-- `𝓕⁻(P(−Δ)g)(ξ) = P(4π²|ξ|²) 𝓕⁻g(ξ)`. -/
theorem fSi_polyLapS (P : Polynomial ℝ) (g : SchwartzMap Rd ℂ) (ξ : Rd) :
    fSi (polyLapS P g) ξ = ((P.eval (qS ξ) : ℝ) : ℂ) * fSi g ξ := by
  rw [fSi_eq_fS_neg, fS_polyLapS, qS_neg, ← fSi_eq_fS_neg]

/-! ### Fourier multipliers with null level sets -/

theorem contDiff_div_of_ne {ψ m : Rd → ℂ} (hψ : ContDiff ℝ ∞ ψ) (hm : ContDiff ℝ ∞ m)
    (hne : ∀ x ∈ tsupport ψ, m x ≠ 0) : ContDiff ℝ ∞ fun x => ψ x / m x := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : m x = 0
  · have hxs : x ∉ tsupport ψ := fun h => hne x h hx
    have hev : (fun y => ψ y / m y) =ᶠ[𝓝 x] fun _ => (0 : ℂ) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hxs] with y hy
      simp [hy]
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · have h := hψ.contDiffAt.mul (hm.contDiffAt.inv hx)
    simpa only [div_eq_mul_inv] using h

theorem schwartz_ext_fSi {φ ψ : SchwartzMap Rd ℂ} (h : ∀ ξ, fSi φ ξ = fSi ψ ξ) : φ = ψ := by
  have h' : fSi φ = fSi ψ := SchwartzMap.ext h
  rw [← fS_fSi φ, ← fS_fSi ψ, h']

/-- **Fourier multipliers with null level sets.**  Let `T` act as the smooth multiplier `m` under
`𝓕⁻`. If `u ∈ L²(ℝ^d)` satisfies `∫ u · Tφ = 0` for every `φ ∈ 𝓢` (i.e. `Tᵗu = 0` in `𝓢'`) and
`{m = 0}` is Lebesgue-null, then `u = 0`. -/
theorem eq_zero_of_multiplier (T : SchwartzMap Rd ℂ →L[ℂ] SchwartzMap Rd ℂ) {m : Rd → ℂ}
    (hm : ContDiff ℝ ∞ m) (hT : ∀ g ξ, fSi (T g) ξ = m ξ * fSi g ξ)
    (hnull : volume {ξ | m ξ = 0} = 0) (u : L2 d)
    (h : ∀ φ : SchwartzMap Rd ℂ, ∫ x, (u : Rd → ℂ) x * T φ x = 0) : u = 0 := by
  have hU : IsOpen {ξ : Rd | m ξ ≠ 0} := isOpen_ne_fun hm.continuous continuous_const
  have hloc : LocallyIntegrableOn (fourierL2 u : Rd → ℂ) {ξ | m ξ ≠ 0} volume :=
    ((Lp.memLp (fourierL2 u)).locallyIntegrable (by norm_num)).locallyIntegrableOn _
  have hz := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc fun g hg hgc hgs => by
    have hgC : ContDiff ℝ ∞ fun x => ((g x : ℝ) : ℂ) := Complex.ofRealCLM.contDiff.comp hg
    have hgCc : HasCompactSupport fun x => ((g x : ℝ) : ℂ) := hgc.comp_left Complex.ofReal_zero
    obtain ⟨ψ, hψ⟩ : ∃ ψ : SchwartzMap Rd ℂ, ∀ x, ψ x = ((g x : ℝ) : ℂ) :=
      ⟨schwartzOfCompact _ hgC hgCc, fun x => rfl⟩
    have hψs : tsupport ⇑ψ = tsupport g := by
      rw [show ⇑ψ = fun x => ((g x : ℝ) : ℂ) from funext hψ, tsupport_ofReal_comp]
    have hne : ∀ x ∈ tsupport ⇑ψ, m x ≠ 0 := fun x hx => hgs (hψs ▸ hx)
    have hdc : ContDiff ℝ ∞ fun x => ψ x / m x := contDiff_div_of_ne ψ.smooth' hm hne
    have hdcc : HasCompactSupport fun x => ψ x / m x := by
      refine HasCompactSupport.mono (f := fun x => ((g x : ℝ) : ℂ)) hgCc fun x hx => ?_
      simp only [Function.mem_support] at hx ⊢
      intro h0
      apply hx
      rw [hψ, h0, zero_div]
    obtain ⟨χ, hχ⟩ : ∃ χ : SchwartzMap Rd ℂ, ∀ x, χ x = ψ x / m x :=
      ⟨schwartzOfCompact _ hdc hdcc, fun x => rfl⟩
    have hTφ : T (fS χ) = fS ψ := by
      refine schwartz_ext_fSi fun ξ => ?_
      rw [hT, fSi_fS, fSi_fS, hχ]
      by_cases hmξ : m ξ = 0
      · have hξ : ξ ∉ tsupport ⇑ψ := fun hx => hne ξ hx hmξ
        rw [hmξ, zero_mul]
        exact (image_eq_zero_of_notMem_tsupport hξ).symm
      · field_simp
    have e : ∫ ξ, g ξ • (fourierL2 u : Rd → ℂ) ξ = ∫ ξ, ψ ξ * (fourierL2 u : Rd → ℂ) ξ := by
      refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
      simp only
      rw [Complex.real_smul, hψ]
    rw [e, integral_mul_fourierL2, ← hTφ]
    have h1 := h (fS χ)
    rw [← h1]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    rw [mul_comm]
  have hae : (fourierL2 u : Rd → ℂ) =ᵐ[volume] 0 := by
    have hZ : ∀ᵐ ξ ∂(volume : Measure Rd), ξ ∉ {ξ | m ξ = 0} :=
      measure_eq_zero_iff_ae_notMem.1 hnull
    filter_upwards [hz, hZ] with ξ h1 h2
    exact h1 h2
  have h0 : fourierL2 u = 0 := Lp.eq_zero_iff_ae_eq_zero.2 hae
  exact (LinearIsometryEquiv.map_eq_zero_iff fourierL2).1 h0

/-! ### Polynomial dispersion -/

theorem contDiff_polyEval (P : Polynomial ℝ) {f : Rd → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ fun x => P.eval (f x) := by
  simp_rw [Polynomial.eval_eq_sum_range]
  exact ContDiff.sum fun i _ => contDiff_const.mul (hf.pow i)

theorem contDiff_qS : ContDiff ℝ ∞ (qS (d := d)) :=
  contDiff_const.mul (contDiff_norm_sq ℝ)

/-- For a nonconstant real polynomial `P`, the set `{ξ : P(4π²|ξ|²) = λ}` is a finite union of
spheres, hence Lebesgue-null (`d ≥ 1`). -/
theorem polyZero_null (hd : 1 ≤ d) {P : Polynomial ℝ} (hP : 0 < P.natDegree) (lam : ℝ) :
    volume {ξ : Rd | P.eval (qS ξ) = lam} = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := Nat.exists_eq_add_of_le' hd
  have hQ : P - C lam ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    rw [h, natDegree_C] at hP
    exact lt_irrefl 0 hP
  have hsub : {ξ : EuclideanSpace ℝ (Fin (n + 1)) | P.eval (qS ξ) = lam} ⊆
      ⋃ s ∈ (P - C lam).roots.toFinset,
        Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) (Real.sqrt (s / (2 * Real.pi) ^ 2)) := by
    intro ξ hξ
    simp only [mem_setOf_eq] at hξ
    simp only [mem_iUnion, Multiset.mem_toFinset, mem_sphere_zero_iff_norm]
    refine ⟨qS ξ, (mem_roots hQ).2 ?_, ?_⟩
    · rw [IsRoot, eval_sub, eval_C, hξ, sub_self]
    · have hπ : (2 * Real.pi) ^ 2 ≠ 0 := by positivity
      rw [qS, mul_div_cancel_left₀ _ hπ, Real.sqrt_sq (norm_nonneg ξ)]
  refine measure_mono_null hsub ?_
  exact (measure_biUnion_null_iff (Finset.countable_toSet _)).2 fun s _ =>
    euclidean_frequency_shell_measure_zero n _

/-- **Corollary (nonconstant polynomial dispersion).**  Let `P` be a nonconstant real polynomial,
`λ ∈ ℝ`, and `u ∈ L²(ℝ^d)` (`d ≥ 1`) with `P(−Δ)u = λu` in `𝓢'(ℝ^d)`, i.e.
`∫ u · P(−Δ)φ = λ ∫ u · φ` for every Schwartz `φ`. Then `u = 0`. -/
theorem poly_dispersion (hd : 1 ≤ d) {P : Polynomial ℝ} (hP : 0 < P.natDegree) (lam : ℝ)
    (u : L2 d)
    (h : ∀ φ : SchwartzMap Rd ℂ,
      ∫ x, (u : Rd → ℂ) x * polyLapS P φ x = (lam : ℂ) * ∫ x, (u : Rd → ℂ) x * φ x) :
    u = 0 := by
  have hm : ContDiff ℝ ∞ fun ξ : Rd => (((P.eval (qS ξ) - lam : ℝ)) : ℂ) :=
    Complex.ofRealCLM.contDiff.comp ((contDiff_polyEval P contDiff_qS).sub contDiff_const)
  refine eq_zero_of_multiplier
    (polyLapS (d := d) P - (lam : ℂ) • ContinuousLinearMap.id ℂ (SchwartzMap Rd ℂ)) hm
    (fun g ξ => ?_) ?_ u fun φ => ?_
  · rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, fSi_eq_fS_neg, fS_sub, fS_smul, SchwartzMap.sub_apply,
      SchwartzMap.smul_apply, ← fSi_eq_fS_neg, ← fSi_eq_fS_neg, fSi_polyLapS, smul_eq_mul,
      Complex.ofReal_sub]
    ring
  · have e : {ξ : Rd | (((P.eval (qS ξ) - lam : ℝ)) : ℂ) = 0} = {ξ | P.eval (qS ξ) = lam} := by
      ext ξ
      simp only [mem_setOf_eq, Complex.ofReal_eq_zero, sub_eq_zero]
    rw [e]
    exact polyZero_null hd hP lam
  · have hi1 : Integrable fun x => (u : Rd → ℂ) x * polyLapS P φ x :=
      (integrable_schwartz_mul (polyLapS P φ) u).congr
        (Eventually.of_forall fun x => mul_comm _ _)
    have hi2 : Integrable fun x => (u : Rd → ℂ) x * φ x :=
      (integrable_schwartz_mul φ u).congr (Eventually.of_forall fun x => mul_comm _ _)
    have e : (fun x => (u : Rd → ℂ) x *
        ((polyLapS (d := d) P - (lam : ℂ) • ContinuousLinearMap.id ℂ (SchwartzMap Rd ℂ)) φ) x) =
        fun x => (u : Rd → ℂ) x * polyLapS P φ x - (lam : ℂ) * ((u : Rd → ℂ) x * φ x) := by
      funext x
      rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.id_apply, SchwartzMap.sub_apply, SchwartzMap.smul_apply, smul_eq_mul]
      ring
    rw [e, integral_sub hi1 (hi2.const_mul _), integral_const_mul, h φ, sub_self]

end Sobolev

end ReyesMath

open Filter Topology Complex InnerProductSpace MeasureTheory Set Polynomial
open scoped ContDiff FourierTransform

namespace ReyesMath

namespace Sobolev

variable {d : ℕ}

local notation "Rd" => EuclideanSpace ℝ (Fin d)

/-! ### Pointwise bounds for the Laplacian -/

/-- `|Δf(x)| ≤ d ‖D²f(x)‖`. -/
theorem norm_laplacian_le (f : Rd → ℂ) (x : Rd) :
    ‖Δ f x‖ ≤ d * ‖iteratedFDeriv ℝ 2 f x‖ := by
  have h := congrFun
    (laplacian_eq_iteratedFDeriv_orthonormalBasis (f := f) (EuclideanSpace.basisFun (Fin d) ℝ)) x
  rw [h]
  refine (norm_sum_le _ _).trans ?_
  have hb : ∀ i : Fin d, ‖iteratedFDeriv ℝ 2 f x
      ![EuclideanSpace.basisFun (Fin d) ℝ i, EuclideanSpace.basisFun (Fin d) ℝ i]‖ ≤
      ‖iteratedFDeriv ℝ 2 f x‖ := by
    intro i
    refine ((iteratedFDeriv ℝ 2 f x).le_opNorm _).trans (le_of_eq ?_)
    simp [Fin.prod_univ_two]
  calc ∑ i, ‖iteratedFDeriv ℝ 2 f x
        ![EuclideanSpace.basisFun (Fin d) ℝ i, EuclideanSpace.basisFun (Fin d) ℝ i]‖
      ≤ ∑ _i : Fin d, ‖iteratedFDeriv ℝ 2 f x‖ := Finset.sum_le_sum fun i _ => hb i
    _ = d * ‖iteratedFDeriv ℝ 2 f x‖ := by simp

/-! ### Cutoffs -/

/-- A smooth bump, equal to `1` on the unit ball and supported in the ball of radius `2`. -/
noncomputable def bumpχ (d : ℕ) : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)) :=
  ⟨1, 2, zero_lt_one, one_lt_two⟩

/-- The cutoff `χ(x/(n+1))`. -/
noncomputable def cutN (n : ℕ) (x : Rd) : ℝ := bumpχ d (((n : ℝ) + 1)⁻¹ • x)

theorem contDiff_cutN (n : ℕ) : ContDiff ℝ ∞ (cutN (d := d) n) :=
  (bumpχ d).contDiff.comp (contDiff_id.const_smul _)

theorem hasCompactSupport_cutN (n : ℕ) : HasCompactSupport (cutN (d := d) n) :=
  (bumpχ d).hasCompactSupport.comp_smul (inv_ne_zero (by positivity))

theorem cutN_eq_one {n : ℕ} {x : Rd} (hx : ‖x‖ ≤ n + 1) : cutN n x = 1 := by
  apply (bumpχ d).one_of_mem_closedBall
  rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_pos (by positivity : (0 : ℝ) < n + 1)]
  show ((n : ℝ) + 1)⁻¹ * ‖x‖ ≤ 1
  rw [inv_mul_le_iff₀ (by positivity), mul_one]
  exact hx

theorem cutN_nonneg (n : ℕ) (x : Rd) : 0 ≤ cutN n x := (bumpχ d).nonneg

theorem cutN_le_one (n : ℕ) (x : Rd) : cutN n x ≤ 1 := (bumpχ d).le_one

theorem norm_iteratedFDeriv_cutN_le (i : ℕ) {B : ℝ}
    (hB : ∀ y, ‖iteratedFDeriv ℝ i (bumpχ d) y‖ ≤ B) (n : ℕ) (x : Rd) :
    ‖iteratedFDeriv ℝ i (cutN (d := d) n) x‖ ≤ B := by
  obtain ⟨L, hL⟩ : ∃ L : Rd →L[ℝ] Rd, L = ((n : ℝ) + 1)⁻¹ • ContinuousLinearMap.id ℝ Rd :=
    ⟨_, rfl⟩
  have hLn : ‖L‖ ≤ 1 := by
    rw [hL]
    refine (norm_smul_le (((n : ℝ) + 1)⁻¹) (ContinuousLinearMap.id ℝ Rd)).trans ?_
    rw [Real.norm_eq_abs, abs_inv, abs_of_pos (by positivity : (0 : ℝ) < n + 1)]
    calc ((n : ℝ) + 1)⁻¹ * ‖ContinuousLinearMap.id ℝ Rd‖ ≤ 1 * 1 :=
          mul_le_mul (inv_le_one_of_one_le₀ (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]))
            (ContinuousLinearMap.norm_id_le) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have e : cutN (d := d) n = ⇑(bumpχ d) ∘ L := by
    funext y
    rw [hL]
    rfl
  rw [e, L.iteratedFDeriv_comp_right (bumpχ d).contDiff x (TemperateGrowth.le_infty i)]
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  calc ‖(iteratedFDeriv ℝ i (⇑(bumpχ d)) (L x)).compContinuousLinearMap fun _ => L‖
      ≤ ‖iteratedFDeriv ℝ i (⇑(bumpχ d)) (L x)‖ * ∏ _j : Fin i, ‖L‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ B * 1 := mul_le_mul (hB _) (Finset.prod_le_one (fun _ _ => norm_nonneg _)
        (fun _ _ => hLn)) (Finset.prod_nonneg fun _ _ => norm_nonneg _) hB0
    _ = B := mul_one B

theorem exists_cutN_bound : ∃ B, 0 ≤ B ∧ ∀ i ≤ 2, ∀ (n : ℕ) (x : Rd),
    ‖iteratedFDeriv ℝ i (cutN (d := d) n) x‖ ≤ B := by
  have hb : ∀ i : ℕ, ∃ B, ∀ y : Rd, ‖iteratedFDeriv ℝ i (bumpχ d) y‖ ≤ B := fun i =>
    ((bumpχ d).contDiff.continuous_iteratedFDeriv (TemperateGrowth.le_infty i)).norm
      |>.bounded_above_of_compact_support ((bumpχ d).hasCompactSupport.iteratedFDeriv i).norm
      |>.imp fun B hB y => by simpa using hB y
  obtain ⟨B₀, h₀⟩ := hb 0
  obtain ⟨B₁, h₁⟩ := hb 1
  obtain ⟨B₂, h₂⟩ := hb 2
  have p₀ : 0 ≤ B₀ := (norm_nonneg _).trans (h₀ 0)
  have p₁ : 0 ≤ B₁ := (norm_nonneg _).trans (h₁ 0)
  have p₂ : 0 ≤ B₂ := (norm_nonneg _).trans (h₂ 0)
  refine ⟨B₀ + B₁ + B₂, by positivity, fun i hi n x => ?_⟩
  interval_cases i
  · exact (norm_iteratedFDeriv_cutN_le 0 h₀ n x).trans (by linarith)
  · exact (norm_iteratedFDeriv_cutN_le 1 h₁ n x).trans (by linarith)
  · exact (norm_iteratedFDeriv_cutN_le 2 h₂ n x).trans (by linarith)

/-- Schwartz decay of the first two derivatives. -/
theorem exists_decay_bound (φ : SchwartzMap Rd ℂ) (K : ℕ) : ∃ A, 0 ≤ A ∧ ∀ j ≤ 2, ∀ x : Rd,
    ‖iteratedFDeriv ℝ j φ x‖ ≤ A / (1 + ‖x‖) ^ K := by
  refine ⟨2 ^ K * (Finset.Iic (K, 2)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) φ,
    by positivity, fun j hj x => ?_⟩
  rw [le_div_iff₀ (by positivity), mul_comm]
  exact SchwartzMap.one_add_le_sup_seminorm_apply (m := (K, 2)) le_rfl hj φ x

/-! ### `L²` convergence by domination -/

theorem tendsto_toL2_of_dominated {ψn : ℕ → SchwartzMap Rd ℂ} {ψ : SchwartzMap Rd ℂ}
    {G : Rd → ℝ} (hG : Integrable G) (hb : ∀ n x, ‖ψn n x - ψ x‖ ^ 2 ≤ G x)
    (hlim : ∀ x, Tendsto (fun n => ψn n x) atTop (𝓝 (ψ x))) :
    Tendsto (fun n => toL2 (ψn n)) atTop (𝓝 (toL2 ψ)) := by
  have e : ∀ n, ‖toL2 (ψn n) - toL2 ψ‖ ^ 2 = ∫ x, ‖ψn n x - ψ x‖ ^ 2 := fun n => by
    rw [← map_sub, norm_toL2_sq]
    rfl
  have hint : Tendsto (fun n => ∫ x, ‖ψn n x - ψ x‖ ^ 2) atTop (𝓝 (∫ _x : Rd, (0 : ℝ))) := by
    refine tendsto_integral_of_dominated_convergence G (fun n => ?_) hG
      (fun n => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
    · exact (((ψn n).continuous.sub ψ.continuous).norm.pow 2).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact hb n x
    · have h := (((hlim x).sub (tendsto_const_nhds (x := ψ x))).norm).pow 2
      simpa using h
  rw [integral_zero] at hint
  simp_rw [← e] at hint
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h2 := hint.sqrt
  simp only [Real.sqrt_zero, Real.sqrt_sq (norm_nonneg _)] at h2
  exact h2

theorem sq_bound_arith {a M t : ℝ} {K : ℕ} (ht : 0 < t) (ha : 0 ≤ a) (h : a ≤ M / t ^ K) :
    a ^ 2 ≤ M ^ 2 * t ^ (-(2 * K : ℝ)) := by
  have hM : 0 ≤ M / t ^ K := ha.trans h
  have e : t ^ (-(2 * K : ℝ)) = ((t ^ K) ^ 2)⁻¹ := by
    rw [Real.rpow_neg ht.le, ← pow_mul, show (2 * K : ℝ) = ((K * 2 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast]
  rw [e, ← div_eq_mul_inv, ← div_pow]
  exact pow_le_pow_left₀ ha h 2

/-- **Cutoff approximation**: every Schwartz function is the limit of compactly supported Schwartz
functions in the graph norm of `Δ` on `L²`. -/
theorem exists_cutoff_seq (φ : SchwartzMap Rd ℂ) :
    ∃ φn : ℕ → SchwartzMap Rd ℂ, (∀ n, HasCompactSupport ⇑(φn n)) ∧
      Tendsto (fun n => toL2 (φn n)) atTop (𝓝 (toL2 φ)) ∧
      Tendsto (fun n => toL2 (lapS (φn n))) atTop (𝓝 (toL2 (lapS φ))) := by
  have hc : ∀ n : ℕ, ContDiff ℝ ∞ fun x => cutN (d := d) n x • φ x := fun n =>
    (contDiff_cutN n).smul φ.smooth'
  have hs : ∀ n : ℕ, HasCompactSupport fun x => cutN (d := d) n x • φ x := fun n =>
    (hasCompactSupport_cutN n).smul_right
  have hev : ∀ x : Rd, ∀ᶠ n : ℕ in atTop, ∀ y ∈ Metric.ball x 1, cutN (d := d) n y = 1 := by
    intro x
    filter_upwards [eventually_ge_atTop ⌈‖x‖⌉₊] with n hn y hy
    apply cutN_eq_one
    have h1 : ‖y‖ ≤ ‖x‖ + 1 := by
      have := norm_le_norm_add_norm_sub' y x
      rw [mem_ball_iff_norm] at hy
      linarith
    have h2 : ‖x‖ ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn)
    linarith
  refine ⟨fun n => schwartzOfCompact _ (hc n) (hs n), fun n => hs n, ?_, ?_⟩
  · refine tendsto_toL2_of_dominated (integrable_normSq φ) (fun n x => ?_) (fun x => ?_)
    · show ‖cutN n x • φ x - φ x‖ ^ 2 ≤ ‖φ x‖ ^ 2
      have e : cutN (d := d) n x • φ x - φ x = (cutN n x - 1) • φ x := by
        rw [sub_smul, one_smul]
      rw [e, norm_smul, Real.norm_eq_abs, abs_of_nonpos (by linarith [cutN_le_one (d := d) n x])]
      have h0 := cutN_nonneg (d := d) n x
      have h1 := cutN_le_one (d := d) n x
      have hφ := norm_nonneg (φ x)
      have h2 : 0 ≤ -(cutN (d := d) n x - 1) := by linarith
      have h4 : -(cutN (d := d) n x - 1) * ‖φ x‖ ≤ ‖φ x‖ := by nlinarith
      exact pow_le_pow_left₀ (mul_nonneg h2 hφ) h4 2
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev x] with n hn
      show φ x = cutN n x • φ x
      rw [hn x (Metric.mem_ball_self one_pos), one_smul]
  · obtain ⟨B, hB0, hB⟩ := exists_cutN_bound (d := d)
    obtain ⟨A, hA0, hA⟩ := exists_decay_bound φ (d + 1)
    obtain ⟨M, hM⟩ : ∃ M, M = d * (4 * B * A) + d * A := ⟨_, rfl⟩
    have hlapn : ∀ (n : ℕ) (x : Rd), ‖Δ (fun y => cutN (d := d) n y • φ y) x‖ ≤
        d * (4 * B * A) / (1 + ‖x‖) ^ (d + 1) := by
      intro n x
      have ht : 0 < (1 + ‖x‖) ^ (d + 1) := by positivity
      refine (norm_laplacian_le _ x).trans ?_
      have hL := norm_iteratedFDeriv_smul_le (contDiff_cutN (d := d) n) φ.smooth' x
        (n := 2) (TemperateGrowth.le_infty 2)
      have hsum : ∑ i ∈ Finset.range (2 + 1), ((2 : ℕ).choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (cutN (d := d) n) x‖ * ‖iteratedFDeriv ℝ (2 - i) (⇑φ) x‖ ≤
          ∑ i ∈ Finset.range (2 + 1), ((2 : ℕ).choose i : ℝ) * B *
            (A / (1 + ‖x‖) ^ (d + 1)) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi2 : i ≤ 2 := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
        refine mul_le_mul (mul_le_mul_of_nonneg_left (hB i hi2 n x) (by positivity))
          (hA (2 - i) (Nat.sub_le 2 i) x) (norm_nonneg _) (by positivity)
      have h4 : ∑ i ∈ Finset.range (2 + 1), ((2 : ℕ).choose i : ℝ) * B *
          (A / (1 + ‖x‖) ^ (d + 1)) = 4 * B * (A / (1 + ‖x‖) ^ (d + 1)) := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]
        norm_num [Finset.sum_range_succ]
      calc (d : ℝ) * ‖iteratedFDeriv ℝ 2 (fun y => cutN (d := d) n y • φ y) x‖
          ≤ d * (4 * B * (A / (1 + ‖x‖) ^ (d + 1))) :=
            mul_le_mul_of_nonneg_left ((hL.trans hsum).trans (le_of_eq h4)) (by positivity)
        _ = d * (4 * B * A) / (1 + ‖x‖) ^ (d + 1) := by ring
    have hlap : ∀ x : Rd, ‖Δ (⇑φ) x‖ ≤ d * A / (1 + ‖x‖) ^ (d + 1) := by
      intro x
      refine (norm_laplacian_le _ x).trans ?_
      calc (d : ℝ) * ‖iteratedFDeriv ℝ 2 (⇑φ) x‖ ≤ d * (A / (1 + ‖x‖) ^ (d + 1)) :=
            mul_le_mul_of_nonneg_left (hA 2 le_rfl x) (by positivity)
        _ = d * A / (1 + ‖x‖) ^ (d + 1) := by ring
    have hG : Integrable fun x : Rd => M ^ 2 * (1 + ‖x‖) ^ (-(2 * (d + 1 : ℕ) : ℝ)) := by
      refine (integrable_one_add_norm ?_).const_mul _
      rw [finrank_euclideanSpace_fin]
      push_cast
      linarith
    refine tendsto_toL2_of_dominated hG (fun n x => ?_) (fun x => ?_)
    · have ht : 0 < 1 + ‖x‖ := by positivity
      refine sq_bound_arith ht (norm_nonneg _) ?_
      show ‖lapS (schwartzOfCompact _ (hc n) (hs n)) x - lapS φ x‖ ≤ M / (1 + ‖x‖) ^ (d + 1)
      rw [lapS_apply, lapS_apply, coe_schwartzOfCompact]
      calc ‖Δ (fun y => cutN (d := d) n y • φ y) x - Δ (⇑φ) x‖
          ≤ ‖Δ (fun y => cutN (d := d) n y • φ y) x‖ + ‖Δ (⇑φ) x‖ := norm_sub_le _ _
        _ ≤ d * (4 * B * A) / (1 + ‖x‖) ^ (d + 1) + d * A / (1 + ‖x‖) ^ (d + 1) :=
            add_le_add (hlapn n x) (hlap x)
        _ = M / (1 + ‖x‖) ^ (d + 1) := by rw [hM, add_div]
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev x] with n hn
      show lapS φ x = lapS (schwartzOfCompact _ (hc n) (hs n)) x
      rw [lapS_apply, lapS_apply, coe_schwartzOfCompact]
      have hfe : (⇑φ : Rd → ℂ) =ᶠ[𝓝 x] fun y => cutN (d := d) n y • φ y := by
        filter_upwards [Metric.ball_mem_nhds x one_pos] with y hy
        rw [hn y hy, one_smul]
      exact (laplacian_congr_nhds hfe).eq_of_nhds

/-! ### The Helmholtz corollary -/

theorem conjS_sub (φ ψ : SchwartzMap Rd ℂ) : conjS (φ - ψ) = conjS φ - conjS ψ := by
  refine SchwartzMap.ext fun x => ?_
  rw [SchwartzMap.sub_apply, conjS_apply, conjS_apply, conjS_apply, SchwartzMap.sub_apply, map_sub]

/-- Passing a pairing identity to `L²` limits of test functions. -/
theorem integral_mul_eq_zero_of_tendsto (u : L2 d) {gn : ℕ → SchwartzMap Rd ℂ}
    {g : SchwartzMap Rd ℂ} (hz : ∀ n, ∫ x, (u : Rd → ℂ) x * gn n x = 0)
    (hlim : Tendsto (fun n => toL2 (gn n)) atTop (𝓝 (toL2 g))) :
    ∫ x, (u : Rd → ℂ) x * g x = 0 := by
  have e : ∀ ψ : SchwartzMap Rd ℂ, ∫ x, (u : Rd → ℂ) x * ψ x = inner ℂ (toL2 (conjS ψ)) u :=
    fun ψ => by
      rw [← integral_schwartz_mul_eq_inner]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only
      rw [mul_comm]
  have hc : Tendsto (fun n => toL2 (conjS (gn n))) atTop (𝓝 (toL2 (conjS g))) := by
    rw [tendsto_iff_norm_sub_tendsto_zero] at hlim ⊢
    refine hlim.congr fun n => ?_
    rw [← map_sub, ← map_sub, ← conjS_sub, norm_toL2_conjS]
  have h := hc.inner (𝕜 := ℂ) (tendsto_const_nhds (x := u))
  have h' : Tendsto (fun n => inner ℂ (toL2 (conjS (gn n))) u) atTop (𝓝 0) := by
    refine tendsto_const_nhds.congr fun n => ?_
    rw [← e, hz]
  rw [e]
  exact tendsto_nhds_unique h h'

/-- **Corollary (free-space Helmholtz equation).**  For `d ≥ 1` and `k₀ ∈ ℝ`, if `u ∈ L²(ℝ^d)`
solves `(−Δ − k₀²)u = 0` in the sense of distributions — `∫ u · (−Δφ − k₀²φ) = 0` for every
smooth compactly supported `φ` — then `u = 0`. -/
theorem helmholtz (hd : 1 ≤ d) (k₀ : ℝ) (u : L2 d)
    (h : ∀ φ : Rd → ℂ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∫ x, (u : Rd → ℂ) x * (-(Δ φ x) - ((k₀ ^ 2 : ℝ) : ℂ) * φ x) = 0) :
    u = 0 := by
  refine poly_dispersion hd (P := X) (by rw [natDegree_X]; exact one_pos) (k₀ ^ 2) u
    fun φ => ?_
  obtain ⟨φn, hφc, hφ0, hφ2⟩ := exists_cutoff_seq φ
  obtain ⟨c, hcdef⟩ : ∃ c : ℂ, c = ((k₀ ^ 2 : ℝ) : ℂ) := ⟨_, rfl⟩
  have hz : ∀ n, ∫ x, (u : Rd → ℂ) x * (-(lapS (φn n)) - c • φn n) x = 0 := fun n => by
    have h1 := h (φn n) (φn n).smooth' (hφc n)
    have e : ∀ x, (-(lapS (φn n)) - c • φn n) x =
        -(Δ (⇑(φn n)) x) - ((k₀ ^ 2 : ℝ) : ℂ) * φn n x := fun x => by
      rw [SchwartzMap.sub_apply, SchwartzMap.smul_apply, smul_eq_mul, hcdef,
        show (-(lapS (φn n))) x = -(lapS (φn n) x) from rfl, lapS_apply]
    simp_rw [e]
    exact h1
  have hlim : Tendsto (fun n => toL2 (-(lapS (φn n)) - c • φn n)) atTop
      (𝓝 (toL2 (-(lapS φ) - c • φ))) := by
    simp only [map_sub, map_neg, map_smul]
    exact hφ2.neg.sub (hφ0.const_smul c)
  have hI := integral_mul_eq_zero_of_tendsto u hz hlim
  have hi1 : Integrable fun x => (u : Rd → ℂ) x * polyLapS (d := d) X φ x :=
    (integrable_schwartz_mul (polyLapS X φ) u).congr (Eventually.of_forall fun x => mul_comm _ _)
  have hi2 : Integrable fun x => (u : Rd → ℂ) x * φ x :=
    (integrable_schwartz_mul φ u).congr (Eventually.of_forall fun x => mul_comm _ _)
  have e1 : (fun x => (u : Rd → ℂ) x * (-(lapS φ) - c • φ) x) =
      fun x => (u : Rd → ℂ) x * polyLapS (d := d) X φ x - c * ((u : Rd → ℂ) x * φ x) := by
    funext x
    rw [polyLapS, Polynomial.aeval_X, SchwartzMap.sub_apply, SchwartzMap.smul_apply, smul_eq_mul,
      ContinuousLinearMap.neg_apply]
    ring
  rw [e1, integral_sub hi1 (hi2.const_mul c), integral_const_mul, sub_eq_zero] at hI
  rw [← hcdef]
  exact hI

end Sobolev

end ReyesMath

open Filter Topology Complex InnerProductSpace MeasureTheory Set
open scoped ContDiff FourierTransform

namespace ReyesMath

namespace Sobolev

variable {d : ℕ}

local notation "Rd" => EuclideanSpace ℝ (Fin d)

/-! ### Carrier wavelength versus envelope scale -/

/-- The modulated wave packet `u_R(x) = R^{-d/2} f(x/R) e^{ik₀ω₀·x}`. -/
noncomputable def packet (f : Rd → ℂ) (k₀ : ℝ) (ω₀ : Rd) (R : ℝ) (x : Rd) : ℂ :=
  ((R ^ (-((d : ℝ) / 2)) : ℝ) : ℂ) * f (R⁻¹ • x) *
    Complex.exp (((k₀ * inner ℝ ω₀ x : ℝ) : ℂ) * Complex.I)

theorem norm_exp_ofReal_mul_I' (θ : ℝ) : ‖Complex.exp ((θ : ℂ) * Complex.I)‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I θ

theorem rpow_neg_half_sq {R : ℝ} (hR : 0 < R) :
    (R ^ (-((d : ℝ) / 2))) ^ 2 * R ^ d = 1 := by
  rw [← Real.rpow_natCast (R ^ (-((d : ℝ) / 2))) 2, ← Real.rpow_mul hR.le, ← Real.rpow_natCast R d,
    ← Real.rpow_add hR]
  norm_num

theorem norm_packet_sq (f : Rd → ℂ) (k₀ : ℝ) (ω₀ : Rd) {R : ℝ} (hR : 0 < R) (x : Rd) :
    ‖packet f k₀ ω₀ R x‖ ^ 2 = (R ^ (-((d : ℝ) / 2))) ^ 2 * ‖f (R⁻¹ • x)‖ ^ 2 := by
  rw [packet, norm_mul, norm_mul, norm_exp_ofReal_mul_I', mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hR _), mul_pow]

theorem tsupport_comp_subset {g : Rd → ℂ} {A : Rd → Rd} (hA : Continuous A) :
    tsupport (g ∘ A) ⊆ A ⁻¹' tsupport g :=
  closure_minimal (fun _ hx => subset_closure hx) ((isClosed_tsupport g).preimage hA)

/-- **Proposition (fixed carrier, freely varying envelope).**  For `f ∈ 𝓢(ℝ^d)` with
`supp f̂ ⊂ B(0, ρ)`, `k₀ > 0`, `|ω₀| = 1` and `R > 0`, the packet `u_R` has
`‖u_R‖₂ = ‖f‖₂`, `û_R(ξ) = R^{d/2} f̂(R(ξ − k₀ω₀))`, `supp û_R ⊆ B(k₀ω₀, ρ/R)` and
`‖|x| u_R‖₂ = R ‖|x| f‖₂`; in particular `||ξ| − k₀| < ρ/R` on `supp û_R`. -/
theorem packet_properties (f : SchwartzMap Rd ℂ) {k₀ ρ R : ℝ} (hk₀ : 0 < k₀) (ω₀ : Rd)
    (hω₀ : ‖ω₀‖ = 1) (hf : tsupport (fourierU (⇑f)) ⊆ Metric.ball 0 ρ) (hR : 0 < R) :
    (∫ x, ‖packet f k₀ ω₀ R x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2) ∧
    (∀ ξ, fourierU (packet f k₀ ω₀ R) ξ =
      ((R ^ ((d : ℝ) / 2) : ℝ) : ℂ) * fourierU (⇑f) (R • (ξ - k₀ • ω₀))) ∧
    tsupport (fourierU (packet f k₀ ω₀ R)) ⊆ Metric.ball (k₀ • ω₀) (ρ / R) ∧
    Real.sqrt (∫ x, ‖x‖ ^ 2 * ‖packet f k₀ ω₀ R x‖ ^ 2) =
      R * Real.sqrt (∫ x, ‖x‖ ^ 2 * ‖f x‖ ^ 2) ∧
    (∀ ξ ∈ tsupport (fourierU (packet f k₀ ω₀ R)), |‖ξ‖ - k₀| < ρ / R) := by
  have hcv : ∀ g : Rd → ℝ, ∫ x, g (R⁻¹ • x) = R ^ d * ∫ x, g x := fun g => by
    rw [Measure.integral_comp_inv_smul_of_nonneg volume g hR.le, finrank_euclideanSpace_fin,
      smul_eq_mul]
  have hc := rpow_neg_half_sq (d := d) hR
  -- the Fourier transform
  have hF : ∀ ξ, fourierU (packet f k₀ ω₀ R) ξ =
      ((R ^ ((d : ℝ) / 2) : ℝ) : ℂ) * fourierU (⇑f) (R • (ξ - k₀ • ω₀)) := by
    intro ξ
    have hcvC : ∀ g : Rd → ℂ, ∫ x, g (R⁻¹ • x) = (R ^ d : ℝ) • ∫ x, g x := fun g => by
      rw [Measure.integral_comp_inv_smul_of_nonneg volume g hR.le, finrank_euclideanSpace_fin]
    obtain ⟨G, hG⟩ : ∃ G : Rd → ℂ, G = fun y =>
        f y * Complex.exp (-((inner ℝ y (R • (ξ - k₀ • ω₀)) : ℝ) : ℂ) * Complex.I) := ⟨_, rfl⟩
    have h2 : ∀ x, packet f k₀ ω₀ R x * Complex.exp (-((inner ℝ x ξ : ℝ) : ℂ) * Complex.I) =
        ((R ^ (-((d : ℝ) / 2)) : ℝ) : ℂ) * G (R⁻¹ • x) := by
      intro x
      rw [hG, packet]
      beta_reduce
      have hRx : R • (R⁻¹ • x) = x := by rw [smul_smul, mul_inv_cancel₀ hR.ne', one_smul]
      have hin : inner ℝ (R⁻¹ • x) (R • (ξ - k₀ • ω₀)) = inner ℝ x ξ - k₀ * inner ℝ ω₀ x := by
        rw [real_inner_smul_right, ← real_inner_smul_left, hRx, inner_sub_right,
          real_inner_smul_right, real_inner_comm ω₀ x]
      rw [hin, mul_assoc, mul_assoc, ← Complex.exp_add]
      congr 3
      push_cast
      ring
    have h3 : ∫ y, G y =
        ∫ y, f y * Complex.exp (-((inner ℝ y (R • (ξ - k₀ • ω₀)) : ℝ) : ℂ) * Complex.I) := by
      rw [hG]
    have e : ((R ^ (-((d : ℝ) / 2)) : ℝ) : ℂ) * ((R ^ d : ℝ) : ℂ) =
        ((R ^ ((d : ℝ) / 2) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul]
      congr 1
      rw [← Real.rpow_natCast R d, ← Real.rpow_add hR]
      congr 1
      ring
    rw [fourierU, fourierU, integral_congr_ae (Eventually.of_forall h2), integral_const_mul,
      hcvC G, Complex.real_smul, h3, ← e]
    ring
  refine ⟨?_, hF, ?_, ?_, ?_⟩
  · -- mass
    simp_rw [norm_packet_sq f k₀ ω₀ hR]
    rw [integral_const_mul, hcv (fun y => ‖f y‖ ^ 2), ← mul_assoc, hc, one_mul]
  · -- support
    intro ξ hξ
    have hsub : tsupport (fourierU (packet f k₀ ω₀ R)) ⊆
        (fun ξ => R • (ξ - k₀ • ω₀)) ⁻¹' tsupport (fourierU (⇑f)) := by
      have heq : fourierU (packet f k₀ ω₀ R) =
          fun ξ => ((R ^ ((d : ℝ) / 2) : ℝ) : ℂ) * (fourierU (⇑f) ∘ fun ξ => R • (ξ - k₀ • ω₀)) ξ :=
        funext hF
      rw [heq]
      exact tsupport_mul_subset_right.trans
        (tsupport_comp_subset ((continuous_id.sub continuous_const).const_smul R))
    have h1 := hf (hsub hξ)
    rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hR] at h1
    rw [Metric.mem_ball, dist_eq_norm, lt_div_iff₀ hR, mul_comm]
    exact h1
  · -- width
    have hw : ∀ x, ‖x‖ ^ 2 * ‖packet f k₀ ω₀ R x‖ ^ 2 =
        (R ^ (-((d : ℝ) / 2))) ^ 2 * (R ^ 2 * (‖R⁻¹ • x‖ ^ 2 * ‖f (R⁻¹ • x)‖ ^ 2)) := by
      intro x
      rw [norm_packet_sq f k₀ ω₀ hR, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR]
      field_simp
    simp_rw [hw]
    rw [integral_const_mul, integral_const_mul,
      hcv (fun y => ‖y‖ ^ 2 * ‖f y‖ ^ 2), ← mul_assoc, ← mul_assoc,
      mul_comm ((R ^ (-((d : ℝ) / 2))) ^ 2) (R ^ 2), mul_assoc (R ^ 2), hc, mul_one,
      Real.sqrt_mul (sq_nonneg R), Real.sqrt_sq hR.le]
  · -- radial bandwidth
    intro ξ hξ
    have hsub : tsupport (fourierU (packet f k₀ ω₀ R)) ⊆ Metric.ball (k₀ • ω₀) (ρ / R) := by
      intro η hη
      have hsub' : tsupport (fourierU (packet f k₀ ω₀ R)) ⊆
          (fun ξ => R • (ξ - k₀ • ω₀)) ⁻¹' tsupport (fourierU (⇑f)) := by
        have heq : fourierU (packet f k₀ ω₀ R) =
            fun ξ => ((R ^ ((d : ℝ) / 2) : ℝ) : ℂ) *
              (fourierU (⇑f) ∘ fun ξ => R • (ξ - k₀ • ω₀)) ξ :=
          funext hF
        rw [heq]
        exact tsupport_mul_subset_right.trans
          (tsupport_comp_subset ((continuous_id.sub continuous_const).const_smul R))
      have h1 := hf (hsub' hη)
      rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hR] at h1
      rw [Metric.mem_ball, dist_eq_norm, lt_div_iff₀ hR, mul_comm]
      exact h1
    have h1 := hsub hξ
    rw [Metric.mem_ball, dist_eq_norm] at h1
    have h2 : ‖k₀ • ω₀‖ = k₀ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hk₀, hω₀, mul_one]
    calc |‖ξ‖ - k₀| = |‖ξ‖ - ‖k₀ • ω₀‖| := by rw [h2]
      _ ≤ ‖ξ - k₀ • ω₀‖ := abs_norm_sub_norm_le _ _
      _ < ρ / R := h1

end Sobolev

end ReyesMath

open Filter Topology Complex InnerProductSpace MeasureTheory Set Polynomial
open scoped ContDiff FourierTransform

namespace ReyesMath

namespace FourierShell

open Sobolev

variable {d : ℕ}

local notation "Rd" => EuclideanSpace ℝ (Fin d)

/-- **Plancherel's theorem** in the normalization of the manuscript: the unitary operator
`FU` on `L²(ℝ^d)` is the Fourier transform `û(ξ) = (2π)^{-d/2} ∫ u(x) e^{-ix·ξ} dx` on
`L¹ ∩ L²`, and `‖û‖₂ = ‖u‖₂`. -/
theorem plancherel (u : L2 d) :
    ‖FU u‖ = ‖u‖ ∧
      (Integrable (u : Rd → ℂ) → (FU u : Rd → ℂ) =ᵐ[volume] fourierU (u : Rd → ℂ)) :=
  ⟨norm_FU u, FU_ae_eq u⟩

/-- **Theorem (zero `L²` state on an isolated Fourier shell)**, essential-support form. -/
theorem shell_theorem (hd : 1 ≤ d) (k₀ : ℝ) (u : L2 d)
    (hsupp : ∀ᵐ ξ ∂volume, ξ ∉ Metric.sphere (0 : Rd) k₀ → (FU u : Rd → ℂ) ξ = 0) :
    u = 0 :=
  Sobolev.shell_theorem hd k₀ u hsupp

/-- **Theorem**, distributional-support form. -/
theorem shell_theorem_distrib (hd : 1 ≤ d) (k₀ : ℝ) (u : L2 d)
    (hsupp : ∀ ψ : Rd → ℂ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ (Metric.sphere (0 : Rd) k₀)ᶜ → ∫ ξ, ψ ξ * (FU u : Rd → ℂ) ξ = 0) :
    u = 0 :=
  Sobolev.shell_theorem_distrib hd k₀ u hsupp

/-- **Corollary (free-space Helmholtz equation).** -/
theorem helmholtz (hd : 1 ≤ d) (k₀ : ℝ) (u : L2 d)
    (h : ∀ φ : Rd → ℂ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∫ x, (u : Rd → ℂ) x * (-(Δ φ x) - ((k₀ ^ 2 : ℝ) : ℂ) * φ x) = 0) :
    u = 0 :=
  Sobolev.helmholtz hd k₀ u h

/-- **Corollary (nonconstant polynomial dispersion).** -/
theorem poly_dispersion (hd : 1 ≤ d) {P : Polynomial ℝ} (hP : 0 < P.natDegree) (lam : ℝ)
    (u : L2 d)
    (h : ∀ φ : SchwartzMap Rd ℂ,
      ∫ x, (u : Rd → ℂ) x * polyLapS P φ x = (lam : ℂ) * ∫ x, (u : Rd → ℂ) x * φ x) :
    u = 0 :=
  Sobolev.poly_dispersion hd hP lam u h

/-- **Remark (general Fourier multipliers)**: an operator acting as a smooth multiplier `m`
whose zero set is Lebesgue-null has no nonzero `L²` solutions of `Tᵗu = 0` in `𝓢'`. -/
theorem multiplier (T : SchwartzMap Rd ℂ →L[ℂ] SchwartzMap Rd ℂ) {m : Rd → ℂ}
    (hm : ContDiff ℝ ∞ m) (hT : ∀ g ξ, fSi (T g) ξ = m ξ * fSi g ξ)
    (hnull : volume {ξ | m ξ = 0} = 0) (u : L2 d)
    (h : ∀ φ : SchwartzMap Rd ℂ, ∫ x, (u : Rd → ℂ) x * T φ x = 0) : u = 0 :=
  eq_zero_of_multiplier T hm hT hnull u h

/-- **Proposition (fixed carrier, freely varying envelope).** -/
theorem packets (f : SchwartzMap Rd ℂ) {k₀ ρ R : ℝ} (hk₀ : 0 < k₀) (ω₀ : Rd)
    (hω₀ : ‖ω₀‖ = 1) (hf : tsupport (fourierU (⇑f)) ⊆ Metric.ball 0 ρ) (hR : 0 < R) :
    (∫ x, ‖packet f k₀ ω₀ R x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2) ∧
    (∀ ξ, fourierU (packet f k₀ ω₀ R) ξ =
      ((R ^ ((d : ℝ) / 2) : ℝ) : ℂ) * fourierU (⇑f) (R • (ξ - k₀ • ω₀))) ∧
    tsupport (fourierU (packet f k₀ ω₀ R)) ⊆ Metric.ball (k₀ • ω₀) (ρ / R) ∧
    Real.sqrt (∫ x, ‖x‖ ^ 2 * ‖packet f k₀ ω₀ R x‖ ^ 2) =
      R * Real.sqrt (∫ x, ‖x‖ ^ 2 * ‖f x‖ ^ 2) ∧
    (∀ ξ ∈ tsupport (fourierU (packet f k₀ ω₀ R)), |‖ξ‖ - k₀| < ρ / R) :=
  packet_properties f hk₀ ω₀ hω₀ hf hR

end FourierShell

end ReyesMath
