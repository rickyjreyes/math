import Mathlib
import MathProofs.FourierShellL2

/-!
# Linear spectral concentration (E16) and the continuous spectral energy fraction (E62)

Formalization of `papers/e16-linear-spectral-concentration/main.tex` and of the continuous part
of `papers/spectral-energy-concentration-e62/main.tex`, on `L²(ℝ^d)` with the unitary Fourier
transform `Sobolev.FU` (`Â(ξ) = (2π)^{-d/2} ∫ e^{-ix·ξ} A(x) dx`, extended by Plancherel).

* The operator `𝓛 = r − aΔ − bΔ²` on Schwartz space (`SpectralConc.Lop`, `SpectralConc.Lop_apply`)
  with symbol `λ(ξ) = r + a|ξ|² − b|ξ|⁴` (`SpectralConc.FU_Lop`); its weak (maximal) realisation on
  `L²` (`SpectralConc.IsGen`) and the Fourier characterisation `𝓛u = w ⇔ λû = ŵ`
  (`SpectralConc.isGen_iff`). Mild solutions `A ∈ C([0,∞); L²)` with `∫₀ᵗ A ∈ D(𝓛)`,
  `𝓛∫₀ᵗ A = A(t) − A₀` (`SpectralConc.IsMild`).
* Proposition (exact modal power law): existence, uniqueness on `[0,∞)`, `Â(t) = e^{λt}Â₀`,
  `P(ξ,t) = P(ξ,0)e^{2λ(ξ)t}` (`SpectralConc.exact_modal_law`).
* Lemma (unique maximising radius and strict gap): `SpectralConc.gap_lemma`.
* `Z(t) > 0` and `ν_t` is a probability measure (`SpectralConc.Z_pos`, `SpectralConc.nuM_prob`).
* Theorem (E16: concentration on the preferred shell): `SpectralConc.concentration`
  (`ν_t(E_δ) ≤ C_δ e^{−bk⋆²δ²t}`, `ν_t(E_δ) → 0`, `ν_t(|ξ| − k⋆| < δ) → 1`).
* Remark (`μ = 0`): `SpectralConc.decay_of_mu_zero`.
* Theorem (argmax convergence): `SpectralConc.argmax_convergence`; Corollary (explicit `t^{-1/2}`
  bound): `SpectralConc.argmax_rate`.
* Radial spectral density `𝒫(k,t) = k^{d−1}∫_{S^{d−1}} P(kω,t)dω` (`SpectralConc.radP`, with
  Mathlib's surface measure `SpectralConc.σS`), polar integration (`SpectralConc.integral_polar`,
  `SpectralConc.integral_radP`), the radial law (`SpectralConc.radial_law`) and Corollary (radial
  concentration, maximising wavenumber and rate): `SpectralConc.radial_corollary`.
* Proposition (failure without spectral access): `SpectralConc.counterexample`.
* E62 (Proposition, continuous spectrum): `SpectralConc.e62_continuous`; Remark (zero-width
  shell): `SpectralConc.etaC_sphere`.
-/

open Filter Topology Complex InnerProductSpace MeasureTheory Set
open scoped ContDiff FourierTransform ComplexConjugate

noncomputable section

namespace ReyesMath
namespace SpectralConc

open Sobolev

variable {d : ℕ}

local notation "Rd" => EuclideanSpace ℝ (Fin d)

/-! ### Multiplication operators on `L²(ℝ^d)` -/

theorem memLp_mul {m : Rd → ℂ} (hm : AEStronglyMeasurable m volume) {C : ℝ}
    (hC : ∀ ξ, ‖m ξ‖ ≤ C) (f : L2 d) : MemLp (fun ξ => m ξ * f ξ) 2 volume := by
  refine MemLp.of_le ((Lp.memLp f).const_smul (C : ℂ)) (hm.mul (Lp.aestronglyMeasurable f)) ?_
  refine Eventually.of_forall fun ξ => ?_
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC ξ)
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hC0]
  exact mul_le_mul_of_nonneg_right (hC ξ) (norm_nonneg _)

/-- Multiplication by a bounded measurable function, as an operator on `L²`. -/
def mulL2 (m : Rd → ℂ) (hm : AEStronglyMeasurable m volume) {C : ℝ} (hC : ∀ ξ, ‖m ξ‖ ≤ C) :
    L2 d →L[ℂ] L2 d :=
  LinearMap.mkContinuous
    { toFun := fun f => (memLp_mul hm hC f).toLp _
      map_add' := fun f g => by
        apply Lp.ext
        filter_upwards [(memLp_mul hm hC (f + g)).coeFn_toLp, (memLp_mul hm hC f).coeFn_toLp,
          (memLp_mul hm hC g).coeFn_toLp, Lp.coeFn_add f g,
          Lp.coeFn_add ((memLp_mul hm hC f).toLp _) ((memLp_mul hm hC g).toLp _)]
          with ξ h1 h2 h3 h4 h5
        rw [h5, Pi.add_apply, h1, h2, h3, h4, Pi.add_apply, mul_add]
      map_smul' := fun c f => by
        apply Lp.ext
        filter_upwards [(memLp_mul hm hC (c • f)).coeFn_toLp, (memLp_mul hm hC f).coeFn_toLp,
          Lp.coeFn_smul c f, Lp.coeFn_smul c ((memLp_mul hm hC f).toLp _)] with ξ h1 h2 h3 h4
        rw [RingHom.id_apply, h4, Pi.smul_apply, h1, h2, h3, Pi.smul_apply, smul_eq_mul,
          smul_eq_mul]
        ring }
    C (fun f => by
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [(memLp_mul hm hC f).coeFn_toLp] with ξ h1
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [h1, norm_mul]
      exact mul_le_mul_of_nonneg_right (hC ξ) (norm_nonneg _))

theorem coeFn_mulL2 {m : Rd → ℂ} (hm : AEStronglyMeasurable m volume) {C : ℝ}
    (hC : ∀ ξ, ‖m ξ‖ ≤ C) (f : L2 d) :
    (mulL2 m hm hC f : Rd → ℂ) =ᵐ[volume] fun ξ => m ξ * f ξ :=
  (memLp_mul hm hC f).coeFn_toLp

theorem norm_sq_L2 (f : L2 d) : ‖f‖ ^ 2 = ∫ ξ, ‖f ξ‖ ^ 2 := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ) f, MeasureTheory.L2.inner_def,
    ← integral_re (L2.integrable_inner (𝕜 := ℂ) f f)]
  congr 1; funext x
  rw [inner_self_eq_norm_sq]

theorem integrable_norm_sq_L2 (f : L2 d) : Integrable fun ξ => ‖f ξ‖ ^ 2 :=
  (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).1 (Lp.memLp f)

theorem real_inner_L2' (f g : L2 d) : (inner ℝ f g : ℝ) = (inner ℂ f g).re := by
  rw [L2.inner_def, L2.inner_def, ← RCLike.re_to_complex, ← integral_re (L2.integrable_inner _ _)]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [Complex.inner, RCLike.inner_apply, RCLike.re_to_complex]

/-! ### The Fourier transform of Schwartz functions -/

theorem FU_toL2 (φ : SchwartzMap Rd ℂ) :
    (FU (toL2 φ) : Rd → ℂ) =ᵐ[volume] dilF (2 * Real.pi)⁻¹ ⇑(fS φ) := by
  rw [FU_apply, fourierL2_toL2]
  filter_upwards [coeFn_dilL2 (inv_pos.2 two_pi_pos') (toL2 (fS φ)),
    dilF_congr_ae (inv_pos.2 two_pi_pos') (coeFn_toL2 (fS φ))] with ξ h1 h2
  rw [h1, h2]

theorem dilF_inv_dilF {lam : ℝ} (hlam : 0 < lam) (f : Rd → ℂ) (ξ : Rd) :
    dilF lam⁻¹ (dilF lam f) ξ = f ξ := by
  simp only [dilF]
  rw [smul_smul, mul_inv_cancel₀ hlam.ne', one_smul, ← mul_assoc, ← Complex.ofReal_mul,
    ← Real.mul_rpow (inv_nonneg.2 hlam.le) hlam.le, inv_mul_cancel₀ hlam.ne', Real.one_rpow,
    Complex.ofReal_one, one_mul]

/-- A smooth compactly supported function, as a Schwartz function. -/
def ofCompact (f : Rd → ℂ) (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) :
    SchwartzMap Rd ℂ where
  toFun := f
  smooth' := hf
  decay' k n := by
    have hc : Continuous fun x : Rd => ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ :=
      (continuous_norm.pow k).mul (hf.continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm
    have hcs : HasCompactSupport fun x : Rd => ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ :=
      (hs.iteratedFDeriv n).norm.mul_left
    obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hcs
    exact ⟨C, fun x => by simpa [abs_of_nonneg] using hC x⟩

theorem coe_ofCompact (f : Rd → ℂ) (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) :
    ⇑(ofCompact f hf hs) = f := rfl

/-- Every smooth compactly supported function is the unitary Fourier transform of a Schwartz
function. -/
theorem exists_schwartz_FU (g : Rd → ℂ) (hg : ContDiff ℝ ∞ g) (hgs : HasCompactSupport g) :
    ∃ φ : SchwartzMap Rd ℂ, (FU (toL2 φ) : Rd → ℂ) =ᵐ[volume] g := by
  have hc : ContDiff ℝ ∞ (dilF (2 * Real.pi) g) := by
    unfold dilF
    exact contDiff_const.mul (hg.comp (contDiff_const_smul _))
  have hs : HasCompactSupport (dilF (2 * Real.pi) g) := by
    unfold dilF
    exact (hgs.comp_smul two_pi_pos'.ne').mul_left
  refine ⟨fSi (ofCompact _ hc hs), ?_⟩
  filter_upwards [FU_toL2 (fSi (ofCompact _ hc hs))] with ξ h
  rw [h, fS_fSi, coe_ofCompact, dilF_inv_dilF two_pi_pos']


/-! ### The operator `𝓛 = r − aΔ − bΔ²` and its symbol -/

variable (a b r : ℝ)

/-- The growth rate `λ(ξ) = r + a|ξ|² − b|ξ|⁴`. -/
def lam (ξ : Rd) : ℝ := r + a * ‖ξ‖ ^ 2 - b * ‖ξ‖ ^ 4

/-- `p(X) = r + aX − bX²`, so that `𝓛 = p(−Δ) = r − aΔ − bΔ²`. -/
def pol : Polynomial ℝ :=
  Polynomial.C r + Polynomial.C a * Polynomial.X - Polynomial.C b * Polynomial.X ^ 2

/-- `𝓛 = r − aΔ − bΔ²` on Schwartz space. -/
def Lop : SchwartzMap Rd ℂ →L[ℂ] SchwartzMap Rd ℂ := polyLapS (pol a b r)

theorem Lop_apply (φ : SchwartzMap Rd ℂ) :
    Lop a b r φ = (r : ℂ) • φ - (a : ℂ) • lapS φ - (b : ℂ) • lapS (lapS φ) := by
  simp only [Lop, polyLapS, pol, Polynomial.aeval_sub, Polynomial.aeval_add,
    Polynomial.aeval_mul, Polynomial.aeval_C, Polynomial.aeval_X,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.mul_apply,
    algebraMap_apply_schwartz, sq, ContinuousLinearMap.neg_apply, map_neg]
  rw [sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg, neg_neg]

theorem continuous_lam : Continuous (lam (d := d) a b r) := by
  unfold lam; fun_prop

theorem pol_eval (s : ℝ) : (pol a b r).eval s = r + a * s - b * s ^ 2 := by simp [pol]

theorem qS_dil (ξ : Rd) : qS ((2 * Real.pi)⁻¹ • ξ) = ‖ξ‖ ^ 2 := by
  rw [qS, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos two_pi_pos']
  field_simp

theorem dilF_fS_Lop (φ : SchwartzMap Rd ℂ) (ξ : Rd) :
    dilF (2 * Real.pi)⁻¹ ⇑(fS (Lop a b r φ)) ξ =
      (lam a b r ξ : ℂ) * dilF (2 * Real.pi)⁻¹ ⇑(fS φ) ξ := by
  simp only [dilF, Lop, fS_polyLapS, qS_dil, pol_eval, lam]
  push_cast; ring

/-- `\widehat{𝓛φ} = λ φ̂`. -/
theorem FU_Lop (φ : SchwartzMap Rd ℂ) :
    (FU (toL2 (Lop a b r φ)) : Rd → ℂ) =ᵐ[volume] fun ξ => (lam a b r ξ : ℂ) * FU (toL2 φ) ξ := by
  filter_upwards [FU_toL2 (Lop a b r φ), FU_toL2 φ] with ξ h1 h2
  rw [h1, h2, dilF_fS_Lop]

/-! ### The generator in the weak sense -/

/-- `𝓛u = w` weakly: `⟪𝓛φ, u⟫ = ⟪φ, w⟫` for every Schwartz `φ` (the maximal realisation of the
formally self-adjoint operator `r − aΔ − bΔ²`, i.e. the adjoint of `𝓛|_𝓢`). -/
def IsGen (u w : L2 d) : Prop :=
  ∀ φ : SchwartzMap Rd ℂ, ⟪toL2 (Lop a b r φ), u⟫_ℂ = ⟪toL2 φ, w⟫_ℂ

theorem inner_FU_eq (f g : L2 d) : ⟪f, g⟫_ℂ = ∫ ξ, conj (FU f ξ) * FU g ξ := by
  rw [← LinearIsometryEquiv.inner_map_map FU f g, L2.inner_def]
  congr 1; funext ξ; rw [RCLike.inner_apply, mul_comm]

theorem inner_Lop_eq (φ : SchwartzMap Rd ℂ) (u : L2 d) :
    ⟪toL2 (Lop a b r φ), u⟫_ℂ = ∫ ξ, conj (FU (toL2 φ) ξ) * ((lam a b r ξ : ℂ) * FU u ξ) := by
  rw [inner_FU_eq]
  apply integral_congr_ae
  filter_upwards [FU_Lop a b r φ] with ξ h
  rw [h, map_mul, Complex.conj_ofReal]; ring

theorem isGen_of_ae {u w : L2 d}
    (h : (fun ξ => (lam a b r ξ : ℂ) * FU u ξ) =ᵐ[volume] (FU w : Rd → ℂ)) : IsGen a b r u w := by
  intro φ
  rw [inner_Lop_eq, inner_FU_eq]
  apply integral_congr_ae
  filter_upwards [h] with ξ hξ
  rw [hξ]

theorem locallyIntegrable_L2 (f : L2 d) : LocallyIntegrable (f : Rd → ℂ) volume :=
  (Lp.memLp f).locallyIntegrable (by norm_num)

theorem locallyIntegrable_lam_mul (f : L2 d) :
    LocallyIntegrable (fun ξ => (lam a b r ξ : ℂ) * f ξ) volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  exact IntegrableOn.continuousOn_mul (Complex.continuous_ofReal.comp (continuous_lam a b r)).continuousOn
    ((locallyIntegrable_L2 f).integrableOn_isCompact hK) hK

/-- Fourier characterisation of the weak generator: `𝓛u = w ⇔ λ û = ŵ` a.e. -/
theorem isGen_iff (u w : L2 d) :
    IsGen a b r u w ↔ (fun ξ => (lam a b r ξ : ℂ) * FU u ξ) =ᵐ[volume] (FU w : Rd → ℂ) := by
  refine ⟨fun h => ?_, isGen_of_ae a b r⟩
  have hF : ∀ᵐ ξ ∂volume, (fun ξ => (lam a b r ξ : ℂ) * FU u ξ - FU w ξ) ξ = 0 := by
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero
      ((locallyIntegrable_lam_mul a b r (FU u)).sub (locallyIntegrable_L2 (FU w))) ?_
    intro g hg hgs
    have hgc : ContDiff ℝ ∞ (fun ξ => (g ξ : ℂ)) := Complex.ofRealCLM.contDiff.comp hg
    obtain ⟨φ, hφ⟩ := exists_schwartz_FU (fun ξ => (g ξ : ℂ)) hgc (hgs.comp_left Complex.ofReal_zero)
    have h1 := h φ
    rw [inner_Lop_eq, inner_FU_eq] at h1
    have e1 : (fun ξ => conj (FU (toL2 φ) ξ) * ((lam a b r ξ : ℂ) * FU u ξ)) =ᵐ[volume]
        fun ξ => g ξ • ((lam a b r ξ : ℂ) * FU u ξ) := by
      filter_upwards [hφ] with ξ hξ
      rw [hξ, Complex.conj_ofReal, Complex.real_smul]
    have e2 : (fun ξ => conj (FU (toL2 φ) ξ) * FU w ξ) =ᵐ[volume] fun ξ => g ξ • FU w ξ := by
      filter_upwards [hφ] with ξ hξ
      rw [hξ, Complex.conj_ofReal, Complex.real_smul]
    have i1 : Integrable (fun ξ => g ξ • ((lam a b r ξ : ℂ) * FU u ξ)) := by
      have := L2.integrable_inner (𝕜 := ℂ) (FU (toL2 (Lop a b r φ))) (FU u)
      refine (integrable_congr ?_).1 this
      filter_upwards [FU_Lop a b r φ, hφ] with ξ h1 h2
      rw [RCLike.inner_apply, h1, h2, map_mul, Complex.conj_ofReal, Complex.conj_ofReal,
        Complex.real_smul]
      ring
    have i2 : Integrable (fun ξ => g ξ • FU w ξ) := by
      have := L2.integrable_inner (𝕜 := ℂ) (FU (toL2 φ)) (FU w)
      refine (integrable_congr ?_).1 this
      filter_upwards [hφ] with ξ h2
      rw [RCLike.inner_apply, h2, Complex.conj_ofReal, Complex.real_smul]
      ring
    rw [integral_congr_ae e1, integral_congr_ae e2] at h1
    simp only [smul_sub]
    rw [integral_sub i1 i2, h1, sub_self]
  filter_upwards [hF] with ξ hξ
  exact sub_eq_zero.1 hξ

theorem isGen_sub {u w u' w' : L2 d} (h : IsGen a b r u w) (h' : IsGen a b r u' w') :
    IsGen a b r (u - u') (w - w') := fun φ => by
  rw [inner_sub_right, inner_sub_right, h φ, h' φ]


/-! ### The completed square -/

/-- `μ = r + a²/(4b)`. -/
def mu : ℝ := r + a ^ 2 / (4 * b)

/-- `k⋆ = √(a/(2b))`. -/
def kstar : ℝ := √(a / (2 * b))

/-- `q(ξ) = (|ξ|² − k⋆²)²`. -/
def qf (ξ : Rd) : ℝ := (‖ξ‖ ^ 2 - kstar a b ^ 2) ^ 2

variable {a b}

theorem kstar_sq (ha : 0 < a) (hb : 0 < b) : kstar a b ^ 2 = a / (2 * b) :=
  Real.sq_sqrt (by positivity)

theorem kstar_pos (ha : 0 < a) (hb : 0 < b) : 0 < kstar a b := Real.sqrt_pos.2 (by positivity)

theorem lam_eq (ha : 0 < a) (hb : 0 < b) (ξ : Rd) : lam a b r ξ = mu a b r - b * qf a b ξ := by
  rw [lam, mu, qf, kstar_sq ha hb]; field_simp; ring

theorem qf_nonneg (ξ : Rd) : 0 ≤ qf a b ξ := sq_nonneg _

theorem lam_le (ha : 0 < a) (hb : 0 < b) (ξ : Rd) : lam a b r ξ ≤ mu a b r := by
  rw [lam_eq r ha hb]; nlinarith [qf_nonneg (a := a) (b := b) ξ]

theorem qf_eq (ξ : Rd) : qf a b ξ = (‖ξ‖ - kstar a b) ^ 2 * (‖ξ‖ + kstar a b) ^ 2 := by
  rw [qf]; ring

/-! ### The semigroup `S(t) = FU⁻¹ e^{tλ} FU` -/

variable (a b) in
/-- The symbol `e^{t⁺ λ(ξ)}` (`t⁺ = max t 0`). -/
def esym (t : ℝ) (ξ : Rd) : ℂ := (Real.exp (max t 0 * lam a b r ξ) : ℂ)

theorem continuous_esym : Continuous fun p : ℝ × Rd => esym a b r p.1 p.2 := by
  unfold esym
  exact Complex.continuous_ofReal.comp (Real.continuous_exp.comp
    ((continuous_fst.max continuous_const).mul ((continuous_lam a b r).comp continuous_snd)))

theorem continuous_esym_t (t : ℝ) : Continuous (esym (d := d) a b r t) := by
  unfold esym
  exact Complex.continuous_ofReal.comp (Real.continuous_exp.comp
    (continuous_const.mul (continuous_lam a b r)))

theorem continuous_esym_s (ξ : Rd) : Continuous fun s => esym a b r s ξ := by
  unfold esym
  exact Complex.continuous_ofReal.comp (Real.continuous_exp.comp
    ((continuous_id.max continuous_const).mul continuous_const))

theorem norm_esym (t : ℝ) (ξ : Rd) : ‖esym a b r t ξ‖ = Real.exp (max t 0 * lam a b r ξ) := by
  rw [esym, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

theorem norm_esym_le (ha : 0 < a) (hb : 0 < b) (t : ℝ) (ξ : Rd) :
    ‖esym a b r t ξ‖ ≤ Real.exp (max t 0 * mu a b r) := by
  rw [norm_esym]
  exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (lam_le r ha hb ξ) (le_max_right _ _))

theorem norm_esym_le_abs (ha : 0 < a) (hb : 0 < b) (t : ℝ) (ξ : Rd) :
    ‖esym a b r t ξ‖ ≤ Real.exp (|t| * |mu a b r|) := by
  refine (norm_esym_le r ha hb t ξ).trans (Real.exp_le_exp.2 ?_)
  calc max t 0 * mu a b r ≤ max t 0 * |mu a b r| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) (le_max_right _ _)
    _ ≤ |t| * |mu a b r| := mul_le_mul_of_nonneg_right (max_le (le_abs_self _) (abs_nonneg _))
        (abs_nonneg _)

variable (ha : 0 < a) (hb : 0 < b)

/-- `e^{tλ} Â₀` in `L²`. -/
def solM (A₀ : L2 d) (t : ℝ) : L2 d :=
  mulL2 (esym a b r t) (continuous_esym_t r t).aestronglyMeasurable (norm_esym_le r ha hb t) (FU A₀)

/-- The semigroup orbit `S(t)A₀ = FU⁻¹(e^{tλ} FU A₀)`. -/
def sol (A₀ : L2 d) (t : ℝ) : L2 d := FU.symm (solM r ha hb A₀ t)

theorem FU_sol (A₀ : L2 d) (t : ℝ) : FU (sol r ha hb A₀ t) = solM r ha hb A₀ t :=
  FU.apply_symm_apply _

theorem coeFn_solM (A₀ : L2 d) (t : ℝ) :
    (solM r ha hb A₀ t : Rd → ℂ) =ᵐ[volume] fun ξ => esym a b r t ξ * FU A₀ ξ :=
  coeFn_mulL2 _ _ _

theorem norm_sub_solM_sq (A₀ : L2 d) (s t : ℝ) :
    ‖solM r ha hb A₀ s - solM r ha hb A₀ t‖ ^ 2 =
      ∫ ξ, ‖esym a b r s ξ - esym a b r t ξ‖ ^ 2 * ‖FU A₀ ξ‖ ^ 2 := by
  rw [norm_sq_L2]; apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (solM r ha hb A₀ s) (solM r ha hb A₀ t), coeFn_solM r ha hb A₀ s,
    coeFn_solM r ha hb A₀ t] with ξ h1 h2 h3
  rw [h1, Pi.sub_apply, h2, h3, ← sub_mul, norm_mul, mul_pow]

theorem continuous_solM (A₀ : L2 d) : Continuous (solM r ha hb A₀) := by
  rw [continuous_iff_continuousAt]; intro t
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  obtain ⟨K, hK⟩ : ∃ K, K = Real.exp ((|t| + 1) * |mu a b r|) := ⟨_, rfl⟩
  have hI : Tendsto (fun s => ∫ ξ, ‖esym a b r s ξ - esym a b r t ξ‖ ^ 2 * ‖FU A₀ ξ‖ ^ 2)
      (𝓝 t) (𝓝 (∫ ξ, ‖esym a b r t ξ - esym a b r t ξ‖ ^ 2 * ‖FU A₀ ξ‖ ^ 2)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun ξ => (2 * K) ^ 2 * ‖FU A₀ ξ‖ ^ 2) ?_ ?_ ?_ ?_
    · refine Eventually.of_forall fun s => ?_
      exact (((continuous_esym_t r s).sub (continuous_esym_t r t)).norm.pow 2).aestronglyMeasurable.mul
        ((Lp.aestronglyMeasurable (FU A₀)).norm.pow 2)
    · filter_upwards [Metric.ball_mem_nhds t one_pos] with s hs
      refine Eventually.of_forall fun ξ => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
      have hs' : |s| ≤ |t| + 1 := by
        rw [Metric.mem_ball, Real.dist_eq] at hs
        calc |s| = |(s - t) + t| := by ring_nf
          _ ≤ |s - t| + |t| := abs_add _ _
          _ ≤ |t| + 1 := by linarith
      have e1 : ‖esym a b r s ξ‖ ≤ K := hK ▸ (norm_esym_le_abs r ha hb s ξ).trans
        (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hs' (abs_nonneg _)))
      have e2 : ‖esym a b r t ξ‖ ≤ K := hK ▸ (norm_esym_le_abs r ha hb t ξ).trans
        (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)))
      calc ‖esym a b r s ξ - esym a b r t ξ‖ ≤ ‖esym a b r s ξ‖ + ‖esym a b r t ξ‖ :=
            norm_sub_le _ _
        _ ≤ 2 * K := by linarith
    · exact (integrable_norm_sq_L2 (FU A₀)).const_mul _
    · refine Eventually.of_forall fun ξ => ?_
      have hc : Continuous fun s => esym a b r s ξ := continuous_esym_s r ξ
      exact ((((hc.sub continuous_const).norm.pow 2).mul continuous_const).tendsto t)
  simp only [sub_self, norm_zero, zero_pow two_ne_zero, zero_mul, integral_zero] at hI
  have h2 : Tendsto (fun s => ‖solM r ha hb A₀ s - solM r ha hb A₀ t‖ ^ 2) (𝓝 t) (𝓝 0) := by
    simpa only [norm_sub_solM_sq] using hI
  have h3 := h2.sqrt
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using h3

theorem continuous_sol (A₀ : L2 d) : Continuous (sol r ha hb A₀) :=
  FU.symm.continuous.comp (continuous_solM r ha hb A₀)

theorem sol_zero (A₀ : L2 d) : sol r ha hb A₀ 0 = A₀ := by
  rw [sol]; apply FU.injective; rw [LinearIsometryEquiv.apply_symm_apply]
  apply Lp.ext
  filter_upwards [coeFn_solM r ha hb A₀ 0] with ξ h
  rw [h, esym, max_self, zero_mul, Real.exp_zero, Complex.ofReal_one, one_mul]


/-! ### Mild solutions -/

variable (a b) in
/-- `A` is a mild solution of `∂ₜA = (r − aΔ − bΔ²)A`, `A(0) = A₀`, on `[0, ∞)`:
`A ∈ C([0,∞); L²)`, and for every `t ≥ 0`, `∫₀ᵗ A ∈ D(𝓛)` with `𝓛 ∫₀ᵗ A = A(t) − A₀`. -/
def IsMild (A₀ : L2 d) (A : ℝ → L2 d) : Prop :=
  ContinuousOn A (Ici 0) ∧ A 0 = A₀ ∧
    ∀ t, 0 ≤ t → IsGen a b r (∫ s in (0 : ℝ)..t, A s) (A t - A₀)

variable (a b) in
/-- `∫₀ᵗ e^{s⁺ λ(ξ)} ds`. -/
def iexp (t : ℝ) (ξ : Rd) : ℂ := ∫ s in (0 : ℝ)..t, esym a b r s ξ

theorem continuous_esym_swap : Continuous fun p : Rd × ℝ => esym a b r p.2 p.1 := by
  unfold esym
  exact Complex.continuous_ofReal.comp (Real.continuous_exp.comp
    ((continuous_snd.max continuous_const).mul ((continuous_lam a b r).comp continuous_fst)))

theorem continuous_iexp (t : ℝ) : Continuous (iexp (d := d) a b r t) := by
  have : Continuous fun p : Rd × ℝ => esym a b r p.2 p.1 := continuous_esym_swap r
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' this 0 t

include ha hb in
theorem norm_iexp_le {t : ℝ} (ht : 0 ≤ t) (ξ : Rd) :
    ‖iexp a b r t ξ‖ ≤ Real.exp (t * |mu a b r|) * t := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t)
    (f := fun s => esym a b r s ξ) (C := Real.exp (t * |mu a b r|)) (fun s hs => by
      rw [Set.uIoc_of_le ht] at hs
      refine (norm_esym_le_abs r ha hb s ξ).trans (Real.exp_le_exp.2 ?_)
      rw [abs_of_pos hs.1]
      exact mul_le_mul_of_nonneg_right hs.2 (abs_nonneg _))
  rwa [sub_zero, abs_of_nonneg ht] at h

/-- `λ ∫₀ᵗ e^{sλ} ds = e^{tλ} − 1` for `t ≥ 0`. -/
theorem lam_mul_iexp {t : ℝ} (ht : 0 ≤ t) (ξ : Rd) :
    (lam a b r ξ : ℂ) * iexp a b r t ξ = esym a b r t ξ - 1 := by
  have e : iexp a b r t ξ = ((∫ s in (0 : ℝ)..t, Real.exp (s * lam a b r ξ) : ℝ) : ℂ) := by
    rw [iexp, ← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [Set.uIcc_of_le ht] at hs
    simp only [esym, max_eq_left hs.1]
  have hd : ∀ s ∈ Set.uIcc (0 : ℝ) t, HasDerivAt (fun s => Real.exp (s * lam a b r ξ))
      (Real.exp (s * lam a b r ξ) * lam a b r ξ) s := fun s _ => by
    simpa using ((hasDerivAt_id s).mul_const (lam a b r ξ)).exp
  have hint : IntervalIntegrable (fun s => Real.exp (s * lam a b r ξ) * lam a b r ξ) volume 0 t :=
    (by fun_prop : Continuous fun s => Real.exp (s * lam a b r ξ) * lam a b r ξ).intervalIntegrable _ _
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint
  rw [intervalIntegral.integral_mul_const] at hftc
  rw [e, esym, max_eq_left ht, ← Complex.ofReal_mul, mul_comm, hftc, zero_mul, Real.exp_zero]
  push_cast; ring

include ha hb in
theorem norm_iexp_le' {t : ℝ} (ht : 0 ≤ t) (ξ : Rd) :
    ‖iexp a b r t ξ‖ ≤ Real.exp (t * |mu a b r|) * t := norm_iexp_le r ha hb ht ξ

/-- `∫₀ᵗ e^{sλ}Â₀ ds` as a multiplier. -/
def iM (A₀ : L2 d) {t : ℝ} (ht : 0 ≤ t) : L2 d :=
  mulL2 (iexp a b r t) (continuous_iexp r t).aestronglyMeasurable (norm_iexp_le' r ha hb ht) (FU A₀)

theorem integrable_inner_mul (h f : L2 d) : Integrable fun ξ => ‖h ξ‖ * ‖f ξ‖ := by
  have := (L2.integrable_inner (𝕜 := ℂ) h f).norm
  refine this.congr (Eventually.of_forall fun ξ => ?_)
  simp only [RCLike.inner_apply, norm_mul, RCLike.norm_conj, mul_comm]

/-- The Bochner integral of the orbit in Fourier variables: `∫₀ᵗ e^{sλ}Â₀ ds`. -/
theorem integral_solM (A₀ : L2 d) {t : ℝ} (ht : 0 ≤ t) :
    ∫ s in (0 : ℝ)..t, solM r ha hb A₀ s = iM r ha hb A₀ ht := by
  apply ext_inner_left ℂ
  intro h
  have hcont := continuous_solM r ha hb A₀
  rw [← innerSL_apply (𝕜 := ℂ) h, ← ContinuousLinearMap.intervalIntegral_comp_comm _
    (hcont.intervalIntegrable 0 t)]
  simp only [innerSL_apply]
  have e1 : ∀ s, ⟪h, solM r ha hb A₀ s⟫_ℂ =
      ∫ ξ, conj (h ξ) * (esym a b r s ξ * FU A₀ ξ) := by
    intro s; rw [L2.inner_def]; apply integral_congr_ae
    filter_upwards [coeFn_solM r ha hb A₀ s] with ξ hξ
    rw [RCLike.inner_apply, hξ, mul_comm]
  have e2 : ⟪h, iM r ha hb A₀ ht⟫_ℂ = ∫ ξ, conj (h ξ) * (iexp a b r t ξ * FU A₀ ξ) := by
    rw [L2.inner_def]; apply integral_congr_ae
    filter_upwards [coeFn_mulL2 (continuous_iexp r t).aestronglyMeasurable
      (norm_iexp_le' r ha hb ht) (FU A₀)] with ξ hξ
    rw [iM, RCLike.inner_apply, hξ, mul_comm]
  simp_rw [e1, e2]
  rw [intervalIntegral.integral_of_le ht]
  have hF : Integrable (Function.uncurry fun s ξ => conj (h ξ) * (esym a b r s ξ * FU A₀ ξ))
      ((volume.restrict (Ioc (0 : ℝ) t)).prod volume) := by
    have hb' : Integrable (fun p : ℝ × Rd => Real.exp (|p.1| * |mu a b r|) * (‖h p.2‖ * ‖FU A₀ p.2‖))
        ((volume.restrict (Ioc (0 : ℝ) t)).prod volume) := by
      have h1 : Integrable (fun s : ℝ => Real.exp (|s| * |mu a b r|)) (volume.restrict (Ioc 0 t)) :=
        (by fun_prop : Continuous fun s : ℝ => Real.exp (|s| * |mu a b r|)).integrableOn_Icc.mono_set
          Ioc_subset_Icc_self
      exact h1.mul_prod (integrable_inner_mul h (FU A₀))
    refine hb'.mono' ?_ (Eventually.of_forall fun ⟨s, ξ⟩ => ?_)
    · have hm1 : AEStronglyMeasurable (fun p : ℝ × Rd => conj (h p.2))
          ((volume.restrict (Ioc (0 : ℝ) t)).prod volume) :=
        ((Lp.aestronglyMeasurable h).star).comp_snd
      have hm2 : AEStronglyMeasurable (fun p : ℝ × Rd => FU A₀ p.2)
          ((volume.restrict (Ioc (0 : ℝ) t)).prod volume) :=
        (Lp.aestronglyMeasurable (FU A₀)).comp_snd
      exact hm1.mul ((continuous_esym (a := a) (b := b) r).aestronglyMeasurable.mul hm2)
    · simp only [Function.uncurry_apply_pair, norm_mul, RCLike.norm_conj]
      have := norm_esym_le_abs r ha hb s ξ
      have h0 : 0 ≤ ‖h ξ‖ * ‖FU A₀ ξ‖ := by positivity
      nlinarith [norm_nonneg (esym a b r s ξ), norm_nonneg (h ξ), norm_nonneg (FU A₀ ξ)]
  rw [integral_integral_swap hF]
  apply integral_congr_ae
  refine Eventually.of_forall fun ξ => ?_
  simp only
  rw [integral_const_mul, integral_mul_const, iexp, intervalIntegral.integral_of_le ht]

/-- **Existence**: the semigroup orbit is a mild solution. -/
theorem isMild_sol (A₀ : L2 d) : IsMild a b r A₀ (sol r ha hb A₀) := by
  refine ⟨(continuous_sol r ha hb A₀).continuousOn, sol_zero r ha hb A₀, fun t ht => ?_⟩
  apply isGen_of_ae
  have hint : IntervalIntegrable (sol r ha hb A₀) volume 0 t :=
    (continuous_sol r ha hb A₀).intervalIntegrable 0 t
  have e : FU (∫ s in (0 : ℝ)..t, sol r ha hb A₀ s) = iM r ha hb A₀ ht := by
    have := ContinuousLinearMap.intervalIntegral_comp_comm
      (FU (d := d)).toContinuousLinearEquiv.toContinuousLinearMap hint
    simp only [ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv]
      at this
    rw [← this]
    simp_rw [FU_sol]
    exact integral_solM r ha hb A₀ ht
  rw [e, map_sub, FU_sol]
  filter_upwards [coeFn_mulL2 (continuous_iexp r t).aestronglyMeasurable
      (norm_iexp_le' r ha hb ht) (FU A₀), Lp.coeFn_sub (solM r ha hb A₀ t) (FU A₀),
    coeFn_solM r ha hb A₀ t] with ξ h1 h2 h3
  rw [iM, h1, h2, Pi.sub_apply, h3, ← mul_assoc, lam_mul_iexp r ht, sub_mul, one_mul]


/-! ### Uniqueness of mild solutions -/

include ha hb in
/-- The energy inequality `Re⟪V, 𝓛V⟫ ≤ μ‖V‖²` for `𝓛V = W`. -/
theorem re_inner_le {V W : L2 d} (h : IsGen a b r V W) :
    (⟪V, W⟫_ℂ).re ≤ mu a b r * ‖V‖ ^ 2 := by
  have hF := ((isGen_iff a b r V W).1 h)
  have e : (fun ξ => conj (FU V ξ) * FU W ξ) =ᵐ[volume]
      fun ξ => ((lam a b r ξ * ‖FU V ξ‖ ^ 2 : ℝ) : ℂ) := by
    filter_upwards [hF] with ξ hξ
    rw [← hξ, ← mul_assoc, mul_comm (conj _), mul_assoc, Complex.conj_mul']
    push_cast; ring
  have hI : Integrable fun ξ => lam a b r ξ * ‖FU V ξ‖ ^ 2 := by
    have := (L2.integrable_inner (𝕜 := ℂ) (FU V) (FU W)).re
    refine this.congr ?_
    filter_upwards [e] with ξ hξ
    simp only [RCLike.inner_apply, RCLike.re_to_complex]
    rw [mul_comm, hξ, Complex.ofReal_re]
  rw [inner_FU_eq, integral_congr_ae e, integral_complex_ofReal, Complex.ofReal_re, ← norm_FU V,
    norm_sq_L2, ← integral_const_mul]
  refine integral_mono hI ((integrable_norm_sq_L2 (FU V)).const_mul _) fun ξ => ?_
  exact mul_le_mul_of_nonneg_right (lam_le r ha hb ξ) (by positivity)

include ha hb in
/-- A mild solution with zero data vanishes. -/
theorem mild_zero {D : ℝ → L2 d} (hcD : ContinuousOn D (Ici 0))
    (hgen : ∀ t, 0 ≤ t → IsGen a b r (∫ s in (0 : ℝ)..t, D s) (D t)) {T : ℝ} (hT : 0 ≤ T) :
    D T = 0 := by
  have hint : ∀ t, 0 ≤ t → IntervalIntegrable D volume 0 t := fun t ht =>
    (hcD.mono (by rw [uIcc_of_le ht]; exact Icc_subset_Ici_self)).intervalIntegrable
  -- `V(T) = 0`
  have hV : (∫ s in (0 : ℝ)..T, D s) = 0 := by
    have hderV : ∀ t, 0 < t → HasDerivAt (fun u => ∫ s in (0 : ℝ)..u, D s) (D t) t := by
      intro t ht
      exact intervalIntegral.integral_hasDerivAt_right (hint t ht.le)
        ((hcD.mono Ioi_subset_Ici_self).stronglyMeasurableAtFilter isOpen_Ioi t ht)
        (hcD.continuousAt (Ici_mem_nhds ht))
    obtain ⟨c, hc⟩ : ∃ c, c = -2 * mu a b r := ⟨_, rfl⟩
    have hg : ∀ t, 0 < t → HasDerivAt
        (fun u => Real.exp (c * u) * ‖∫ s in (0 : ℝ)..u, D s‖ ^ 2)
        (Real.exp (c * t) * (c * 1) * ‖∫ s in (0 : ℝ)..t, D s‖ ^ 2 +
          Real.exp (c * t) * (2 * inner ℝ (∫ s in (0 : ℝ)..t, D s) (D t))) t := by
      intro t ht
      exact (((hasDerivAt_id t).const_mul c).exp).mul (hderV t ht).norm_sq
    have hgle : ∀ t, 0 < t →
        Real.exp (c * t) * (c * 1) * ‖∫ s in (0 : ℝ)..t, D s‖ ^ 2 +
          Real.exp (c * t) * (2 * inner ℝ (∫ s in (0 : ℝ)..t, D s) (D t)) ≤ 0 := by
      intro t ht
      have h1 := re_inner_le r ha hb (hgen t ht.le)
      rw [← real_inner_L2'] at h1
      have he := Real.exp_pos (c * t)
      have e : Real.exp (c * t) * (c * 1) * ‖∫ s in (0 : ℝ)..t, D s‖ ^ 2 +
          Real.exp (c * t) * (2 * inner ℝ (∫ s in (0 : ℝ)..t, D s) (D t)) =
          2 * Real.exp (c * t) * (inner ℝ (∫ s in (0 : ℝ)..t, D s) (D t) -
            mu a b r * ‖∫ s in (0 : ℝ)..t, D s‖ ^ 2) := by
        rw [hc]; ring
      rw [e]
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    rcases hT.eq_or_lt with h0 | hpos
    · rw [← h0, intervalIntegral.integral_same]
    have hcont : ContinuousOn (fun u => ∫ s in (0 : ℝ)..u, D s) (Icc 0 T) := by
      have := intervalIntegral.continuousOn_primitive_interval' (hint T hT) left_mem_uIcc
      rwa [uIcc_of_le hT] at this
    have hanti : AntitoneOn (fun u => Real.exp (c * u) * ‖∫ s in (0 : ℝ)..u, D s‖ ^ 2) (Icc 0 T) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc 0 T)
        ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul
          (hcont.norm.pow 2)) ?_ ?_
      · rw [interior_Icc]
        exact fun t ht => (hg t ht.1).differentiableAt.differentiableWithinAt
      · rw [interior_Icc]
        intro t ht
        rw [(hg t ht.1).deriv]
        exact hgle t ht.1
    have h1 := hanti (left_mem_Icc.2 hT) (right_mem_Icc.2 hT) hT
    simp only [intervalIntegral.integral_same, norm_zero, mul_zero, zero_pow two_ne_zero] at h1
    have h2 : ‖∫ s in (0 : ℝ)..T, D s‖ ^ 2 = 0 := by
      have he := Real.exp_pos (c * T)
      have := sq_nonneg ‖∫ s in (0 : ℝ)..T, D s‖
      nlinarith
    rwa [sq_eq_zero_iff, norm_eq_zero] at h2
  have hF := ((isGen_iff a b r _ _).1 (hgen T hT))
  rw [hV, map_zero] at hF
  apply FU.injective
  rw [map_zero]
  apply Lp.ext
  filter_upwards [hF, Lp.coeFn_zero ℂ 2 (volume : Measure Rd)] with ξ h1 h2
  rw [← h1, h2]
  simp

/-- **Uniqueness** of mild solutions on `[0, ∞)`. -/
theorem mild_unique {A₀ : L2 d} {A : ℝ → L2 d} (hA : IsMild a b r A₀ A) {T : ℝ} (hT : 0 ≤ T) :
    A T = sol r ha hb A₀ T := by
  obtain ⟨hcA, -, hgA⟩ := hA
  obtain ⟨hcS, -, hgS⟩ := isMild_sol r ha hb A₀
  have hint : ∀ t, 0 ≤ t → ∀ {F : ℝ → L2 d}, ContinuousOn F (Ici 0) →
      IntervalIntegrable F volume 0 t := fun t ht F hF =>
    (hF.mono (by rw [uIcc_of_le ht]; exact Icc_subset_Ici_self)).intervalIntegrable
  have h := mild_zero r ha hb (D := fun s => A s - sol r ha hb A₀ s) (hcA.sub hcS) (fun t ht => by
    have h1 := isGen_sub a b r (hgA t ht) (hgS t ht)
    rw [← intervalIntegral.integral_sub (hint t ht hcA) (hint t ht hcS)] at h1
    convert h1 using 1
    show A t - sol r ha hb A₀ t = _
    rw [sub_sub_sub_cancel_right]) hT
  exact sub_eq_zero.1 h


/-! ### The exact modal power law -/

theorem esym_of_nonneg {t : ℝ} (ht : 0 ≤ t) (ξ : Rd) :
    esym a b r t ξ = (Real.exp (lam a b r ξ * t) : ℂ) := by
  rw [esym, max_eq_left ht, mul_comm]

include ha hb in
theorem FU_mild {A₀ : L2 d} {A : ℝ → L2 d} (hA : IsMild a b r A₀ A) {t : ℝ} (ht : 0 ≤ t) :
    (FU (A t) : Rd → ℂ) =ᵐ[volume] fun ξ => (Real.exp (lam a b r ξ * t) : ℂ) * FU A₀ ξ := by
  rw [mild_unique r ha hb hA ht, FU_sol]
  filter_upwards [coeFn_solM r ha hb A₀ t] with ξ h
  rw [h, esym_of_nonneg r ht]

include ha hb in
theorem power_mild {A₀ : L2 d} {A : ℝ → L2 d} (hA : IsMild a b r A₀ A) {t : ℝ} (ht : 0 ≤ t) :
    (fun ξ => ‖FU (A t) ξ‖ ^ 2) =ᵐ[volume]
      fun ξ => ‖FU A₀ ξ‖ ^ 2 * Real.exp (2 * lam a b r ξ * t) := by
  filter_upwards [FU_mild r ha hb hA ht] with ξ h
  rw [h, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow,
    ← Real.exp_nat_mul, mul_comm]
  congr 2; push_cast; ring

include ha hb in
/-- **Proposition (exact modal power law).** For every `A₀ ∈ L²(ℝ^d)` the flow has a mild
solution, it is unique on `[0,∞)`, and `Â(t,ξ) = e^{λ(ξ)t}Â₀(ξ)`,
`P(ξ,t) = P(ξ,0) e^{2λ(ξ)t}` for a.e. `ξ`. -/
theorem exact_modal_law (A₀ : L2 d) :
    (∃ A : ℝ → L2 d, IsMild a b r A₀ A) ∧
    (∀ A B : ℝ → L2 d, IsMild a b r A₀ A → IsMild a b r A₀ B → ∀ t, 0 ≤ t → A t = B t) ∧
    ∀ A : ℝ → L2 d, IsMild a b r A₀ A → ∀ t, 0 ≤ t →
      (FU (A t) : Rd → ℂ) =ᵐ[volume] (fun ξ => (Real.exp (lam a b r ξ * t) : ℂ) * FU (A 0) ξ) ∧
      (fun ξ => ‖FU (A t) ξ‖ ^ 2) =ᵐ[volume]
        fun ξ => ‖FU (A 0) ξ‖ ^ 2 * Real.exp (2 * lam a b r ξ * t) := by
  refine ⟨⟨_, isMild_sol r ha hb A₀⟩, fun A B hA hB t ht => ?_, fun A hA t ht => ?_⟩
  · rw [mild_unique r ha hb hA ht, mild_unique r ha hb hB ht]
  · rw [hA.2.1]; exact ⟨FU_mild r ha hb hA ht, power_mild r ha hb hA ht⟩

/-! ### Unique maximising radius and the strict gap -/

include ha hb in
/-- **Lemma (unique maximising radius and strict gap).** The maximisers of `λ` are exactly the
shell `|ξ| = k⋆`, and `||ξ| − k⋆| ≥ δ ⇒ μ − λ(ξ) ≥ b k⋆² δ²`. -/
theorem gap_lemma (hd : 1 ≤ d) :
    {ξ : Rd | ∀ η : Rd, lam a b r η ≤ lam a b r ξ} = {ξ : Rd | ‖ξ‖ = kstar a b} ∧
      (∀ ξ : Rd, lam a b r ξ ≤ mu a b r) ∧
      ∀ δ > 0, ∀ ξ : Rd, δ ≤ |‖ξ‖ - kstar a b| →
        b * kstar a b ^ 2 * δ ^ 2 ≤ mu a b r - lam a b r ξ := by
  have hk := kstar_pos ha hb
  have hq0 : ∀ ξ : Rd, qf a b ξ = 0 ↔ ‖ξ‖ = kstar a b := by
    intro ξ
    rw [qf_eq, mul_eq_zero, sq_eq_zero_iff, sq_eq_zero_iff, sub_eq_zero]
    constructor
    · rintro (h | h)
      · exact h
      · exfalso; linarith [norm_nonneg ξ]
    · exact Or.inl
  -- a vector on the shell
  refine ⟨?_, lam_le r ha hb, fun δ _ ξ hξ => ?_⟩
  · ext ξ
    simp only [Set.mem_setOf_eq]
    constructor
    · intro h
      have hη : ‖EuclideanSpace.single (⟨0, hd⟩ : Fin d) (kstar a b)‖ = kstar a b := by
        rw [EuclideanSpace.norm_single, Real.norm_eq_abs, abs_of_pos hk]
      have h1 := h (EuclideanSpace.single (⟨0, hd⟩ : Fin d) (kstar a b))
      rw [lam_eq r ha hb, lam_eq r ha hb, (hq0 _).2 hη] at h1
      have h2 : qf a b ξ = 0 := le_antisymm (by nlinarith) (qf_nonneg ξ)
      exact (hq0 ξ).1 h2
    · intro h η
      rw [lam_eq r ha hb, lam_eq r ha hb, (hq0 ξ).2 h]
      nlinarith [qf_nonneg (a := a) (b := b) η]
  · rw [lam_eq r ha hb, qf_eq]
    have h1 : δ ^ 2 ≤ (‖ξ‖ - kstar a b) ^ 2 := by
      rw [← sq_abs (‖ξ‖ - kstar a b)]; exact pow_le_pow_left₀ (by linarith) hξ 2
    have h2 : kstar a b ^ 2 ≤ (‖ξ‖ + kstar a b) ^ 2 :=
      pow_le_pow_left₀ hk.le (by linarith [norm_nonneg ξ]) 2
    have : δ ^ 2 * kstar a b ^ 2 ≤ (‖ξ‖ - kstar a b) ^ 2 * (‖ξ‖ + kstar a b) ^ 2 :=
      mul_le_mul h1 h2 (by positivity) (by positivity)
    nlinarith


/-! ### Concentration of the normalised spectral power -/

variable (a b) in
/-- Hypothesis (H): `∫_{||ξ|−k⋆|<ε} |Â₀|² > 0` for every `ε > 0` (essential spectral access). -/
def SpecAccess (A₀ : L2 d) : Prop :=
  ∀ ε > 0, 0 < ∫ ξ in {ξ : Rd | |‖ξ‖ - kstar a b| < ε}, ‖FU A₀ ξ‖ ^ 2

/-- The normalised spectral measure `ν_t(E) = ∫_E P(ξ,t) dξ / Z(t)`, `P(ξ,t) = |Â(t,ξ)|²`. -/
def nu (A : ℝ → L2 d) (t : ℝ) (E : Set Rd) : ℝ :=
  (∫ ξ in E, ‖FU (A t) ξ‖ ^ 2) / ∫ ξ, ‖FU (A t) ξ‖ ^ 2

theorem measurableSet_far (δ : ℝ) : MeasurableSet {ξ : Rd | δ ≤ |‖ξ‖ - kstar a b|} :=
  measurableSet_le measurable_const ((continuous_norm.sub continuous_const).abs.measurable)

theorem measurableSet_near (δ : ℝ) : MeasurableSet {ξ : Rd | |‖ξ‖ - kstar a b| < δ} :=
  measurableSet_lt ((continuous_norm.sub continuous_const).abs.measurable) measurable_const

theorem continuous_weight (t : ℝ) :
    Continuous fun ξ : Rd => Real.exp (2 * lam a b r ξ * t) :=
  Real.continuous_exp.comp ((continuous_const.mul (continuous_lam a b r)).mul continuous_const)

include ha hb in
theorem integrable_power_weight {f : Rd → ℝ} (hf : Integrable f) {t : ℝ} (ht : 0 ≤ t) :
    Integrable fun ξ => f ξ * Real.exp (2 * lam a b r ξ * t) := by
  have := hf.bdd_mul' (c := Real.exp (2 * mu a b r * t))
    (continuous_weight r t).aestronglyMeasurable (Eventually.of_forall fun ξ => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (by linarith [lam_le r ha hb ξ]) ht))
  simpa only [mul_comm] using this

include ha hb in
theorem gap_bound {δ : ℝ} {ξ : Rd} (hξ : δ ≤ |‖ξ‖ - kstar a b|) (hδ : 0 ≤ δ) :
    b * kstar a b ^ 2 * δ ^ 2 ≤ mu a b r - lam a b r ξ := by
  have hk := kstar_pos ha hb
  rw [lam_eq r ha hb, qf_eq]
  have h1 : δ ^ 2 ≤ (‖ξ‖ - kstar a b) ^ 2 := by
    rw [← sq_abs (‖ξ‖ - kstar a b)]; exact pow_le_pow_left₀ hδ hξ 2
  have h2 : kstar a b ^ 2 ≤ (‖ξ‖ + kstar a b) ^ 2 :=
    pow_le_pow_left₀ hk.le (by linarith [norm_nonneg ξ]) 2
  have : δ ^ 2 * kstar a b ^ 2 ≤ (‖ξ‖ - kstar a b) ^ 2 * (‖ξ‖ + kstar a b) ^ 2 :=
    mul_le_mul h1 h2 (by positivity) (by positivity)
  nlinarith

include ha hb in
theorem tube_bound {δ : ℝ} (hδ : 0 < δ) {ξ : Rd}
    (hξ : |‖ξ‖ - kstar a b| < min (δ / 4) (kstar a b / 4)) :
    mu a b r - lam a b r ξ < b * kstar a b ^ 2 * δ ^ 2 / 2 := by
  have hk := kstar_pos ha hb
  rw [lam_eq r ha hb, qf_eq]
  have he1 : |‖ξ‖ - kstar a b| < δ / 4 := lt_of_lt_of_le hξ (min_le_left _ _)
  have he2 : |‖ξ‖ - kstar a b| < kstar a b / 4 := lt_of_lt_of_le hξ (min_le_right _ _)
  have h1 : (‖ξ‖ - kstar a b) ^ 2 ≤ (δ / 4) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) he1.le 2
  have h3 : ‖ξ‖ + kstar a b ≤ 9 * kstar a b / 4 := by
    have := (abs_lt.1 he2).2; linarith
  have h2 : (‖ξ‖ + kstar a b) ^ 2 ≤ (9 * kstar a b / 4) ^ 2 :=
    pow_le_pow_left₀ (by linarith [norm_nonneg ξ]) h3 2
  have h4 : (‖ξ‖ - kstar a b) ^ 2 * (‖ξ‖ + kstar a b) ^ 2 ≤ (δ / 4) ^ 2 * (9 * kstar a b / 4) ^ 2 :=
    mul_le_mul h1 h2 (by positivity) (by positivity)
  have h5 : (δ / 4) ^ 2 * (9 * kstar a b / 4) ^ 2 < kstar a b ^ 2 * δ ^ 2 / 2 := by
    have : 0 < kstar a b ^ 2 * δ ^ 2 := by positivity
    nlinarith
  have := mul_le_mul_of_nonneg_left h4 hb.le
  nlinarith

include ha hb in
/-- **Theorem (E16: concentration on the preferred shell).** Under (H), for every `δ > 0` there is
`C_δ ∈ (0,∞)` (depending only on `Â₀` and `δ`) with `ν_t(E_δ) ≤ C_δ e^{−bk⋆²δ²t}` for all
`t ≥ 0`, `E_δ = {||ξ| − k⋆| ≥ δ}`; hence `ν_t(E_δ) → 0` and `ν_t({||ξ| − k⋆| < δ}) → 1`. -/
theorem concentration {A₀ : L2 d} (hA₀ : A₀ ≠ 0) (hH : SpecAccess a b A₀) {A : ℝ → L2 d}
    (hA : IsMild a b r A₀ A) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C, 0 < C ∧
      (∀ t, 0 ≤ t → nu A t {ξ | δ ≤ |‖ξ‖ - kstar a b|} ≤
        C * Real.exp (-(b * kstar a b ^ 2 * δ ^ 2) * t)) ∧
      Tendsto (fun t => nu A t {ξ | δ ≤ |‖ξ‖ - kstar a b|}) atTop (𝓝 0) ∧
      Tendsto (fun t => nu A t {ξ | |‖ξ‖ - kstar a b| < δ}) atTop (𝓝 1) := by
  have hk := kstar_pos ha hb
  obtain ⟨m, hm⟩ : ∃ m, m = b * kstar a b ^ 2 * δ ^ 2 := ⟨_, rfl⟩
  have hm0 : 0 < m := by rw [hm]; positivity
  obtain ⟨ε, hε⟩ : ∃ ε, ε = min (δ / 4) (kstar a b / 4) := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hε]; exact lt_min (by linarith) (by linarith)
  have hfi : Integrable fun ξ => ‖FU A₀ ξ‖ ^ 2 := integrable_norm_sq_L2 (FU A₀)
  have hf0 : ∀ ξ, 0 ≤ ‖FU A₀ ξ‖ ^ 2 := fun ξ => by positivity
  obtain ⟨c, hc⟩ : ∃ c, c = ∫ ξ in {ξ : Rd | |‖ξ‖ - kstar a b| < ε}, ‖FU A₀ ξ‖ ^ 2 := ⟨_, rfl⟩
  have hc0 : 0 < c := hc ▸ hH ε hε0
  obtain ⟨F, hF⟩ : ∃ F, F = ∫ ξ, ‖FU A₀ ξ‖ ^ 2 := ⟨_, rfl⟩
  have hF0 : 0 < F := by
    rw [hF, ← norm_sq_L2, norm_FU]
    exact pow_pos (norm_pos_iff.2 hA₀) 2
  -- numerator and denominator in terms of the initial spectrum
  have hnum : ∀ t, 0 ≤ t → ∀ E : Set Rd, ∫ ξ in E, ‖FU (A t) ξ‖ ^ 2 =
      ∫ ξ in E, ‖FU A₀ ξ‖ ^ 2 * Real.exp (2 * lam a b r ξ * t) := fun t ht E =>
    integral_congr_ae (ae_restrict_of_ae (power_mild r ha hb hA ht))
  have hden : ∀ t, 0 ≤ t → ∫ ξ, ‖FU (A t) ξ‖ ^ 2 =
      ∫ ξ, ‖FU A₀ ξ‖ ^ 2 * Real.exp (2 * lam a b r ξ * t) := fun t ht =>
    integral_congr_ae (power_mild r ha hb hA ht)
  have hw : ∀ t, 0 ≤ t → Integrable fun ξ => ‖FU A₀ ξ‖ ^ 2 * Real.exp (2 * lam a b r ξ * t) :=
    fun t ht => integrable_power_weight r ha hb hfi ht
  -- the outer bound
  have hout : ∀ t, 0 ≤ t → ∫ ξ in {ξ | δ ≤ |‖ξ‖ - kstar a b|},
      ‖FU A₀ ξ‖ ^ 2 * Real.exp (2 * lam a b r ξ * t) ≤
        Real.exp (2 * mu a b r * t - 2 * m * t) * F := by
    intro t ht
    calc ∫ ξ in {ξ | δ ≤ |‖ξ‖ - kstar a b|}, ‖FU A₀ ξ‖ ^ 2 * Real.exp (2 * lam a b r ξ * t)
        ≤ ∫ ξ in {ξ | δ ≤ |‖ξ‖ - kstar a b|},
            ‖FU A₀ ξ‖ ^ 2 * Real.exp (2 * mu a b r * t - 2 * m * t) := by
          refine setIntegral_mono_on (hw t ht).integrableOn (hfi.mul_const _).integrableOn
            (measurableSet_far δ) fun ξ hξ => ?_
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (hf0 ξ)
          have := gap_bound r ha hb hξ hδ.le
          rw [← hm] at this
          nlinarith
      _ = Real.exp (2 * mu a b r * t - 2 * m * t) *
            ∫ ξ in {ξ | δ ≤ |‖ξ‖ - kstar a b|}, ‖FU A₀ ξ‖ ^ 2 := by
          rw [integral_mul_const, mul_comm]
      _ ≤ Real.exp (2 * mu a b r * t - 2 * m * t) * F := by
          rw [hF]
          exact mul_le_mul_of_nonneg_left (setIntegral_le_integral hfi (Eventually.of_forall hf0))
            (Real.exp_pos _).le
  -- the inner bound
  have hin : ∀ t, 0 ≤ t → Real.exp (2 * mu a b r * t - m * t) * c ≤
      ∫ ξ, ‖FU A₀ ξ‖ ^ 2 * Real.exp (2 * lam a b r ξ * t) := by
    intro t ht
    calc Real.exp (2 * mu a b r * t - m * t) * c
        = ∫ ξ in {ξ : Rd | |‖ξ‖ - kstar a b| < ε},
            ‖FU A₀ ξ‖ ^ 2 * Real.exp (2 * mu a b r * t - m * t) := by
          rw [hc, integral_mul_const, mul_comm]
      _ ≤ ∫ ξ in {ξ : Rd | |‖ξ‖ - kstar a b| < ε},
            ‖FU A₀ ξ‖ ^ 2 * Real.exp (2 * lam a b r ξ * t) := by
          refine setIntegral_mono_on (hfi.mul_const _).integrableOn (hw t ht).integrableOn
            (measurableSet_near ε) fun ξ hξ => ?_
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (hf0 ξ)
          have := tube_bound r ha hb hδ (hε ▸ hξ)
          rw [← hm] at this
          nlinarith
      _ ≤ ∫ ξ, ‖FU A₀ ξ‖ ^ 2 * Real.exp (2 * lam a b r ξ * t) :=
          setIntegral_le_integral (hw t ht) (Eventually.of_forall fun ξ => by positivity)
  have hZ : ∀ t, 0 ≤ t → 0 < ∫ ξ, ‖FU (A t) ξ‖ ^ 2 := fun t ht => by
    rw [hden t ht]; exact lt_of_lt_of_le (by positivity) (hin t ht)
  have hbound : ∀ t, 0 ≤ t → nu A t {ξ | δ ≤ |‖ξ‖ - kstar a b|} ≤ F / c * Real.exp (-m * t) := by
    intro t ht
    rw [nu, hnum t ht, hden t ht, div_le_iff₀ (lt_of_lt_of_le (by positivity) (hin t ht))]
    calc ∫ ξ in {ξ | δ ≤ |‖ξ‖ - kstar a b|}, ‖FU A₀ ξ‖ ^ 2 * Real.exp (2 * lam a b r ξ * t)
        ≤ Real.exp (2 * mu a b r * t - 2 * m * t) * F := hout t ht
      _ = F / c * Real.exp (-m * t) * (Real.exp (2 * mu a b r * t - m * t) * c) := by
          rw [show 2 * mu a b r * t - 2 * m * t = -m * t + (2 * mu a b r * t - m * t) by ring,
            Real.exp_add]
          field_simp
      _ ≤ F / c * Real.exp (-m * t) * ∫ ξ, ‖FU A₀ ξ‖ ^ 2 * Real.exp (2 * lam a b r ξ * t) :=
          mul_le_mul_of_nonneg_left (hin t ht) (by positivity)
  have hnu0 : ∀ t, 0 ≤ t → 0 ≤ nu A t {ξ | δ ≤ |‖ξ‖ - kstar a b|} := fun t ht =>
    div_nonneg (setIntegral_nonneg (measurableSet_far δ) fun ξ _ => by positivity)
      (hZ t ht).le
  have hlim0 : Tendsto (fun t => nu A t {ξ | δ ≤ |‖ξ‖ - kstar a b|}) atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => F / c * Real.exp (-m * t)) atTop (𝓝 0) := by
      have := (Real.tendsto_exp_atBot.comp
        (tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos hm0))).const_mul (F / c)
      simpa [Function.comp_def] using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h1 ?_ ?_
    · filter_upwards [eventually_ge_atTop 0] with t ht using hnu0 t ht
    · filter_upwards [eventually_ge_atTop 0] with t ht using hbound t ht
  refine ⟨F / c, by positivity, fun t ht => by rw [← hm]; exact hbound t ht, hlim0, ?_⟩
  -- the complementary set
  have hcompl : ∀ t, 0 ≤ t → nu A t {ξ | |‖ξ‖ - kstar a b| < δ} =
      1 - nu A t {ξ | δ ≤ |‖ξ‖ - kstar a b|} := by
    intro t ht
    have hset : {ξ : Rd | |‖ξ‖ - kstar a b| < δ} = {ξ | δ ≤ |‖ξ‖ - kstar a b|}ᶜ := by
      ext ξ; simp [not_le]
    have hsum := integral_add_compl (measurableSet_far (a := a) (b := b) δ)
      (integrable_norm_sq_L2 (FU (A t)))
    rw [nu, nu, hset, eq_sub_iff_add_eq, ← add_div, add_comm, hsum, div_self (hZ t ht).ne']
  have h2 := hlim0.const_sub 1
  rw [sub_zero] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with t ht using (hcompl t ht).symm


/-! ### Convergence of the spectral argmax -/

/-- A continuous nonnegative function vanishing at infinity (relative to a closed set) is bounded
there. -/
theorem bdd_of_van {X : Type*} [TopologicalSpace X] {s : Set X} (hs : IsClosed s) {f : X → ℝ}
    (hf : ContinuousOn f s) (hvan : ∀ ε > 0, ∃ K, IsCompact K ∧ ∀ x ∈ s, x ∉ K → f x < ε) :
    ∃ M, ∀ x ∈ s, f x ≤ M := by
  obtain ⟨K, hK, hKf⟩ := hvan 1 one_pos
  obtain ⟨M₁, hM₁⟩ : ∃ M₁, ∀ x ∈ s ∩ K, f x ≤ M₁ := by
    rcases (s ∩ K).eq_empty_or_nonempty with h | h
    · exact ⟨0, fun x hx => by rw [h] at hx; exact absurd hx (Set.notMem_empty x)⟩
    · obtain ⟨x, -, hx⟩ := (hK.inter_left hs).exists_isMaxOn h (hf.mono inter_subset_left)
      exact ⟨f x, fun y hy => hx hy⟩
  refine ⟨max M₁ 1, fun x hx => ?_⟩
  by_cases hxK : x ∈ K
  · exact (hM₁ x ⟨hx, hxK⟩).trans (le_max_left _ _)
  · exact (hKf x hx hxK).le.trans (le_max_right _ _)

/-- The comparison argument behind the argmax theorems: if `f ≥ 0` is continuous, vanishes at
infinity and is positive arbitrarily close to `{q = 0}`, then the maximisers of
`f e^{−ctq}` exist and every choice of them has `q → 0`. -/
theorem argmax_abstract {X : Type*} [TopologicalSpace X] {s : Set X} (hs : IsClosed s)
    {f q : X → ℝ} (hf : ContinuousOn f s) (hq : ContinuousOn q s) (hf0 : ∀ x ∈ s, 0 ≤ f x)
    (hq0 : ∀ x ∈ s, 0 ≤ q x) (hvan : ∀ ε > 0, ∃ K, IsCompact K ∧ ∀ x ∈ s, x ∉ K → f x < ε)
    (hacc : ∀ ε > 0, ∃ x ∈ s, 0 < f x ∧ q x < ε) {c : ℝ} (hc : 0 < c) :
    (∀ t, 0 ≤ t → ∃ x ∈ s, IsMaxOn (fun x => f x * Real.exp (-(c * t * q x))) s x) ∧
    ∀ xt : ℝ → X, (∀ᶠ t in atTop, xt t ∈ s ∧
        IsMaxOn (fun x => f x * Real.exp (-(c * t * q x))) s (xt t)) →
      Tendsto (fun t => q (xt t)) atTop (𝓝 0) := by
  obtain ⟨M, hM⟩ := bdd_of_van hs hf hvan
  refine ⟨fun t ht => ?_, fun xt hxt => ?_⟩
  · obtain ⟨x₀, hx₀s, hx₀, -⟩ := hacc 1 one_pos
    have hG : ContinuousOn (fun x => f x * Real.exp (-(c * t * q x))) s :=
      hf.mul (Real.continuous_exp.comp_continuousOn ((continuousOn_const.mul hq).neg))
    have hGx₀ : 0 < f x₀ * Real.exp (-(c * t * q x₀)) := mul_pos hx₀ (Real.exp_pos _)
    have hGle : ∀ x ∈ s, f x * Real.exp (-(c * t * q x)) ≤ f x := fun x hx => by
      have : Real.exp (-(c * t * q x)) ≤ 1 := Real.exp_le_one_iff.2 (by
        have := hq0 x hx; have : 0 ≤ c * t * q x := by positivity
        linarith)
      nlinarith [hf0 x hx, Real.exp_pos (-(c * t * q x))]
    obtain ⟨K, hK, hKf⟩ := hvan _ hGx₀
    have hx₀K : x₀ ∈ K := by
      by_contra h
      exact absurd (hKf x₀ hx₀s h) (not_lt.2 (hGle x₀ hx₀s))
    obtain ⟨x₁, ⟨hx₁s, -⟩, hx₁⟩ := (hK.inter_left hs).exists_isMaxOn ⟨x₀, hx₀s, hx₀K⟩
      (hG.mono inter_subset_left)
    refine ⟨x₁, hx₁s, fun y hy => ?_⟩
    by_cases hyK : y ∈ K
    · exact hx₁ ⟨hy, hyK⟩
    · exact (hGle y hy).trans ((hKf y hy hyK).le.trans (hx₁ ⟨hx₀s, hx₀K⟩))
  · rw [tendsto_order]
    refine ⟨fun a ha => ?_, fun ε hε => ?_⟩
    · filter_upwards [hxt] with t ht using lt_of_lt_of_le ha (hq0 _ ht.1)
    obtain ⟨x₁, hx₁s, hfx₁, hqx₁⟩ := hacc (ε / 2) (by linarith)
    have hlim : Tendsto (fun t => Real.exp (c * (ε / 2) * t)) atTop atTop :=
      Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by positivity))
    filter_upwards [hxt, hlim.eventually_gt_atTop (M / f x₁), eventually_ge_atTop 0]
      with t ht hbig ht0
    by_contra hcon
    push_neg at hcon
    have h1 := ht.2 hx₁s
    simp only [Set.mem_setOf_eq] at h1
    -- `f(xₜ) e^{-ctq(xₜ)} ≤ M e^{-ctε}`
    have h2 : f (xt t) * Real.exp (-(c * t * q (xt t))) ≤ M * Real.exp (-(c * t * ε)) := by
      apply mul_le_mul (hM _ ht.1) (Real.exp_le_exp.2 _) (Real.exp_pos _).le
        ((hf0 _ ht.1).trans (hM _ ht.1))
      have : c * t * ε ≤ c * t * q (xt t) := mul_le_mul_of_nonneg_left hcon (by positivity)
      linarith
    -- `f(x₁) e^{-ctq(x₁)} ≥ f(x₁) e^{-ctε/2}`
    have h3 : f x₁ * Real.exp (-(c * t * (ε / 2))) ≤ f x₁ * Real.exp (-(c * t * q x₁)) := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 _) hfx₁.le
      have : c * t * q x₁ ≤ c * t * (ε / 2) := mul_le_mul_of_nonneg_left hqx₁.le (by positivity)
      linarith
    have h4 : M < f x₁ * Real.exp (c * (ε / 2) * t) := by rwa [div_lt_iff₀ hfx₁, mul_comm] at hbig
    have h5 : M * Real.exp (-(c * t * ε)) < f x₁ * Real.exp (-(c * t * (ε / 2))) := by
      have e : Real.exp (-(c * t * ε)) = (Real.exp (c * (ε / 2) * t))⁻¹ *
          Real.exp (-(c * t * (ε / 2))) := by
        rw [← Real.exp_neg, ← Real.exp_add]; congr 1; ring
      rw [e, ← mul_assoc]
      refine mul_lt_mul_of_pos_right ?_ (Real.exp_pos _)
      rw [mul_inv_lt_iff₀ (Real.exp_pos _)]
      linarith
    linarith

theorem abs_norm_sub_le_of_qf (ha : 0 < a) (hb : 0 < b) (ξ : Rd) :
    |‖ξ‖ - kstar a b| ≤ √(qf a b ξ) / kstar a b := by
  have hk := kstar_pos ha hb
  rw [le_div_iff₀ hk, qf_eq, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs,
    Real.sqrt_sq_eq_abs]
  have : kstar a b ≤ |‖ξ‖ + kstar a b| := by
    rw [abs_of_nonneg (by positivity)]; linarith [norm_nonneg ξ]
  exact mul_le_mul_of_nonneg_left this (abs_nonneg _)

include ha hb in
/-- Points of positive initial power near the shell, from (H). -/
theorem exists_pos_near {A₀ : L2 d} (hH : SpecAccess a b A₀) {f : Rd → ℝ}
    (hf_rep : f =ᵐ[volume] fun ξ => ‖FU A₀ ξ‖ ^ 2) {ε : ℝ} (hε : 0 < ε) :
    ∃ ξ : Rd, 0 < f ξ ∧ qf a b ξ < ε := by
  have hk := kstar_pos ha hb
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = √(2 * ε) / kstar a b := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have hpos := hH (min (δ / 4) (kstar a b / 4)) (lt_min (by linarith) (by linarith))
  by_contra hne
  push_neg at hne
  have hle : ∫ ξ in {ξ : Rd | |‖ξ‖ - kstar a b| < min (δ / 4) (kstar a b / 4)},
      ‖FU A₀ ξ‖ ^ 2 ≤ 0 := by
    rw [← integral_congr_ae (ae_restrict_of_ae hf_rep)]
    refine setIntegral_nonpos (measurableSet_near _) fun ξ hξ => ?_
    by_contra hpos'
    push_neg at hpos'
    have h1 := hne ξ hpos'
    have h2 := tube_bound 0 ha hb hδ0 hξ
    rw [lam_eq 0 ha hb] at h2
    have h3 : b * kstar a b ^ 2 * δ ^ 2 / 2 = b * ε := by
      rw [hδ, div_pow, Real.sq_sqrt (by positivity)]; field_simp
    nlinarith
  linarith

include ha hb in
/-- **Theorem (argmax convergence).** Assume (H) and that `f = |Â₀|²` has a nonnegative continuous
representative vanishing at infinity. Then for every `t ≥ 0` the continuous power
`P(ξ,t) = f(ξ) e^{2λ(ξ)t}` (a representative of `|Â(t,ξ)|²`) attains its maximum, and every choice
of maximisers satisfies `|ξ_t| → k⋆`. -/
theorem argmax_convergence {A₀ : L2 d} (hH : SpecAccess a b A₀) {f : Rd → ℝ} (hfc : Continuous f)
    (hf0 : ∀ ξ, 0 ≤ f ξ) (hf_van : Tendsto f (cocompact Rd) (𝓝 0))
    (hf_rep : f =ᵐ[volume] fun ξ => ‖FU A₀ ξ‖ ^ 2) :
    (∀ A : ℝ → L2 d, IsMild a b r A₀ A → ∀ t, 0 ≤ t →
      (fun ξ => ‖FU (A t) ξ‖ ^ 2) =ᵐ[volume] fun ξ => f ξ * Real.exp (2 * lam a b r ξ * t)) ∧
    (∀ t, 0 ≤ t → ∃ ξ, IsMaxOn (fun ξ => f ξ * Real.exp (2 * lam a b r ξ * t)) univ ξ) ∧
    ∀ ξt : ℝ → Rd,
      (∀ᶠ t in atTop, IsMaxOn (fun ξ => f ξ * Real.exp (2 * lam a b r ξ * t)) univ (ξt t)) →
        Tendsto (fun t => ‖ξt t‖) atTop (𝓝 (kstar a b)) := by
  have hk := kstar_pos ha hb
  -- rewrite the power as `e^{2μt} · f e^{−2btq}`
  have hfac : ∀ t ξ, f ξ * Real.exp (2 * lam a b r ξ * t) =
      Real.exp (2 * mu a b r * t) * (f ξ * Real.exp (-(2 * b * t * qf a b ξ))) := by
    intro t ξ
    rw [lam_eq r ha hb, mul_left_comm, ← Real.exp_add]; congr 2; ring
  have hmax_iff : ∀ t ξ, IsMaxOn (fun ξ => f ξ * Real.exp (2 * lam a b r ξ * t)) univ ξ ↔
      IsMaxOn (fun ξ => f ξ * Real.exp (-(2 * b * t * qf a b ξ))) univ ξ := by
    intro t ξ
    simp only [isMaxOn_iff, mem_univ, true_implies, hfac]
    exact forall_congr' fun η => mul_le_mul_iff_of_pos_left (Real.exp_pos _)
  have hcq : Continuous (qf (d := d) a b) := by unfold qf; fun_prop
  have hvan : ∀ ε > 0, ∃ K, IsCompact K ∧ ∀ x ∈ (univ : Set Rd), x ∉ K → f x < ε := by
    intro ε hε
    obtain ⟨K, hK, hKs⟩ := mem_cocompact.1 (hf_van.eventually (gt_mem_nhds hε))
    exact ⟨K, hK, fun x _ hx => hKs hx⟩
  have hacc : ∀ ε > 0, ∃ x ∈ (univ : Set Rd), 0 < f x ∧ qf a b x < ε := by
    intro ε hε
    obtain ⟨ξ, h1, h2⟩ := exists_pos_near ha hb hH hf_rep hε
    exact ⟨ξ, mem_univ _, h1, h2⟩
  obtain ⟨hex, hconv⟩ := argmax_abstract isClosed_univ hfc.continuousOn hcq.continuousOn
    (fun x _ => hf0 x) (fun x _ => qf_nonneg x) hvan hacc (c := 2 * b) (by positivity)
  refine ⟨fun A hA t ht => ?_, fun t ht => ?_, fun ξt hξt => ?_⟩
  · filter_upwards [power_mild r ha hb hA ht, hf_rep] with ξ h1 h2
    rw [h1, h2]
  · obtain ⟨ξ, -, hξ⟩ := hex t ht
    exact ⟨ξ, (hmax_iff t ξ).2 hξ⟩
  · have hq := hconv ξt (by
      filter_upwards [hξt] with t ht using ⟨mem_univ _, (hmax_iff t (ξt t)).1 ht⟩)
    have hsq : Tendsto (fun t => √(qf a b (ξt t)) / kstar a b) atTop (𝓝 0) := by
      have := (hq.sqrt).div_const (kstar a b)
      rwa [Real.sqrt_zero, zero_div] at this
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun t => norm_nonneg _) (fun t => ?_) hsq
    rw [Real.norm_eq_abs]; exact abs_norm_sub_le_of_qf ha hb (ξt t)

include ha hb in
/-- **Corollary (explicit `t^{-1/2}` bound).** If `f(η⋆) > 0` at a shell point `|η⋆| = k⋆` and
`M = sup f`, every maximiser `ξ_t` of `P(·,t)`, `t > 0`, satisfies
`||ξ_t| − k⋆| ≤ √(log(M/f(η⋆)) / (2bk⋆²t))`. -/
theorem argmax_rate {f : Rd → ℝ} (hfc : Continuous f)
    (hf_van : Tendsto f (cocompact Rd) (𝓝 0)) {η : Rd} (hη : ‖η‖ = kstar a b) (hfη : 0 < f η)
    {t : ℝ} (ht : 0 < t) {ξ : Rd}
    (hξ : IsMaxOn (fun ξ => f ξ * Real.exp (2 * lam a b r ξ * t)) univ ξ) :
    |‖ξ‖ - kstar a b| ≤ √(Real.log ((⨆ ζ, f ζ) / f η) / (2 * b * kstar a b ^ 2 * t)) := by
  have hk := kstar_pos ha hb
  have hvan : ∀ ε > 0, ∃ K, IsCompact K ∧ ∀ x ∈ (univ : Set Rd), x ∉ K → f x < ε := by
    intro ε hε
    obtain ⟨K, hK, hKs⟩ := mem_cocompact.1 (hf_van.eventually (gt_mem_nhds hε))
    exact ⟨K, hK, fun x _ hx => hKs hx⟩
  obtain ⟨M₀, hM₀⟩ := bdd_of_van isClosed_univ hfc.continuousOn hvan
  have hbdd : BddAbove (range f) := ⟨M₀, by rintro _ ⟨x, rfl⟩; exact hM₀ x (mem_univ _)⟩
  obtain ⟨M, hM⟩ : ∃ M, M = ⨆ ζ, f ζ := ⟨_, rfl⟩
  rw [← hM]
  have hfM : ∀ ζ, f ζ ≤ M := fun ζ => hM ▸ le_ciSup hbdd ζ
  have hMpos : 0 < M := lt_of_lt_of_le hfη (hfM η)
  have hqη : qf a b η = 0 := by rw [qf, hη, sub_self]; ring
  -- `f(ξ) e^{−2btq(ξ)} ≥ f(η)`
  have h1 := hξ (mem_univ η)
  simp only [Set.mem_setOf_eq] at h1
  rw [lam_eq r ha hb, lam_eq r ha hb, hqη] at h1
  have h2 : f η ≤ f ξ * Real.exp (-(2 * b * t * qf a b ξ)) := by
    have e1 : f η * Real.exp (2 * (mu a b r - b * 0) * t) =
        Real.exp (2 * mu a b r * t) * f η := by ring_nf
    have e2 : f ξ * Real.exp (2 * (mu a b r - b * qf a b ξ) * t) =
        Real.exp (2 * mu a b r * t) * (f ξ * Real.exp (-(2 * b * t * qf a b ξ))) := by
      rw [mul_left_comm, ← Real.exp_add]; congr 2; ring
    rw [e1, e2] at h1
    exact le_of_mul_le_mul_left h1 (Real.exp_pos _)
  have h3 : f η ≤ M * Real.exp (-(2 * b * t * qf a b ξ)) :=
    h2.trans (mul_le_mul_of_nonneg_right (hfM ξ) (Real.exp_pos _).le)
  -- `q(ξ) ≤ log(M/f(η)) / (2bt)`
  have h4 : 2 * b * t * qf a b ξ ≤ Real.log (M / f η) := by
    have h5 : f η / M ≤ Real.exp (-(2 * b * t * qf a b ξ)) := by
      rw [div_le_iff₀ hMpos]; linarith
    have h6 := Real.log_le_log (div_pos hfη hMpos) h5
    rw [Real.log_exp, Real.log_div hfη.ne' hMpos.ne'] at h6
    rw [Real.log_div hMpos.ne' hfη.ne']; linarith
  have h7 : (‖ξ‖ - kstar a b) ^ 2 * kstar a b ^ 2 ≤ qf a b ξ := by
    rw [qf_eq]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hk.le (by linarith [norm_nonneg ξ]) 2)
      (sq_nonneg _)
  rw [← Real.sqrt_sq_eq_abs]
  refine Real.sqrt_le_sqrt ?_
  rw [le_div_iff₀ (by positivity)]
  have h8 := mul_le_mul_of_nonneg_left h7 (show (0 : ℝ) ≤ 2 * b * t by positivity)
  have e : (‖ξ‖ - kstar a b) ^ 2 * (2 * b * kstar a b ^ 2 * t) =
      2 * b * t * ((‖ξ‖ - kstar a b) ^ 2 * kstar a b ^ 2) := by ring
  rw [e]; linarith


/-! ### Polar coordinates and the radial spectral density -/

theorem nontrivial_Rd (hd : 1 ≤ d) : Nontrivial Rd :=
  ⟨⟨EuclideanSpace.single (⟨0, hd⟩ : Fin d) 1, 0, by
    intro h
    have := congrArg (fun v : Rd => v (⟨0, hd⟩ : Fin d)) h
    simp at this⟩⟩

/-- The surface measure `dω` on `S^{d−1}` (Mathlib's `toSphere`, the cone measure; counting
measure for `d = 1`). -/
abbrev σS (d : ℕ) : Measure (Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1) :=
  (volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere

/-- **Polar integration**: `∫_{ℝ^d} g = ∫_0^∞ k^{d−1} ∫_{S^{d−1}} g(kω) dω dk`. -/
theorem integral_polar (hd : 1 ≤ d) {g : Rd → ℝ} (hg : Integrable g) :
    ∫ ξ, g ξ = ∫ k in Ioi (0 : ℝ), k ^ (d - 1) * ∫ w, g (k • (w : Rd)) ∂(σS d) := by
  haveI := nontrivial_Rd hd
  have hmp := (volume : Measure Rd).measurePreserving_homeomorphUnitSphereProd
  rw [finrank_euclideanSpace_fin] at hmp
  have h1 : ∫ ξ, g ξ = ∫ x : ({(0 : Rd)}ᶜ : Set Rd), g x ∂(volume.comap Subtype.val) := by
    rw [integral_subtype_comap (measurableSet_singleton _).compl, restrict_compl_singleton]
  have hG : (fun x : ({(0 : Rd)}ᶜ : Set Rd) => g x) =
      (fun p : Metric.sphere (0 : Rd) 1 × Ioi (0 : ℝ) => g (p.2.1 • (p.1 : Rd))) ∘
        homeomorphUnitSphereProd Rd := by
    funext x
    simp only [Function.comp_apply]
    congr 1
    have := congrArg Subtype.val ((homeomorphUnitSphereProd Rd).symm_apply_apply x)
    rw [← this]; rfl
  have h2 : ∫ x : ({(0 : Rd)}ᶜ : Set Rd), g x ∂(volume.comap Subtype.val) =
      ∫ p : Metric.sphere (0 : Rd) 1 × Ioi (0 : ℝ), g (p.2.1 • (p.1 : Rd))
        ∂((σS d).prod (Measure.volumeIoiPow (d - 1))) := by
    rw [hG]
    exact hmp.integral_comp (Homeomorph.measurableEmbedding _)
      (fun p : Metric.sphere (0 : Rd) 1 × Ioi (0 : ℝ) => g (p.2.1 • (p.1 : Rd)))
  have hint : Integrable (fun p : Metric.sphere (0 : Rd) 1 × Ioi (0 : ℝ) => g (p.2.1 • (p.1 : Rd)))
      ((σS d).prod (Measure.volumeIoiPow (d - 1))) := by
    rw [← hmp.integrable_comp_emb (Homeomorph.measurableEmbedding _), ← hG]
    exact (integrableOn_iff_comap_subtypeVal (measurableSet_singleton _).compl).1 hg.integrableOn
  rw [h1, h2, integral_prod_symm _ hint]
  simp only [Measure.volumeIoiPow, ENNReal.ofReal]
  rw [integral_withDensity_eq_integral_smul
      ((measurable_subtype_coe.pow_const _).real_toNNReal),
    integral_subtype_comap measurableSet_Ioi
      (fun k => Real.toNNReal (k ^ (d - 1)) • ∫ w, g (k • (w : Rd)) ∂(σS d))]
  refine setIntegral_congr_fun measurableSet_Ioi fun k hk => ?_
  rw [NNReal.smul_def, Real.coe_toNNReal _ (pow_nonneg (le_of_lt hk) _), smul_eq_mul]


/-- Almost-everywhere statements pass to polar coordinates. -/
theorem ae_polar {p : Rd → Prop} (h : ∀ᵐ ξ ∂(volume : Measure Rd), p ξ) :
    ∀ᵐ k ∂(volume.restrict (Ioi (0 : ℝ))), ∀ᵐ (w : Metric.sphere (0 : Rd) 1) ∂(σS d), p (k • (w : Rd)) := by
  have hmp := (volume : Measure Rd).measurePreserving_homeomorphUnitSphereProd
  rw [finrank_euclideanSpace_fin] at hmp
  have h1 : ∀ᵐ (x : ({(0 : Rd)}ᶜ : Set Rd)) ∂(volume.comap (Subtype.val : ({(0 : Rd)}ᶜ : Set Rd) → Rd)),
      p x := by
    have := (MeasurableEmbedding.subtype_coe (measurableSet_singleton (0 : Rd)).compl).ae_map_iff
      (μ := volume.comap Subtype.val) (p := p)
    rw [map_comap_subtype_coe (measurableSet_singleton _).compl] at this
    exact this.1 (ae_restrict_of_ae h)
  have hmps := hmp.symm (homeomorphUnitSphereProd Rd).toMeasurableEquiv
  have h2 : ∀ᵐ q ∂((σS d).prod (Measure.volumeIoiPow (d - 1))), p (q.2.1 • (q.1 : Rd)) :=
    hmps.quasiMeasurePreserving.ae h1
  have h3 : ∀ᵐ q ∂((Measure.volumeIoiPow (d - 1)).prod (σS d)), p (q.1.1 • (q.2 : Rd)) :=
    (Measure.measurePreserving_swap (μ := Measure.volumeIoiPow (d - 1)) (ν := σS d)).quasiMeasurePreserving.ae h2
  have h4 := Measure.ae_ae_of_ae_prod h3
  simp only [Measure.volumeIoiPow] at h4
  rw [ae_withDensity_iff ((measurable_subtype_coe.pow_const _).ennreal_ofReal)] at h4
  have h5 : ∀ᵐ (k : Ioi (0 : ℝ)) ∂(volume.comap (Subtype.val : Ioi (0 : ℝ) → ℝ)),
      ∀ᵐ (w : Metric.sphere (0 : Rd) 1) ∂(σS d), p ((k : ℝ) • (w : Rd)) := by
    filter_upwards [h4] with k hk
    exact hk (by rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact pow_pos k.2 _)
  have := (MeasurableEmbedding.subtype_coe measurableSet_Ioi).ae_map_iff
    (μ := volume.comap (Subtype.val : Ioi (0 : ℝ) → ℝ))
    (p := fun k : ℝ => ∀ᵐ (w : Metric.sphere (0 : Rd) 1) ∂(σS d), p (k • (w : Rd)))
  rw [map_comap_subtype_coe measurableSet_Ioi] at this
  exact this.2 h5

/-- The radial spectral density `𝒫(k,t) = k^{d−1} ∫_{S^{d−1}} P(kω,t) dω`. -/
def radP (A : ℝ → L2 d) (t k : ℝ) : ℝ := k ^ (d - 1) * ∫ w, ‖FU (A t) (k • (w : Rd))‖ ^ 2 ∂(σS d)

variable (a b) in
/-- `Λ(k) = μ − b(k² − k⋆²)²`, the growth rate on the shell of radius `k`. -/
def lamR (k : ℝ) : ℝ := mu a b r - b * (k ^ 2 - kstar a b ^ 2) ^ 2

theorem norm_smul_sphere {k : ℝ} (hk : 0 < k) (w : Metric.sphere (0 : Rd) 1) :
    ‖k • (w : Rd)‖ = k := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hk, norm_eq_of_mem_sphere w, mul_one]

/-- `∫_{ℝ^d} P(ξ,t) dξ = ∫_0^∞ 𝒫(k,t) dk`. -/
theorem integral_radP (hd : 1 ≤ d) (A : ℝ → L2 d) (t : ℝ) :
    ∫ ξ, ‖FU (A t) ξ‖ ^ 2 = ∫ k in Ioi (0 : ℝ), radP A t k :=
  integral_polar hd (integrable_norm_sq_L2 _)

/-- Radial sets: `∫_{|ξ| ∈ S} P(ξ,t) dξ = ∫_{(0,∞) ∩ S} 𝒫(k,t) dk`. -/
theorem setIntegral_radial (hd : 1 ≤ d) (A : ℝ → L2 d) (t : ℝ) {S : Set ℝ} (hS : MeasurableSet S) :
    ∫ ξ in {ξ : Rd | ‖ξ‖ ∈ S}, ‖FU (A t) ξ‖ ^ 2 = ∫ k in Ioi (0 : ℝ) ∩ S, radP A t k := by
  have hmS : MeasurableSet {ξ : Rd | ‖ξ‖ ∈ S} := measurable_norm hS
  rw [← integral_indicator hmS, integral_polar hd ((integrable_norm_sq_L2 _).indicator hmS),
    ← setIntegral_indicator hS]
  refine setIntegral_congr_fun measurableSet_Ioi fun k hk => ?_
  have e : ∀ w : Metric.sphere (0 : Rd) 1,
      {ξ : Rd | ‖ξ‖ ∈ S}.indicator (fun ξ => ‖FU (A t) ξ‖ ^ 2) (k • (w : Rd)) =
        S.indicator (fun _ => ‖FU (A t) (k • (w : Rd))‖ ^ 2) k := by
    intro w
    have hmem : (k • (w : Rd)) ∈ {ξ : Rd | ‖ξ‖ ∈ S} ↔ k ∈ S := by
      rw [Set.mem_setOf_eq, norm_smul_sphere (mem_Ioi.1 hk) w]
    by_cases hkS : k ∈ S
    · rw [Set.indicator_of_mem (hmem.2 hkS), Set.indicator_of_mem hkS]
    · rw [Set.indicator_of_notMem (fun h => hkS (hmem.1 h)), Set.indicator_of_notMem hkS]
  simp_rw [e]
  by_cases hkS : k ∈ S
  · simp [Set.indicator_of_mem hkS, radP]
  · simp [Set.indicator_of_notMem hkS]

include ha hb in
/-- **Radial power law**: `𝒫(k,t) = 𝒫(k,0) e^{2[μ − b(k² − k⋆²)²]t}` for a.e. `k > 0`. -/
theorem radial_law {A₀ : L2 d} {A : ℝ → L2 d} (hA : IsMild a b r A₀ A) {t : ℝ}
    (ht : 0 ≤ t) :
    ∀ᵐ k ∂(volume.restrict (Ioi (0 : ℝ))), radP A t k = radP A 0 k * Real.exp (2 * lamR a b r k * t) := by
  have h := ae_polar (power_mild r ha hb hA ht)
  filter_upwards [h, ae_restrict_mem measurableSet_Ioi] with k hk hk0
  rw [radP, radP, hA.2.1, mul_assoc, ← integral_mul_const]
  congr 1
  apply integral_congr_ae
  filter_upwards [hk] with w hw
  rw [hw, lam_eq r ha hb, qf, norm_smul_sphere hk0 w, lamR]


/-- The comparison bound behind the explicit rates. -/
theorem rate_abstract {X : Type*} {s : Set X} {f q : X → ℝ} {M c t : ℝ}
    (hfM : ∀ x ∈ s, f x ≤ M) {x₀ x : X} (hx₀ : x₀ ∈ s) (hfx₀ : 0 < f x₀) (hq₀ : q x₀ = 0)
    (hx : x ∈ s) (hmax : IsMaxOn (fun x => f x * Real.exp (-(c * t * q x))) s x) :
    c * t * q x ≤ Real.log (M / f x₀) := by
  have hMpos : 0 < M := lt_of_lt_of_le hfx₀ (hfM x₀ hx₀)
  have h1 := hmax hx₀
  simp only [Set.mem_setOf_eq, hq₀, mul_zero, neg_zero, Real.exp_zero, mul_one] at h1
  have h3 : f x₀ ≤ M * Real.exp (-(c * t * q x)) :=
    h1.trans (mul_le_mul_of_nonneg_right (hfM x hx) (Real.exp_pos _).le)
  have h5 : f x₀ / M ≤ Real.exp (-(c * t * q x)) := by
    rw [div_le_iff₀ hMpos]; linarith
  have h6 := Real.log_le_log (div_pos hfx₀ hMpos) h5
  rw [Real.log_exp, Real.log_div hfx₀.ne' hMpos.ne'] at h6
  rw [Real.log_div hMpos.ne' hfx₀.ne']; linarith

theorem lamR_factor (g : ℝ → ℝ) (t k : ℝ) :
    g k * Real.exp (2 * lamR a b r k * t) =
      Real.exp (2 * mu a b r * t) * (g k * Real.exp (-(2 * b * t * (k ^ 2 - kstar a b ^ 2) ^ 2))) := by
  rw [lamR, mul_left_comm, ← Real.exp_add]; congr 2; ring

theorem isMaxOn_lamR_iff (g : ℝ → ℝ) (t k : ℝ) :
    IsMaxOn (fun k => g k * Real.exp (2 * lamR a b r k * t)) (Ici 0) k ↔
      IsMaxOn (fun k => g k * Real.exp (-(2 * b * t * (k ^ 2 - kstar a b ^ 2) ^ 2))) (Ici 0) k := by
  simp only [isMaxOn_iff, lamR_factor r g t]
  exact forall₂_congr fun η _ => mul_le_mul_iff_of_pos_left (Real.exp_pos _)

theorem abs_sub_le_of_sq (ha : 0 < a) (hb : 0 < b) {k : ℝ} (hk : 0 ≤ k) :
    |k - kstar a b| ≤ √((k ^ 2 - kstar a b ^ 2) ^ 2) / kstar a b := by
  have hks := kstar_pos ha hb
  rw [le_div_iff₀ hks, Real.sqrt_sq_eq_abs,
    show k ^ 2 - kstar a b ^ 2 = (k - kstar a b) * (k + kstar a b) by ring, abs_mul]
  exact mul_le_mul_of_nonneg_left (by rw [abs_of_nonneg (by positivity)]; linarith) (abs_nonneg _)

include ha hb in
/-- **Corollary (radial concentration and maximising wavenumber).** Under (H): the radial mass
fraction outside `|k − k⋆| < δ` tends to zero; if `𝒫(·,0)` has a nonnegative continuous
representative `g ∈ C₀([0,∞))`, the maximisers `k_t` of `𝒫(·,t) = g e^{2Λt}` over `k ≥ 0` exist and
every choice satisfies `k_t → k⋆`; if moreover `g(k⋆) > 0`, then
`|k_t − k⋆| ≤ √(log(sup g / g(k⋆)) / (2bk⋆²t))`. -/
theorem radial_corollary (hd : 1 ≤ d) {A₀ : L2 d} (hA₀ : A₀ ≠ 0) (hH : SpecAccess a b A₀)
    {A : ℝ → L2 d} (hA : IsMild a b r A₀ A) :
    (∀ δ > 0, Tendsto (fun t => (∫ k in Ioi (0 : ℝ) ∩ {k | δ ≤ |k - kstar a b|}, radP A t k) /
        ∫ k in Ioi (0 : ℝ), radP A t k) atTop (𝓝 0)) ∧
    ∀ g : ℝ → ℝ, ContinuousOn g (Ici 0) → (∀ k, 0 ≤ k → 0 ≤ g k) → Tendsto g atTop (𝓝 0) →
      g =ᵐ[volume.restrict (Ioi 0)] radP A 0 →
      (∀ t, 0 ≤ t → ∀ᵐ k ∂(volume.restrict (Ioi (0 : ℝ))),
          radP A t k = g k * Real.exp (2 * lamR a b r k * t)) ∧
      (∀ t, 0 ≤ t → ∃ k, 0 ≤ k ∧ IsMaxOn (fun k => g k * Real.exp (2 * lamR a b r k * t)) (Ici 0) k) ∧
      (∀ kt : ℝ → ℝ, (∀ᶠ t in atTop, 0 ≤ kt t ∧
          IsMaxOn (fun k => g k * Real.exp (2 * lamR a b r k * t)) (Ici 0) (kt t)) →
        Tendsto kt atTop (𝓝 (kstar a b))) ∧
      (0 < g (kstar a b) → ∀ t, 0 < t → ∀ k, 0 ≤ k →
        IsMaxOn (fun k => g k * Real.exp (2 * lamR a b r k * t)) (Ici 0) k →
        |k - kstar a b| ≤ √(Real.log ((⨆ j : Ici (0 : ℝ), g j) / g (kstar a b)) /
          (2 * b * kstar a b ^ 2 * t))) := by
  have hks := kstar_pos ha hb
  refine ⟨fun δ hδ => ?_, fun g hgc hg0 hgvan hgrep => ?_⟩
  · -- the ratio is `ν_t(E_δ)`
    obtain ⟨-, -, -, hlim, -⟩ := concentration r ha hb hA₀ hH hA hδ
    refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with t ht
    rw [nu, ← integral_radP hd A t]
    congr 1
    have hS : MeasurableSet {k : ℝ | δ ≤ |k - kstar a b|} :=
      measurableSet_le measurable_const (measurable_id.sub_const _).abs
    rw [← setIntegral_radial hd A t hS]
    rfl
  -- radial argmax
  have hq : Continuous fun k : ℝ => (k ^ 2 - kstar a b ^ 2) ^ 2 := by fun_prop
  have hvan : ∀ ε > 0, ∃ K, IsCompact K ∧ ∀ x ∈ Ici (0 : ℝ), x ∉ K → g x < ε := by
    intro ε hε
    obtain ⟨R, hR⟩ := eventually_atTop.1 (hgvan.eventually (gt_mem_nhds hε))
    refine ⟨Icc 0 R, isCompact_Icc, fun x hx hxK => hR x ?_⟩
    by_contra h; push_neg at h
    exact hxK ⟨hx, h.le⟩
  have hacc : ∀ ε > 0, ∃ x ∈ Ici (0 : ℝ), 0 < g x ∧ (x ^ 2 - kstar a b ^ 2) ^ 2 < ε := by
    intro ε hε
    obtain ⟨η, hη⟩ : ∃ η, η = min (kstar a b) (√ε / (3 * kstar a b)) := ⟨_, rfl⟩
    have hη0 : 0 < η := by rw [hη]; exact lt_min hks (by positivity)
    have hpos := hH η hη0
    have hS : MeasurableSet {k : ℝ | |k - kstar a b| < η} :=
      measurableSet_lt (measurable_id.sub_const _).abs measurable_const
    have e1 : ∫ ξ in {ξ : Rd | |‖ξ‖ - kstar a b| < η}, ‖FU A₀ ξ‖ ^ 2 =
        ∫ k in Ioi (0 : ℝ) ∩ {k | |k - kstar a b| < η}, g k := by
      have := setIntegral_radial hd A 0 hS
      rw [hA.2.1] at this
      rw [show {ξ : Rd | |‖ξ‖ - kstar a b| < η} = {ξ : Rd | ‖ξ‖ ∈ {k : ℝ | |k - kstar a b| < η}} from
        rfl, this]
      refine integral_congr_ae ?_
      have : ∀ᵐ k ∂(volume.restrict (Ioi (0 : ℝ) ∩ {k | |k - kstar a b| < η})), g k = radP A 0 k :=
        ae_restrict_of_ae_restrict_of_subset inter_subset_left hgrep
      filter_upwards [this] with k hk using hk.symm
    rw [e1] at hpos
    by_contra hne
    push_neg at hne
    have : ∫ k in Ioi (0 : ℝ) ∩ {k | |k - kstar a b| < η}, g k ≤ 0 := by
      refine setIntegral_nonpos (measurableSet_Ioi.inter hS) fun k hk => ?_
      by_contra hgk; push_neg at hgk
      have hk1 := hne k (mem_Ici.2 (le_of_lt hk.1)) hgk
      -- `|k − k⋆| < η` forces `(k² − k⋆²)² < ε`
      have hk2 : |k - kstar a b| < η := hk.2
      have hk3 : |k - kstar a b| < kstar a b := lt_of_lt_of_le hk2 (hη ▸ min_le_left _ _)
      have hk4 : |k - kstar a b| < √ε / (3 * kstar a b) := lt_of_lt_of_le hk2 (hη ▸ min_le_right _ _)
      have hk5 : |k + kstar a b| < 3 * kstar a b := by
        rw [abs_of_pos (by linarith [hk.1.out])]; linarith [(abs_lt.1 hk3).2]
      have h6 : (k ^ 2 - kstar a b ^ 2) ^ 2 = (|k - kstar a b| * |k + kstar a b|) ^ 2 := by
        rw [← abs_mul, sq_abs]; ring
      have h7 : |k - kstar a b| * |k + kstar a b| < √ε / (3 * kstar a b) * (3 * kstar a b) :=
        mul_lt_mul'' hk4 hk5 (abs_nonneg _) (abs_nonneg _)
      rw [div_mul_cancel₀ _ (by positivity)] at h7
      have h8 : (|k - kstar a b| * |k + kstar a b|) ^ 2 < ε := by
        calc (|k - kstar a b| * |k + kstar a b|) ^ 2 < (√ε) ^ 2 :=
              pow_lt_pow_left₀ h7 (by positivity) two_ne_zero
          _ = ε := Real.sq_sqrt hε.le
      linarith
    linarith
  obtain ⟨hex, hconv⟩ := argmax_abstract isClosed_Ici hgc hq.continuousOn hg0
    (fun x _ => sq_nonneg _) hvan hacc (c := 2 * b) (by positivity)
  refine ⟨fun t ht => ?_, fun t ht => ?_, fun kt hkt => ?_, fun hgk t ht k hk hmax => ?_⟩
  · filter_upwards [radial_law r ha hb hA ht, hgrep] with k h1 h2
    rw [h1, ← h2]
  · obtain ⟨k, hk, hmax⟩ := hex t ht
    exact ⟨k, hk, (isMaxOn_lamR_iff r g t k).2 hmax⟩
  · have hq0 := hconv kt (by
      filter_upwards [hkt] with t ht using ⟨ht.1, (isMaxOn_lamR_iff r g t (kt t)).1 ht.2⟩)
    have hsq : Tendsto (fun t => √((kt t ^ 2 - kstar a b ^ 2) ^ 2) / kstar a b) atTop (𝓝 0) := by
      have := (hq0.sqrt).div_const (kstar a b)
      rwa [Real.sqrt_zero, zero_div] at this
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun t => norm_nonneg _) ?_ hsq
    filter_upwards [hkt] with t ht
    rw [Real.norm_eq_abs]; exact abs_sub_le_of_sq ha hb ht.1
  · -- the explicit rate
    obtain ⟨M₀, hM₀⟩ := bdd_of_van isClosed_Ici hgc hvan
    have hbdd : BddAbove (range fun j : Ici (0 : ℝ) => g j) :=
      ⟨M₀, by rintro _ ⟨j, rfl⟩; exact hM₀ j j.2⟩
    have hfM : ∀ x ∈ Ici (0 : ℝ), g x ≤ ⨆ j : Ici (0 : ℝ), g j := fun x hx =>
      le_ciSup hbdd (⟨x, hx⟩ : Ici (0 : ℝ))
    have h1 := rate_abstract hfM (mem_Ici.2 hks.le) hgk (by ring) hk
      ((isMaxOn_lamR_iff r g t k).1 hmax)
    have h7 : (k - kstar a b) ^ 2 * kstar a b ^ 2 ≤ (k ^ 2 - kstar a b ^ 2) ^ 2 := by
      rw [show (k ^ 2 - kstar a b ^ 2) ^ 2 = (k - kstar a b) ^ 2 * (k + kstar a b) ^ 2 by ring]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hks.le (by linarith [hk]) 2)
        (sq_nonneg _)
    rw [← Real.sqrt_sq_eq_abs]
    refine Real.sqrt_le_sqrt ?_
    rw [le_div_iff₀ (by positivity)]
    have h8 := mul_le_mul_of_nonneg_left h7 (show (0 : ℝ) ≤ 2 * b * t by positivity)
    have e : (k - kstar a b) ^ 2 * (2 * b * kstar a b ^ 2 * t) =
        2 * b * t * ((k - kstar a b) ^ 2 * kstar a b ^ 2) := by ring
    rw [e]; linarith


/-! ### Failure without spectral access -/

/-- Existence of a maximiser of `f e^{−ctq}` when `f` is positive somewhere. -/
theorem exists_isMaxOn_weight {X : Type*} [TopologicalSpace X] {s : Set X} (hs : IsClosed s)
    {f q : X → ℝ} (hf : ContinuousOn f s) (hq : ContinuousOn q s) (hf0 : ∀ x ∈ s, 0 ≤ f x)
    (hq0 : ∀ x ∈ s, 0 ≤ q x) (hvan : ∀ ε > 0, ∃ K, IsCompact K ∧ ∀ x ∈ s, x ∉ K → f x < ε)
    {x₀ : X} (hx₀s : x₀ ∈ s) (hx₀ : 0 < f x₀) {c t : ℝ} (hc : 0 ≤ c) (ht : 0 ≤ t) :
    ∃ x ∈ s, IsMaxOn (fun x => f x * Real.exp (-(c * t * q x))) s x := by
  have hG : ContinuousOn (fun x => f x * Real.exp (-(c * t * q x))) s :=
    hf.mul (Real.continuous_exp.comp_continuousOn ((continuousOn_const.mul hq).neg))
  have hGx₀ : 0 < f x₀ * Real.exp (-(c * t * q x₀)) := mul_pos hx₀ (Real.exp_pos _)
  have hGle : ∀ x ∈ s, f x * Real.exp (-(c * t * q x)) ≤ f x := fun x hx => by
    have : Real.exp (-(c * t * q x)) ≤ 1 := Real.exp_le_one_iff.2 (by
      have := hq0 x hx; have : 0 ≤ c * t * q x := by positivity
      linarith)
    nlinarith [hf0 x hx, Real.exp_pos (-(c * t * q x))]
  obtain ⟨K, hK, hKf⟩ := hvan _ hGx₀
  have hx₀K : x₀ ∈ K := by
    by_contra h
    exact absurd (hKf x₀ hx₀s h) (not_lt.2 (hGle x₀ hx₀s))
  obtain ⟨x₁, ⟨hx₁s, -⟩, hx₁⟩ := (hK.inter_left hs).exists_isMaxOn ⟨x₀, hx₀s, hx₀K⟩
    (hG.mono inter_subset_left)
  refine ⟨x₁, hx₁s, fun y hy => ?_⟩
  by_cases hyK : y ∈ K
  · exact hx₁ ⟨hy, hyK⟩
  · exact (hGle y hy).trans ((hKf y hy hyK).le.trans (hx₁ ⟨hx₀s, hx₀K⟩))

theorem power_factor (ha : 0 < a) (hb : 0 < b) (f : Rd → ℝ) (t : ℝ) (ξ : Rd) :
    f ξ * Real.exp (2 * lam a b r ξ * t) =
      Real.exp (2 * mu a b r * t) * (f ξ * Real.exp (-(2 * b * t * qf a b ξ))) := by
  rw [lam_eq r ha hb, mul_left_comm, ← Real.exp_add]; congr 2; ring

theorem isMaxOn_power_iff (ha : 0 < a) (hb : 0 < b) (f : Rd → ℝ) (t : ℝ) (ξ : Rd) :
    IsMaxOn (fun ξ => f ξ * Real.exp (2 * lam a b r ξ * t)) univ ξ ↔
      IsMaxOn (fun ξ => f ξ * Real.exp (-(2 * b * t * qf a b ξ))) univ ξ := by
  simp only [isMaxOn_iff, mem_univ, true_implies, power_factor r ha hb f t]
  exact forall_congr' fun η => mul_le_mul_iff_of_pos_left (Real.exp_pos _)

include ha hb in
/-- **Proposition (failure without spectral access).** There is a nonzero Schwartz datum `A₀`
whose initial power has a continuous `C₀` representative `f` vanishing on `|ξ| ≤ k⋆ + 1`;
(H) fails, every `P(·,t) = f e^{2λt}` (`t ≥ 0`) has maximisers, all of them satisfy
`|ξ_t| > k⋆ + 1`, so no choice of maximisers converges radially to `k⋆`. -/
theorem counterexample (hd : 1 ≤ d) :
    ∃ φ : SchwartzMap Rd ℂ, toL2 φ ≠ 0 ∧ ∃ f : Rd → ℝ, Continuous f ∧ (∀ ξ, 0 ≤ f ξ) ∧
      Tendsto f (cocompact Rd) (𝓝 0) ∧ f =ᵐ[volume] (fun ξ => ‖FU (toL2 φ) ξ‖ ^ 2) ∧
      ¬ SpecAccess a b (toL2 φ) ∧
      (∀ t, 0 ≤ t → ∃ ξ, IsMaxOn (fun ξ => f ξ * Real.exp (2 * lam a b r ξ * t)) univ ξ) ∧
      (∀ t ξ, IsMaxOn (fun ξ => f ξ * Real.exp (2 * lam a b r ξ * t)) univ ξ →
        kstar a b + 1 < ‖ξ‖) ∧
      ∀ ξt : ℝ → Rd,
        (∀ᶠ t in atTop, IsMaxOn (fun ξ => f ξ * Real.exp (2 * lam a b r ξ * t)) univ (ξt t)) →
          ¬ Tendsto (fun t => ‖ξt t‖) atTop (𝓝 (kstar a b)) := by
  have hks := kstar_pos ha hb
  obtain ⟨c, hc⟩ : ∃ c : Rd, c = EuclideanSpace.single (⟨0, hd⟩ : Fin d) (kstar a b + 3) :=
    ⟨_, rfl⟩
  have hcn : ‖c‖ = kstar a b + 3 := by
    rw [hc, EuclideanSpace.norm_single, Real.norm_eq_abs, abs_of_pos (by linarith)]
  obtain ⟨β, hβ⟩ : ∃ β : ContDiffBump c, β = ⟨1 / 2, 1, by norm_num, by norm_num⟩ := ⟨_, rfl⟩
  have hβout : β.rOut = 1 := by rw [hβ]
  obtain ⟨g, hg⟩ : ∃ g : Rd → ℝ, g = ⇑β := ⟨_, rfl⟩
  have hg1 : g c = 1 := hg ▸ β.one_of_mem_closedBall (Metric.mem_closedBall_self β.rIn_pos.le)
  have hgc : ContDiff ℝ ∞ g := hg ▸ β.contDiff
  have hgs : HasCompactSupport g := hg ▸ β.hasCompactSupport
  have hgsupp : Function.support g = Metric.ball c 1 := by rw [hg, β.support_eq, hβout]
  have hψc : ContDiff ℝ ∞ (fun ξ => ((g ξ : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp hgc
  have hψs : HasCompactSupport (fun ξ => ((g ξ : ℝ) : ℂ)) := hgs.comp_left Complex.ofReal_zero
  obtain ⟨φ, hφ⟩ := exists_schwartz_FU _ hψc hψs
  -- `f = g²` vanishes on `|ξ| ≤ k⋆ + 2`
  have hfar : ∀ ξ : Rd, g ξ ≠ 0 → kstar a b + 2 < ‖ξ‖ := by
    intro ξ hξ
    have hmem : ξ ∈ Metric.ball c 1 := by
      have : ξ ∈ Function.support g := hξ
      rwa [hgsupp] at this
    rw [Metric.mem_ball, dist_eq_norm] at hmem
    have := norm_sub_norm_le c ξ
    rw [norm_sub_rev] at hmem
    linarith
  have hfc : Continuous fun ξ => g ξ ^ 2 := hgc.continuous.pow 2
  have hfs : HasCompactSupport fun ξ => g ξ ^ 2 :=
    hgs.comp_left (g := fun x : ℝ => x ^ 2) (by norm_num)
  have hfv : Tendsto (fun ξ => g ξ ^ 2) (cocompact Rd) (𝓝 0) := hfs.is_zero_at_infty
  have hne0 : toL2 φ ≠ 0 := by
    intro h0
    have h1 : (fun ξ => ((g ξ : ℝ) : ℂ)) =ᵐ[volume] fun _ => (0 : ℂ) := by
      filter_upwards [hφ.symm, Lp.coeFn_zero ℂ 2 (volume : Measure Rd)] with ξ h1 h2
      rw [h1, h0, map_zero, h2]; rfl
    have h2 := (Continuous.ae_eq_iff_eq volume (Complex.continuous_ofReal.comp hgc.continuous)
      continuous_const).1 h1
    have := congrFun h2 c
    simp [hg1] at this
  have hrep : (fun ξ => g ξ ^ 2) =ᵐ[volume] (fun ξ => ‖FU (toL2 φ) ξ‖ ^ 2) := by
    filter_upwards [hφ] with ξ h
    rw [h, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  refine ⟨φ, hne0, fun ξ => g ξ ^ 2, hfc, fun ξ => sq_nonneg _, hfv, hrep, ?_, ?_, ?_, ?_⟩
  · intro hH
    have hpos := hH 1 one_pos
    have hzero : ∫ ξ in {ξ : Rd | |‖ξ‖ - kstar a b| < 1}, ‖FU (toL2 φ) ξ‖ ^ 2 = 0 := by
      rw [← integral_congr_ae (ae_restrict_of_ae hrep)]
      refine setIntegral_eq_zero_of_forall_eq_zero fun ξ hξ => ?_
      have hξ' : ‖ξ‖ < kstar a b + 1 := by
        have h' : |‖ξ‖ - kstar a b| < 1 := hξ
        have := (abs_lt.1 h').2; linarith
      by_contra hne
      have : g ξ ≠ 0 := fun h => hne (by simp [h])
      linarith [hfar ξ this]
    linarith
  · intro t ht
    have hvan : ∀ ε > 0, ∃ K, IsCompact K ∧ ∀ x ∈ (univ : Set Rd), x ∉ K → g x ^ 2 < ε := by
      intro ε hε
      refine ⟨tsupport g, hgs, fun x _ hx => ?_⟩
      rw [image_eq_zero_of_notMem_tsupport hx]; simpa using hε
    have hq : Continuous (qf (d := d) a b) := by unfold qf; fun_prop
    obtain ⟨ξ, -, hξ⟩ := exists_isMaxOn_weight isClosed_univ (hgc.continuous.pow 2).continuousOn
      hq.continuousOn (fun x _ => sq_nonneg _) (fun x _ => qf_nonneg x) hvan (mem_univ c)
      (by rw [hg1]; norm_num) (c := 2 * b) (by positivity) ht
    exact ⟨ξ, (isMaxOn_power_iff r ha hb (fun ξ => g ξ ^ 2) t ξ).2 hξ⟩
  · intro t ξ hξ
    have h1 := hξ (mem_univ c)
    simp only [Set.mem_setOf_eq, hg1, one_pow, one_mul] at h1
    have h2 : 0 < g ξ ^ 2 * Real.exp (2 * lam a b r ξ * t) := lt_of_lt_of_le (Real.exp_pos _) h1
    have h3 : g ξ ≠ 0 := by
      intro h; rw [h] at h2; simp at h2
    linarith [hfar ξ h3]
  · intro ξt hξt hlim
    have hev := hlim.eventually (gt_mem_nhds (show kstar a b < kstar a b + 1 by linarith))
    obtain ⟨t, ht1, ht2⟩ := (hξt.and hev).exists
    have h1 := ht1 (mem_univ c)
    simp only [Set.mem_setOf_eq, hg1, one_pow, one_mul] at h1
    have h2 : 0 < g (ξt t) ^ 2 * Real.exp (2 * lam a b r (ξt t) * t) :=
      lt_of_lt_of_le (Real.exp_pos _) h1
    have h3 : g (ξt t) ≠ 0 := by
      intro h; rw [h] at h2; simp at h2
    linarith [hfar (ξt t) h3]

/-! ### The normalised spectral measure, and the remark on `μ = 0` -/

include ha hb in
/-- `Z(t) = ∫ P(ξ,t) dξ = ‖A(t)‖²` is finite and strictly positive. -/
theorem Z_pos {A₀ : L2 d} (hA₀ : A₀ ≠ 0) {A : ℝ → L2 d} (hA : IsMild a b r A₀ A) {t : ℝ}
    (ht : 0 ≤ t) : 0 < ∫ ξ, ‖FU (A t) ξ‖ ^ 2 := by
  rw [← norm_sq_L2, norm_FU]
  refine pow_pos (norm_pos_iff.2 fun h0 => hA₀ ?_) 2
  have h1 := FU_mild r ha hb hA ht
  rw [h0, map_zero] at h1
  apply FU.injective
  rw [map_zero]
  apply Lp.ext
  filter_upwards [h1, Lp.coeFn_zero ℂ 2 (volume : Measure Rd)] with ξ e1 e2
  have : (Real.exp (lam a b r ξ * t) : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos _).ne'
  rw [e2] at e1 ⊢
  simp only [Pi.zero_apply] at e1 ⊢
  exact (mul_eq_zero.1 e1.symm).resolve_left this

/-- `ν_t` as a measure: the probability measure with density `P(·,t)/Z(t)`. -/
def nuM (A : ℝ → L2 d) (t : ℝ) : Measure Rd :=
  volume.withDensity fun ξ => ENNReal.ofReal (‖FU (A t) ξ‖ ^ 2 / ∫ ζ, ‖FU (A t) ζ‖ ^ 2)

include ha hb in
/-- `ν_t` is a probability measure with `ν_t(E) = ∫_E P / Z`. -/
theorem nuM_prob {A₀ : L2 d} (hA₀ : A₀ ≠ 0) {A : ℝ → L2 d} (hA : IsMild a b r A₀ A) {t : ℝ}
    (ht : 0 ≤ t) :
    IsProbabilityMeasure (nuM A t) ∧ ∀ E, MeasurableSet E → (nuM A t E).toReal = nu A t E := by
  have hZ := Z_pos r ha hb hA₀ hA ht
  have hint : Integrable fun ξ => ‖FU (A t) ξ‖ ^ 2 / ∫ ζ, ‖FU (A t) ζ‖ ^ 2 :=
    (integrable_norm_sq_L2 _).div_const _
  have hnn : 0 ≤ᵐ[volume] fun ξ => ‖FU (A t) ξ‖ ^ 2 / ∫ ζ, ‖FU (A t) ζ‖ ^ 2 :=
    Eventually.of_forall fun ξ => div_nonneg (by positivity) hZ.le
  have key : ∀ E, MeasurableSet E → nuM A t E =
      ENNReal.ofReal (∫ ξ in E, ‖FU (A t) ξ‖ ^ 2 / ∫ ζ, ‖FU (A t) ζ‖ ^ 2) := by
    intro E hE
    rw [nuM, withDensity_apply _ hE, ofReal_integral_eq_lintegral_ofReal hint.integrableOn
      (ae_restrict_of_ae hnn)]
  refine ⟨⟨?_⟩, fun E hE => ?_⟩
  · rw [key univ MeasurableSet.univ, Measure.restrict_univ, integral_div, div_self hZ.ne',
      ENNReal.ofReal_one]
  · rw [key E hE, ENNReal.toReal_ofReal (setIntegral_nonneg hE fun ξ _ => div_nonneg
      (by positivity) hZ.le), integral_div, nu]

include ha hb in
/-- Remark (normalised does not mean persistent amplitude): if `μ = 0` then `‖A(t)‖ → 0`, while
`ν_t` still concentrates under (H). -/
theorem decay_of_mu_zero (hd : 1 ≤ d) (hμ : mu a b r = 0) {A₀ : L2 d} {A : ℝ → L2 d}
    (hA : IsMild a b r A₀ A) : Tendsto (fun t => ‖A t‖) atTop (𝓝 0) := by
  haveI := nontrivial_Rd hd
  have hks := kstar_pos ha hb
  have hsq : Tendsto (fun t => ‖A t‖ ^ 2) atTop (𝓝 0) := by
    have e : ∀ t, 0 ≤ t → ‖A t‖ ^ 2 = ∫ ξ, ‖FU A₀ ξ‖ ^ 2 * Real.exp (2 * lam a b r ξ * t) := by
      intro t ht
      rw [← norm_FU, norm_sq_L2]
      exact integral_congr_ae (power_mild r ha hb hA ht)
    have hlim : Tendsto (fun t => ∫ ξ, ‖FU A₀ ξ‖ ^ 2 * Real.exp (2 * lam a b r ξ * t)) atTop
        (𝓝 (∫ _ξ : Rd, (0 : ℝ))) := by
      refine tendsto_integral_filter_of_dominated_convergence (fun ξ => ‖FU A₀ ξ‖ ^ 2) ?_ ?_
        (integrable_norm_sq_L2 _) ?_
      · exact Eventually.of_forall fun t => ((Lp.aestronglyMeasurable _).norm.pow 2).mul
          (continuous_weight r t).aestronglyMeasurable
      · filter_upwards [eventually_ge_atTop 0] with t ht
        refine Eventually.of_forall fun ξ => ?_
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        have : Real.exp (2 * lam a b r ξ * t) ≤ 1 := Real.exp_le_one_iff.2 (by
          have := lam_le r ha hb ξ; rw [hμ] at this; nlinarith)
        nlinarith [sq_nonneg ‖FU A₀ ξ‖]
      · have hnull : (volume : Measure Rd) (Metric.sphere 0 (kstar a b)) = 0 :=
          Measure.addHaar_sphere _ _ _
        have hae : ∀ᵐ ξ ∂(volume : Measure Rd), ξ ∉ Metric.sphere 0 (kstar a b) :=
          measure_eq_zero_iff_ae_notMem.1 hnull
        filter_upwards [hae] with ξ hξ
        have hq : 0 < qf a b ξ := by
          rcases (qf_nonneg (a := a) (b := b) ξ).lt_or_eq with h | h
          · exact h
          · exfalso; apply hξ
            rw [mem_sphere_zero_iff_norm]
            rw [qf_eq] at h
            rcases mul_eq_zero.1 h.symm with h1 | h1
            · nlinarith [sq_nonneg (‖ξ‖ - kstar a b)]
            · nlinarith [norm_nonneg ξ]
        have hl : lam a b r ξ < 0 := by rw [lam_eq r ha hb, hμ]; nlinarith
        have : Tendsto (fun t => Real.exp (2 * lam a b r ξ * t)) atTop (𝓝 0) :=
          Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by linarith))
        simpa using this.const_mul (‖FU A₀ ξ‖ ^ 2)
    rw [integral_zero] at hlim
    refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with t ht using (e t ht).symm
  have := hsq.sqrt
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using this

/-! ### E62: the continuous-spectrum fraction -/

/-- `η_ℬ(A) = ∫_ℬ |Â|² / ∫_{ℝ^d} |Â|²`. -/
def etaC (A : L2 d) (B : Set Rd) : ℝ := (∫ ξ in B, ‖FU A ξ‖ ^ 2) / ∫ ξ, ‖FU A ξ‖ ^ 2

/-- **Proposition (E62, continuous spectrum).** For nonzero `A ∈ L²(ℝ^d)` and measurable
`ℬ ⊆ ℝ^d`: `0 ≤ η_ℬ ≤ 1`, `η_ℬ = 0 ⇔ Â = 0` a.e. on `ℬ`, `η_ℬ = 1 ⇔ Â = 0` a.e. off `ℬ`. -/
theorem e62_continuous {A : L2 d} (hA : A ≠ 0) {B : Set Rd} (hB : MeasurableSet B) :
    0 < ∫ ξ, ‖FU A ξ‖ ^ 2 ∧ 0 ≤ etaC A B ∧ etaC A B ≤ 1 ∧
      (etaC A B = 0 ↔ ∀ᵐ ξ ∂volume, ξ ∈ B → FU A ξ = 0) ∧
      (etaC A B = 1 ↔ ∀ᵐ ξ ∂volume, ξ ∉ B → FU A ξ = 0) := by
  have hi := integrable_norm_sq_L2 (FU A)
  have hZ : 0 < ∫ ξ, ‖FU A ξ‖ ^ 2 := by
    rw [← norm_sq_L2, norm_FU]; exact pow_pos (norm_pos_iff.2 hA) 2
  have hnn : ∀ S : Set Rd, 0 ≤ᵐ[volume.restrict S] fun ξ => ‖FU A ξ‖ ^ 2 :=
    fun S => Eventually.of_forall fun ξ => by positivity
  have hzero : ∀ S : Set Rd, MeasurableSet S →
      ((∫ ξ in S, ‖FU A ξ‖ ^ 2) = 0 ↔ ∀ᵐ ξ ∂volume, ξ ∈ S → FU A ξ = 0) := by
    intro S hS
    rw [setIntegral_eq_zero_iff_of_nonneg_ae (hnn S) hi.integrableOn, EventuallyEq,
      ae_restrict_iff' hS]
    refine eventually_congr (Eventually.of_forall fun ξ => ?_)
    simp only [Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff,
      norm_eq_zero]
  have hsum := integral_add_compl hB hi
  refine ⟨hZ, div_nonneg (setIntegral_nonneg hB fun ξ _ => by positivity) hZ.le,
    (div_le_one hZ).2 (setIntegral_le_integral hi (Eventually.of_forall fun ξ => by positivity)),
    ?_, ?_⟩
  · rw [etaC, div_eq_zero_iff, or_iff_left hZ.ne', hzero B hB]
  · rw [etaC, div_eq_one_iff_eq hZ.ne']
    have : (∫ ξ in B, ‖FU A ξ‖ ^ 2) = ∫ ξ, ‖FU A ξ‖ ^ 2 ↔ (∫ ξ in Bᶜ, ‖FU A ξ‖ ^ 2) = 0 := by
      constructor <;> intro h <;> linarith
    rw [this, hzero Bᶜ hB.compl]
    rfl

/-- Remark (zero-width shell): the exact sphere `|ξ| = k⋆` carries no `L²` energy, so its
concentration fraction vanishes for every `L²` field. -/
theorem etaC_sphere (hd : 1 ≤ d) (A : L2 d) (k : ℝ) : etaC A (Metric.sphere 0 k) = 0 := by
  haveI := nontrivial_Rd hd
  rw [etaC, Measure.restrict_eq_zero.2 (Measure.addHaar_sphere _ _ _), integral_zero_measure,
    zero_div]

end SpectralConc
end ReyesMath
