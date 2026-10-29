import MathProofs.SpectralConcentration

/-!
# Fourier multipliers on `L²(ℝ^d)`: norms, Sobolev weights and unbounded realisations

Shared infrastructure for E58, E61 and M3/E57, built on the unitary Fourier transform
`Sobolev.FU` (`û(ξ) = (2π)^{-d/2} ∫ e^{-ix·ξ} u(x) dx`, extended by Plancherel).

* `FMult.fmul m`: the bounded multiplier `𝓕⁻¹ M_m 𝓕`, with `‖𝓕⁻¹ M_m 𝓕‖ = ‖M_m‖`
  (`FMult.opNorm_fmul`) and, for continuous bounded `m`, `‖M_m‖ ≥ |m(ξ₀)|` for every `ξ₀`
  (`FMult.le_opNorm_mulL2`); hence `‖M_m‖ = sup |m|` (`FMult.opNorm_mulL2_eq`).
* `FMult.ind U`: the indicator `1_U ∈ L²` of a measurable set of finite measure.
* Sobolev spaces by Fourier weights: `u ∈ H^{2k}` iff `(1 + |ξ|²)^k û ∈ L²` (`FMult.InH k`,
  the submodule `FMult.Hdom k`).
* Unbounded Fourier multipliers with domain `H^{2k}` (`FMult.pmulOp`, a `LinearPMap`) and the
  resolvent set / spectrum of a partially defined operator (`FMult.IsResolvent`,
  `FMult.uspectrum`): `z` is resolvent iff `z − T : D(T) → L²` is bijective with bounded inverse.
-/

open Filter Topology Complex InnerProductSpace MeasureTheory Set
open scoped ContDiff FourierTransform ComplexConjugate ENNReal

noncomputable section

namespace ReyesMath
namespace FMult

open Sobolev SpectralConc

variable {d : ℕ}

local notation "Rd" => EuclideanSpace ℝ (Fin d)

/-! ### Bounded multipliers conjugated by the Fourier transform -/

/-- The bounded Fourier multiplier `𝓕⁻¹ M_m 𝓕` on `L²(ℝ^d)`. -/
def fmul (m : Rd → ℂ) (hm : AEStronglyMeasurable m volume) {C : ℝ} (hC : ∀ ξ, ‖m ξ‖ ≤ C) :
    L2 d →L[ℂ] L2 d :=
  (FU (d := d)).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((mulL2 m hm hC).comp (FU (d := d)).toContinuousLinearEquiv.toContinuousLinearMap)

theorem FU_fmul (m : Rd → ℂ) (hm : AEStronglyMeasurable m volume) {C : ℝ}
    (hC : ∀ ξ, ‖m ξ‖ ≤ C) (f : L2 d) : FU (fmul m hm hC f) = mulL2 m hm hC (FU f) := by
  simp [fmul]

theorem coeFn_FU_fmul (m : Rd → ℂ) (hm : AEStronglyMeasurable m volume) {C : ℝ}
    (hC : ∀ ξ, ‖m ξ‖ ≤ C) (f : L2 d) :
    (FU (fmul m hm hC f) : Rd → ℂ) =ᵐ[volume] fun ξ => m ξ * FU f ξ := by
  rw [FU_fmul]; exact coeFn_mulL2 _ _ _

theorem norm_fmul_apply (m : Rd → ℂ) (hm : AEStronglyMeasurable m volume) {C : ℝ}
    (hC : ∀ ξ, ‖m ξ‖ ≤ C) (f : L2 d) : ‖fmul m hm hC f‖ = ‖mulL2 m hm hC (FU f)‖ := by
  rw [← norm_FU, FU_fmul]

/-- Conjugation by the unitary Fourier transform preserves the operator norm. -/
theorem opNorm_fmul (m : Rd → ℂ) (hm : AEStronglyMeasurable m volume) {C : ℝ}
    (hC : ∀ ξ, ‖m ξ‖ ≤ C) : ‖fmul m hm hC‖ = ‖mulL2 m hm hC‖ := by
  apply le_antisymm
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun f => ?_
    rw [norm_fmul_apply, ← norm_FU f]; exact (mulL2 m hm hC).le_opNorm _
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun g => ?_
    have := (fmul m hm hC).le_opNorm (FU.symm g)
    rwa [norm_fmul_apply, LinearIsometryEquiv.apply_symm_apply,
      LinearIsometryEquiv.norm_map] at this

theorem opNorm_mulL2_le (m : Rd → ℂ) (hm : AEStronglyMeasurable m volume) {C : ℝ}
    (hC : ∀ ξ, ‖m ξ‖ ≤ C) : ‖mulL2 m hm hC‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ ((norm_nonneg _).trans (hC 0)) _

/-! ### Indicator test functions -/

/-- The indicator `1_U` as an element of `L²` (`U` measurable, of finite measure). -/
def ind (U : Set Rd) (hU : MeasurableSet U) (hfin : volume U ≠ ⊤) : L2 d :=
  indicatorConstLp 2 hU hfin (1 : ℂ)

theorem coeFn_ind (U : Set Rd) (hU : MeasurableSet U) (hfin : volume U ≠ ⊤) :
    (ind U hU hfin : Rd → ℂ) =ᵐ[volume] U.indicator fun _ => (1 : ℂ) :=
  indicatorConstLp_coeFn

theorem norm_ind_sq (U : Set Rd) (hU : MeasurableSet U) (hfin : volume U ≠ ⊤) :
    ‖ind U hU hfin‖ ^ 2 = (volume U).toReal := by
  rw [SpectralConc.norm_sq_L2]
  calc ∫ ξ, ‖(ind U hU hfin : Rd → ℂ) ξ‖ ^ 2 = ∫ ξ, U.indicator (fun _ => (1 : ℝ)) ξ := by
        refine integral_congr_ae ?_
        filter_upwards [coeFn_ind U hU hfin] with ξ hξ
        rw [hξ]
        by_cases h : ξ ∈ U <;> simp [h]
    _ = (volume U).toReal := by
        rw [integral_indicator_const _ hU, smul_eq_mul, mul_one, Measure.real]

/-- `‖M_m 1_U‖² = ∫_U |m|²`. -/
theorem norm_mulL2_ind_sq (m : Rd → ℂ) (hm : AEStronglyMeasurable m volume) {C : ℝ}
    (hC : ∀ ξ, ‖m ξ‖ ≤ C) (U : Set Rd) (hU : MeasurableSet U) (hfin : volume U ≠ ⊤) :
    ‖mulL2 m hm hC (ind U hU hfin)‖ ^ 2 = ∫ ξ in U, ‖m ξ‖ ^ 2 := by
  rw [SpectralConc.norm_sq_L2, ← integral_indicator hU]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_mulL2 hm hC (ind U hU hfin), coeFn_ind U hU hfin] with ξ h1 h2
  rw [h1, h2]
  by_cases h : ξ ∈ U <;> simp [h]

/-- For a continuous bounded symbol, `‖M_m‖ ≥ |m(ξ₀)|` at every point (test functions
concentrated in small balls around `ξ₀`). -/
theorem le_opNorm_mulL2 {m : Rd → ℂ} (hmc : Continuous m) {C : ℝ} (hC : ∀ ξ, ‖m ξ‖ ≤ C)
    (ξ₀ : Rd) : ‖m ξ₀‖ ≤ ‖mulL2 m hmc.aestronglyMeasurable hC‖ := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  by_cases hsmall : ‖m ξ₀‖ - ε ≤ 0
  · linarith [norm_nonneg (mulL2 m hmc.aestronglyMeasurable hC)]
  push_neg at hsmall
  obtain ⟨ρ, hρ, hball⟩ := Metric.continuous_iff.1 hmc ξ₀ ε hε
  have hU : MeasurableSet (Metric.ball ξ₀ ρ) := measurableSet_ball
  have hfin : volume (Metric.ball ξ₀ ρ) ≠ ⊤ := measure_ball_lt_top.ne
  have hpos : 0 < (volume (Metric.ball ξ₀ ρ)).toReal :=
    ENNReal.toReal_pos (Metric.measure_ball_pos volume ξ₀ hρ).ne' hfin
  set M := mulL2 m hmc.aestronglyMeasurable hC
  set f := ind (Metric.ball ξ₀ ρ) hU hfin
  have hint : IntegrableOn (fun ξ => ‖m ξ‖ ^ 2) (Metric.ball ξ₀ ρ) :=
    ((hmc.norm.pow 2).continuousOn.integrableOn_compact (isCompact_closedBall ξ₀ ρ)).mono_set
      Metric.ball_subset_closedBall
  have hlow : (‖m ξ₀‖ - ε) ^ 2 * (volume (Metric.ball ξ₀ ρ)).toReal ≤ ‖M f‖ ^ 2 := by
    rw [norm_mulL2_ind_sq]
    have := setIntegral_ge_of_const_le (c := (‖m ξ₀‖ - ε) ^ 2) hU hfin (fun ξ hξ => by
      have h1 := hball ξ hξ
      rw [dist_eq_norm] at h1
      have h2 : ‖m ξ₀‖ - ε ≤ ‖m ξ‖ := by
        have := norm_sub_norm_le (m ξ₀) (m ξ)
        rw [norm_sub_rev] at this
        linarith
      exact pow_le_pow_left₀ hsmall.le h2 2) hint
    simpa [Measure.real] using this
  have hup : ‖M f‖ ^ 2 ≤ ‖M‖ ^ 2 * (volume (Metric.ball ξ₀ ρ)).toReal := by
    rw [← norm_ind_sq _ hU hfin, ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (M.le_opNorm f) 2
  have h3 : (‖m ξ₀‖ - ε) ^ 2 ≤ ‖M‖ ^ 2 := le_of_mul_le_mul_right (hlow.trans hup) hpos
  have h4 := (pow_le_pow_iff_left₀ hsmall.le (norm_nonneg _) two_ne_zero).1 h3
  linarith

/-- For a continuous symbol with `|m| ≤ C` and `sup |m| = C`, `‖M_m‖ = C`. -/
theorem opNorm_mulL2_eq {m : Rd → ℂ} (hmc : Continuous m) {C : ℝ} (hC : ∀ ξ, ‖m ξ‖ ≤ C)
    (hsup : ∀ ε > 0, ∃ ξ, C - ε < ‖m ξ‖) : ‖mulL2 m hmc.aestronglyMeasurable hC‖ = C := by
  refine le_antisymm (opNorm_mulL2_le m _ hC) (le_of_forall_pos_le_add fun ε hε => ?_)
  obtain ⟨ξ, hξ⟩ := hsup ε hε
  linarith [le_opNorm_mulL2 hmc hC ξ]

/-- The norm of a Fourier multiplier with continuous symbol attaining its bound. -/
theorem opNorm_fmul_eq_of_attained {m : Rd → ℂ} (hmc : Continuous m) {C : ℝ}
    (hC : ∀ ξ, ‖m ξ‖ ≤ C) {ξ₀ : Rd} (h₀ : ‖m ξ₀‖ = C) :
    ‖fmul m hmc.aestronglyMeasurable hC‖ = C := by
  rw [opNorm_fmul]
  exact opNorm_mulL2_eq hmc hC fun ε hε => ⟨ξ₀, by linarith⟩

/-! ### Sobolev spaces through Fourier weights -/

/-- The Bessel weight `⟨ξ⟩² = 1 + |ξ|²`. -/
def bw (ξ : Rd) : ℝ := 1 + ‖ξ‖ ^ 2

theorem one_le_bw (ξ : Rd) : 1 ≤ bw ξ := by
  have := sq_nonneg ‖ξ‖; unfold bw; linarith

theorem bw_pos (ξ : Rd) : 0 < bw ξ := lt_of_lt_of_le one_pos (one_le_bw ξ)

theorem continuous_bw : Continuous (bw (d := d)) := by unfold bw; fun_prop

/-- `u ∈ H^{2k}(ℝ^d)`: `(1 + |ξ|²)^k û ∈ L²` (the Bessel-potential definition). -/
def InH (k : ℕ) (u : L2 d) : Prop :=
  MemLp (fun ξ => ((bw ξ ^ k : ℝ) : ℂ) * FU u ξ) 2 volume

theorem aestronglyMeasurable_bw_mul (k : ℕ) (u : L2 d) :
    AEStronglyMeasurable (fun ξ => ((bw ξ ^ k : ℝ) : ℂ) * FU u ξ) volume :=
  (Complex.continuous_ofReal.comp (continuous_bw.pow k)).aestronglyMeasurable.mul
    (Lp.aestronglyMeasurable _)

/-- A symbol of order `2k`, applied to an `H^{2k}` function, gives an `L²` function. -/
theorem memLp_mul_of_inH {k : ℕ} {m : Rd → ℂ} (hm : AEStronglyMeasurable m volume) {C : ℝ}
    (hb : ∀ ξ, ‖m ξ‖ ≤ C * bw ξ ^ k) {u : L2 d} (hu : InH k u) :
    MemLp (fun ξ => m ξ * FU u ξ) 2 volume := by
  refine hu.of_le_mul (c := C) (hm.mul (Lp.aestronglyMeasurable _))
    (Eventually.of_forall fun ξ => ?_)
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (bw_pos ξ).le k), ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hb ξ) (norm_nonneg _)

theorem inH_of_memLp {k : ℕ} {u : L2 d}
    (h : MemLp (fun ξ => ((bw ξ ^ k : ℝ) : ℂ) * FU u ξ) 2 volume) : InH k u := h

theorem inH_add {k : ℕ} {u v : L2 d} (hu : InH k u) (hv : InH k v) : InH k (u + v) := by
  have h : (FU (u + v) : Rd → ℂ) =ᵐ[volume] fun ξ => FU u ξ + FU v ξ := by
    rw [map_add]; exact Lp.coeFn_add _ _
  refine (hu.add hv).ae_eq ?_
  filter_upwards [h] with ξ h1
  simp only [Pi.add_apply, h1, mul_add]

theorem inH_smul {k : ℕ} {u : L2 d} (hu : InH k u) (c : ℂ) : InH k (c • u) := by
  refine (hu.const_mul c).ae_eq ?_
  filter_upwards [Lp.coeFn_smul c (FU u)] with ξ h1
  rw [map_smul, h1, Pi.smul_apply, smul_eq_mul]; ring

theorem inH_zero (k : ℕ) : InH k (0 : L2 d) := by
  refine (MemLp.zero (μ := (volume : Measure Rd)) (p := 2) (ε := ℂ)).ae_eq ?_
  filter_upwards [Lp.coeFn_zero ℂ 2 (volume : Measure Rd)] with ξ h1
  rw [map_zero, h1]; simp

theorem inH_mono {j k : ℕ} (hjk : j ≤ k) {u : L2 d} (hu : InH k u) : InH j u := by
  refine hu.of_le (aestronglyMeasurable_bw_mul j u) (Eventually.of_forall fun ξ => ?_)
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg (pow_nonneg (bw_pos ξ).le j), abs_of_nonneg (pow_nonneg (bw_pos ξ).le k)]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (one_le_bw ξ) hjk) (norm_nonneg _)

/-- `H^{2k}` as a submodule of `L²`. -/
def Hdom (k : ℕ) : Submodule ℂ (L2 d) where
  carrier := {u | InH k u}
  add_mem' hu hv := inH_add hu hv
  zero_mem' := inH_zero k
  smul_mem' c _ hu := inH_smul hu c

theorem mem_Hdom {k : ℕ} {u : L2 d} : u ∈ Hdom (d := d) k ↔ InH k u := Iff.rfl

/-- Functions whose Fourier transform vanishes off a bounded set lie in every `H^{2k}`. -/
theorem inH_of_bounded {k : ℕ} {u : L2 d} {R : ℝ}
    (h : ∀ᵐ ξ ∂volume, R < ‖ξ‖ → FU u ξ = 0) : InH k u := by
  refine ((Lp.memLp (FU u)).const_mul (((1 + R ^ 2) ^ k : ℝ) : ℂ)).of_le
    (aestronglyMeasurable_bw_mul k u) ?_
  filter_upwards [h] with ξ hξ
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (bw_pos ξ).le k), abs_of_nonneg (by positivity)]
  by_cases hR : R < ‖ξ‖
  · rw [hξ hR, norm_zero, mul_zero, mul_zero]
  · push_neg at hR
    refine mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (bw_pos ξ).le ?_ k) (norm_nonneg _)
    have : ‖ξ‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hR 2
    unfold bw; linarith

/-! ### Unbounded multipliers with domain `H^{2k}` -/

/-- The realisation of a symbol of order `2k` as an operator on `L²` with domain `H^{2k}`:
`u ↦ 𝓕⁻¹(m û)`. -/
def pmulOp (k : ℕ) (m : Rd → ℂ) (hm : AEStronglyMeasurable m volume) {C : ℝ}
    (hb : ∀ ξ, ‖m ξ‖ ≤ C * bw ξ ^ k) : L2 d →ₗ.[ℂ] L2 d where
  domain := Hdom k
  toFun :=
    { toFun := fun u => FU.symm ((memLp_mul_of_inH hm hb u.2).toLp _)
      map_add' := fun u v => by
        rw [← map_add]; congr 1
        apply Lp.ext
        filter_upwards [(memLp_mul_of_inH hm hb (u + v).2).coeFn_toLp,
          (memLp_mul_of_inH hm hb u.2).coeFn_toLp, (memLp_mul_of_inH hm hb v.2).coeFn_toLp,
          Lp.coeFn_add ((memLp_mul_of_inH hm hb u.2).toLp _)
            ((memLp_mul_of_inH hm hb v.2).toLp _),
          Lp.coeFn_add (FU (u : L2 d)) (FU (v : L2 d))] with ξ h1 h2 h3 h4 h5
        rw [h1, h4, Pi.add_apply, h2, h3, Submodule.coe_add, map_add, h5, Pi.add_apply, mul_add]
      map_smul' := fun c u => by
        rw [RingHom.id_apply, ← map_smul]; congr 1
        apply Lp.ext
        filter_upwards [(memLp_mul_of_inH hm hb (c • u).2).coeFn_toLp,
          (memLp_mul_of_inH hm hb u.2).coeFn_toLp,
          Lp.coeFn_smul c ((memLp_mul_of_inH hm hb u.2).toLp _),
          Lp.coeFn_smul c (FU (u : L2 d))] with ξ h1 h2 h3 h4
        rw [h1, h3, Pi.smul_apply, h2, Submodule.coe_smul, map_smul, h4, Pi.smul_apply,
          smul_eq_mul, smul_eq_mul]; ring }

theorem FU_pmulOp (k : ℕ) (m : Rd → ℂ) (hm : AEStronglyMeasurable m volume) {C : ℝ}
    (hb : ∀ ξ, ‖m ξ‖ ≤ C * bw ξ ^ k) (u : (pmulOp k m hm hb).domain) :
    (FU (pmulOp k m hm hb u) : Rd → ℂ) =ᵐ[volume] fun ξ => m ξ * FU (u : L2 d) ξ := by
  change (FU (FU.symm ((memLp_mul_of_inH hm hb u.2).toLp _)) : Rd → ℂ) =ᵐ[volume] _
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact (memLp_mul_of_inH hm hb u.2).coeFn_toLp

theorem pmulOp_domain (k : ℕ) (m : Rd → ℂ) (hm : AEStronglyMeasurable m volume) {C : ℝ}
    (hb : ∀ ξ, ‖m ξ‖ ≤ C * bw ξ ^ k) : (pmulOp k m hm hb).domain = Hdom k := rfl

/-! ### Resolvent set and spectrum of a partially defined operator -/

section Spectrum

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- `z` lies in the resolvent set of `T` when `z − T : D(T) → E` is bijective with a bounded
inverse `R`: `R f ∈ D(T)`, `(z − T) R f = f` and `R (z − T) u = u`. -/
def IsResolvent (T : E →ₗ.[ℂ] E) (z : ℂ) : Prop :=
  ∃ R : E →L[ℂ] E, ∃ hR : ∀ f, R f ∈ T.domain,
    (∀ f, z • R f - T ⟨R f, hR f⟩ = f) ∧ ∀ u : T.domain, R (z • (u : E) - T u) = u

/-- The spectrum of a partially defined operator. -/
def uspectrum (T : E →ₗ.[ℂ] E) : Set ℂ := {z | ¬ IsResolvent T z}

/-- Approximate eigenvectors exclude the resolvent set (Weyl criterion, easy direction). -/
theorem mem_uspectrum_of_approx {T : E →ₗ.[ℂ] E} {z : ℂ}
    (h : ∀ ε > 0, ∃ u : T.domain, (u : E) ≠ 0 ∧ ‖z • (u : E) - T u‖ ≤ ε * ‖(u : E)‖) :
    z ∈ uspectrum T := by
  rintro ⟨R, hR, h1, h2⟩
  obtain ⟨u, hu0, hu⟩ := h (1 / (2 * (‖R‖ + 1))) (by positivity)
  have hpos : 0 < ‖(u : E)‖ := norm_pos_iff.2 hu0
  have : ‖(u : E)‖ ≤ ‖R‖ * (1 / (2 * (‖R‖ + 1)) * ‖(u : E)‖) := by
    calc ‖(u : E)‖ = ‖R (z • (u : E) - T u)‖ := by rw [h2 u]
      _ ≤ ‖R‖ * ‖z • (u : E) - T u‖ := R.le_opNorm _
      _ ≤ ‖R‖ * (1 / (2 * (‖R‖ + 1)) * ‖(u : E)‖) :=
          mul_le_mul_of_nonneg_left hu (norm_nonneg _)
  have hR0 := norm_nonneg R
  have h3 : ‖R‖ * (1 / (2 * (‖R‖ + 1))) < 1 := by
    rw [mul_one_div, div_lt_one (by positivity)]; linarith
  nlinarith

end Spectrum

end FMult
end ReyesMath
