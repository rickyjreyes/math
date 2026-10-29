import Mathlib

/-!
# Fourier analysis on the flat torus, the dominant-annulus projection (E59) and the discrete
spectral energy fraction (E62)

Formalization of `papers/e59-dominant-annulus-projection/main.tex` and of the discrete part of
`papers/spectral-energy-concentration-e62/main.tex`.

* The flat torus `𝕋_L^d = (ℝ/Lℤ)^d` (`TorusL2.Tor`), its normalised measure `|𝕋|⁻¹ dx`
  (`TorusL2.μ`, `TorusL2.volume_eq_smul_μ`), the Fourier modes `e_n` (`TorusL2.emode`,
  `TorusL2.emode_two_pi`: `e_k(x) = e^{ik·x}` on `(ℝ/2πℤ)^d`) and the Fourier Hilbert basis of
  `L²(𝕋_L^d)` (`TorusL2.basis`), obtained by transporting Mathlib's basis on `(ℝ/ℤ)^d` along the
  rescaling `t ↦ Lt`. Coefficients `Â_n = |𝕋|⁻¹ ∫ A ē_n` (`TorusL2.coef`, `TorusL2.coef_eq_volume`),
  Parseval (`TorusL2.hasSum_inner`, `TorusL2.hasSum_sq`, `TorusL2.integral_norm_sq_volume`),
  the `L²`-convergent Fourier series (`TorusL2.hasSum_series`) and uniqueness of coefficients
  (`TorusL2.ext_coef`).
* Bounded Fourier multipliers `Q` with `\widehat{QA}_k = w(k) Â_k` (`TorusL2.mult`): composition,
  adjoint, and the smooth-multiplier remark `Q² = Q ⇔ w(k) ∈ {0,1}` (`TorusL2.mult_idem_iff_mem`).
* E59 (Theorem): for the fixed annulus `𝒜⋆ = {k : ||k| − k⋆| ≤ Δk}` (`TorusL2.annulus`) the
  projection `P_{k⋆} A = Σ_{k∈𝒜⋆} Â_k e^{ik·x}` (`TorusL2.Pk`) is bounded with `P² = P`, `P* = P`,
  `‖PA‖ ≤ ‖A‖`, is the orthogonal projection onto `ℋ_{𝒜⋆}` (its range), satisfies
  `‖A‖² = ‖PA‖² + ‖(I − P)A‖²`, gives the unique best approximation, and `‖P‖ = 1` (`𝒜⋆ ≠ ∅`),
  `P = 0` (`𝒜⋆ = ∅`): `TorusL2.e59`; the spectral-fraction section `TorusL2.e59_fraction`; the
  discrete FFT identity `TorusL2.fft_projector`; the annulus-convention remark
  `TorusL2.zero_mem_oneSided_not_mem_annulus`. Everything is proved for an arbitrary mask
  `S ⊆ ℤ^d` (`TorusL2.P`, `TorusL2.H`).
* E62 (Theorem, discrete): `TorusL2.e62` (well-defined, `0 ≤ η ≤ 1`, both equality cases), the
  Parseval normalisation `TorusL2.e62_parseval`, the projector formulation `TorusL2.eta_proj`,
  sharpness `TorusL2.eta_basis_mem`/`TorusL2.eta_basis_not_mem`, and the non-monotone example
  `TorusL2.eta_not_monotone` (`η(t) = cos² t`).
-/

open MeasureTheory Complex Filter Topology
open scoped ComplexConjugate Real ENNReal InnerProductSpace

noncomputable section

namespace ReyesMath
namespace TorusL2

attribute [local instance] Real.fact_zero_lt_one

/-- The normalised Haar measure on the unit torus `(ℝ/ℤ)^d`, exactly as in
`Mathlib.Analysis.Fourier.AddCircleMulti`. -/
abbrev volU (d : ℕ) : Measure (UnitAddTorus (Fin d)) :=
  @volume _ (@MeasureSpace.pi (Fin d) _ (fun _ => UnitAddCircle)
    fun _ => instMeasureSpaceUnitAddCircle)

variable {L : ℝ} [hL : Fact (0 < L)] {d : ℕ}

variable (L d) in
/-- The flat torus `𝕋_L^d = (ℝ/Lℤ)^d`. -/
abbrev Tor := Fin d → AddCircle L

variable (L d) in
/-- The normalised measure `|𝕋_L^d|⁻¹ dx` (a probability measure). -/
def μ : Measure (Tor L d) := Measure.pi fun _ => AddCircle.haarAddCircle

instance : IsProbabilityMeasure (μ L d) := by unfold μ; infer_instance

variable (L d) in
/-- `L²(𝕋_L^d)` with the normalised inner product `⟪A, B⟫ = |𝕋|⁻¹ ∫ conj A · B`. -/
abbrev L2 := Lp ℂ 2 (μ L d)

/-- Continuous additive isomorphisms between circles preserve the normalised Haar measures. -/
theorem mp_addEquiv {p q : ℝ} [Fact (0 < p)] [Fact (0 < q)] (e : AddCircle p ≃+ AddCircle q)
    (he : Continuous e) (hes : Continuous e.symm) :
    MeasurePreserving e AddCircle.haarAddCircle AddCircle.haarAddCircle := by
  refine ⟨he.measurable, ?_⟩
  haveI := e.isAddHaarMeasure_map AddCircle.haarAddCircle he hes
  haveI : IsProbabilityMeasure (Measure.map e AddCircle.haarAddCircle) :=
    isProbabilityMeasure_map he.aemeasurable
  exact Measure.isAddHaarMeasure_eq_of_isProbabilityMeasure _ _

/-- The rescaling `ℝ/ℤ → ℝ/Lℤ`, `t ↦ L t`. -/
def sc : AddCircle (1 : ℝ) ≃+ AddCircle L :=
  AddCircle.equivAddCircle 1 L one_ne_zero hL.out.ne'

theorem continuous_sc : Continuous (sc (L := L)) :=
  (AddCircle.homeomorphAddCircle (1 : ℝ) L one_ne_zero hL.out.ne').continuous

theorem continuous_sc_symm : Continuous (sc (L := L)).symm :=
  (AddCircle.homeomorphAddCircle (1 : ℝ) L one_ne_zero hL.out.ne').symm.continuous

/-- The coordinatewise rescaling `Φ : (ℝ/ℤ)^d → (ℝ/Lℤ)^d`. -/
def Φ : UnitAddTorus (Fin d) → Tor L d := fun y i => sc (y i)

/-- Its inverse `Ψ`. -/
def Ψ : Tor L d → UnitAddTorus (Fin d) := fun x i => (sc (L := L)).symm (x i)

theorem Φ_Ψ (x : Tor L d) : Φ (Ψ x) = x := by
  funext i; simp [Φ, Ψ]

theorem Ψ_Φ (y : UnitAddTorus (Fin d)) : Ψ (L := L) (Φ y) = y := by
  funext i; simp [Φ, Ψ]

theorem mp_Φ : MeasurePreserving (Φ (L := L) (d := d)) (volU d) (μ L d) :=
  measurePreserving_pi _ _ fun _ => mp_addEquiv sc continuous_sc continuous_sc_symm

theorem mp_Ψ : MeasurePreserving (Ψ (L := L) (d := d)) (μ L d) (volU d) :=
  measurePreserving_pi (fun _ => AddCircle.haarAddCircle) (fun _ => AddCircle.haarAddCircle)
    fun _ => mp_addEquiv (sc (L := L)).symm continuous_sc_symm continuous_sc

/-- Transport of `L²` from `(ℝ/Lℤ)^d` to the unit torus. -/
def toU : L2 L d →ₗᵢ[ℂ] Lp ℂ 2 (volU d) := Lp.compMeasurePreservingₗᵢ ℂ Φ mp_Φ

/-- Transport of `L²` from the unit torus to `(ℝ/Lℤ)^d`. -/
def ofU : Lp ℂ 2 (volU d) →ₗᵢ[ℂ] L2 L d := Lp.compMeasurePreservingₗᵢ ℂ Ψ mp_Ψ

theorem ofU_toU (A : L2 L d) : ofU (toU A) = A := by
  apply Lp.ext
  have h1 : (ofU (toU A) : Tor L d → ℂ) =ᵐ[μ L d] (toU A) ∘ Ψ :=
    Lp.coeFn_compMeasurePreserving _ _
  have h2 : ((toU A : Lp ℂ 2 (volU d)) : UnitAddTorus (Fin d) → ℂ) =ᵐ[volU d] A ∘ Φ (L := L) :=
    Lp.coeFn_compMeasurePreserving _ _
  have h3 := (mp_Ψ (L := L)).quasiMeasurePreserving.ae_eq_comp h2
  filter_upwards [h1, h3] with x hx1 hx3
  rw [hx1, hx3]; simp [Φ_Ψ]

theorem toU_ofU (B : Lp ℂ 2 (volU d)) : toU (ofU (L := L) B) = B := by
  apply Lp.ext
  have h1 : (toU (ofU (L := L) B) : UnitAddTorus (Fin d) → ℂ) =ᵐ[volU d] (ofU (L := L) B) ∘ Φ :=
    Lp.coeFn_compMeasurePreserving _ _
  have h2 : ((ofU (L := L) B : L2 L d) : Tor L d → ℂ) =ᵐ[μ L d] B ∘ Ψ :=
    Lp.coeFn_compMeasurePreserving _ _
  have h3 := (mp_Φ (L := L)).quasiMeasurePreserving.ae_eq_comp h2
  filter_upwards [h1, h3] with x hx1 hx3
  rw [hx1, hx3]; simp [Ψ_Φ]

/-- The isometric isomorphism `L²(𝕋_L^d) ≃ L²((ℝ/ℤ)^d)`. -/
def eqU : L2 L d ≃ₗᵢ[ℂ] Lp ℂ 2 (volU d) :=
  { toU with
    invFun := ofU
    left_inv := ofU_toU
    right_inv := toU_ofU }

/-! ### Fourier modes and the Hilbert basis -/

/-- The Fourier mode `e_n(x) = ∏ᵢ exp(2πi nᵢ xᵢ / L)`; for `L = 2π` this is `e^{i n·x}`. -/
def emode (n : Fin d → ℤ) : C(Tor L d, ℂ) where
  toFun x := ∏ i, fourier (n i) (x i)
  continuous_toFun := continuous_finset_prod _
    fun i _ => (fourier (n i)).continuous.comp (continuous_apply i)

theorem fourier_sc (n : ℤ) (t : AddCircle (1 : ℝ)) : fourier n (sc (L := L) t) = fourier n t := by
  induction t using QuotientAddGroup.induction_on with
  | H z =>
    have : sc (L := L) (z : AddCircle (1 : ℝ)) = ((z * L : ℝ) : AddCircle L) := by
      simp [sc]
    rw [this, fourier_coe_apply, fourier_coe_apply]
    congr 1
    have hL0 : (L : ℂ) ≠ 0 := by exact_mod_cast hL.out.ne'
    push_cast
    field_simp

theorem emode_Φ (n : Fin d → ℤ) (y : UnitAddTorus (Fin d)) :
    emode (L := L) n (Φ y) = UnitAddTorus.mFourier n y := by
  simp only [emode, ContinuousMap.coe_mk, UnitAddTorus.mFourier, Φ, fourier_sc]


variable (L d) in
/-- The Fourier Hilbert basis `(e_n)_{n ∈ ℤ^d}` of `L²(𝕋_L^d)`. -/
def basis : HilbertBasis (Fin d → ℤ) ℂ (L2 L d) :=
  HilbertBasis.ofRepr ((eqU (L := L)).trans UnitAddTorus.mFourierBasis.repr)

theorem basis_repr_apply (A : L2 L d) :
    (basis L d).repr A = UnitAddTorus.mFourierBasis.repr (eqU A) := rfl

theorem basis_eq_ofU (n : Fin d → ℤ) :
    basis L d n = ofU (L := L) (UnitAddTorus.mFourierLp 2 n) := by
  classical
  apply (basis L d).repr.injective
  rw [HilbertBasis.repr_self, basis_repr_apply]
  have : eqU (L := L) (ofU (UnitAddTorus.mFourierLp 2 n)) = UnitAddTorus.mFourierBasis n := by
    rw [UnitAddTorus.coe_mFourierBasis]; exact toU_ofU _
  rw [this, HilbertBasis.repr_self]

theorem basis_ae_eq (n : Fin d → ℤ) : (basis L d n : Tor L d → ℂ) =ᵐ[μ L d] emode n := by
  rw [basis_eq_ofU]
  have h1 : ((ofU (L := L) (UnitAddTorus.mFourierLp 2 n) : L2 L d) : Tor L d → ℂ) =ᵐ[μ L d]
      (UnitAddTorus.mFourierLp 2 n : UnitAddTorus (Fin d) → ℂ) ∘ Ψ :=
    Lp.coeFn_compMeasurePreserving _ _
  have h2 := (mp_Ψ (L := L)).quasiMeasurePreserving.ae_eq_comp
    (UnitAddTorus.coeFn_mFourierLp (d := Fin d) 2 n)
  filter_upwards [h1, h2] with x hx1 hx2
  rw [hx1, hx2, Function.comp_apply, ← emode_Φ (L := L), Φ_Ψ]

theorem basis_eq_toLp (n : Fin d → ℤ) :
    basis L d n = (emode n).toLp 2 (μ L d) ℂ := by
  apply Lp.ext
  filter_upwards [basis_ae_eq (L := L) n, ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (μ L d) (emode (L := L) n)]
    with x h1 h2
  rw [h1, h2]

/-- The Fourier coefficient `Â_n = ⨍ A(x) \overline{e_n(x)} dx` (normalised measure). -/
def coef (A : L2 L d) (n : Fin d → ℤ) : ℂ := ∫ x, A x * conj (emode n x) ∂(μ L d)

theorem repr_eq_coef (A : L2 L d) (n : Fin d → ℤ) : (basis L d).repr A n = coef A n := by
  rw [HilbertBasis.repr_apply_apply, MeasureTheory.L2.inner_def, coef]
  apply integral_congr_ae
  filter_upwards [basis_ae_eq (L := L) n] with x hx
  rw [hx]; simp

theorem coef_add (A B : L2 L d) (n : Fin d → ℤ) : coef (A + B) n = coef A n + coef B n := by
  simp only [← repr_eq_coef, map_add, lp.coeFn_add, Pi.add_apply]

theorem coef_smul (c : ℂ) (A : L2 L d) (n : Fin d → ℤ) : coef (c • A) n = c * coef A n := by
  simp only [← repr_eq_coef, map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]

theorem coef_sub (A B : L2 L d) (n : Fin d → ℤ) : coef (A - B) n = coef A n - coef B n := by
  simp only [← repr_eq_coef, map_sub, lp.coeFn_sub, Pi.sub_apply]

theorem coef_zero (n : Fin d → ℤ) : coef (0 : L2 L d) n = 0 := by
  simp only [← repr_eq_coef, map_zero, lp.coeFn_zero, Pi.zero_apply]

theorem coef_basis (m n : Fin d → ℤ) : coef (basis L d m) n = if n = m then 1 else 0 := by
  classical
  rw [← repr_eq_coef, HilbertBasis.repr_self, lp.single_apply, Pi.single_apply]

/-- Uniqueness of Fourier coefficients. -/
theorem ext_coef {A B : L2 L d} (h : ∀ n, coef A n = coef B n) : A = B := by
  apply (basis L d).repr.injective
  ext n; simp only [repr_eq_coef, h]

/-- `A = Σ Â_n e_n` in `L²`. -/
theorem hasSum_series (A : L2 L d) : HasSum (fun n => coef A n • basis L d n) A := by
  simpa only [repr_eq_coef] using (basis L d).hasSum_repr A

/-- Parseval's identity for inner products. -/
theorem hasSum_inner (A B : L2 L d) :
    HasSum (fun n => conj (coef A n) * coef B n) ⟪A, B⟫_ℂ := by
  have := (basis L d).hasSum_inner_mul_inner A B
  refine this.congr_fun fun n => ?_
  rw [← repr_eq_coef, ← repr_eq_coef, HilbertBasis.repr_apply_apply,
    HilbertBasis.repr_apply_apply, inner_conj_symm]

/-- Parseval's identity: `‖A‖² = Σ |Â_n|²`. -/
theorem hasSum_sq (A : L2 L d) : HasSum (fun n => ‖coef A n‖ ^ 2) (‖A‖ ^ 2) := by
  have h := (hasSum_inner A A).mapL Complex.reCLM
  have e : Complex.reCLM ⟪A, A⟫_ℂ = ‖A‖ ^ 2 := by
    rw [Complex.reCLM_apply]
    simpa using inner_self_eq_norm_sq (𝕜 := ℂ) A
  rw [e] at h
  refine h.congr_fun fun n => ?_
  rw [Complex.reCLM_apply, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

theorem summable_sq (A : L2 L d) : Summable fun n => ‖coef A n‖ ^ 2 := (hasSum_sq A).summable

theorem norm_sq_eq_tsum (A : L2 L d) : ‖A‖ ^ 2 = ∑' n, ‖coef A n‖ ^ 2 := (hasSum_sq A).tsum_eq.symm

/-- The normalised measure is `|𝕋_L^d|⁻¹ dx`: `dx = L^d · μ`. -/
theorem volume_eq_smul_μ : (volume : Measure (Tor L d)) = ENNReal.ofReal (L ^ d) • μ L d := by
  show Measure.pi (fun _ => (volume : Measure (AddCircle L))) = _
  refine Measure.pi_eq fun s _ => ?_
  simp only [Measure.smul_apply, μ, Measure.pi_pi, smul_eq_mul,
    AddCircle.volume_eq_smul_haarAddCircle, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, ENNReal.ofReal_pow hL.out.le]

/-- `∫ f dx = L^d ⨍ f`: integrals against Lebesgue measure on `𝕋_L^d`. -/
theorem integral_volume (f : Tor L d → ℂ) : ∫ x, f x = L ^ d * ∫ x, f x ∂(μ L d) := by
  rw [volume_eq_smul_μ, integral_smul_measure, ENNReal.toReal_ofReal (pow_pos hL.out d).le,
    Complex.real_smul]; push_cast; ring

omit hL in
/-- The Fourier mode at a point `x = (tᵢ mod L)`: `e_n(x) = exp(2πi Σ nᵢ tᵢ / L)`; for `L = 2π`
this is `e^{i n·t}`. -/
theorem emode_coe (n : Fin d → ℤ) (t : Fin d → ℝ) :
    emode (L := L) n (fun i => (t i : AddCircle L)) =
      Complex.exp (2 * π * Complex.I * (∑ i, (n i : ℂ) * t i) / L) := by
  simp only [emode, ContinuousMap.coe_mk, fourier_coe_apply, ← Complex.exp_sum, Finset.mul_sum,
    Finset.sum_div]
  congr 1
  refine Finset.sum_congr rfl fun i _ => by ring

/-- The literal coefficient formula `Â_n = |𝕋|⁻¹ ∫ A(x) \overline{e_n(x)} dx`. -/
theorem coef_eq_volume (A : L2 L d) (n : Fin d → ℤ) :
    coef A n = ((L ^ d)⁻¹ : ℝ) * ∫ x, A x * conj (emode n x) := by
  rw [integral_volume, coef]
  have : (L ^ d : ℂ) ≠ 0 := by exact_mod_cast (pow_pos hL.out d).ne'
  push_cast; field_simp


theorem norm_sq_eq_integral (A : L2 L d) : ‖A‖ ^ 2 = ∫ x, ‖A x‖ ^ 2 ∂(μ L d) := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ) A, MeasureTheory.L2.inner_def,
    ← integral_re (L2.integrable_inner (𝕜 := ℂ) A A)]
  congr 1; funext x
  rw [inner_self_eq_norm_sq]

/-- Parseval with Lebesgue measure: `‖A‖²_{L²(𝕋_L^d, dx)} = L^d Σ |Â_k|²`. -/
theorem integral_norm_sq_volume (A : L2 L d) :
    ∫ x, ‖A x‖ ^ 2 = L ^ d * ∑' k, ‖coef A k‖ ^ 2 := by
  rw [volume_eq_smul_μ, integral_smul_measure, ENNReal.toReal_ofReal (pow_pos hL.out d).le,
    ← norm_sq_eq_integral, norm_sq_eq_tsum, smul_eq_mul]

theorem continuous_coef (k : Fin d → ℤ) : Continuous fun B : L2 L d => coef B k := by
  have : (fun B : L2 L d => coef B k) = fun B => ⟪basis L d k, B⟫_ℂ := by
    funext B; rw [← repr_eq_coef, HilbertBasis.repr_apply_apply]
  rw [this]; exact continuous_const.inner continuous_id

theorem norm_basis (k : Fin d → ℤ) : ‖basis L d k‖ = 1 := (basis L d).orthonormal.1 k

/-! ### Bounded Fourier multipliers -/

theorem memℓp_mul {w : (Fin d → ℤ) → ℂ} {C : ℝ} (hw : ∀ k, ‖w k‖ ≤ C)
    (a : ℓ²(Fin d → ℤ, ℂ)) : Memℓp (fun k => w k * a k) 2 := by
  have hC : 0 ≤ C := (norm_nonneg _).trans (hw 0)
  refine memℓp_gen ?_
  have ha := (lp.memℓp a).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun k => ?_)
    (ha.mul_left (C ^ (2 : ℝ≥0∞).toReal))
  rw [norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (norm_nonneg _) (hw k) (by positivity))
    (by positivity)

variable (L d) in
/-- The linear Fourier multiplier `A ↦ Σ w(k) Â_k e_k`. -/
def multₗ (w : (Fin d → ℤ) → ℂ) {C : ℝ} (hw : ∀ k, ‖w k‖ ≤ C) : L2 L d →ₗ[ℂ] L2 L d where
  toFun A := (basis L d).repr.symm ⟨fun k => w k * (basis L d).repr A k, memℓp_mul hw _⟩
  map_add' A B := by
    rw [← map_add]; congr 1; ext k; simp [mul_add]
  map_smul' c A := by
    rw [RingHom.id_apply, ← map_smul]; congr 1; ext k; simp [mul_left_comm]

theorem coef_multₗ {w : (Fin d → ℤ) → ℂ} {C : ℝ} (hw : ∀ k, ‖w k‖ ≤ C) (A : L2 L d)
    (k : Fin d → ℤ) : coef (multₗ L d w hw A) k = w k * coef A k := by
  rw [← repr_eq_coef, ← repr_eq_coef]
  simp [multₗ]

theorem norm_multₗ_le {w : (Fin d → ℤ) → ℂ} {C : ℝ} (hw : ∀ k, ‖w k‖ ≤ C) (A : L2 L d) :
    ‖multₗ L d w hw A‖ ≤ C * ‖A‖ := by
  have hC : 0 ≤ C := (norm_nonneg _).trans (hw 0)
  have h : ‖multₗ L d w hw A‖ ^ 2 ≤ C ^ 2 * ‖A‖ ^ 2 :=
    hasSum_le (fun k => by
      rw [coef_multₗ, norm_mul, mul_pow]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hw k) 2)
        (by positivity)) (hasSum_sq _) ((hasSum_sq A).mul_left (C ^ 2))
  rw [← mul_pow] at h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h

variable (L d) in
/-- The bounded Fourier multiplier with symbol `w` (`‖w k‖ ≤ C`), as an operator on
`L²(𝕋_L^d)`. -/
def mult (w : (Fin d → ℤ) → ℂ) {C : ℝ} (hw : ∀ k, ‖w k‖ ≤ C) : L2 L d →L[ℂ] L2 L d :=
  (multₗ L d w hw).mkContinuous C (norm_multₗ_le hw)

section mult
variable {w v : (Fin d → ℤ) → ℂ} {C C' : ℝ} (hw : ∀ k, ‖w k‖ ≤ C) (hv : ∀ k, ‖v k‖ ≤ C')

include hw in
/-- The multiplier formula `\widehat{(QA)}_k = w(k) Â_k`. -/
theorem coef_mult (A : L2 L d) (k : Fin d → ℤ) : coef (mult L d w hw A) k = w k * coef A k :=
  coef_multₗ hw A k

include hw in
/-- `QA = Σ w(k) Â_k e_k` in `L²`. -/
theorem hasSum_mult (A : L2 L d) :
    HasSum (fun k => (w k * coef A k) • basis L d k) (mult L d w hw A) := by
  simpa only [coef_mult hw] using hasSum_series (mult L d w hw A)

include hw in
theorem norm_mult_sq (A : L2 L d) :
    HasSum (fun k => ‖w k‖ ^ 2 * ‖coef A k‖ ^ 2) (‖mult L d w hw A‖ ^ 2) := by
  simpa only [coef_mult hw, norm_mul, mul_pow] using hasSum_sq (mult L d w hw A)

include hw hv in
theorem norm_mul_le_of : ∀ k, ‖w k * v k‖ ≤ C * C' := fun k => by
  rw [norm_mul]
  exact mul_le_mul (hw k) (hv k) (norm_nonneg _) ((norm_nonneg _).trans (hw k))

include hw hv in
theorem mult_comp :
    (mult L d w hw).comp (mult L d v hv) = mult L d (fun k => w k * v k) (norm_mul_le_of hw hv) := by
  ext1 A; apply ext_coef; intro k
  simp only [ContinuousLinearMap.comp_apply, coef_mult]; ring

include hw in
/-- A bounded multiplier is idempotent iff its symbol satisfies `w(k)² = w(k)` for every mode. -/
theorem mult_idem_iff :
    (mult L d w hw).comp (mult L d w hw) = mult L d w hw ↔ ∀ k, w k ^ 2 = w k := by
  constructor
  · intro h k
    have := congrArg (fun T : L2 L d →L[ℂ] L2 L d => coef (T (basis L d k)) k) h
    simpa [coef_mult, coef_basis, sq] using this
  · intro h; ext1 A; apply ext_coef; intro k
    simp only [ContinuousLinearMap.comp_apply, coef_mult, ← mul_assoc, ← sq, h]

include hw in
theorem norm_conj_le : ∀ k, ‖conj (w k)‖ ≤ C := fun k => by rw [Complex.norm_conj]; exact hw k

include hw in
/-- `Q* ` is the multiplier with the conjugate symbol. -/
theorem adjoint_mult :
    ContinuousLinearMap.adjoint (mult L d w hw) = mult L d (fun k => conj (w k)) (norm_conj_le hw) := by
  symm; rw [ContinuousLinearMap.eq_adjoint_iff]; intro A B
  refine (hasSum_inner _ _).unique ((hasSum_inner A (mult L d w hw B)).congr_fun fun k => ?_)
  rw [coef_mult, coef_mult, map_mul, Complex.conj_conj]; ring

end mult

/-! ### Sharp spectral masks -/

/-- The indicator `χ_S` of a set `S ⊆ ℤ^d` of Fourier modes. -/
def chi (S : Set (Fin d → ℤ)) : (Fin d → ℤ) → ℂ := S.indicator 1

theorem chi_mem {S : Set (Fin d → ℤ)} {k : Fin d → ℤ} (hk : k ∈ S) : chi S k = 1 := by
  simp [chi, hk]

theorem chi_not_mem {S : Set (Fin d → ℤ)} {k : Fin d → ℤ} (hk : k ∉ S) : chi S k = 0 := by
  simp [chi, hk]

theorem norm_chi_le (S : Set (Fin d → ℤ)) (k : Fin d → ℤ) : ‖chi S k‖ ≤ 1 := by
  by_cases hk : k ∈ S <;> simp [chi_mem, chi_not_mem, hk]

theorem chi_sq (S : Set (Fin d → ℤ)) (k : Fin d → ℤ) : chi S k ^ 2 = chi S k := by
  by_cases hk : k ∈ S <;> simp [chi_mem, chi_not_mem, hk]

theorem conj_chi (S : Set (Fin d → ℤ)) (k : Fin d → ℤ) : conj (chi S k) = chi S k := by
  by_cases hk : k ∈ S <;> simp [chi_mem, chi_not_mem, hk]

variable (L d) in
/-- The sharp spectral projection `P_S A = Σ_{k ∈ S} Â_k e_k = Σ_k χ_S(k) Â_k e_k`. -/
def P (S : Set (Fin d → ℤ)) : L2 L d →L[ℂ] L2 L d := mult L d (chi S) (norm_chi_le S)

variable (L d) in
/-- The band-limited subspace `ℋ_S = {B : B̂_k = 0 for k ∉ S}`. -/
def H (S : Set (Fin d → ℤ)) : Submodule ℂ (L2 L d) where
  carrier := {B | ∀ k ∉ S, coef B k = 0}
  add_mem' {A B} hA hB k hk := by
    rw [Set.mem_setOf_eq] at hA hB; rw [coef_add, hA k hk, hB k hk, add_zero]
  zero_mem' k _ := coef_zero k
  smul_mem' c B hB k hk := by
    rw [Set.mem_setOf_eq] at hB; rw [coef_smul, hB k hk, mul_zero]

theorem mem_H {S : Set (Fin d → ℤ)} {B : L2 L d} : B ∈ H L d S ↔ ∀ k ∉ S, coef B k = 0 := Iff.rfl

theorem isClosed_H (S : Set (Fin d → ℤ)) : IsClosed (H L d S : Set (L2 L d)) := by
  have : (H L d S : Set (L2 L d)) = ⋂ k ∈ Sᶜ, {B | coef B k = 0} := by
    ext B; simp [H]
  rw [this]
  exact isClosed_biInter fun k _ => isClosed_eq (continuous_coef k) continuous_const

instance (S : Set (Fin d → ℤ)) : CompleteSpace (H L d S) :=
  @IsClosed.completeSpace_coe _ _ _ _ (isClosed_H S)

instance (S : Set (Fin d → ℤ)) : (H L d S).HasOrthogonalProjection :=
  Submodule.HasOrthogonalProjection.ofCompleteSpace _


theorem mult_congr {w v : (Fin d → ℤ) → ℂ} {C C' : ℝ} (hw : ∀ k, ‖w k‖ ≤ C)
    (hv : ∀ k, ‖v k‖ ≤ C') (h : ∀ k, w k = v k) : mult L d w hw = mult L d v hv := by
  ext1 A; apply ext_coef; intro k; simp [coef_mult, h]

/-! ### The sharp projection `P_S` -/

section proj
variable (S : Set (Fin d → ℤ))

theorem coef_P (A : L2 L d) (k : Fin d → ℤ) : coef (P L d S A) k = chi S k * coef A k :=
  coef_mult _ A k

/-- `P_S A = Σ_k χ_S(k) Â_k e_k`, convergent in `L²`. -/
theorem hasSum_P (A : L2 L d) :
    HasSum (fun k => (chi S k * coef A k) • basis L d k) (P L d S A) :=
  hasSum_mult _ A

/-- Idempotence `P² = P`. -/
theorem P_idem : (P L d S).comp (P L d S) = P L d S := (mult_idem_iff _).2 (chi_sq S)

/-- Self-adjointness `P* = P`. -/
theorem P_adjoint : ContinuousLinearMap.adjoint (P L d S) = P L d S := by
  rw [P, adjoint_mult]; exact mult_congr _ _ (conj_chi S)

theorem P_isSelfAdjoint : IsSelfAdjoint (P L d S) :=
  ContinuousLinearMap.isSelfAdjoint_iff'.2 (P_adjoint S)

theorem inner_P (A B : L2 L d) : ⟪P L d S A, B⟫_ℂ = ⟪A, P L d S B⟫_ℂ := by
  rw [← ContinuousLinearMap.adjoint_inner_right, P_adjoint]

/-- Contraction `‖P A‖ ≤ ‖A‖`. -/
theorem norm_P_le (A : L2 L d) : ‖P L d S A‖ ≤ ‖A‖ := by
  have := norm_multₗ_le (L := L) (norm_chi_le S) A
  rw [one_mul] at this; exact this

theorem P_mem (A : L2 L d) : P L d S A ∈ H L d S := fun k hk => by
  rw [coef_P, chi_not_mem hk, zero_mul]

theorem P_eq_self {B : L2 L d} (hB : B ∈ H L d S) : P L d S B = B := by
  apply ext_coef; intro k; rw [coef_P]
  by_cases hk : k ∈ S
  · rw [chi_mem hk, one_mul]
  · rw [chi_not_mem hk, zero_mul, hB k hk]

theorem P_eq_self_iff (A : L2 L d) : P L d S A = A ↔ A ∈ H L d S :=
  ⟨fun h => h ▸ P_mem S A, P_eq_self S⟩

/-- `Ran P_S = ℋ_S`. -/
theorem range_P : LinearMap.range (P L d S) = H L d S := by
  ext B; constructor
  · rintro ⟨A, rfl⟩; exact P_mem S A
  · intro hB; exact ⟨B, P_eq_self S hB⟩

theorem inner_sub_P_eq_zero (A : L2 L d) {B : L2 L d} (hB : B ∈ H L d S) :
    ⟪A - P L d S A, B⟫_ℂ = 0 := by
  refine (hasSum_inner _ _).unique ?_
  convert hasSum_zero using 1
  funext k
  rw [coef_sub, coef_P]
  by_cases hk : k ∈ S
  · rw [chi_mem hk, one_mul, sub_self, map_zero, zero_mul]
  · rw [hB k hk, mul_zero]

/-- `P_S` is the orthogonal projection onto `ℋ_S`. -/
theorem P_eq_starProjection (A : L2 L d) : P L d S A = (H L d S).starProjection A :=
  (Submodule.eq_starProjection_of_mem_of_inner_eq_zero (P_mem S A)
    fun _ hB => inner_sub_P_eq_zero S A hB).symm

/-- The energy decomposition `‖A‖² = ‖PA‖² + ‖(I − P)A‖²`. -/
theorem pythagoras (A : L2 L d) : ‖A‖ ^ 2 = ‖P L d S A‖ ^ 2 + ‖A - P L d S A‖ ^ 2 := by
  have h : ⟪P L d S A, A - P L d S A⟫_ℂ = 0 := by
    rw [← inner_conj_symm, inner_sub_P_eq_zero S A (P_mem S A), map_zero]
  have := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ h
  rw [add_sub_cancel] at this
  simpa only [sq] using this

theorem dist_sq_of_mem (A : L2 L d) {B : L2 L d} (hB : B ∈ H L d S) :
    ‖A - B‖ ^ 2 = ‖A - P L d S A‖ ^ 2 + ‖P L d S A - B‖ ^ 2 := by
  have hm : P L d S A - B ∈ H L d S := (H L d S).sub_mem (P_mem S A) hB
  have := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ (inner_sub_P_eq_zero S A hm)
  rw [show A - P L d S A + (P L d S A - B) = A - B by abel] at this
  simpa only [sq] using this

/-- `P_S A` is the unique best `L²` approximation to `A` from `ℋ_S`. -/
theorem best_approx (A : L2 L d) :
    P L d S A ∈ H L d S ∧ (∀ B ∈ H L d S, ‖A - P L d S A‖ ≤ ‖A - B‖) ∧
      ∀ B ∈ H L d S, ‖A - B‖ ≤ ‖A - P L d S A‖ → B = P L d S A := by
  refine ⟨P_mem S A, fun B hB => ?_, fun B hB h => ?_⟩
  · have := dist_sq_of_mem S A hB
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1
      (by nlinarith [sq_nonneg ‖P L d S A - B‖])
  · have := dist_sq_of_mem S A hB
    have h2 : ‖A - B‖ ^ 2 ≤ ‖A - P L d S A‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    have h3 : ‖P L d S A - B‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖P L d S A - B‖]
    rw [sq_eq_zero_iff, norm_eq_zero, sub_eq_zero] at h3
    exact h3.symm

/-- `‖P_S‖_op = 1` when `S ≠ ∅`. -/
theorem opNorm_P (hS : S.Nonempty) : ‖P L d S‖ = 1 := by
  apply le_antisymm
  · exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun A => by
      rw [one_mul]; exact norm_P_le S A
  · obtain ⟨k, hk⟩ := hS
    have hb : P L d S (basis L d k) = basis L d k := P_eq_self S fun n hn => by
      rw [coef_basis, if_neg (fun h : n = k => hn (h ▸ hk))]
    have := (P L d S).le_opNorm (basis L d k)
    rwa [hb, norm_basis, mul_one] at this

end proj

/-- `P_∅ = 0`. -/
theorem P_empty : P L d (∅ : Set (Fin d → ℤ)) = 0 := by
  ext1 A; apply ext_coef; intro k
  rw [coef_P, chi_not_mem (Set.notMem_empty k), zero_mul, ContinuousLinearMap.zero_apply,
    coef_zero]


theorem sq_eq_self_iff (z : ℂ) : z ^ 2 = z ↔ z = 0 ∨ z = 1 := by
  constructor
  · intro h
    have : z * (z - 1) = 0 := by rw [mul_sub, mul_one, ← sq, h, sub_self]
    rcases mul_eq_zero.1 this with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (sub_eq_zero.1 h1)
  · rintro (rfl | rfl) <;> norm_num

/-- Remark (smooth multipliers): a bounded multiplier is idempotent iff `w(k) ∈ {0, 1}` for
every mode. -/
theorem mult_idem_iff_mem {w : (Fin d → ℤ) → ℂ} {C : ℝ} (hw : ∀ k, ‖w k‖ ≤ C) :
    (mult L d w hw).comp (mult L d w hw) = mult L d w hw ↔ ∀ k, w k = 0 ∨ w k = 1 := by
  rw [mult_idem_iff]; exact forall_congr' fun k => sq_eq_self_iff (w k)

/-! ### The spectral energy fraction (E62) -/

/-- `E⋆ = Σ_{k ∈ S} |Â_k|²`. -/
def Estar (S : Set (Fin d → ℤ)) (A : L2 L d) : ℝ :=
  ∑' k, S.indicator (fun k => ‖coef A k‖ ^ 2) k

/-- `E_tot = Σ_k |Â_k|²`. -/
def Etot (A : L2 L d) : ℝ := ∑' k, ‖coef A k‖ ^ 2

/-- The spectral energy concentration fraction `η = E⋆ / E_tot`. -/
def eta (S : Set (Fin d → ℤ)) (A : L2 L d) : ℝ := Estar S A / Etot A

section eta
variable (S : Set (Fin d → ℤ))

theorem hasSum_Estar (A : L2 L d) :
    HasSum (fun k => S.indicator (fun k => ‖coef A k‖ ^ 2) k) (‖P L d S A‖ ^ 2) := by
  refine (norm_mult_sq (L := L) (norm_chi_le S) A).congr_fun fun k => ?_
  by_cases hk : k ∈ S <;> simp [hk, chi_mem, chi_not_mem]

theorem Estar_eq (A : L2 L d) : Estar S A = ‖P L d S A‖ ^ 2 := (hasSum_Estar S A).tsum_eq

theorem Etot_eq (A : L2 L d) : Etot A = ‖A‖ ^ 2 := (hasSum_sq A).tsum_eq

/-- Projector form `η(A) = ‖P A‖² / ‖A‖²`. -/
theorem eta_eq (A : L2 L d) : eta S A = ‖P L d S A‖ ^ 2 / ‖A‖ ^ 2 := by
  rw [eta, Estar_eq, Etot_eq]

theorem P_eq_zero_iff (A : L2 L d) : P L d S A = 0 ↔ ∀ k ∈ S, coef A k = 0 := by
  constructor
  · intro h k hk
    have := coef_P S A k
    rw [h, coef_zero, chi_mem hk, one_mul] at this; exact this.symm
  · intro h; apply ext_coef; intro k; rw [coef_P, coef_zero]
    by_cases hk : k ∈ S
    · rw [h k hk, mul_zero]
    · rw [chi_not_mem hk, zero_mul]

theorem norm_P_sq_le (A : L2 L d) : ‖P L d S A‖ ^ 2 ≤ ‖A‖ ^ 2 :=
  pow_le_pow_left₀ (norm_nonneg _) (norm_P_le S A) 2

/-- The projector formulation of the endpoint cases: `η = 0 ⇔ P A = 0`, `η = 1 ⇔ (I − P)A = 0`. -/
theorem eta_proj {A : L2 L d} (hA : A ≠ 0) :
    0 ≤ eta S A ∧ eta S A ≤ 1 ∧ (eta S A = 0 ↔ P L d S A = 0) ∧
      (eta S A = 1 ↔ A - P L d S A = 0) := by
  have hA2 : 0 < ‖A‖ ^ 2 := by positivity
  rw [eta_eq]
  refine ⟨by positivity, (div_le_one hA2).2 (norm_P_sq_le S A), ?_, ?_⟩
  · rw [div_eq_zero_iff, or_iff_left hA2.ne', sq_eq_zero_iff, norm_eq_zero]
  · rw [div_eq_one_iff_eq hA2.ne']
    have := pythagoras S A
    constructor
    · intro h
      have h0 : ‖A - P L d S A‖ ^ 2 = 0 := by linarith
      rwa [sq_eq_zero_iff, norm_eq_zero] at h0
    · intro h; rw [h, norm_zero] at this; simpa using this.symm

/-- **E62** (spectral concentration bound): for nonzero `A ∈ L²(𝕋^d)` and any `S ⊆ ℤ^d`,
`η` is well defined (`0 < E_tot < ∞`), `0 ≤ η ≤ 1`, `η = 0 ⇔ Â_k = 0 on S` and
`η = 1 ⇔ Â_k = 0 off S`. -/
theorem e62 {A : L2 L d} (hA : A ≠ 0) :
    Summable (fun k => ‖coef A k‖ ^ 2) ∧
      Summable (fun k => S.indicator (fun k => ‖coef A k‖ ^ 2) k) ∧ 0 < Etot A ∧
      0 ≤ eta S A ∧ eta S A ≤ 1 ∧ (eta S A = 0 ↔ ∀ k ∈ S, coef A k = 0) ∧
      (eta S A = 1 ↔ ∀ k ∉ S, coef A k = 0) := by
  obtain ⟨h0, h1, h2, h3⟩ := eta_proj S hA
  refine ⟨summable_sq A, (hasSum_Estar S A).summable, by rw [Etot_eq]; positivity, h0, h1,
    h2.trans (P_eq_zero_iff S A), h3.trans ?_⟩
  rw [sub_eq_zero, eq_comm, P_eq_self_iff]; exact Iff.rfl

/-- Remark (sharpness): a selected mode has `η = 1`, an unselected mode has `η = 0`. -/
theorem eta_basis_mem {p : Fin d → ℤ} (hp : p ∈ S) : eta S (basis L d p) = 1 := by
  have hne : basis L d p ≠ 0 := by
    intro h; have := norm_basis (L := L) p; rw [h, norm_zero] at this; exact zero_ne_one this
  refine ((e62 S hne).2.2.2.2.2.2).2 fun k hk => ?_
  rw [coef_basis, if_neg (fun h : k = p => hk (h ▸ hp))]

theorem eta_basis_not_mem {q : Fin d → ℤ} (hq : q ∉ S) : eta S (basis L d q) = 0 := by
  have hne : basis L d q ≠ 0 := by
    intro h; have := norm_basis (L := L) q; rw [h, norm_zero] at this; exact zero_ne_one this
  refine ((e62 S hne).2.2.2.2.2.1).2 fun k hk => ?_
  rw [coef_basis, if_neg (fun h : k = q => hq (h ▸ hk))]

/-- Remark (no monotonicity): `A(t) = cos t e_p + sin t e_q` with `p ∈ S`, `q ∉ S` has
`η(t) = cos² t`, which is neither monotone nor antitone. -/
theorem eta_not_monotone {p q : Fin d → ℤ} (hp : p ∈ S) (hq : q ∉ S) :
    (∀ t : ℝ, (Real.cos t : ℂ) • basis L d p + (Real.sin t : ℂ) • basis L d q ≠ 0) ∧
      (∀ t : ℝ, eta S ((Real.cos t : ℂ) • basis L d p + (Real.sin t : ℂ) • basis L d q) =
        Real.cos t ^ 2) ∧
      ¬ Monotone (fun t : ℝ => eta S ((Real.cos t : ℂ) • basis L d p +
        (Real.sin t : ℂ) • basis L d q)) ∧
      ¬ Antitone (fun t : ℝ => eta S ((Real.cos t : ℂ) • basis L d p +
        (Real.sin t : ℂ) • basis L d q)) := by
  have hPp : P L d S (basis L d p) = basis L d p := P_eq_self S fun k hk => by
    rw [coef_basis, if_neg (fun h : k = p => hk (h ▸ hp))]
  have hPq : P L d S (basis L d q) = 0 := (P_eq_zero_iff S _).2 fun k hk => by
    rw [coef_basis, if_neg (fun h : k = q => hq (h ▸ hk))]
  have key : ∀ t : ℝ,
      ‖(Real.cos t : ℂ) • basis L d p + (Real.sin t : ℂ) • basis L d q‖ ^ 2 = 1 ∧
      ‖P L d S ((Real.cos t : ℂ) • basis L d p + (Real.sin t : ℂ) • basis L d q)‖ ^ 2 =
        Real.cos t ^ 2 := by
    intro t
    have hPA : P L d S ((Real.cos t : ℂ) • basis L d p + (Real.sin t : ℂ) • basis L d q) =
        (Real.cos t : ℂ) • basis L d p := by
      rw [map_add, map_smul, map_smul, hPp, hPq, smul_zero, add_zero]
    have hpy := pythagoras S ((Real.cos t : ℂ) • basis L d p + (Real.sin t : ℂ) • basis L d q)
    rw [hPA, add_sub_cancel_left, norm_smul, norm_smul, norm_basis, norm_basis, mul_one,
      mul_one, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs,
      sq_abs, Real.cos_sq_add_sin_sq] at hpy
    refine ⟨hpy, ?_⟩
    rw [hPA, norm_smul, norm_basis, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hne : ∀ t : ℝ, (Real.cos t : ℂ) • basis L d p + (Real.sin t : ℂ) • basis L d q ≠ 0 := by
    intro t h; have := (key t).1; rw [h, norm_zero] at this; norm_num at this
  have heta : ∀ t : ℝ, eta S ((Real.cos t : ℂ) • basis L d p + (Real.sin t : ℂ) • basis L d q) =
      Real.cos t ^ 2 := by
    intro t; rw [eta_eq, (key t).1, (key t).2, div_one]
  refine ⟨hne, heta, fun hm => ?_, fun ha => ?_⟩
  · have := hm (show (0 : ℝ) ≤ π / 2 by positivity)
    simp only [heta] at this
    simp only [Real.cos_zero, Real.cos_pi_div_two] at this; norm_num at this
  · have := ha (show π / 2 ≤ π by linarith [Real.pi_pos])
    simp only [heta] at this
    simp only [Real.cos_pi, Real.cos_pi_div_two] at this; norm_num at this

end eta

/-! ### The discrete FFT identity (E59 §3) -/

/-- For a unitary DFT matrix `F` (`F F* = I` suffices) and a fixed `0/1` mask `D`,
`P = F* D F` satisfies `P² = P` and `P* = P`. -/
theorem fft_projector {N : ℕ} (F : Matrix (Fin N) (Fin N) ℂ) (hF : F * F.conjTranspose = 1)
    (m : Fin N → ℂ) (hm : ∀ j, m j = 0 ∨ m j = 1) :
    (F.conjTranspose * Matrix.diagonal m * F) * (F.conjTranspose * Matrix.diagonal m * F) =
        F.conjTranspose * Matrix.diagonal m * F ∧
      (F.conjTranspose * Matrix.diagonal m * F).conjTranspose =
        F.conjTranspose * Matrix.diagonal m * F := by
  have hD : Matrix.diagonal m * Matrix.diagonal m = Matrix.diagonal m := by
    rw [Matrix.diagonal_mul_diagonal]; congr 1; funext j
    rcases hm j with h | h <;> simp [h]
  have hDs : (Matrix.diagonal m).conjTranspose = Matrix.diagonal m := by
    rw [Matrix.diagonal_conjTranspose]; congr 1; funext j
    rcases hm j with h | h <;> simp [h]
  constructor
  · calc F.conjTranspose * Matrix.diagonal m * F * (F.conjTranspose * Matrix.diagonal m * F)
        = F.conjTranspose * Matrix.diagonal m * (F * F.conjTranspose) * Matrix.diagonal m * F := by
          simp only [Matrix.mul_assoc]
      _ = F.conjTranspose * Matrix.diagonal m * F := by
          rw [hF, Matrix.mul_one, Matrix.mul_assoc (F.conjTranspose), hD]
  · rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hDs, Matrix.mul_assoc]


/-! ### The dominant annulus on `𝕋^d = (ℝ/2πℤ)^d` (E59) -/

/-- `|k| = (Σᵢ kᵢ²)^{1/2}` for `k ∈ ℤ^d`. -/
def knorm (k : Fin d → ℤ) : ℝ := √(∑ i, ((k i : ℝ)) ^ 2)

/-- The fixed dominant annulus `𝒜⋆ = {k ∈ ℤ^d : ||k| − k⋆| ≤ Δk}`. -/
def annulus (kstar dk : ℝ) : Set (Fin d → ℤ) := {k | |knorm k - kstar| ≤ dk}

/-- Remark (annulus convention): for `0 ≤ Δk < k⋆` the one-sided set `{|k| − k⋆ ≤ Δk}` contains
the zero mode, which the symmetric annulus excludes. -/
theorem zero_mem_oneSided_not_mem_annulus {kstar dk : ℝ} (hdk : 0 ≤ dk) (hlt : dk < kstar) :
    (0 : Fin d → ℤ) ∈ {k : Fin d → ℤ | knorm k - kstar ≤ dk} ∧
      (0 : Fin d → ℤ) ∉ annulus kstar dk := by
  have h0 : knorm (0 : Fin d → ℤ) = 0 := by simp [knorm]
  refine ⟨by simp only [Set.mem_setOf_eq, h0]; linarith, ?_⟩
  simp only [annulus, Set.mem_setOf_eq, h0, zero_sub, abs_neg, not_le]
  rw [abs_of_pos (hdk.trans_lt hlt)]; exact hlt

instance : Fact (0 < 2 * π) := ⟨Real.two_pi_pos⟩

omit hL in
/-- On `𝕋^d = (ℝ/2πℤ)^d` the modes are `e_k(x) = e^{i k·x}`. -/
theorem emode_two_pi (k : Fin d → ℤ) (t : Fin d → ℝ) :
    emode (L := 2 * π) k (fun i => (t i : AddCircle (2 * π))) =
      Complex.exp (Complex.I * ∑ i, (k i : ℂ) * t i) := by
  rw [emode_coe]; congr 1
  have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast; field_simp

/-- The E59 projection `P_{k⋆} A = Σ_{k ∈ 𝒜⋆} Â_k e^{ik·x}` on `L²(𝕋^d)`, `𝕋^d = (ℝ/2πℤ)^d`. -/
abbrev Pk (kstar dk : ℝ) : L2 (2 * π) d →L[ℂ] L2 (2 * π) d := P (2 * π) d (annulus kstar dk)

/-- The band-limited subspace `ℋ_{𝒜⋆}`. -/
abbrev Hk (kstar dk : ℝ) : Submodule ℂ (L2 (2 * π) d) := H (2 * π) d (annulus kstar dk)

/-- **E59** (dominant-annulus projection). On `𝕋^d = (ℝ/2πℤ)^d` with the normalised inner
product, the annulus projection `P_{k⋆}` (defined by the `L²`-convergent series) is a bounded
operator with `P² = P`, `P* = P`, `‖PA‖ ≤ ‖A‖`; it is the orthogonal projection onto `ℋ_{𝒜⋆}`
(its range), satisfies `‖A‖² = ‖PA‖² + ‖(I − P)A‖²`, `PA` is the unique best approximation to `A`
from `ℋ_{𝒜⋆}`, and `‖P‖_op = 1` if `𝒜⋆ ≠ ∅`, `P = 0` if `𝒜⋆ = ∅`. -/
theorem e59 (kstar dk : ℝ) :
    (∀ A : L2 (2 * π) d, HasSum (fun k => (chi (annulus kstar dk) k * coef A k) •
      basis (2 * π) d k) (Pk kstar dk A)) ∧
    (Pk kstar dk).comp (Pk kstar dk) = Pk (d := d) kstar dk ∧
    ContinuousLinearMap.adjoint (Pk (d := d) kstar dk) = Pk kstar dk ∧
    (∀ A : L2 (2 * π) d, ‖Pk kstar dk A‖ ≤ ‖A‖) ∧
    LinearMap.range (Pk (d := d) kstar dk) = Hk kstar dk ∧
    (∀ A : L2 (2 * π) d, Pk kstar dk A = (Hk kstar dk).starProjection A) ∧
    (∀ A : L2 (2 * π) d, ‖A‖ ^ 2 = ‖Pk kstar dk A‖ ^ 2 + ‖A - Pk kstar dk A‖ ^ 2) ∧
    (∀ A : L2 (2 * π) d, Pk kstar dk A ∈ Hk kstar dk ∧
      (∀ B ∈ Hk kstar dk, ‖A - Pk kstar dk A‖ ≤ ‖A - B‖) ∧
      ∀ B ∈ Hk kstar dk, ‖A - B‖ ≤ ‖A - Pk kstar dk A‖ → B = Pk kstar dk A) ∧
    ((annulus (d := d) kstar dk).Nonempty → ‖Pk (d := d) kstar dk‖ = 1) ∧
    (annulus (d := d) kstar dk = ∅ → Pk (d := d) kstar dk = 0) :=
  ⟨hasSum_P _, P_idem _, P_adjoint _, norm_P_le _, range_P _, P_eq_starProjection _,
    pythagoras _, best_approx _, opNorm_P _, fun h => by rw [Pk, h]; exact P_empty⟩

/-- E59, spectral concentration section: `η(A) = ‖PA‖²/‖A‖² = Σ_{𝒜⋆}|Â_k|² / Σ|Â_k|² ∈ [0,1]`,
and `η(A) = 1 ⇔ PA = A`. -/
theorem e59_fraction (kstar dk : ℝ) {A : L2 (2 * π) d} (hA : A ≠ 0) :
    eta (annulus kstar dk) A = ‖Pk kstar dk A‖ ^ 2 / ‖A‖ ^ 2 ∧
      0 ≤ eta (annulus kstar dk) A ∧ eta (annulus kstar dk) A ≤ 1 ∧
      (eta (annulus kstar dk) A = 1 ↔ Pk kstar dk A = A) := by
  obtain ⟨h0, h1, -, h3⟩ := eta_proj (annulus kstar dk) hA
  exact ⟨eta_eq _ A, h0, h1, h3.trans (by rw [sub_eq_zero, eq_comm])⟩

/-- E62 Parseval normalisation on `𝕋^d = (ℝ/2πℤ)^d`: `‖A‖²_{L²(dx)} = (2π)^d Σ |Â_k|²`, and the
coefficients are `Â_k = (2π)^{-d} ∫ A(x) e^{-ik·x} dx`. -/
theorem e62_parseval (A : L2 (2 * π) d) :
    ∫ x, ‖A x‖ ^ 2 = (2 * π) ^ d * Etot A ∧
      ∀ k, coef A k = (((2 * π) ^ d)⁻¹ : ℝ) * ∫ x, A x * conj (emode k x) :=
  ⟨integral_norm_sq_volume A, coef_eq_volume A⟩

end TorusL2
end ReyesMath
