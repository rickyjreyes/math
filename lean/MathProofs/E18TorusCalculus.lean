import MathProofs.BandPassFlow

/-!
# E18: classical calculus on the flat torus

Classical partial derivatives on `𝕋_L^d = (ℝ/Lℤ)^d` along the coordinate directions, and their
Fourier description.

* `sh j s = s e_j`, `HasPartial j f g`: `d/ds f(x + s e_j)|_{s=0} = g(x)` for every `x`, with
  product, conjugation and chain rules.
* `cfun f k = ⨍ f ē_k`; `cfun_translate`: translation multiplies coefficients by `e_k(y)`
  (translation invariance of the Haar measure).
* **Periodic integration by parts** `cfun_hasPartial`: for continuous `f` with continuous partial
  derivative `∂_j f`, `(∂_j f)^_k = i ξ_{k,j} f̂_k`.
* `integral_dpart_conj`: `⨍ (∂_j u) φ̄ = −⨍ u (∂_jφ)‾` for `u` in the domain of the Fourier
  derivative and `φ ∈ C¹`.
* `ser a = Σ_k a_k e_k`: continuity, termwise partial derivatives (`hasPartial_ser`), coefficients
  (`cfun_ser`), and `ae_eq_ser`: every `A ∈ L²` with summable coefficients is a.e. its series.
-/

open Filter Topology Complex MeasureTheory Set
open scoped ENNReal Real ComplexConjugate

namespace ReyesMath

namespace E18

open TorusL2 BandPass

variable {L : ℝ} [hL : Fact (0 < L)] {d : ℕ}

instance instAddRightInvariantμ : (μ L d).IsAddRightInvariant := by
  unfold μ
  infer_instance

/-! ### Translations and partial derivatives -/

/-- The translation vector `s e_j ∈ 𝕋_L^d`. -/
noncomputable def sh (j : Fin d) (s : ℝ) : Tor L d := Pi.single j (s : AddCircle L)

omit hL in
theorem sh_zero (j : Fin d) : sh (L := L) j 0 = 0 := by simp [sh]

omit hL in
theorem sh_add (j : Fin d) (s t : ℝ) : sh (L := L) j (s + t) = sh j s + sh j t := by
  simp only [sh, AddCircle.coe_add, Pi.single_add]

/-- `f` has partial derivative `g` in the direction `j`: `d/ds f(x + s e_j)|_{s=0} = g(x)`. -/
def HasPartial (j : Fin d) (f g : Tor L d → ℂ) : Prop :=
  ∀ x, HasDerivAt (fun s : ℝ => f (x + sh j s)) (g x) 0

/-- The real-valued version of `HasPartial`. -/
def HasPartialR (j : Fin d) (f g : Tor L d → ℝ) : Prop :=
  ∀ x, HasDerivAt (fun s : ℝ => f (x + sh j s)) (g x) 0

omit hL in
/-- The partial derivative along the whole line `s ↦ x + s e_j`. -/
theorem HasPartial.at {j : Fin d} {f g : Tor L d → ℂ} (h : HasPartial j f g) (x : Tor L d)
    (s₀ : ℝ) : HasDerivAt (fun s => f (x + sh j s)) (g (x + sh j s₀)) s₀ := by
  have h1 := h (x + sh j s₀)
  rw [← sub_self s₀] at h1
  have h2 := h1.comp_sub_const s₀ s₀
  refine h2.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
  simp only
  rw [add_assoc, ← sh_add, add_sub_cancel]

omit hL in
theorem HasPartial.add {j : Fin d} {f g f' g' : Tor L d → ℂ} (hf : HasPartial j f f')
    (hg : HasPartial j g g') : HasPartial j (fun x => f x + g x) (fun x => f' x + g' x) :=
  fun x => (hf x).add (hg x)

omit hL in
theorem HasPartial.sub {j : Fin d} {f g f' g' : Tor L d → ℂ} (hf : HasPartial j f f')
    (hg : HasPartial j g g') : HasPartial j (fun x => f x - g x) (fun x => f' x - g' x) :=
  fun x => (hf x).sub (hg x)

omit hL in
theorem HasPartial.mul {j : Fin d} {f g f' g' : Tor L d → ℂ} (hf : HasPartial j f f')
    (hg : HasPartial j g g') :
    HasPartial j (fun x => f x * g x) (fun x => f' x * g x + f x * g' x) := fun x => by
  have h := (hf x).mul (hg x)
  simp only [sh_zero, add_zero] at h
  exact h

omit hL in
theorem HasPartial.const_mul {j : Fin d} {f f' : Tor L d → ℂ} (c : ℂ) (hf : HasPartial j f f') :
    HasPartial j (fun x => c * f x) (fun x => c * f' x) := fun x => (hf x).const_mul c

omit hL in
theorem HasPartial.conj {j : Fin d} {f f' : Tor L d → ℂ} (hf : HasPartial j f f') :
    HasPartial j (fun x => conj (f x)) (fun x => conj (f' x)) := fun x => (hf x).star

omit hL in
theorem HasPartial.sum {j : Fin d} {ι : Type*} (s : Finset ι) {f f' : ι → Tor L d → ℂ}
    (hf : ∀ i ∈ s, HasPartial j (f i) (f' i)) :
    HasPartial j (fun x => ∑ i ∈ s, f i x) (fun x => ∑ i ∈ s, f' i x) := fun x => by
  have := HasDerivAt.fun_sum (u := s) (A := fun i s' => f i (x + sh j s'))
    (A' := fun i => f' i x) (x := 0) fun i hi => hf i hi x
  simpa using this

omit hL in
theorem HasPartialR.ofReal {j : Fin d} {f f' : Tor L d → ℝ} (hf : HasPartialR j f f') :
    HasPartial j (fun x => (f x : ℂ)) (fun x => (f' x : ℂ)) := fun x => (hf x).ofReal_comp

omit hL in
theorem HasPartialR.add {j : Fin d} {f g f' g' : Tor L d → ℝ} (hf : HasPartialR j f f')
    (hg : HasPartialR j g g') : HasPartialR j (fun x => f x + g x) (fun x => f' x + g' x) :=
  fun x => (hf x).add (hg x)

omit hL in
theorem HasPartialR.mul {j : Fin d} {f g f' g' : Tor L d → ℝ} (hf : HasPartialR j f f')
    (hg : HasPartialR j g g') :
    HasPartialR j (fun x => f x * g x) (fun x => f' x * g x + f x * g' x) := fun x => by
  have h := (hf x).mul (hg x)
  simp only [sh_zero, add_zero] at h
  exact h

omit hL in
theorem HasPartialR.const_mul {j : Fin d} {f f' : Tor L d → ℝ} (c : ℝ) (hf : HasPartialR j f f') :
    HasPartialR j (fun x => c * f x) (fun x => c * f' x) := fun x => (hf x).const_mul c

omit hL in
/-- The chain rule with a real function. -/
theorem HasPartialR.comp {j : Fin d} {f f' : Tor L d → ℝ} (hf : HasPartialR j f f')
    {F F' : ℝ → ℝ} (hF : ∀ x, HasDerivAt F (F' (f x)) (f x)) :
    HasPartialR j (fun x => F (f x)) (fun x => F' (f x) * f' x) := fun x => by
  have hF' : HasDerivAt F (F' (f x)) (f (x + sh j 0)) := by
    rw [sh_zero, add_zero]
    exact hF x
  have h := hF'.comp (0 : ℝ) (hf x)
  simpa [Function.comp_def, mul_comm] using h

omit hL in
/-- `∂_j |f|² = 2 Re(f̄ ∂_j f)`. -/
theorem HasPartial.normSq {j : Fin d} {f f' : Tor L d → ℂ} (hf : HasPartial j f f') :
    HasPartialR j (fun x => ‖f x‖ ^ 2) (fun x => 2 * (conj (f x) * f' x).re) := fun x => by
  have h := (hf x).norm_sq
  simp only [sh_zero, add_zero, Complex.inner] at h
  convert h using 2
  ring_nf

omit hL in
/-- `∂_j Re(f̄ g) = Re(f̄' g + f̄ g')`. -/
theorem HasPartial.re_conj_mul {j : Fin d} {f g f' g' : Tor L d → ℂ} (hf : HasPartial j f f')
    (hg : HasPartial j g g') :
    HasPartialR j (fun x => (conj (f x) * g x).re)
      (fun x => (conj (f' x) * g x + conj (f x) * g' x).re) := fun x => by
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) ((hf.conj.mul hg) x)

/-! ### Fourier modes -/

omit hL in
theorem emode_add (k : Fin d → ℤ) (x y : Tor L d) :
    emode (L := L) k (x + y) = emode k x * emode k y := by
  simp only [emode, ContinuousMap.coe_mk, Pi.add_apply]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [fourier_apply, fourier_apply, fourier_apply, smul_add, AddCircle.toCircle_add,
    Circle.coe_mul]

omit hL in
theorem emode_sh (k : Fin d → ℤ) (j : Fin d) (s : ℝ) :
    emode (L := L) k (sh j s) = Complex.exp (2 * π * I * (k j : ℂ) * s / L) := by
  simp only [emode, ContinuousMap.coe_mk, sh]
  rw [Finset.prod_eq_single j]
  · rw [Pi.single_eq_same, fourier_coe_apply]
  · intro i _ hi
    rw [Pi.single_eq_of_ne hi, fourier_eval_zero]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem hasDerivAt_emode_sh (k : Fin d → ℤ) (j : Fin d) :
    HasDerivAt (fun s : ℝ => emode (L := L) k (sh j s)) (I * xi L k j) 0 := by
  have hL0 : (L : ℂ) ≠ 0 := by exact_mod_cast hL.out.ne'
  have h1 : HasDerivAt (fun s : ℝ => 2 * π * I * (k j : ℂ) * (s : ℂ) / L)
      (2 * π * I * (k j : ℂ) / L) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).ofReal_comp).const_mul (2 * π * I * (k j : ℂ))
    have := this.div_const (L : ℂ)
    simpa using this
  have h2 := h1.cexp
  simp only [emode_sh]
  convert h2 using 1
  simp only [Complex.ofReal_zero, mul_zero, zero_div, Complex.exp_zero, one_mul, xi]
  push_cast
  field_simp

theorem hasPartial_emode (k : Fin d → ℤ) (j : Fin d) :
    HasPartial j (fun x => emode (L := L) k x) (fun x => I * xi L k j * emode k x) := fun x => by
  have h := (hasDerivAt_emode_sh (L := L) k j).const_mul (emode (L := L) k x)
  simp only [emode_add]
  convert h using 1
  ring

omit hL in
theorem conj_emode_mul_self (k : Fin d → ℤ) (y : Tor L d) :
    conj (emode (L := L) k y) * emode k y = 1 := by
  rw [Complex.conj_mul', norm_emode_apply]
  simp

/-! ### Fourier coefficients of functions and periodic integration by parts -/

/-- The Fourier coefficient `f̂_k = ⨍ f ē_k` of a function on the torus. -/
noncomputable def cfun (f : Tor L d → ℂ) (k : Fin d → ℤ) : ℂ :=
  ∫ x, f x * conj (emode k x) ∂(μ L d)

theorem coef_eq_cfun (A : L2 L d) (k : Fin d → ℤ) : coef A k = cfun A k := rfl

theorem cfun_congr_ae {f g : Tor L d → ℂ} (h : f =ᵐ[μ L d] g) (k : Fin d → ℤ) :
    cfun f k = cfun g k :=
  integral_congr_ae (h.mono fun x hx => by simp only [hx])

/-- **Translation**: `(f(· + y))^_k = e_k(y) f̂_k`. -/
theorem cfun_translate (f : Tor L d → ℂ) (k : Fin d → ℤ) (y : Tor L d) :
    cfun (fun x => f (x + y)) k = emode k y * cfun f k := by
  have e : ∀ x, f (x + y) * conj (emode (L := L) k x) =
      emode k y * (f (x + y) * conj (emode k (x + y))) := fun x => by
    rw [emode_add, map_mul]
    have := conj_emode_mul_self (L := L) k y
    linear_combination -(f (x + y) * conj (emode (L := L) k x)) * this
  simp only [cfun]
  simp_rw [e]
  rw [integral_const_mul, integral_add_right_eq_self (fun x => f x * conj (emode k x)) y]

/-- **Periodic integration by parts**: for continuous `f` with continuous partial derivative
`g = ∂_j f`, `ĝ_k = i ξ_{k,j} f̂_k`. -/
theorem cfun_hasPartial {j : Fin d} {f g : Tor L d → ℂ} (hf : Continuous f) (hg : Continuous g)
    (h : HasPartial j f g) (k : Fin d → ℤ) : cfun g k = I * xi L k j * cfun f k := by
  have hΦ : HasDerivAt (fun s => cfun (fun x => f (x + sh j s)) k) (I * xi L k j * cfun f k) 0 := by
    simp_rw [cfun_translate]
    exact (hasDerivAt_emode_sh k j).mul_const _
  obtain ⟨C, hC⟩ : ∃ C, ∀ x, ‖g x‖ ≤ C :=
    ⟨‖(⟨g, hg⟩ : C(Tor L d, ℂ))‖, fun x => (⟨g, hg⟩ : C(Tor L d, ℂ)).norm_coe_le_norm x⟩
  have hcont : ∀ s : ℝ, Continuous fun x : Tor L d => f (x + sh j s) * conj (emode k x) :=
    fun s => (hf.comp (continuous_add_right _)).mul (Complex.continuous_conj.comp (emode k).continuous)
  have hcont' : ∀ s : ℝ, Continuous fun x : Tor L d => g (x + sh j s) * conj (emode k x) :=
    fun s => (hg.comp (continuous_add_right _)).mul (Complex.continuous_conj.comp (emode k).continuous)
  have hint := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ L d) (x₀ := (0 : ℝ))
    (F := fun s x => f (x + sh j s) * conj (emode k x))
    (F' := fun s x => g (x + sh j s) * conj (emode k x)) (bound := fun _ => C) one_pos
    (Eventually.of_forall fun s => (hcont s).aestronglyMeasurable)
    (integrable_of_continuous_c (hcont 0))
    ((hcont' 0).aestronglyMeasurable)
    (Eventually.of_forall fun x s _ => by
      rw [norm_mul, Complex.norm_conj, norm_emode_apply, mul_one]
      exact hC _)
    (integrable_const C)
    (Eventually.of_forall fun x s _ => (h.at x s).mul_const _)
  have hΦ' : HasDerivAt (fun s => cfun (fun x => f (x + sh j s)) k) (cfun g k) 0 := by
    have := hint.2
    simp only [sh_zero, add_zero] at this
    exact this
  exact hΦ'.unique hΦ

/-! ### Pairings -/

theorem integrable_mul_continuous (A : L2 L d) {φ : Tor L d → ℂ} (hφ : Continuous φ) :
    Integrable (fun x => A x * φ x) (μ L d) := by
  obtain ⟨C, hC⟩ : ∃ C, ∀ x, ‖φ x‖ ≤ C :=
    ⟨‖(⟨φ, hφ⟩ : C(Tor L d, ℂ))‖, fun x => (⟨φ, hφ⟩ : C(Tor L d, ℂ)).norm_coe_le_norm x⟩
  have hA : Integrable (A : Tor L d → ℂ) (μ L d) := (Lp.memLp A).integrable one_le_two
  refine (hA.bdd_mul' (c := C) hφ.aestronglyMeasurable (Eventually.of_forall hC)).congr ?_
  exact Eventually.of_forall fun x => mul_comm _ _

/-- Parseval against a continuous function: `⨍ A φ̄ = Σ_k Â_k \overline{φ̂_k}`. -/
theorem hasSum_integral_mul_conj (A : L2 L d) {φ : Tor L d → ℂ} (hφ : Continuous φ) :
    HasSum (fun k => coef A k * conj (cfun φ k)) (∫ x, A x * conj (φ x) ∂(μ L d)) := by
  set B : L2 L d := (⟨φ, hφ⟩ : C(Tor L d, ℂ)).toLp 2 (μ L d) ℂ
  have hB : (B : Tor L d → ℂ) =ᵐ[μ L d] φ :=
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (μ L d) (⟨φ, hφ⟩ : C(Tor L d, ℂ))
  have h := hasSum_inner B A
  have e1 : ∀ k, conj (coef B k) * coef A k = coef A k * conj (cfun φ k) := fun k => by
    rw [coef_eq_cfun B, cfun_congr_ae hB k, mul_comm]
  have e2 : inner ℂ B A = ∫ x, A x * conj (φ x) ∂(μ L d) := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hB] with x hx
    rw [RCLike.inner_apply, hx]
  rw [e2] at h
  exact h.congr_fun fun k => (e1 k).symm

/-- **Integration by parts against a `C¹` function**: `⨍ (∂_j u) φ̄ = −⨍ u (∂_jφ)‾`, with the
Fourier derivative of `u` and the classical derivative of `φ`. -/
theorem integral_dpart_conj {j : Fin d} {u : L2 L d}
    (hu : Memℓp (fun k => I * xi L k j * coef u k) 2) {φ φ' : Tor L d → ℂ}
    (hφ : Continuous φ) (hφ' : Continuous φ') (h : HasPartial j φ φ') :
    ∫ x, (dpart j u : Tor L d → ℂ) x * conj (φ x) ∂(μ L d) =
      -∫ x, u x * conj (φ' x) ∂(μ L d) := by
  rw [← (hasSum_integral_mul_conj (dpart j u) hφ).tsum_eq,
    ← (hasSum_integral_mul_conj u hφ').tsum_eq, ← tsum_neg]
  congr 1
  funext k
  rw [dpart, coef_pmul hu, cfun_hasPartial hφ hφ' h k, map_mul, map_mul, Complex.conj_I,
    Complex.conj_ofReal]
  ring

/-! ### Fourier series with summable coefficients -/

/-- `Σ_k a_k e_k`. -/
noncomputable def ser (a : (Fin d → ℤ) → ℂ) (x : Tor L d) : ℂ := ∑' k, a k * emode k x

omit hL in
theorem norm_term_le (a : (Fin d → ℤ) → ℂ) (k : Fin d → ℤ) (x : Tor L d) :
    ‖a k * emode (L := L) k x‖ ≤ ‖a k‖ := by
  rw [norm_mul, norm_emode_apply, mul_one]

omit hL in
theorem continuous_ser {a : (Fin d → ℤ) → ℂ} (ha : Summable fun k => ‖a k‖) :
    Continuous (ser (L := L) a) :=
  continuous_tsum (fun k => continuous_const.mul (emode k).continuous) ha (norm_term_le a)

/-- The series as a continuous function, summable in the sup norm. -/
noncomputable def serC (a : (Fin d → ℤ) → ℂ) : C(Tor L d, ℂ) := ∑' k, a k • emode (L := L) k

theorem summable_serC {a : (Fin d → ℤ) → ℂ} (ha : Summable fun k => ‖a k‖) :
    Summable fun k => a k • emode (L := L) k :=
  Summable.of_norm_bounded ha fun k => by
    rw [norm_smul]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_emode_le k)

theorem serC_apply {a : (Fin d → ℤ) → ℂ} (ha : Summable fun k => ‖a k‖) (x : Tor L d) :
    serC (L := L) a x = ser a x := by
  rw [serC, ← ContinuousMap.tsum_apply (summable_serC ha)]
  rfl

theorem toLp_serC {a : (Fin d → ℤ) → ℂ} (ha : Summable fun k => ‖a k‖) :
    HasSum (fun k => a k • basis L d k) ((serC (L := L) a).toLp 2 (μ L d) ℂ) := by
  have h1 := (summable_serC (L := L) ha).hasSum.mapL (ContinuousMap.toLp (E := ℂ) 2 (μ L d) ℂ)
  refine h1.congr_fun fun k => ?_
  rw [map_smul, ← basis_eq_toLp]

theorem coef_toLp_serC {a : (Fin d → ℤ) → ℂ} (ha : Summable fun k => ‖a k‖) (k : Fin d → ℤ) :
    coef ((serC (L := L) a).toLp 2 (μ L d) ℂ) k = a k := by
  have h := (toLp_serC (L := L) ha).mapL (innerSL ℂ (basis L d k))
  have hc : ∀ B : L2 L d, innerSL ℂ (basis L d k) B = coef B k := fun B => by
    rw [innerSL_apply, ← repr_eq_coef, HilbertBasis.repr_apply_apply]
  simp only [hc] at h
  have e : (fun m => coef (a m • basis L d m) k) = fun m => if m = k then a k else 0 := by
    funext m
    rw [coef_smul, coef_basis]
    split_ifs with h1 h2 h2
    · subst h2; simp
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · simp
  rw [e] at h
  exact h.unique (hasSum_ite_eq k (a k))

theorem ae_eq_serC {a : (Fin d → ℤ) → ℂ} (ha : Summable fun k => ‖a k‖) :
    ((serC (L := L) a).toLp 2 (μ L d) ℂ : Tor L d → ℂ) =ᵐ[μ L d] ser a := by
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (μ L d) (serC (L := L) a)]
    with x hx
  rw [hx, serC_apply ha]

/-- The coefficients of the series are `a`. -/
theorem cfun_ser {a : (Fin d → ℤ) → ℂ} (ha : Summable fun k => ‖a k‖) (k : Fin d → ℤ) :
    cfun (ser (L := L) a) k = a k := by
  rw [← cfun_congr_ae (ae_eq_serC ha) k, ← coef_eq_cfun, coef_toLp_serC ha]

/-- **An `L²` function with summable Fourier coefficients is a.e. its Fourier series.** -/
theorem ae_eq_ser {A : L2 L d} (hA : Summable fun k => ‖coef A k‖) :
    (A : Tor L d → ℂ) =ᵐ[μ L d] ser (coef A) := by
  have e : (serC (L := L) (coef A)).toLp 2 (μ L d) ℂ = A :=
    ext_coef (L := L) fun k => coef_toLp_serC (L := L) hA k
  have h := ae_eq_serC (L := L) hA
  rw [e] at h
  exact h

/-- **Termwise differentiation**: `∂_j Σ a_k e_k = Σ i ξ_{k,j} a_k e_k` when
`Σ |a_k|(1 + |ξ_{k,j}|) < ∞`. -/
theorem hasPartial_ser {j : Fin d} {a : (Fin d → ℤ) → ℂ} (ha : Summable fun k => ‖a k‖)
    (haj : Summable fun k => ‖a k‖ * |xi L k j|) :
    HasPartial j (ser (L := L) a) (ser fun k => I * xi L k j * a k) := fun x => by
  have h := hasDerivAt_tsum (𝕜 := ℝ) (u := fun k => ‖a k‖ * |xi L k j|)
    (g := fun k s => a k * emode (L := L) k (x + sh j s))
    (g' := fun k s => I * xi L k j * a k * emode (L := L) k (x + sh j s)) (y₀ := 0) haj
    (fun k s => by
      have := ((hasPartial_emode (L := L) k j).at x s).const_mul (a k)
      convert this using 1
      ring)
    (fun k s => by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
        norm_emode_apply]
      nlinarith [abs_nonneg (xi L k j), norm_nonneg (a k)])
    (Summable.of_norm_bounded ha fun k => norm_term_le a k _) 0
  simp only [sh_zero, add_zero] at h
  exact h

end E18

end ReyesMath
