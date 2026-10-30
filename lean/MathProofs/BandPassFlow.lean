import Mathlib
import MathProofs.TorusFourier

/-!
# The band-pass amplitude equation as a negative gradient flow (E13/E14)

Formalization of `papers/band-pass-amplitude-negative-gradient-flow/main.tex` (E13) and of its
companion `E14_full_proof.tex`, on the flat torus `Ω = 𝕋_L^d = (ℝ/Lℤ)^d`, `d ≤ 3`, with Lebesgue
measure (`|Ω| = L^d`).

* Sobolev scale: `H^{2k}(𝕋_L^d)` is `BandPass.InH k` (`Σ w_n^{2k}|Â_n|² < ∞`, `w_n = 1 + |ξ_n|²`,
  `ξ_n = 2πn/L`), realised isometrically on `ℓ²(ℤ^d)` by `BandPass.iota` (`BandPass.inH_iff`).
  Derivatives are the Fourier multipliers `∂_j` (`BandPass.dpart`, symbol `iξ_{n,j}`) and `Δ`
  (`BandPass.lap`, symbol `−|ξ_n|²`), which agree with the classical derivatives of the modes
  (`BandPass.hasDerivAt_emode`, `BandPass.dpart_basis`, `BandPass.lap_basis`).
* Sobolev embedding `H² ⊂ C(𝕋_L^d)` for `d ≤ 3` (`BandPass.Phi`, `BandPass.norm_Phi_le`) from
  `Σ_n w_n^{-2} < ∞` (`BandPass.summable_wt_inv_sq`). Hence the energy
  `E[A] = ∫_Ω (−r|A|² − a|∇A|² + b|ΔA|² + (β/2)|A|⁴) dx` (`BandPass.energy`) is a `C¹` functional
  on `H²` (the quartic term: `BandPass.hasFDerivAt_Nq`).
* Theorem E13 (`BandPass.e13`). For `A ∈ C¹([0,T]; H²)` with `A(t) ∈ H⁴` solving
  `∂ₜA = (r − aΔ − bΔ²)A − β|A|²A` in `L²`:
  * the first variation is `DE[A](h) = 2 Re ∫_Ω (δE/δĀ) h̄` for every `h ∈ H²`, with
    `δE/δĀ = −rA + aΔA + bΔ²A + β|A|²A` (`BandPass.wirt`);
  * `∂ₜA = −δE/δĀ`;
  * `dE/dt = −2‖∂ₜA‖² ≤ 0`, and the balance law `E[A(T)] + 2∫₀ᵀ‖∂ₜA‖² = E[A(0)]` holds
    (on every subinterval `[t₁, t₂]`: `BandPass.balance_interval`);
  * equality at time `t` holds iff `∂ₜA(t) = 0`, i.e. iff the stationary equation holds.

  No sign conditions on `r, a, b, β` are needed.
* Real-gradient normalisation:
  * `∇_ℝE = 2 δE/δĀ`, which is unique (`BandPass.real_gradient`);
  * for `F = E/2` (`BandPass.halfEnergy`): `∇_ℝF = δE/δĀ`, `∂ₜA = −∇_ℝF` and `dF/dt = −‖∂ₜA‖²`
    (`BandPass.half_gradient`, `BandPass.half_flow`).
* Centred Swift–Hohenberg form, with `k⋆² = a/(2b)` and `μ = r + a²/(4b)`:
  * `r − aΔ − bΔ² = μ − b(Δ + k⋆²)²` on `H⁴` (`BandPass.centred_operator`,
    `BandPass.rhs_centred`, `BandPass.wirt_centred`);
  * periodic integration by parts (`BandPass.re_integral_lap_conj`, `BandPass.norm_shiftOp_sq`);
  * the exact identity `E_SH = E` on `H²` (`BandPass.energySH_eq`) and the centred first variation
    (`BandPass.centred_first_variation`).
* Preferred Fourier shell:
  * the linearisation at `A = 0` (`BandPass.linearization`) acts diagonally with symbol
    `λ(|ξ_n|²)`, where `λ(q) = r + aq − bq² = μ − b(q − k⋆²)²` (`BandPass.coef_linear`,
    `BandPass.lamq_eq`);
  * `λ' = a − 2bq` and `λ'' = −2b` (`BandPass.deriv_lamq`, `BandPass.deriv2_lamq`);
  * the unique maximiser is `q = k⋆²`, i.e. the sphere `|k| = k⋆ > 0` (`BandPass.preferred_shell`);
  * the growing band is `|q − k⋆²| < √(μ/b)` (`BandPass.growing_band`);
  * ultraviolet damping (`BandPass.uv_damping`); with the opposite sign `+b(Δ + k⋆²)²` high
    frequencies would grow instead (`BandPass.opposite_sign_growth`);
  * a fastest lattice mode exists (`BandPass.lattice_maximiser`), but a lattice mode on the shell
    need not (`BandPass.shell_not_attained`);
  * the nonlinear flow does not preserve finite shells (`BandPass.shell_not_invariant`).
* For `β > 0`:
  * `E[A] ≥ −(|Ω|/(2β)) max{μ,0}²` on `H²` (`BandPass.energy_lower`);
  * a global solution satisfies `∫₀^∞ ‖∂ₜA‖² dt ≤ ½ (E[A(0)] + (|Ω|/(2β)) max{μ,0}²)`
    (`BandPass.finite_dissipation`).
* Time-periodic solutions are stationary (`BandPass.periodic_stationary`).

The manuscript's limitations carry over: nothing here asserts global well-posedness, convergence
to a unique equilibrium, or a physical derivation of the amplitude equation.
-/

open Filter Topology Complex InnerProductSpace MeasureTheory Set
open scoped ComplexConjugate Real ENNReal

noncomputable section

namespace ReyesMath
namespace BandPass

open TorusL2

variable {L : ℝ} [hL : Fact (0 < L)] {d : ℕ}

/-! ### Frequencies -/

variable (L) in
/-- The wave vector `ξ_n = (2π/L) n` of the mode `e_n` on `𝕋_L^d`. -/
def xi (n : Fin d → ℤ) (j : Fin d) : ℝ := 2 * π / L * n j

variable (L) in
/-- `|ξ_n|²`. -/
def xi2 (n : Fin d → ℤ) : ℝ := ∑ j, xi L n j ^ 2

variable (L) in
/-- The weight `w_n = 1 + |ξ_n|²`. -/
def wt (n : Fin d → ℤ) : ℝ := 1 + xi2 L n

omit hL in
theorem xi2_nonneg (n : Fin d → ℤ) : 0 ≤ xi2 L n := Finset.sum_nonneg fun _ _ => sq_nonneg _

omit hL in
theorem wt_pos (n : Fin d → ℤ) : 0 < wt L n := by
  have := xi2_nonneg (L := L) n; unfold wt; linarith

omit hL in
theorem one_le_wt (n : Fin d → ℤ) : 1 ≤ wt L n := by
  have := xi2_nonneg (L := L) n; unfold wt; linarith

omit hL in
theorem xi_sq_le_xi2 (n : Fin d → ℤ) (j : Fin d) : xi L n j ^ 2 ≤ xi2 L n :=
  Finset.single_le_sum (f := fun j => xi L n j ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ j)

omit hL in
theorem xi2_le_wt (n : Fin d → ℤ) : xi2 L n ≤ wt L n := by unfold wt; linarith

/-! ### Fourier multipliers with unbounded symbols -/

open Classical in
/-- The Fourier multiplier `A ↦ Σ s(n) Â_n e_n`, defined when `(s(n)Â_n) ∈ ℓ²` (and `0`
otherwise). -/
def pmul (s : (Fin d → ℤ) → ℂ) (A : L2 L d) : L2 L d :=
  if h : Memℓp (fun n => s n * coef A n) 2 then (basis L d).repr.symm ⟨_, h⟩ else 0

theorem coef_pmul {s : (Fin d → ℤ) → ℂ} {A : L2 L d} (h : Memℓp (fun n => s n * coef A n) 2)
    (n : Fin d → ℤ) : coef (pmul s A) n = s n * coef A n := by
  classical
  rw [pmul, dif_pos h, ← repr_eq_coef]
  simp

theorem memℓp_two_iff {f : (Fin d → ℤ) → ℂ} : Memℓp f 2 ↔ Summable fun n => ‖f n‖ ^ 2 := by
  rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
  simp

/-- `∂_j A`, the multiplier with symbol `i ξ_{n,j}`. -/
def dpart (j : Fin d) (A : L2 L d) : L2 L d := pmul (fun n => Complex.I * xi L n j) A

/-- `ΔA`, the multiplier with symbol `−|ξ_n|²`. -/
def lap (A : L2 L d) : L2 L d := pmul (fun n => -(xi2 L n : ℂ)) A

/-- Membership in `H^{2k}(𝕋_L^d)`: `Σ w_n^{2k} |Â_n|² < ∞`. -/
def InH (k : ℕ) (A : L2 L d) : Prop := Summable fun n => wt L n ^ (2 * k) * ‖coef A n‖ ^ 2

/-! ### Consistency with classical derivatives -/

/-- The mode `e_n` lifted to `ℝ^d`: `t ↦ exp(i ξ_n · t)`. -/
theorem emode_lift (n : Fin d → ℤ) (t : Fin d → ℝ) :
    emode (L := L) n (fun i => (t i : AddCircle L)) =
      Complex.exp (Complex.I * ∑ i, (xi L n i : ℂ) * t i) := by
  rw [emode_coe]; congr 1
  have : (L : ℂ) ≠ 0 := by exact_mod_cast hL.out.ne'
  simp only [xi]; push_cast
  rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  field_simp

/-- The classical partial derivative of a lifted mode: `∂_j e_n = i ξ_{n,j} e_n`. -/
theorem hasDerivAt_emode (n : Fin d → ℤ) (t : Fin d → ℝ) (j : Fin d) :
    HasDerivAt (fun s : ℝ => emode (L := L) n (fun i => ((Function.update t j s i : ℝ) : AddCircle L)))
      (Complex.I * xi L n j * emode (L := L) n (fun i => (t i : AddCircle L))) (t j) := by
  simp only [emode_lift]
  have h : HasDerivAt (fun s : ℝ => Complex.I * ∑ i, (xi L n i : ℂ) * (Function.update t j s i : ℝ))
      (Complex.I * (xi L n j : ℂ)) (t j) := by
    have : (fun s : ℝ => Complex.I * ∑ i, (xi L n i : ℂ) * (Function.update t j s i : ℝ)) =
        fun s : ℝ => Complex.I * ((xi L n j : ℂ) * s +
          ∑ i ∈ Finset.univ.erase j, (xi L n i : ℂ) * t i) := by
      funext s
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
      congr 2
      · simp
      · refine Finset.sum_congr rfl fun i hi => ?_
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
    rw [this]
    have h1 : HasDerivAt (fun s : ℝ => ((s : ℝ) : ℂ)) 1 (t j) := Complex.ofRealCLM.hasDerivAt
    simpa using ((h1.const_mul (xi L n j : ℂ)).add_const
      (∑ i ∈ Finset.univ.erase j, (xi L n i : ℂ) * t i)).const_mul Complex.I
  have h2 := h.cexp
  convert h2 using 1
  · rw [Function.update_eq_self]; ring

theorem dpart_basis (j : Fin d) (n : Fin d → ℤ) :
    dpart j (basis L d n) = (Complex.I * xi L n j) • basis L d n := by
  have hm : Memℓp (fun m => Complex.I * xi L m j * coef (basis L d n) m) 2 := by
    rw [memℓp_two_iff]
    classical
    refine summable_of_ne_finset_zero (s := {n}) fun m hm => ?_
    rw [coef_basis, if_neg (by simpa using hm), mul_zero, norm_zero, zero_pow two_ne_zero]
  apply ext_coef; intro m
  rw [dpart, coef_pmul hm, coef_smul, coef_basis]
  split_ifs with h
  · rw [h]
  · simp

theorem lap_basis (n : Fin d → ℤ) : lap (basis L d n) = (-(xi2 L n : ℂ)) • basis L d n := by
  have hm : Memℓp (fun m => -(xi2 L m : ℂ) * coef (basis L d n) m) 2 := by
    rw [memℓp_two_iff]
    classical
    refine summable_of_ne_finset_zero (s := {n}) fun m hm => ?_
    rw [coef_basis, if_neg (by simpa using hm), mul_zero, norm_zero, zero_pow two_ne_zero]
  apply ext_coef; intro m
  rw [lap, coef_pmul hm, coef_smul, coef_basis]
  split_ifs with h
  · rw [h]
  · simp


/-! ### `H^{2k}` as weighted `ℓ²` -/

variable (d) in
/-- The coefficient space `ℓ²(ℤ^d)`. -/
abbrev ell2 := ℓ²(Fin d → ℤ, ℂ)

theorem norm_sq_ell2 (c : ell2 d) : ‖c‖ ^ 2 = ∑' n, ‖c n‖ ^ 2 := by
  have := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) c
  simpa using this

theorem hasSum_sq_ell2 (c : ell2 d) : HasSum (fun n => ‖c n‖ ^ 2) (‖c‖ ^ 2) := by
  rw [norm_sq_ell2]
  exact (memℓp_two_iff.1 (lp.memℓp c)).hasSum

/-- The diagonal operator with bounded symbol `m` on `ℓ²`. -/
def diagL (m : (Fin d → ℤ) → ℂ) {C : ℝ} (hm : ∀ n, ‖m n‖ ≤ C) : ell2 d →L[ℂ] ell2 d :=
  LinearMap.mkContinuous
    { toFun := fun c => ⟨fun n => m n * c n, memℓp_mul hm c⟩
      map_add' := fun c c' => by ext n; simp [mul_add]
      map_smul' := fun z c => by ext n; simp [mul_left_comm] }
    C (fun c => by
      have hC : 0 ≤ C := (norm_nonneg _).trans (hm 0)
      refine lp.norm_le_of_tsum_le (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (by positivity) ?_
      simp only [LinearMap.coe_mk, AddHom.coe_mk, ENNReal.toReal_ofNat]
      have h1 := (memℓp_two_iff.1 (lp.memℓp c)).mul_left (C ^ 2)
      calc ∑' n, ‖m n * c n‖ ^ (2 : ℝ) = ∑' n, ‖m n * c n‖ ^ 2 := by
            congr 1; funext n; exact Real.rpow_natCast _ 2
        _ ≤ ∑' n, C ^ 2 * ‖c n‖ ^ 2 := by
            refine Summable.tsum_le_tsum (fun n => ?_) ?_ h1
            · rw [norm_mul, mul_pow]
              exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hm n) 2)
                (by positivity)
            · exact (memℓp_two_iff.1 (memℓp_mul hm c))
        _ = (C * ‖c‖) ^ (2 : ℝ) := by
            rw [tsum_mul_left, ← norm_sq_ell2, Real.rpow_two, mul_pow])

theorem diagL_apply (m : (Fin d → ℤ) → ℂ) {C : ℝ} (hm : ∀ n, ‖m n‖ ≤ C) (c : ell2 d)
    (n : Fin d → ℤ) : diagL m hm c n = m n * c n := rfl

/-- `L² ≃ ℓ²` (coefficients), as a continuous linear map `ℓ² → L²`. -/
def ofCoef : ell2 d →L[ℂ] L2 L d :=
  (basis L d).repr.symm.toContinuousLinearEquiv.toContinuousLinearMap

theorem coef_ofCoef (c : ell2 d) (n : Fin d → ℤ) : coef (ofCoef (L := L) c) n = c n := by
  rw [← repr_eq_coef, ofCoef]
  simp

omit hL in
theorem norm_wt_inv_pow_le (k : ℕ) (n : Fin d → ℤ) : ‖((wt L n)⁻¹ : ℂ) ^ k‖ ≤ 1 := by
  rw [norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (wt_pos n)]
  exact pow_le_one₀ (inv_pos.2 (wt_pos n)).le (inv_le_one_of_one_le₀ (one_le_wt n))

variable (L) in
/-- The realisation `ι_k : ℓ² → L²`, `c ↦ Σ c_n w_n^{-k} e_n`: an isometry of `ℓ²` onto
`H^{2k}(𝕋_L^d)` with the norm `‖A‖²_{H^{2k}} = Σ w_n^{2k}|Â_n|²`. -/
def iota (k : ℕ) : ell2 d →L[ℂ] L2 L d :=
  ofCoef ∘L diagL (fun n => ((wt L n)⁻¹ : ℂ) ^ k) (norm_wt_inv_pow_le k)

theorem coef_iota (k : ℕ) (c : ell2 d) (n : Fin d → ℤ) :
    coef (iota L k c) n = ((wt L n)⁻¹ : ℂ) ^ k * c n := by
  rw [iota, ContinuousLinearMap.comp_apply, coef_ofCoef, diagL_apply]

omit hL in
theorem wt_pow_mul_inv_pow (k : ℕ) (n : Fin d → ℤ) :
    ((wt L n : ℂ)) ^ k * ((wt L n)⁻¹ : ℂ) ^ k = 1 := by
  rw [← mul_pow, mul_inv_cancel₀ (by exact_mod_cast (wt_pos n).ne'), one_pow]

omit hL in
theorem wt_pow_two_mul_inv (k : ℕ) (n : Fin d → ℤ) :
    wt L n ^ (2 * k) * ((wt L n)⁻¹ ^ k) ^ 2 = 1 := by
  rw [← pow_mul, mul_comm k 2, ← mul_pow, mul_inv_cancel₀ (wt_pos n).ne', one_pow]

theorem norm_coef_iota_sq (k : ℕ) (c : ell2 d) (n : Fin d → ℤ) :
    wt L n ^ (2 * k) * ‖coef (iota L k c) n‖ ^ 2 = ‖c n‖ ^ 2 := by
  rw [coef_iota, norm_mul, norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (wt_pos n), mul_pow, ← mul_assoc, wt_pow_two_mul_inv, one_mul]

/-- `H^{2k}` is exactly the range of `ι_k`. -/
theorem inH_iff (k : ℕ) (A : L2 L d) : InH k A ↔ ∃ c : ell2 d, A = iota L k c := by
  constructor
  · intro h
    have hm : Memℓp (fun n => (wt L n : ℂ) ^ k * coef A n) 2 := by
      rw [memℓp_two_iff]
      refine h.congr fun n => ?_
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (wt_pos n),
        mul_pow, ← pow_mul, mul_comm k 2]
    refine ⟨⟨_, hm⟩, ext_coef fun n => ?_⟩
    rw [coef_iota]
    show coef A n = ((wt L n)⁻¹ : ℂ) ^ k * ((wt L n : ℂ) ^ k * coef A n)
    rw [← mul_assoc, mul_comm (((wt L n)⁻¹ : ℂ) ^ k), wt_pow_mul_inv_pow, one_mul]
  · rintro ⟨c, rfl⟩
    exact (memℓp_two_iff.1 (lp.memℓp c)).congr fun n => (norm_coef_iota_sq k c n).symm

/-- The `H^{2k}` norm of `ι_k c` is `‖c‖`. -/
theorem norm_H_iota (k : ℕ) (c : ell2 d) :
    HasSum (fun n => wt L n ^ (2 * k) * ‖coef (iota L k c) n‖ ^ 2) (‖c‖ ^ 2) := by
  exact (hasSum_sq_ell2 c).congr_fun fun n => norm_coef_iota_sq k c n

omit hL in
theorem opS_bound (k : ℕ) {s : (Fin d → ℤ) → ℂ} {C : ℝ} (hs : ∀ n, ‖s n‖ ≤ C * wt L n ^ k) :
    ∀ n, ‖s n * ((wt L n)⁻¹ : ℂ) ^ k‖ ≤ C := fun n => by
  rw [norm_mul, norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (wt_pos n)]
  calc ‖s n‖ * ((wt L n)⁻¹) ^ k ≤ C * wt L n ^ k * (wt L n)⁻¹ ^ k :=
        mul_le_mul_of_nonneg_right (hs n) (by have := wt_pos (L := L) n; positivity)
    _ = C := by rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ (wt_pos n).ne', one_pow, mul_one]

/-- Multipliers on `H^{2k}`: for `|s(n)| ≤ C w_n^k`, `c ↦ Σ s(n) w_n^{-k} c_n e_n`. -/
def opS (k : ℕ) (s : (Fin d → ℤ) → ℂ) {C : ℝ} (hs : ∀ n, ‖s n‖ ≤ C * wt L n ^ k) :
    ell2 d →L[ℂ] L2 L d :=
  ofCoef ∘L diagL (fun n => s n * ((wt L n)⁻¹ : ℂ) ^ k) (opS_bound k hs)

theorem coef_opS (k : ℕ) (s : (Fin d → ℤ) → ℂ) {C : ℝ} (hs : ∀ n, ‖s n‖ ≤ C * wt L n ^ k)
    (c : ell2 d) (n : Fin d → ℤ) : coef (opS k s hs c) n = s n * ((wt L n)⁻¹ : ℂ) ^ k * c n := by
  rw [opS, ContinuousLinearMap.comp_apply, coef_ofCoef, diagL_apply]

theorem memℓp_pmul_iota (k : ℕ) {s : (Fin d → ℤ) → ℂ} {C : ℝ}
    (hs : ∀ n, ‖s n‖ ≤ C * wt L n ^ k) (c : ell2 d) :
    Memℓp (fun n => s n * coef (iota L k c) n) 2 := by
  have := lp.memℓp (diagL (fun n => s n * ((wt L n)⁻¹ : ℂ) ^ k) (opS_bound k hs) c)
  convert this using 1
  funext n; rw [coef_iota, diagL_apply]; ring

/-- The multiplier `pmul s` agrees with `opS` on `H^{2k}`. -/
theorem pmul_iota (k : ℕ) (s : (Fin d → ℤ) → ℂ) {C : ℝ} (hs : ∀ n, ‖s n‖ ≤ C * wt L n ^ k)
    (c : ell2 d) : pmul s (iota L k c) = opS k s hs c := by
  apply ext_coef; intro n
  rw [coef_pmul (memℓp_pmul_iota k hs c), coef_iota, coef_opS]; ring


/-! ### The lattice sum `Σ w_n^{-2}` for `d ≤ 3` -/

theorem summable_one_add_sq_rpow :
    Summable fun m : ℤ => (1 + (m : ℝ) ^ 2) ^ (-(2 / 3 : ℝ)) := by
  refine Summable.of_norm_bounded_eventually (Real.summable_abs_int_rpow (b := 4 / 3) (by norm_num)) ?_
  have : {(0 : ℤ)}ᶜ ∈ cofinite := (Set.finite_singleton 0).compl_mem_cofinite
  filter_upwards [this] with m hm
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have hpos : 0 < |(m : ℝ)| := abs_pos.2 hm0
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  calc (1 + (m : ℝ) ^ 2) ^ (-(2 / 3 : ℝ)) ≤ (|(m : ℝ)| ^ (2 : ℝ)) ^ (-(2 / 3 : ℝ)) := by
        refine Real.rpow_le_rpow_of_exponent_nonpos (Real.rpow_pos_of_pos hpos _) ?_ (by norm_num)
        rw [Real.rpow_two, sq_abs]; linarith
    _ = |(m : ℝ)| ^ (-(4 / 3 : ℝ)) := by
        rw [← Real.rpow_mul (abs_nonneg _)]; norm_num

omit hL in
theorem summable_pi_prod {f : ℤ → ℝ} (hf0 : ∀ m, 0 ≤ f m) (hf : Summable f) (k : ℕ) :
    Summable fun n : Fin k → ℤ => ∏ i, f (n i) := by
  induction k with
  | zero => exact (hasSum_unique _).summable
  | succ k ih =>
    have hf' : 0 ≤ f := fun m => hf0 m
    have hg' : 0 ≤ fun n : Fin k → ℤ => ∏ i, f (n i) := fun n => Finset.prod_nonneg fun i _ => hf0 _
    have h2 := Summable.mul_of_nonneg hf ih hf' hg'
    have e : ∀ p : ℤ × (Fin k → ℤ),
        (∏ i, f ((Fin.consEquiv (fun _ : Fin (k + 1) => ℤ) p) i)) = f p.1 * ∏ i, f (p.2 i) := by
      intro p
      rw [Fin.prod_univ_succ]
      rfl
    rw [← (Fin.consEquiv (fun _ : Fin (k + 1) => ℤ)).summable_iff]
    exact h2.congr fun p => (e p).symm

omit hL in
theorem prod_rpow_le {d : ℕ} (hd : d ≤ 3) (n : Fin d → ℤ) :
    (1 + ∑ j, ((n j : ℝ)) ^ 2) ^ (-(2 : ℝ)) ≤ ∏ i, (1 + ((n i : ℝ)) ^ 2) ^ (-(2 / 3 : ℝ)) := by
  set N : ℝ := 1 + ∑ j, ((n j : ℝ)) ^ 2 with hN
  have hN1 : 1 ≤ N := by
    have : 0 ≤ ∑ j, ((n j : ℝ)) ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
    linarith
  have hle : ∀ i, 1 + ((n i : ℝ)) ^ 2 ≤ N := fun i => by
    have := Finset.single_le_sum (f := fun j => ((n j : ℝ)) ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ i)
    simp only at this; linarith
  have h1 : ∏ i, (1 + ((n i : ℝ)) ^ 2) ^ (2 / 3 : ℝ) ≤ N ^ (2 : ℝ) := by
    calc ∏ i, (1 + ((n i : ℝ)) ^ 2) ^ (2 / 3 : ℝ) ≤ ∏ _i : Fin d, N ^ (2 / 3 : ℝ) :=
          Finset.prod_le_prod (fun i _ => by positivity)
            (fun i _ => Real.rpow_le_rpow (by positivity) (hle i) (by norm_num))
      _ = N ^ ((2 / 3 : ℝ) * d) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.rpow_natCast,
            ← Real.rpow_mul (by linarith)]
      _ ≤ N ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 (by
          have : (d : ℝ) ≤ 3 := by exact_mod_cast hd
          linarith)
  have h2 : 0 < ∏ i, (1 + ((n i : ℝ)) ^ 2) ^ (2 / 3 : ℝ) :=
    Finset.prod_pos fun i _ => by positivity
  have e : ∏ i, (1 + ((n i : ℝ)) ^ 2) ^ (-(2 / 3 : ℝ)) =
      (∏ i, (1 + ((n i : ℝ)) ^ 2) ^ (2 / 3 : ℝ))⁻¹ := by
    rw [← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl fun i _ => Real.rpow_neg (by positivity) _
  rw [Real.rpow_neg (by linarith), e]
  exact inv_anti₀ h2 h1


/-- For `d ≤ 3`, `Σ_{n ∈ ℤ^d} w_n^{-2} < ∞`. -/
theorem summable_wt_inv_sq (hd : d ≤ 3) : Summable fun n : Fin d → ℤ => ((wt L n)⁻¹) ^ 2 := by
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℝ, c₀ = min 1 ((2 * π / L) ^ 2) := ⟨_, rfl⟩
  have hπL : 0 < 2 * π / L := div_pos Real.two_pi_pos hL.out
  have hc₀pos : 0 < c₀ := by rw [hc₀]; exact lt_min one_pos (by positivity)
  have hwt : ∀ n : Fin d → ℤ, c₀ * (1 + ∑ j, ((n j : ℝ)) ^ 2) ≤ wt L n := by
    intro n
    have h1 : c₀ ≤ 1 := hc₀ ▸ min_le_left _ _
    have h2 : c₀ ≤ (2 * π / L) ^ 2 := hc₀ ▸ min_le_right _ _
    have hs : 0 ≤ ∑ j, ((n j : ℝ)) ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
    have e : xi2 L n = (2 * π / L) ^ 2 * ∑ j, ((n j : ℝ)) ^ 2 := by
      rw [xi2, Finset.mul_sum]; simp only [xi]; congr 1; funext j; ring
    rw [wt, e, mul_add, mul_one]
    have := mul_le_mul_of_nonneg_right h2 hs
    linarith
  have hsum := (summable_pi_prod (fun m => Real.rpow_nonneg (by positivity) _)
    summable_one_add_sq_rpow d).mul_left (c₀⁻¹ ^ 2)
  refine Summable.of_nonneg_of_le (fun n => by have := wt_pos (L := L) n; positivity)
    (fun n => ?_) hsum
  have hN : 0 < 1 + ∑ j, ((n j : ℝ)) ^ 2 := by
    have : 0 ≤ ∑ j, ((n j : ℝ)) ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
    linarith
  calc ((wt L n)⁻¹) ^ 2 ≤ ((c₀ * (1 + ∑ j, ((n j : ℝ)) ^ 2))⁻¹) ^ 2 :=
        pow_le_pow_left₀ (inv_pos.2 (wt_pos n)).le (inv_anti₀ (by positivity) (hwt n)) 2
    _ = c₀⁻¹ ^ 2 * (1 + ∑ j, ((n j : ℝ)) ^ 2) ^ (-(2 : ℝ)) := by
        rw [Real.rpow_neg hN.le, Real.rpow_two, mul_inv, mul_pow]
        simp only [inv_pow]
    _ ≤ c₀⁻¹ ^ 2 * ∏ i, (1 + ((n i : ℝ)) ^ 2) ^ (-(2 / 3 : ℝ)) :=
        mul_le_mul_of_nonneg_left (prod_rpow_le hd n) (by positivity)

/-- Cauchy–Schwarz against the weights: `Σ |c_n| w_n^{-1} ≤ ‖c‖ (Σ w_n^{-2})^{1/2}`. -/
theorem tsum_norm_mul_wt_inv (hd : d ≤ 3) (c : ell2 d) :
    Summable (fun n => ‖c n‖ * (wt L n)⁻¹) ∧
      ∑' n, ‖c n‖ * (wt L n)⁻¹ ≤ ‖c‖ * √(∑' n : Fin d → ℤ, ((wt L n)⁻¹) ^ 2) := by
  have hc2 : Summable fun n => ‖c n‖ ^ (2 : ℝ) := by
    simpa [Real.rpow_two] using memℓp_two_iff.1 (lp.memℓp c)
  have hw2 : Summable fun n : Fin d → ℤ => ((wt L n)⁻¹) ^ (2 : ℝ) := by
    simpa [Real.rpow_two] using summable_wt_inv_sq (L := L) hd
  have h := Real.inner_le_Lp_mul_Lq_tsum_of_nonneg Real.HolderConjugate.two_two (fun n => norm_nonneg (c n))
    (fun n => (inv_pos.2 (wt_pos (L := L) n)).le) hc2 hw2
  refine ⟨h.1, h.2.trans (le_of_eq ?_)⟩
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
  simp only [Real.rpow_two]
  rw [← norm_sq_ell2, Real.sqrt_sq (norm_nonneg _)]

omit hL in
theorem norm_emode_apply (n : Fin d → ℤ) (x : Tor L d) : ‖emode n x‖ = 1 := by
  simp only [emode, ContinuousMap.coe_mk, Complex.norm_prod, fourier_apply, Circle.norm_coe,
    Finset.prod_const_one]

theorem norm_emode_le (n : Fin d → ℤ) : ‖emode (L := L) n‖ ≤ 1 :=
  (ContinuousMap.norm_le _ zero_le_one).2 fun x => (norm_emode_apply n x).le

theorem summable_Phi_terms (hd : d ≤ 3) (c : ell2 d) :
    Summable fun n => (c n * ((wt L n)⁻¹ : ℂ)) • emode (L := L) n := by
  refine Summable.of_norm_bounded (tsum_norm_mul_wt_inv (L := L) hd c).1 fun n => ?_
  rw [norm_smul, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (wt_pos n)]
  have := norm_emode_le (L := L) n
  have h0 : 0 ≤ ‖c n‖ * (wt L n)⁻¹ := by have := wt_pos (L := L) n; positivity
  nlinarith

variable (L) in
/-- The continuous representative of `H²` functions for `d ≤ 3`:
`Φ c = Σ_n c_n w_n^{-1} e_n`, uniformly convergent (the Sobolev embedding `H² ⊂ C(𝕋^d)`). -/
def Phi (hd : d ≤ 3) : ell2 d →L[ℂ] C(Tor L d, ℂ) :=
  LinearMap.mkContinuous
    { toFun := fun c => ∑' n, (c n * ((wt L n)⁻¹ : ℂ)) • emode (L := L) n
      map_add' := fun c c' => by
        rw [← (summable_Phi_terms hd c).tsum_add (summable_Phi_terms hd c')]
        congr 1; funext n
        rw [lp.coeFn_add, Pi.add_apply, add_mul, add_smul]
      map_smul' := fun z c => by
        rw [RingHom.id_apply, ← (summable_Phi_terms hd c).tsum_const_smul z]
        congr 1; funext n
        rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_assoc, smul_smul] }
    (√(∑' n : Fin d → ℤ, ((wt L n)⁻¹) ^ 2)) (fun c => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      have h1 := norm_tsum_le_tsum_norm (f := fun n => (c n * ((wt L n)⁻¹ : ℂ)) • emode (L := L) n)
        (Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
          (tsum_norm_mul_wt_inv (L := L) hd c).1)
      · refine h1.trans ((Summable.tsum_le_tsum (fun n => ?_) (Summable.of_nonneg_of_le
          (fun n => norm_nonneg _) (fun n => ?_) (tsum_norm_mul_wt_inv (L := L) hd c).1)
          (tsum_norm_mul_wt_inv (L := L) hd c).1).trans ?_)
        · rw [norm_smul, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (wt_pos n)]
          have := norm_emode_le (L := L) n
          have h0 : 0 ≤ ‖c n‖ * (wt L n)⁻¹ := by have := wt_pos (L := L) n; positivity
          nlinarith
        · rw [norm_smul, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (wt_pos n)]
          have := norm_emode_le (L := L) n
          have h0 : 0 ≤ ‖c n‖ * (wt L n)⁻¹ := by have := wt_pos (L := L) n; positivity
          nlinarith
        · rw [mul_comm]; exact (tsum_norm_mul_wt_inv (L := L) hd c).2
      · rw [norm_smul, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (wt_pos n)]
        have := norm_emode_le (L := L) n
        have h0 : 0 ≤ ‖c n‖ * (wt L n)⁻¹ := by have := wt_pos (L := L) n; positivity
        nlinarith)

theorem hasSum_Phi (hd : d ≤ 3) (c : ell2 d) :
    HasSum (fun n => (c n * ((wt L n)⁻¹ : ℂ)) • emode (L := L) n) (Phi L hd c) :=
  (summable_Phi_terms hd c).hasSum

/-- The `L²` class of `Φ c` is `ι₁ c`. -/
theorem toLp_Phi (hd : d ≤ 3) (c : ell2 d) :
    ContinuousMap.toLp (E := ℂ) 2 (μ L d) ℂ (Phi L hd c) = iota L 1 c := by
  have h1 := (hasSum_Phi hd c).mapL (ContinuousMap.toLp (E := ℂ) 2 (μ L d) ℂ)
  have h2 := (basis L d).hasSum_repr_symm (diagL (fun n => ((wt L n)⁻¹ : ℂ) ^ 1)
    (norm_wt_inv_pow_le 1) c)
  refine h1.unique (h2.congr_fun fun n => ?_)
  rw [map_smul, ← basis_eq_toLp, diagL_apply, pow_one, mul_comm]

theorem iota_ae_eq_Phi (hd : d ≤ 3) (c : ell2 d) :
    (iota L 1 c : Tor L d → ℂ) =ᵐ[μ L d] Phi L hd c := by
  rw [← toLp_Phi hd c]
  exact ContinuousMap.coeFn_toLp _ _

/-- The uniform bound `‖Φ c‖_∞ ≤ K ‖c‖_{H²}`. -/
theorem norm_Phi_le (hd : d ≤ 3) (c : ell2 d) :
    ‖Phi L hd c‖ ≤ √(∑' n : Fin d → ℤ, ((wt L n)⁻¹) ^ 2) * ‖c‖ :=
  (Phi L hd).le_of_opNorm_le (LinearMap.mkContinuous_norm_le _ (Real.sqrt_nonneg _) _) c


/-! ### The quartic functional on `C(𝕋^d)` and its Fréchet derivative -/

theorem integrable_of_continuous {g : Tor L d → ℝ} (hg : Continuous g) : Integrable g (μ L d) :=
  hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem integrable_of_continuous_c {g : Tor L d → ℂ} (hg : Continuous g) : Integrable g (μ L d) :=
  hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem integral_le_of_le_const {g : Tor L d → ℝ} {C : ℝ} (h : ∀ x, ‖g x‖ ≤ C) :
    ‖∫ x, g x ∂(μ L d)‖ ≤ C := by
  have := norm_integral_le_of_norm_le_const (μ := μ L d) (Eventually.of_forall h)
  simpa using this

omit hL in
theorem continuous_DN_integrand (F G : C(Tor L d, ℂ)) :
    Continuous fun x => ‖F x‖ ^ 2 * (conj (F x) * G x).re :=
  ((continuous_norm.comp F.continuous).pow 2).mul
    (Complex.continuous_re.comp ((Complex.continuous_conj.comp F.continuous).mul G.continuous))

omit hL in
theorem continuous_R_integrand (F G : C(Tor L d, ℂ)) :
    Continuous fun x => 2 * ‖F x‖ ^ 2 * ‖G x‖ ^ 2 + (2 * (conj (F x) * G x).re + ‖G x‖ ^ 2) ^ 2 :=
  ((continuous_const.mul ((continuous_norm.comp F.continuous).pow 2)).mul
    ((continuous_norm.comp G.continuous).pow 2)).add
    (((continuous_const.mul (Complex.continuous_re.comp
      ((Complex.continuous_conj.comp F.continuous).mul G.continuous))).add
      ((continuous_norm.comp G.continuous).pow 2)).pow 2)

/-- `N(F) = ⨍ |F|⁴`. -/
def Nq (F : C(Tor L d, ℂ)) : ℝ := ∫ x, ‖F x‖ ^ 4 ∂(μ L d)

/-- The real derivative `DN(F)G = 4 ⨍ |F|² Re(F̄ G)`. -/
def DNq (F : C(Tor L d, ℂ)) : C(Tor L d, ℂ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun G => 4 * ∫ x, ‖F x‖ ^ 2 * (conj (F x) * G x).re ∂(μ L d)
      map_add' := fun G G' => by
        rw [← mul_add, ← integral_add]
        · congr 2; funext x
          rw [ContinuousMap.add_apply, mul_add, Complex.add_re, mul_add]
        · exact integrable_of_continuous (continuous_DN_integrand F G)
        · exact integrable_of_continuous (continuous_DN_integrand F G')
      map_smul' := fun t G => by
        simp only [RingHom.id_apply, smul_eq_mul]
        rw [show (fun x => ‖F x‖ ^ 2 * (conj (F x) * (t • G) x).re) =
            fun x => t * (‖F x‖ ^ 2 * (conj (F x) * G x).re) from by
          funext x
          rw [ContinuousMap.smul_apply, Complex.real_smul, mul_left_comm, Complex.re_ofReal_mul]
          ring]
        rw [integral_const_mul]; ring }
    (4 * ‖F‖ ^ 3) (fun G => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, norm_mul, Real.norm_eq_abs, abs_of_pos
        (show (0 : ℝ) < 4 by norm_num)]
      have h := integral_le_of_le_const (L := L) (d := d)
        (g := fun x => ‖F x‖ ^ 2 * (conj (F x) * G x).re) (C := ‖F‖ ^ 3 * ‖G‖) fun x => by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity)]
          have h1 := ContinuousMap.norm_coe_le_norm F x
          have h2 := ContinuousMap.norm_coe_le_norm G x
          have h3 : |(conj (F x) * G x).re| ≤ ‖F x‖ * ‖G x‖ := by
            have := Complex.abs_re_le_norm (conj (F x) * G x)
            rwa [norm_mul, Complex.norm_conj] at this
          calc ‖F x‖ ^ 2 * |(conj (F x) * G x).re| ≤ ‖F x‖ ^ 2 * (‖F x‖ * ‖G x‖) :=
                mul_le_mul_of_nonneg_left h3 (by positivity)
            _ = ‖F x‖ ^ 3 * ‖G x‖ := by ring
            _ ≤ ‖F‖ ^ 3 * ‖G‖ := mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) h1 3) h2
                (norm_nonneg _) (by positivity)
      rw [Real.norm_eq_abs] at h
      nlinarith [abs_nonneg (∫ x, ‖F x‖ ^ 2 * (conj (F x) * G x).re ∂(μ L d))])

theorem DNq_apply (F G : C(Tor L d, ℂ)) :
    DNq F G = 4 * ∫ x, ‖F x‖ ^ 2 * (conj (F x) * G x).re ∂(μ L d) := rfl

/-- The pointwise identity `|z+w|⁴ − |z|⁴ − 4|z|² Re(z̄w) = 2|z|²|w|² + (2 Re(z̄w) + |w|²)²`. -/
theorem quartic_identity (z w : ℂ) :
    ‖z + w‖ ^ 4 - ‖z‖ ^ 4 - 4 * ‖z‖ ^ 2 * (conj z * w).re =
      2 * ‖z‖ ^ 2 * ‖w‖ ^ 2 + (2 * (conj z * w).re + ‖w‖ ^ 2) ^ 2 := by
  have h : ‖z + w‖ ^ 2 = ‖z‖ ^ 2 + 2 * (conj z * w).re + ‖w‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
      Complex.normSq_add]
    have : (z * conj w).re = (conj z * w).re := by
      rw [← Complex.conj_re (z * conj w), map_mul, Complex.conj_conj]
    rw [this]; ring
  have e4 : ‖z + w‖ ^ 4 = (‖z + w‖ ^ 2) ^ 2 := by ring
  rw [e4, h]; ring

theorem Nq_remainder (F G : C(Tor L d, ℂ)) :
    |Nq (F + G) - Nq F - DNq F G| ≤ ‖G‖ ^ 2 * (2 * ‖F‖ ^ 2 + (2 * ‖F‖ + ‖G‖) ^ 2) := by
  have e : Nq (F + G) - Nq F - DNq F G = ∫ x, (2 * ‖F x‖ ^ 2 * ‖G x‖ ^ 2 +
      (2 * (conj (F x) * G x).re + ‖G x‖ ^ 2) ^ 2) ∂(μ L d) := by
    rw [Nq, Nq, DNq_apply, ← integral_const_mul, ← integral_sub, ← integral_sub]
    · congr 1; funext x
      rw [ContinuousMap.add_apply, ← quartic_identity]; ring
    all_goals first
      | exact integrable_of_continuous (((continuous_norm.comp (F + G).continuous).pow 4).sub
          ((continuous_norm.comp F.continuous).pow 4))
      | exact integrable_of_continuous (continuous_const.mul (continuous_DN_integrand F G))
      | exact integrable_of_continuous ((continuous_norm.comp (F + G).continuous).pow 4)
      | exact integrable_of_continuous ((continuous_norm.comp F.continuous).pow 4)
  rw [e]
  refine (Real.norm_eq_abs _ ▸ integral_le_of_le_const (L := L) (d := d) fun x => ?_)
  have h1 := ContinuousMap.norm_coe_le_norm F x
  have h2 := ContinuousMap.norm_coe_le_norm G x
  have h3 : |(conj (F x) * G x).re| ≤ ‖F x‖ * ‖G x‖ := by
    have := Complex.abs_re_le_norm (conj (F x) * G x)
    rwa [norm_mul, Complex.norm_conj] at this
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h4 : (2 * (conj (F x) * G x).re + ‖G x‖ ^ 2) ^ 2 ≤ (2 * ‖F x‖ * ‖G x‖ + ‖G x‖ ^ 2) ^ 2 := by
    rw [← sq_abs]
    refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
    calc |2 * (conj (F x) * G x).re + ‖G x‖ ^ 2| ≤ |2 * (conj (F x) * G x).re| + |‖G x‖ ^ 2| :=
          abs_add _ _
      _ ≤ 2 * ‖F x‖ * ‖G x‖ + ‖G x‖ ^ 2 := by
          have e1 : |2 * (conj (F x) * G x).re| = 2 * |(conj (F x) * G x).re| := by
            rw [abs_mul, abs_two]
          have e2 : |‖G x‖ ^ 2| = ‖G x‖ ^ 2 := abs_of_nonneg (by positivity)
          rw [e1, e2]; nlinarith [h3]
  have hF0 := norm_nonneg (F x)
  have hG0 := norm_nonneg (G x)
  calc 2 * ‖F x‖ ^ 2 * ‖G x‖ ^ 2 + (2 * (conj (F x) * G x).re + ‖G x‖ ^ 2) ^ 2
      ≤ 2 * ‖F x‖ ^ 2 * ‖G x‖ ^ 2 + (2 * ‖F x‖ * ‖G x‖ + ‖G x‖ ^ 2) ^ 2 := by linarith
    _ = ‖G x‖ ^ 2 * (2 * ‖F x‖ ^ 2 + (2 * ‖F x‖ + ‖G x‖) ^ 2) := by ring
    _ ≤ ‖G‖ ^ 2 * (2 * ‖F‖ ^ 2 + (2 * ‖F‖ + ‖G‖) ^ 2) := by
        apply mul_le_mul (pow_le_pow_left₀ hG0 h2 2) _ (by positivity) (by positivity)
        have := pow_le_pow_left₀ hF0 h1 2
        have := pow_le_pow_left₀ (by positivity) (add_le_add (mul_le_mul_of_nonneg_left h1
          (by norm_num : (0 : ℝ) ≤ 2)) h2) 2
        linarith

/-- `N` is Fréchet differentiable on `C(𝕋^d)` with derivative `DN(F)`. -/
theorem hasFDerivAt_Nq (F : C(Tor L d, ℂ)) : HasFDerivAt (Nq (L := L) (d := d)) (DNq F) F := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  have hbig : (fun G => Nq (F + G) - Nq F - DNq F G) =O[𝓝 0] fun G => ‖G‖ ^ 2 := by
    refine Asymptotics.IsBigO.of_bound (2 * ‖F‖ ^ 2 + (2 * ‖F‖ + 1) ^ 2) ?_
    filter_upwards [Metric.ball_mem_nhds (0 : C(Tor L d, ℂ)) one_pos] with G hG
    rw [Metric.mem_ball, dist_zero_right] at hG
    rw [Real.norm_eq_abs, norm_pow, norm_norm]
    refine (Nq_remainder F G).trans ?_
    rw [mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    have := pow_le_pow_left₀ (by positivity) (add_le_add_left hG.le (2 * ‖F‖)) 2
    linarith
  exact hbig.trans_isLittleO (Asymptotics.isLittleO_norm_pow_id one_lt_two)


/-! ### `∇` and `Δ` on `H²`, and the energy -/

omit hL in
theorem abs_le_one_add_sq (x : ℝ) : |x| ≤ 1 + x ^ 2 := by
  nlinarith [sq_nonneg (|x| - 1), abs_nonneg x, sq_abs x]

omit hL in
theorem norm_I_xi_le (j : Fin d) (n : Fin d → ℤ) :
    ‖Complex.I * (xi L n j : ℂ)‖ ≤ 1 * wt L n ^ 1 := by
  rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, one_mul, pow_one]
  calc |xi L n j| ≤ 1 + xi L n j ^ 2 := abs_le_one_add_sq _
    _ ≤ wt L n := by have := xi_sq_le_xi2 (L := L) n j; unfold wt; linarith

omit hL in
theorem norm_xi2_le (n : Fin d → ℤ) : ‖-(xi2 L n : ℂ)‖ ≤ 1 * wt L n ^ 1 := by
  rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (xi2_nonneg n), one_mul,
    pow_one]
  exact xi2_le_wt n

variable (L) in
/-- `∂_j : H² → L²` in the `ℓ²` model. -/
def Dj (j : Fin d) : ell2 d →L[ℂ] L2 L d :=
  opS 1 (fun n => Complex.I * (xi L n j : ℂ)) (norm_I_xi_le j)

variable (L) in
/-- `Δ : H² → L²` in the `ℓ²` model. -/
def DL : ell2 d →L[ℂ] L2 L d := opS 1 (fun n => -(xi2 L n : ℂ)) norm_xi2_le

theorem dpart_iota (j : Fin d) (c : ell2 d) : dpart j (iota L 1 c) = Dj L j c :=
  pmul_iota 1 _ (norm_I_xi_le j) c

theorem lap_iota (c : ell2 d) : lap (iota L 1 c) = DL L c := pmul_iota 1 _ norm_xi2_le c

variable (r a b β : ℝ)

/-- The Swift–Hohenberg energy
`E[A] = ∫_Ω (−r|A|² − a|∇A|² + b|ΔA|² + (β/2)|A|⁴) dx` (Lebesgue measure on `Ω = 𝕋_L^d`). -/
def energy (A : L2 L d) : ℝ :=
  ∫ x, (-r * ‖A x‖ ^ 2 - a * ∑ j, ‖dpart j A x‖ ^ 2 + b * ‖lap A x‖ ^ 2 + β / 2 * ‖A x‖ ^ 4)

variable (L) in
/-- The energy in the `ℓ²` model of `H²`. -/
def Ec (hd : d ≤ 3) (c : ell2 d) : ℝ :=
  L ^ d * (-r * ‖iota L 1 c‖ ^ 2 - a * ∑ j, ‖Dj L j c‖ ^ 2 + b * ‖DL L c‖ ^ 2 +
    β / 2 * Nq (Phi L hd c))

theorem integral_volume_real (g : Tor L d → ℝ) : ∫ x, g x = L ^ d * ∫ x, g x ∂(μ L d) := by
  rw [volume_eq_smul_μ, integral_smul_measure, ENNReal.toReal_ofReal (pow_pos hL.out d).le,
    smul_eq_mul]

theorem integrable_norm_sq (A : L2 L d) : Integrable (fun x => ‖A x‖ ^ 2) (μ L d) :=
  (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable A)).1 (Lp.memLp A)

theorem integrable_norm_four_iota (hd : d ≤ 3) (c : ell2 d) :
    Integrable (fun x => ‖(iota L 1 c : L2 L d) x‖ ^ 4) (μ L d) := by
  refine (integrable_of_continuous ((continuous_norm.comp (Phi L hd c).continuous).pow 4)).congr ?_
  filter_upwards [iota_ae_eq_Phi (L := L) hd c] with x hx
  simp only [Function.comp_apply]; rw [hx]

/-- On `H²` the energy is the `ℓ²`-model expression. -/
theorem energy_iota (hd : d ≤ 3) (c : ell2 d) :
    energy r a b β (iota L 1 c) = Ec L r a b β hd c := by
  have h0 := integrable_norm_sq (iota L 1 c)
  have hj : ∀ j, Integrable (fun x => ‖(dpart j (iota L 1 c) : L2 L d) x‖ ^ 2) (μ L d) :=
    fun j => integrable_norm_sq _
  have hΔ := integrable_norm_sq (lap (iota L 1 c))
  have h4 := integrable_norm_four_iota (L := L) hd c
  have e0 : ∫ x, ‖(iota L 1 c : L2 L d) x‖ ^ 2 ∂(μ L d) = ‖iota L 1 c‖ ^ 2 :=
    (norm_sq_eq_integral _).symm
  have ej : ∀ j, ∫ x, ‖(dpart j (iota L 1 c) : L2 L d) x‖ ^ 2 ∂(μ L d) = ‖Dj L j c‖ ^ 2 :=
    fun j => by rw [← norm_sq_eq_integral, dpart_iota]
  have eΔ : ∫ x, ‖(lap (iota L 1 c) : L2 L d) x‖ ^ 2 ∂(μ L d) = ‖DL L c‖ ^ 2 := by
    rw [← norm_sq_eq_integral, lap_iota]
  have e4 : ∫ x, ‖(iota L 1 c : L2 L d) x‖ ^ 4 ∂(μ L d) = Nq (Phi L hd c) := by
    rw [Nq]
    refine integral_congr_ae ?_
    filter_upwards [iota_ae_eq_Phi (L := L) hd c] with x hx
    rw [hx]
  have hs : Integrable (fun x => ∑ j, ‖(dpart j (iota L 1 c) : L2 L d) x‖ ^ 2) (μ L d) :=
    integrable_finset_sum _ fun j _ => hj j
  have i1 := h0.const_mul (-r)
  have i2 := hs.const_mul a
  have i3 := hΔ.const_mul b
  have i4 := h4.const_mul (β / 2)
  have i12 : Integrable (fun x => -r * ‖(iota L 1 c : L2 L d) x‖ ^ 2 -
      a * ∑ j, ‖(dpart j (iota L 1 c) : L2 L d) x‖ ^ 2) (μ L d) := i1.sub i2
  have i123 : Integrable (fun x => -r * ‖(iota L 1 c : L2 L d) x‖ ^ 2 -
      a * ∑ j, ‖(dpart j (iota L 1 c) : L2 L d) x‖ ^ 2 +
      b * ‖(lap (iota L 1 c) : L2 L d) x‖ ^ 2) (μ L d) := i12.add i3
  rw [energy, integral_volume_real, Ec]
  congr 1
  rw [integral_add i123 i4, integral_add i12 i3, integral_sub i1 i2,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_finset_sum _ (fun j _ => hj j), e0, eΔ, e4]
  simp only [ej]


/-! ### Differentiating the energy along curves in `H²` -/

theorem hasDerivWithinAt_clm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : ell2 d →L[ℂ] E) {γ : ℝ → ell2 d} {γ' : ell2 d} {s : Set ℝ} {t : ℝ}
    (hγ : HasDerivWithinAt γ γ' s t) : HasDerivWithinAt (fun u => T (γ u)) (T γ') s t :=
  ((T.hasFDerivAt (x := γ t)).restrictScalars ℝ).comp_hasDerivWithinAt t hγ

/-- The derivative of the energy along a curve in `H²` (the chain rule in the `ℓ²` model). -/
theorem hasDerivWithinAt_Ec (hd : d ≤ 3) {γ : ℝ → ell2 d} {γ' : ell2 d} {s : Set ℝ} {t : ℝ}
    (hγ : HasDerivWithinAt γ γ' s t) :
    HasDerivWithinAt (fun u => Ec L r a b β hd (γ u))
      (L ^ d * (-r * (2 * inner ℝ (iota L 1 (γ t)) (iota L 1 γ')) -
        a * ∑ j, 2 * inner ℝ (Dj L j (γ t)) (Dj L j γ') +
        b * (2 * inner ℝ (DL L (γ t)) (DL L γ')) +
        β / 2 * DNq (Phi L hd (γ t)) (Phi L hd γ'))) s t := by
  have h0 := (hasDerivWithinAt_clm (iota L 1) hγ).norm_sq
  have hj : ∀ j ∈ (Finset.univ : Finset (Fin d)),
      HasDerivWithinAt (fun u => ‖Dj L j (γ u)‖ ^ 2) (2 * inner ℝ (Dj L j (γ t)) (Dj L j γ')) s t :=
    fun j _ => (hasDerivWithinAt_clm (Dj L j) hγ).norm_sq
  have hΔ := (hasDerivWithinAt_clm (DL L) hγ).norm_sq
  have hPhi := hasDerivWithinAt_clm (Phi L hd) hγ
  have h4 : HasDerivWithinAt (fun u => Nq (Phi L hd (γ u)))
      (DNq (Phi L hd (γ t)) (Phi L hd γ')) s t :=
    (hasFDerivAt_Nq (Phi L hd (γ t))).comp_hasDerivWithinAt (f := fun u => Phi L hd (γ u)) t hPhi
  have hsum : HasDerivWithinAt (fun u => ∑ j, ‖Dj L j (γ u)‖ ^ 2)
      (∑ j, 2 * inner ℝ (Dj L j (γ t)) (Dj L j γ')) s t := HasDerivWithinAt.fun_sum hj
  unfold Ec
  exact ((((h0.const_mul (-r)).sub (hsum.const_mul a)).add
    (hΔ.const_mul b)).add (h4.const_mul (β / 2))).const_mul (L ^ d)


/-! ### The Wirtinger derivative -/

open Classical in
/-- `|A|²A` as an element of `L²` (for `A ∈ H²`, `d ≤ 3`, it is square integrable). -/
def cubic (A : L2 L d) : L2 L d :=
  if h : MemLp (fun x => ((‖A x‖ ^ 2 : ℝ) : ℂ) * A x) 2 (μ L d) then h.toLp _ else 0

/-- The Wirtinger variational derivative `δE/δĀ = −rA + aΔA + bΔ²A + β|A|²A`. -/
def wirt (A : L2 L d) : L2 L d :=
  -(r : ℂ) • A + (a : ℂ) • lap A + (b : ℂ) • lap (lap A) + (β : ℂ) • cubic A

/-- The right-hand side `(r − aΔ − bΔ²)A − β|A|²A` of the amplitude equation. -/
def rhs (A : L2 L d) : L2 L d :=
  (r : ℂ) • A - (a : ℂ) • lap A - (b : ℂ) • lap (lap A) - (β : ℂ) • cubic A

/-- The amplitude equation is the negative Wirtinger gradient flow: `rhs = −δE/δĀ`. -/
theorem rhs_eq_neg_wirt (A : L2 L d) : rhs r a b β A = -wirt r a b β A := by
  unfold rhs wirt
  simp only [neg_add, neg_smul, neg_neg, sub_eq_add_neg]

theorem cubic_ae_of_continuous {A : L2 L d} {g : C(Tor L d, ℂ)}
    (hA : (A : Tor L d → ℂ) =ᵐ[μ L d] g) :
    (cubic A : Tor L d → ℂ) =ᵐ[μ L d] fun x => ((‖g x‖ ^ 2 : ℝ) : ℂ) * g x := by
  classical
  have hcont : Continuous fun x => ((‖g x‖ ^ 2 : ℝ) : ℂ) * g x :=
    (Complex.continuous_ofReal.comp ((continuous_norm.comp g.continuous).pow 2)).mul g.continuous
  have heq : (fun x => ((‖A x‖ ^ 2 : ℝ) : ℂ) * A x) =ᵐ[μ L d]
      fun x => ((‖g x‖ ^ 2 : ℝ) : ℂ) * g x := by
    filter_upwards [hA] with x hx; rw [hx]
  have hm : MemLp (fun x => ((‖A x‖ ^ 2 : ℝ) : ℂ) * A x) 2 (μ L d) := by
    obtain ⟨C, hC⟩ := (g.continuous.norm.pow 3).bounded_above_of_compact_support
      (HasCompactSupport.of_compactSpace _)
    refine MemLp.of_bound (hcont.aestronglyMeasurable.congr heq.symm) C ?_
    filter_upwards [heq] with x hx
    rw [hx, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have := hC x
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at this
    calc ‖g x‖ ^ 2 * ‖g x‖ = ‖g x‖ ^ 3 := by ring
      _ ≤ C := this
  rw [cubic, dif_pos hm]
  exact hm.coeFn_toLp.trans heq

theorem cubic_iota_ae (hd : d ≤ 3) (c : ell2 d) :
    (cubic (iota L 1 c) : Tor L d → ℂ) =ᵐ[μ L d]
      fun x => ((‖Phi L hd c x‖ ^ 2 : ℝ) : ℂ) * Phi L hd c x :=
  cubic_ae_of_continuous (iota_ae_eq_Phi hd c)

theorem real_inner_eq_re (X Y : L2 L d) : (inner ℝ X Y : ℝ) = (⟪X, Y⟫_ℂ).re := by
  rw [L2.inner_def, L2.inner_def, ← RCLike.re_to_complex, ← integral_re (L2.integrable_inner _ _)]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [Complex.inner, RCLike.inner_apply, RCLike.re_to_complex]

theorem re_inner_comm (X Y : L2 L d) : (⟪X, Y⟫_ℂ).re = (⟪Y, X⟫_ℂ).re := by
  rw [← inner_conj_symm, Complex.conj_re]

/-- Periodic integration by parts: `Σ_j ⟪∂_jA, ∂_jh⟫ = −⟪ΔA, h⟫`. -/
theorem sum_inner_Dj (c k : ell2 d) :
    ∑ j, ⟪Dj L j c, Dj L j k⟫_ℂ = -⟪DL L c, iota L 1 k⟫_ℂ := by
  have h1 := hasSum_sum (s := Finset.univ) fun j _ => hasSum_inner (Dj L j c) (Dj L j k)
  have h2 := (hasSum_inner (DL L c) (iota L 1 k)).neg
  refine h1.unique (h2.congr_fun fun n => ?_)
  simp only [Dj, DL, coef_opS, coef_iota, pow_one, map_mul, map_neg, Complex.conj_ofReal,
    Complex.conj_I, map_inv₀]
  have hx : xi2 L n = ∑ j, xi L n j ^ 2 := rfl
  rw [hx]; push_cast
  have hterm : ∀ x : Fin d, -Complex.I * (xi L n x : ℂ) * ((wt L n : ℂ))⁻¹ * conj (c n) *
      (Complex.I * (xi L n x : ℂ) * ((wt L n : ℂ))⁻¹ * k n) =
      (xi L n x : ℂ) ^ 2 * (((wt L n : ℂ))⁻¹ ^ 2 * conj (c n) * k n) := fun x => by
    linear_combination (-((xi L n x : ℂ) ^ 2 * ((wt L n : ℂ))⁻¹ ^ 2 * conj (c n) * k n)) *
      Complex.I_mul_I
  rw [Finset.sum_congr rfl fun x _ => hterm x, ← Finset.sum_mul]
  ring


omit hL in
theorem xi2_sq_le_wt_sq (n : Fin d → ℤ) : xi2 L n ^ 2 ≤ wt L n ^ 2 :=
  pow_le_pow_left₀ (xi2_nonneg n) (xi2_le_wt n) 2

theorem memℓp_lap_lap {c : ell2 d} (h4 : InH 2 (iota L 1 c)) :
    Memℓp (fun n => -(xi2 L n : ℂ) * coef (DL L c) n) 2 := by
  rw [memℓp_two_iff]
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) h4
  have hw := wt_pos (L := L) n
  have h0 := xi2_nonneg (L := L) n
  have h1 := xi2_sq_le_wt_sq (L := L) n
  have e1 : ‖-(xi2 L n : ℂ) * coef (DL L c) n‖ = xi2 L n ^ 2 * (wt L n)⁻¹ * ‖c n‖ := by
    rw [DL, coef_opS, pow_one, norm_mul, norm_mul, norm_mul, norm_neg, norm_inv]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0, abs_of_pos hw]
    ring
  have e2 : ‖coef (iota L 1 c) n‖ = (wt L n)⁻¹ * ‖c n‖ := by
    rw [coef_iota, pow_one, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hw]
  rw [e1, e2]
  have e3 : (xi2 L n ^ 2 * (wt L n)⁻¹ * ‖c n‖) ^ 2 =
      (xi2 L n ^ 2) ^ 2 * ((wt L n)⁻¹ * ‖c n‖) ^ 2 := by ring
  rw [e3, show wt L n ^ (2 * 2) = (wt L n ^ 2) ^ 2 by ring]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) h1 2) (by positivity)

theorem coef_lap_lap {c : ell2 d} (h4 : InH 2 (iota L 1 c)) (n : Fin d → ℤ) :
    coef (lap (lap (iota L 1 c))) n = (xi2 L n : ℂ) ^ 2 * ((wt L n : ℂ))⁻¹ * c n := by
  rw [lap_iota, lap, coef_pmul (memℓp_lap_lap h4), DL, coef_opS, pow_one]; ring

/-- `⟪ΔA, Δh⟫ = ⟪Δ²A, h⟫` for `A ∈ H⁴`, `h ∈ H²`. -/
theorem inner_DL_DL {c : ell2 d} (h4 : InH 2 (iota L 1 c)) (k : ell2 d) :
    ⟪DL L c, DL L k⟫_ℂ = ⟪lap (lap (iota L 1 c)), iota L 1 k⟫_ℂ := by
  refine (hasSum_inner (DL L c) (DL L k)).unique
    ((hasSum_inner (lap (lap (iota L 1 c))) (iota L 1 k)).congr_fun fun n => ?_)
  rw [coef_lap_lap h4, coef_iota, DL, coef_opS, coef_opS]
  simp only [map_mul, map_neg, map_pow, Complex.conj_ofReal, map_inv₀, pow_one]
  ring

/-- The quartic term: `DN(Φc)(Φk) = 4 Re⟪h, |A|²A⟫`. -/
theorem DNq_Phi (hd : d ≤ 3) (c k : ell2 d) :
    DNq (Phi L hd c) (Phi L hd k) = 4 * (⟪iota L 1 k, cubic (iota L 1 c)⟫_ℂ).re := by
  rw [DNq_apply, L2.inner_def, ← RCLike.re_to_complex,
    ← integral_re (L2.integrable_inner (𝕜 := ℂ) _ _)]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [iota_ae_eq_Phi (L := L) hd k, cubic_iota_ae (L := L) hd c] with x h1 h2
  rw [RCLike.inner_apply, h1, h2, RCLike.re_to_complex, mul_assoc, Complex.re_ofReal_mul]
  congr 1
  rw [← Complex.conj_re, map_mul, Complex.conj_conj, mul_comm]

/-- **First variation**: for `A = ι₁c ∈ H⁴` and `h = ι₁k ∈ H²`, the derivative of the energy in
the direction `h` equals `2 L^d Re⟪h, δE/δĀ⟫ = 2 Re ∫_Ω (δE/δĀ) h̄ dx`. -/
theorem DE_eq (hd : d ≤ 3) {c : ell2 d} (h4 : InH 2 (iota L 1 c)) (k : ell2 d) :
    L ^ d * (-r * (2 * inner ℝ (iota L 1 c) (iota L 1 k)) -
        a * ∑ j, 2 * inner ℝ (Dj L j c) (Dj L j k) +
        b * (2 * inner ℝ (DL L c) (DL L k)) +
        β / 2 * DNq (Phi L hd c) (Phi L hd k)) =
      2 * L ^ d * (⟪iota L 1 k, wirt r a b β (iota L 1 c)⟫_ℂ).re := by
  have hs : ∑ j, 2 * inner ℝ (Dj L j c) (Dj L j k) = -2 * (⟪DL L c, iota L 1 k⟫_ℂ).re := by
    simp only [real_inner_eq_re]
    rw [← Finset.mul_sum, ← Complex.re_sum, sum_inner_Dj, Complex.neg_re]; ring
  rw [hs, real_inner_eq_re, real_inner_eq_re, inner_DL_DL h4, DNq_Phi hd]
  simp only [wirt, inner_add_right, inner_smul_right, Complex.add_re, neg_mul, Complex.neg_re,
    Complex.re_ofReal_mul, lap_iota]
  rw [re_inner_comm (iota L 1 c), re_inner_comm (DL L c), re_inner_comm (lap (DL L c))]
  ring


/-! ### Theorem E13 -/

theorem integral_mul_conj_volume (G h : L2 L d) :
    ∫ x, G x * conj (h x) = (L ^ d : ℂ) * ⟪h, G⟫_ℂ := by
  rw [integral_volume, L2.inner_def]
  congr 1

theorem integral_norm_sq_vol (F : L2 L d) : ∫ x, ‖F x‖ ^ 2 = L ^ d * ‖F‖ ^ 2 := by
  rw [integral_volume_real, ← norm_sq_eq_integral]

theorem iota_add_smul (c k : ell2 d) (ε : ℝ) :
    iota L 1 (c + (ε : ℂ) • k) = iota L 1 c + (ε : ℂ) • iota L 1 k := by
  rw [map_add, map_smul]

/-- **Theorem E13** (negative Wirtinger gradient flow and energy dissipation). Let `d ≤ 3`,
`T > 0`, and let `A ∈ C¹([0,T]; H²(𝕋_L^d)) ` (given by a `C¹` curve `c` in the isometric model
`ι₁ : ℓ² ≅ H²`) with `A(t) ∈ H⁴` solve `∂ₜA = (r − aΔ − bΔ²)A − β|A|²A` in `L²`. Then, for every
`t ∈ [0,T]`: the first variation of `E` at `A(t)` in every direction `h ∈ H²` is
`2 Re ∫_Ω (δE/δĀ) h̄ dx` with `δE/δĀ = −rA + aΔA + bΔ²A + β|A|²A`; `∂ₜA = −δE/δĀ`;
`dE/dt = −2‖∂ₜA‖²_{L²(Ω)} ≤ 0`; `E[A(T)] + 2∫₀ᵀ ‖∂ₜA‖² dt = E[A(0)]`; and equality holds at `t`
iff `∂ₜA(t) = 0`, i.e. iff `A(t)` solves the stationary equation. -/
theorem e13 (hd : d ≤ 3) {T : ℝ} (hT : 0 < T) {A : ℝ → L2 L d} {c c' : ℝ → ell2 d}
    (hAc : ∀ t ∈ Icc 0 T, A t = iota L 1 (c t))
    (hc : ∀ t ∈ Icc 0 T, HasDerivWithinAt c (c' t) (Icc 0 T) t)
    (hc' : ContinuousOn c' (Icc 0 T)) (h4 : ∀ t ∈ Icc 0 T, InH 2 (A t))
    (hpde : ∀ t ∈ Icc 0 T, HasDerivWithinAt A (rhs r a b β (A t)) (Icc 0 T) t) :
    (∀ t ∈ Icc 0 T, ∀ h : L2 L d, InH 1 h →
      HasDerivAt (fun ε : ℝ => energy r a b β (A t + (ε : ℂ) • h))
        (2 * (∫ x, wirt r a b β (A t) x * conj (h x)).re) 0) ∧
    (∀ t ∈ Icc 0 T, HasDerivWithinAt A (-wirt r a b β (A t)) (Icc 0 T) t) ∧
    (∀ t ∈ Icc 0 T, HasDerivWithinAt (fun s => energy r a b β (A s))
      (-2 * ∫ x, ‖rhs r a b β (A t) x‖ ^ 2) (Icc 0 T) t) ∧
    (∀ t ∈ Icc 0 T, -2 * ∫ x, ‖rhs r a b β (A t) x‖ ^ 2 ≤ 0) ∧
    energy r a b β (A T) + 2 * ∫ t in (0 : ℝ)..T, ∫ x, ‖rhs r a b β (A t) x‖ ^ 2 =
      energy r a b β (A 0) ∧
    (∀ t ∈ Icc 0 T, (-2 * ∫ x, ‖rhs r a b β (A t) x‖ ^ 2 = 0 ↔ rhs r a b β (A t) = 0)) := by
  have hLd : 0 < L ^ d := pow_pos hL.out d
  -- the time derivative of `A` is `ι₁ c'`
  have hdA : ∀ t ∈ Icc 0 T, iota L 1 (c' t) = rhs r a b β (A t) := by
    intro t ht
    have h1 : HasDerivWithinAt A (iota L 1 (c' t)) (Icc 0 T) t :=
      (hasDerivWithinAt_clm (iota L 1) (hc t ht)).congr (fun s hs => hAc s hs) (hAc t ht)
    exact (uniqueDiffOn_Icc hT t ht).eq_deriv _ h1 (hpde t ht)
  -- the derivative of the energy along `c`
  have hE : ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun s => energy r a b β (A s))
      (2 * L ^ d * (⟪iota L 1 (c' t), wirt r a b β (A t)⟫_ℂ).re) (Icc 0 T) t := by
    intro t ht
    have h4' : InH 2 (iota L 1 (c t)) := by rw [← hAc t ht]; exact h4 t ht
    have h1 := hasDerivWithinAt_Ec (L := L) r a b β hd (hc t ht)
    rw [DE_eq r a b β hd h4', ← hAc t ht] at h1
    exact h1.congr (fun s hs => by rw [hAc s hs, energy_iota]) (by rw [hAc t ht, energy_iota])
  have hval : ∀ t ∈ Icc 0 T, 2 * L ^ d * (⟪iota L 1 (c' t), wirt r a b β (A t)⟫_ℂ).re =
      -2 * ∫ x, ‖rhs r a b β (A t) x‖ ^ 2 := by
    intro t ht
    rw [hdA t ht, ← neg_neg (wirt r a b β (A t)), ← rhs_eq_neg_wirt, inner_neg_right,
      Complex.neg_re, integral_norm_sq_vol]
    have := inner_self_eq_norm_sq (𝕜 := ℂ) (rhs r a b β (A t))
    rw [RCLike.re_to_complex] at this
    rw [this]; ring
  refine ⟨fun t ht h hh => ?_, fun t ht => ?_, fun t ht => ?_, fun t ht => ?_, ?_, fun t ht => ?_⟩
  · -- first variation
    obtain ⟨k, rfl⟩ := (inH_iff 1 h).1 hh
    have hγ : HasDerivAt (fun ε : ℝ => c t + (ε : ℂ) • k) k 0 := by
      have : (fun ε : ℝ => c t + (ε : ℂ) • k) = fun ε : ℝ => c t + ε • k := by
        funext ε; rw [Complex.coe_smul]
      rw [this]
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const k).const_add (c t)
    have h4' : InH 2 (iota L 1 (c t)) := by rw [← hAc t ht]; exact h4 t ht
    have h1 := (hasDerivWithinAt_Ec (L := L) r a b β hd hγ.hasDerivWithinAt (s := univ)).hasDerivAt
      Filter.univ_mem
    simp only [zero_smul, add_zero, Complex.ofReal_zero] at h1
    rw [DE_eq r a b β hd h4', ← hAc t ht] at h1
    refine h1.congr_of_eventuallyEq (Eventually.of_forall fun ε => ?_) |>.congr_deriv ?_
    · show energy r a b β (A t + (ε : ℂ) • iota L 1 k) = Ec L r a b β hd (c t + (ε : ℂ) • k)
      rw [hAc t ht, ← iota_add_smul, energy_iota]
    · rw [integral_mul_conj_volume, ← Complex.ofReal_pow, Complex.re_ofReal_mul]; ring
  · rw [← rhs_eq_neg_wirt]; exact hpde t ht
  · rw [← hval t ht]; exact hE t ht
  · have : 0 ≤ ∫ x, ‖rhs r a b β (A t) x‖ ^ 2 := integral_nonneg fun x => by positivity
    linarith
  · -- the balance identity
    have hcont : ContinuousOn (fun t => ∫ x, ‖rhs r a b β (A t) x‖ ^ 2) (Icc 0 T) := by
      have : ContinuousOn (fun t => L ^ d * ‖iota L 1 (c' t)‖ ^ 2) (Icc 0 T) :=
        continuousOn_const.mul ((continuous_norm.comp (iota L 1).continuous).continuousOn.comp hc'
          (mapsTo_univ _ _) |>.pow 2)
      refine this.congr fun t ht => ?_
      show ∫ x, ‖rhs r a b β (A t) x‖ ^ 2 = L ^ d * ‖iota L 1 (c' t)‖ ^ 2
      rw [hdA t ht, integral_norm_sq_vol]
    have hftc := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hT.le
      (f := fun s => energy r a b β (A s)) (f' := fun t => -2 * ∫ x, ‖rhs r a b β (A t) x‖ ^ 2)
      (fun t ht => (hE t ht).continuousWithinAt)
      (fun t ht => by
        have h1 : HasDerivWithinAt (fun s => energy r a b β (A s))
            (-2 * ∫ x, ‖rhs r a b β (A t) x‖ ^ 2) (Icc 0 T) t := by
          rw [← hval t (Ioo_subset_Icc_self ht)]; exact hE t (Ioo_subset_Icc_self ht)
        exact (h1.hasDerivAt (Icc_mem_nhds ht.1 ht.2)).hasDerivWithinAt)
      ((continuousOn_const.mul hcont).intervalIntegrable_of_Icc hT.le)
    rw [intervalIntegral.integral_const_mul] at hftc
    linarith
  · constructor
    · intro h0
      have h1 : ∫ x, ‖rhs r a b β (A t) x‖ ^ 2 = 0 := by linarith
      rw [integral_norm_sq_vol] at h1
      have := (mul_eq_zero.1 h1).resolve_left hLd.ne'
      rwa [sq_eq_zero_iff, norm_eq_zero] at this
    · intro h0
      rw [h0]
      simp


/-! ### The real `L²` gradient (E14 normalisation) -/

/-- The real inner product `(u, v)_ℝ = Re ∫_Ω u v̄ dx`. -/
def rinner (u v : L2 L d) : ℝ := (∫ x, u x * conj (v x)).re

theorem rinner_eq (u v : L2 L d) : rinner u v = L ^ d * (⟪v, u⟫_ℂ).re := by
  rw [rinner, integral_mul_conj_volume, ← Complex.ofReal_pow, Complex.re_ofReal_mul]

theorem inH_basis (k : ℕ) (n : Fin d → ℤ) : InH k (basis L d n) := by
  classical
  refine summable_of_ne_finset_zero (s := {n}) fun m hm => ?_
  rw [coef_basis, if_neg (by simpa using hm), norm_zero, zero_pow two_ne_zero, mul_zero]

theorem inH_smul {k : ℕ} {h : L2 L d} (hh : InH k h) (z : ℂ) : InH k (z • h) := by
  refine (hh.mul_left (‖z‖ ^ 2)).congr fun n => ?_
  rw [coef_smul, norm_mul, mul_pow]; ring

/-- An element of `L²` that is real-orthogonal to `H²` vanishes. -/
theorem eq_zero_of_rinner {G : L2 L d} (h : ∀ v : L2 L d, InH 1 v → rinner G v = 0) : G = 0 := by
  have hLd : (0 : ℝ) < L ^ d := pow_pos hL.out d
  apply ext_coef; intro n
  have h1 := h _ (inH_basis 1 n)
  have h2 := h _ (inH_smul (inH_basis 1 n) Complex.I)
  rw [rinner_eq] at h1 h2
  rw [inner_smul_left, Complex.conj_I] at h2
  have hre : (⟪basis L d n, G⟫_ℂ).re = 0 := (mul_eq_zero.1 h1).resolve_left hLd.ne'
  have him : (⟪basis L d n, G⟫_ℂ).im = 0 := by
    have := (mul_eq_zero.1 h2).resolve_left hLd.ne'
    simpa using this
  rw [coef_zero, ← repr_eq_coef, HilbertBasis.repr_apply_apply]
  exact Complex.ext hre him

/-- **The real `L²` gradient.** For `A ∈ H⁴`, `∇_ℝE[A] = 2 δE/δĀ`: the first variation in every
direction `h ∈ H²` is `(2 δE/δĀ, h)_ℝ`, and `2 δE/δĀ` is the only element of `L²` with this
property. -/
theorem real_gradient (hd : d ≤ 3) {A : L2 L d} (hA2 : InH 1 A) (hA4 : InH 2 A) :
    (∀ h : L2 L d, InH 1 h → HasDerivAt (fun ε : ℝ => energy r a b β (A + (ε : ℂ) • h))
      (rinner ((2 : ℂ) • wirt r a b β A) h) 0) ∧
    ∀ g : L2 L d, (∀ h : L2 L d, InH 1 h →
      HasDerivAt (fun ε : ℝ => energy r a b β (A + (ε : ℂ) • h)) (rinner g h) 0) →
      g = (2 : ℂ) • wirt r a b β A := by
  obtain ⟨c, rfl⟩ := (inH_iff 1 A).1 hA2
  have hvar : ∀ h : L2 L d, InH 1 h → HasDerivAt (fun ε : ℝ => energy r a b β (iota L 1 c + (ε : ℂ) • h))
      (rinner ((2 : ℂ) • wirt r a b β (iota L 1 c)) h) 0 := by
    intro h hh
    obtain ⟨k, rfl⟩ := (inH_iff 1 h).1 hh
    have hγ : HasDerivAt (fun ε : ℝ => c + (ε : ℂ) • k) k 0 := by
      have : (fun ε : ℝ => c + (ε : ℂ) • k) = fun ε : ℝ => c + ε • k := by
        funext ε; rw [Complex.coe_smul]
      rw [this]
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const k).const_add c
    have h1 := (hasDerivWithinAt_Ec (L := L) r a b β hd hγ.hasDerivWithinAt (s := univ)).hasDerivAt
      Filter.univ_mem
    simp only [zero_smul, add_zero, Complex.ofReal_zero] at h1
    rw [DE_eq r a b β hd hA4] at h1
    refine h1.congr_of_eventuallyEq (Eventually.of_forall fun ε => ?_) |>.congr_deriv ?_
    · show energy r a b β (iota L 1 c + (ε : ℂ) • iota L 1 k) = Ec L r a b β hd (c + (ε : ℂ) • k)
      rw [← iota_add_smul, energy_iota]
    · rw [rinner_eq, inner_smul_right,
        show ((2 : ℂ) * ⟪iota L 1 k, wirt r a b β (iota L 1 c)⟫_ℂ).re =
          2 * (⟪iota L 1 k, wirt r a b β (iota L 1 c)⟫_ℂ).re from by simp [Complex.mul_re]]
      ring
  refine ⟨hvar, fun g hg => ?_⟩
  have h0 : ∀ v : L2 L d, InH 1 v → rinner (g - (2 : ℂ) • wirt r a b β (iota L 1 c)) v = 0 := by
    intro v hv
    have e := (hg v hv).unique (hvar v hv)
    rw [rinner_eq, rinner_eq] at e
    rw [rinner_eq, inner_sub_right, Complex.sub_re, mul_sub, e, sub_self]
  exact sub_eq_zero.1 (eq_zero_of_rinner h0)


/-! ### The half-energy normalisation -/

/-- The half energy `F = E/2`. -/
def halfEnergy (A : L2 L d) : ℝ := energy r a b β A / 2

theorem rinner_smul_left (z : ℝ) (u v : L2 L d) : rinner ((z : ℂ) • u) v = z * rinner u v := by
  rw [rinner_eq, rinner_eq, inner_smul_right, Complex.re_ofReal_mul]; ring

/-- **The half energy is a literal real `L²` gradient potential**: for `A ∈ H⁴`, `∇_ℝF[A] = δE/δĀ`
(and it is the only such element of `L²`). -/
theorem half_gradient (hd : d ≤ 3) {A : L2 L d} (hA2 : InH 1 A) (hA4 : InH 2 A) :
    (∀ h : L2 L d, InH 1 h → HasDerivAt (fun ε : ℝ => halfEnergy r a b β (A + (ε : ℂ) • h))
      (rinner (wirt r a b β A) h) 0) ∧
    ∀ g : L2 L d, (∀ h : L2 L d, InH 1 h →
      HasDerivAt (fun ε : ℝ => halfEnergy r a b β (A + (ε : ℂ) • h)) (rinner g h) 0) →
      g = wirt r a b β A := by
  obtain ⟨h1, h2⟩ := real_gradient r a b β hd hA2 hA4
  have two : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_num
  refine ⟨fun h hh => ?_, fun g hg => ?_⟩
  · have := (h1 h hh).div_const 2
    rw [two, rinner_smul_left] at this
    convert this using 1
    ring
  · have e := h2 ((2 : ℂ) • g) fun h hh => by
      have := (hg h hh).const_mul 2
      rw [two, rinner_smul_left]
      refine this.congr_of_eventuallyEq (Eventually.of_forall fun ε => ?_)
      simp only [halfEnergy]; ring
    exact smul_right_injective (L2 L d) two_ne_zero e

/-- **E13 as a literal negative real gradient flow** (half-energy normalisation): under the
hypotheses of `e13`, `∂ₜA = −∇_ℝF[A]` and `dF/dt = −‖∂ₜA‖²_{L²(Ω)}`. -/
theorem half_flow (hd : d ≤ 3) {T : ℝ} (hT : 0 < T) {A : ℝ → L2 L d} {c c' : ℝ → ell2 d}
    (hAc : ∀ t ∈ Icc 0 T, A t = iota L 1 (c t))
    (hc : ∀ t ∈ Icc 0 T, HasDerivWithinAt c (c' t) (Icc 0 T) t)
    (hc' : ContinuousOn c' (Icc 0 T)) (h4 : ∀ t ∈ Icc 0 T, InH 2 (A t))
    (hpde : ∀ t ∈ Icc 0 T, HasDerivWithinAt A (rhs r a b β (A t)) (Icc 0 T) t) :
    (∀ t ∈ Icc 0 T, HasDerivWithinAt A (-wirt r a b β (A t)) (Icc 0 T) t) ∧
    (∀ t ∈ Icc 0 T, HasDerivWithinAt (fun s => halfEnergy r a b β (A s))
      (-∫ x, ‖rhs r a b β (A t) x‖ ^ 2) (Icc 0 T) t) := by
  obtain ⟨-, h2, h3, -⟩ := e13 r a b β hd hT hAc hc hc' h4 hpde
  refine ⟨h2, fun t ht => ?_⟩
  have := (h3 t ht).div_const 2
  convert this using 1
  ring


/-! ### The centred Swift–Hohenberg form -/

/-- `k⋆² = a/(2b)`. -/
def kstar2 : ℝ := a / (2 * b)

/-- `μ = r + a²/(4b)`. -/
def muSH : ℝ := r + a ^ 2 / (4 * b)

/-- `(Δ + k⋆²)A`. -/
def shiftOp (A : L2 L d) : L2 L d := lap A + ((kstar2 a b : ℝ) : ℂ) • A

/-- The centred energy `E_SH[A] = ∫_Ω (−μ|A|² + b|(Δ + k⋆²)A|² + (β/2)|A|⁴) dx`. -/
def energySH (A : L2 L d) : ℝ :=
  ∫ x, (-muSH r a b * ‖A x‖ ^ 2 + b * ‖shiftOp a b A x‖ ^ 2 + β / 2 * ‖A x‖ ^ 4)

theorem memℓp_of_inH {k : ℕ} {s : (Fin d → ℤ) → ℂ} {C : ℝ} (hs : ∀ n, ‖s n‖ ≤ C * wt L n ^ k)
    {A : L2 L d} (hA : InH k A) : Memℓp (fun n => s n * coef A n) 2 := by
  obtain ⟨c, rfl⟩ := (inH_iff k A).1 hA
  exact memℓp_pmul_iota k hs c

theorem inH_one_of_two {A : L2 L d} (hA : InH 2 A) : InH 1 A := by
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (pow_nonneg (wt_pos n).le _) (sq_nonneg _))
    (fun n => ?_) hA
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (one_le_wt n) (by norm_num))
    (by positivity)

theorem inH_add {k : ℕ} {A B : L2 L d} (hA : InH k A) (hB : InH k B) : InH k (A + B) := by
  obtain ⟨c, rfl⟩ := (inH_iff k A).1 hA
  obtain ⟨c', rfl⟩ := (inH_iff k B).1 hB
  exact (inH_iff k _).2 ⟨c + c', by rw [map_add]⟩

theorem coef_lap {A : L2 L d} (hA : InH 1 A) (n : Fin d → ℤ) :
    coef (lap A) n = -(xi2 L n : ℂ) * coef A n :=
  coef_pmul (memℓp_of_inH norm_xi2_le hA) n

omit hL in
theorem norm_xi2_sq_le (n : Fin d → ℤ) : ‖(xi2 L n : ℂ) ^ 2‖ ≤ 1 * wt L n ^ 2 := by
  rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (xi2_nonneg n), one_mul]
  exact xi2_sq_le_wt_sq n

theorem inH_lap {A : L2 L d} (hA : InH 2 A) : InH 1 (lap A) := by
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (pow_nonneg (wt_pos n).le _) (sq_nonneg _))
    (fun n => ?_) hA
  rw [coef_lap (inH_one_of_two hA), norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (xi2_nonneg n), mul_pow, ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  have h1 := xi2_sq_le_wt_sq (L := L) n
  have hw := wt_pos (L := L) n
  calc wt L n ^ (2 * 1) * xi2 L n ^ 2 ≤ wt L n ^ 2 * wt L n ^ 2 :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = wt L n ^ (2 * 2) := by ring

theorem coef_lap_lap' {A : L2 L d} (hA : InH 2 A) (n : Fin d → ℤ) :
    coef (lap (lap A)) n = (xi2 L n : ℂ) ^ 2 * coef A n := by
  rw [coef_lap (inH_lap hA), coef_lap (inH_one_of_two hA)]; ring

theorem coef_shiftOp {A : L2 L d} (hA : InH 1 A) (n : Fin d → ℤ) :
    coef (shiftOp a b A) n = ((kstar2 a b : ℂ) - xi2 L n) * coef A n := by
  rw [shiftOp, coef_add, coef_smul, coef_lap hA]; ring

theorem inH_shiftOp {A : L2 L d} (hA : InH 2 A) : InH 1 (shiftOp a b A) :=
  inH_add (inH_lap hA) (inH_smul (inH_one_of_two hA) _)

theorem coef_shiftOp_shiftOp {A : L2 L d} (hA : InH 2 A) (n : Fin d → ℤ) :
    coef (shiftOp a b (shiftOp a b A)) n = ((kstar2 a b : ℂ) - xi2 L n) ^ 2 * coef A n := by
  rw [coef_shiftOp a b (inH_shiftOp a b hA), coef_shiftOp a b (inH_one_of_two hA)]; ring

/-- The linear growth rate `λ(q) = r + aq − bq²` of a mode with `|k|² = q`. -/
def lamq (q : ℝ) : ℝ := r + a * q - b * q ^ 2

theorem lamq_eq (hb : b ≠ 0) (q : ℝ) :
    lamq r a b q = muSH r a b - b * (q - kstar2 a b) ^ 2 := by
  unfold lamq muSH kstar2; field_simp; ring

/-- The linear part of E13 acts diagonally: `((r − aΔ − bΔ²)A)^_n = λ(|ξ_n|²) Â_n` on `H⁴`. -/
theorem coef_linear {A : L2 L d} (hA : InH 2 A) (n : Fin d → ℤ) :
    coef ((r : ℂ) • A - (a : ℂ) • lap A - (b : ℂ) • lap (lap A)) n =
      (lamq r a b (xi2 L n) : ℂ) * coef A n := by
  rw [coef_sub, coef_sub, coef_smul, coef_smul, coef_smul, coef_lap (inH_one_of_two hA),
    coef_lap_lap' hA, lamq]
  push_cast; ring

/-- `r − aΔ − bΔ² = μ − b(Δ + k⋆²)²` on `H⁴`. -/
theorem centred_operator (hb : b ≠ 0) {A : L2 L d} (hA : InH 2 A) :
    (r : ℂ) • A - (a : ℂ) • lap A - (b : ℂ) • lap (lap A) =
      (muSH r a b : ℂ) • A - (b : ℂ) • shiftOp a b (shiftOp a b A) := by
  apply ext_coef; intro n
  rw [coef_linear r a b hA, coef_sub, coef_smul, coef_smul, coef_shiftOp_shiftOp a b hA,
    lamq_eq r a b hb]
  push_cast; ring

/-- **The centred flow**: `(r − aΔ − bΔ²)A − β|A|²A = μA − b(Δ + k⋆²)²A − β|A|²A` on `H⁴`. -/
theorem rhs_centred (hb : b ≠ 0) {A : L2 L d} (hA : InH 2 A) :
    rhs r a b β A =
      (muSH r a b : ℂ) • A - (b : ℂ) • shiftOp a b (shiftOp a b A) - (β : ℂ) • cubic A := by
  rw [rhs, centred_operator r a b hb hA]

/-- The Wirtinger derivative in centred form: `δE/δĀ = −μA + b(Δ + k⋆²)²A + β|A|²A`. -/
theorem wirt_centred (hb : b ≠ 0) {A : L2 L d} (hA : InH 2 A) :
    wirt r a b β A =
      -(muSH r a b : ℂ) • A + (b : ℂ) • shiftOp a b (shiftOp a b A) + (β : ℂ) • cubic A := by
  rw [← neg_neg (wirt r a b β A), ← rhs_eq_neg_wirt, rhs_centred r a b β hb hA]
  simp only [neg_smul, sub_eq_add_neg, neg_add, neg_neg]

theorem norm_shiftOp_sq_iota (c : ell2 d) :
    ‖shiftOp a b (iota L 1 c)‖ ^ 2 = ‖DL L c‖ ^ 2 - 2 * kstar2 a b * ∑ j, ‖Dj L j c‖ ^ 2 +
      kstar2 a b ^ 2 * ‖iota L 1 c‖ ^ 2 := by
  have h := congrArg Complex.re (sum_inner_Dj (L := L) c c)
  rw [Complex.re_sum, Complex.neg_re] at h
  have hn : ∀ j, (⟪Dj L j c, Dj L j c⟫_ℂ).re = ‖Dj L j c‖ ^ 2 := fun j => by
    have := inner_self_eq_norm_sq (𝕜 := ℂ) (Dj L j c); rwa [RCLike.re_to_complex] at this
  simp only [hn] at h
  rw [shiftOp, lap_iota, @norm_add_sq ℂ, inner_smul_right, RCLike.re_to_complex,
    Complex.re_ofReal_mul, norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs, h]
  ring

/-- Periodic integration by parts: `Re ∫_Ω (ΔA) Ā dx = −∫_Ω |∇A|² dx` on `H²`. -/
theorem re_integral_lap_conj {A : L2 L d} (hA : InH 1 A) :
    (∫ x, lap A x * conj (A x)).re = -∑ j, ∫ x, ‖dpart j A x‖ ^ 2 := by
  obtain ⟨c, rfl⟩ := (inH_iff 1 A).1 hA
  have h := congrArg Complex.re (sum_inner_Dj (L := L) c c)
  rw [Complex.re_sum, Complex.neg_re] at h
  have hn : ∀ j, (⟪Dj L j c, Dj L j c⟫_ℂ).re = ‖Dj L j c‖ ^ 2 := fun j => by
    have := inner_self_eq_norm_sq (𝕜 := ℂ) (Dj L j c); rwa [RCLike.re_to_complex] at this
  simp only [hn] at h
  rw [integral_mul_conj_volume, ← Complex.ofReal_pow, Complex.re_ofReal_mul, re_inner_comm,
    lap_iota]
  simp only [dpart_iota, integral_norm_sq_vol]
  rw [← Finset.mul_sum, h]; ring

/-- `‖(Δ + k⋆²)A‖² = ‖ΔA‖² − 2k⋆²‖∇A‖² + k⋆⁴‖A‖²` in `L²(Ω)`, for `A ∈ H²`. -/
theorem norm_shiftOp_sq {A : L2 L d} (hA : InH 1 A) :
    ∫ x, ‖shiftOp a b A x‖ ^ 2 = (∫ x, ‖lap A x‖ ^ 2) -
      2 * kstar2 a b * (∑ j, ∫ x, ‖dpart j A x‖ ^ 2) + kstar2 a b ^ 2 * ∫ x, ‖A x‖ ^ 2 := by
  obtain ⟨c, rfl⟩ := (inH_iff 1 A).1 hA
  simp only [integral_norm_sq_vol, dpart_iota, lap_iota, norm_shiftOp_sq_iota]
  rw [← Finset.mul_sum]; ring

theorem energySH_iota (hd : d ≤ 3) (c : ell2 d) :
    energySH r a b β (iota L 1 c) = L ^ d * (-muSH r a b * ‖iota L 1 c‖ ^ 2 +
      b * ‖shiftOp a b (iota L 1 c)‖ ^ 2 + β / 2 * Nq (Phi L hd c)) := by
  have h0 := integrable_norm_sq (iota L 1 c)
  have hS := integrable_norm_sq (shiftOp a b (iota L 1 c))
  have h4 := integrable_norm_four_iota (L := L) hd c
  have e4 : ∫ x, ‖(iota L 1 c : L2 L d) x‖ ^ 4 ∂(μ L d) = Nq (Phi L hd c) := by
    rw [Nq]
    refine integral_congr_ae ?_
    filter_upwards [iota_ae_eq_Phi (L := L) hd c] with x hx
    rw [hx]
  have i1 := h0.const_mul (-muSH r a b)
  have i2 := hS.const_mul b
  have i4 := h4.const_mul (β / 2)
  have i12 : Integrable (fun x => -muSH r a b * ‖(iota L 1 c : L2 L d) x‖ ^ 2 +
      b * ‖(shiftOp a b (iota L 1 c) : L2 L d) x‖ ^ 2) (μ L d) := i1.add i2
  rw [energySH, integral_volume_real]
  congr 1
  rw [integral_add i12 i4, integral_add i1 i2, integral_const_mul, integral_const_mul,
    integral_const_mul, ← norm_sq_eq_integral, ← norm_sq_eq_integral, e4]

/-- **Exact complete-square equivalence**: `E_SH[A] = E[A]` for every `A ∈ H²` (not merely up to a
constant). -/
theorem energySH_eq (hd : d ≤ 3) (hb : b ≠ 0) {A : L2 L d} (hA : InH 1 A) :
    energySH r a b β A = energy r a b β A := by
  obtain ⟨c, rfl⟩ := (inH_iff 1 A).1 hA
  rw [energySH_iota r a b β hd, energy_iota r a b β hd, Ec, norm_shiftOp_sq_iota]
  unfold muSH kstar2
  field_simp
  ring

/-- **The centred first variation**: for `A ∈ H⁴`, `h ∈ H²`,
`d/dε E_SH[A + εh]|₀ = 2 Re ∫_Ω (−μA + b(Δ + k⋆²)²A + β|A|²A) h̄ dx`; hence the negative Wirtinger
gradient flow of `E_SH` is `∂ₜA = μA − b(Δ + k⋆²)²A − β|A|²A`, the same flow as E13. -/
theorem centred_first_variation (hd : d ≤ 3) (hb : b ≠ 0) {A : L2 L d} (hA4 : InH 2 A)
    {h : L2 L d} (hh : InH 1 h) :
    HasDerivAt (fun ε : ℝ => energySH r a b β (A + (ε : ℂ) • h))
      (2 * (∫ x, (-(muSH r a b : ℂ) • A + (b : ℂ) • shiftOp a b (shiftOp a b A) +
        (β : ℂ) • cubic A) x * conj (h x)).re) 0 := by
  have hA2 := inH_one_of_two hA4
  have h1 := (real_gradient r a b β hd hA2 hA4).1 h hh
  rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, rinner_smul_left, wirt_centred r a b β hb hA4]
    at h1
  refine h1.congr_of_eventuallyEq (Eventually.of_forall fun ε => ?_)
  exact energySH_eq r a b β hd hb (inH_add hA2 (inH_smul hh _))


/-! ### The preferred Fourier shell -/

theorem hasDerivAt_lamq (q : ℝ) : HasDerivAt (lamq r a b) (a - 2 * b * q) q := by
  have := (((hasDerivAt_id q).const_mul a).const_add r).sub ((hasDerivAt_pow 2 q).const_mul b)
  convert this using 1
  simp; ring

theorem deriv_lamq : deriv (lamq r a b) = fun q => a - 2 * b * q :=
  funext fun q => (hasDerivAt_lamq r a b q).deriv

/-- `λ'(q) = a − 2bq` and `λ''(q) = −2b`. -/
theorem deriv2_lamq : deriv (deriv (lamq r a b)) = fun _ => -2 * b := by
  rw [deriv_lamq]
  funext q
  have := ((hasDerivAt_id q).const_mul (2 * b)).const_sub a
  simpa using this.deriv

theorem lamq_le (hb : 0 < b) (q : ℝ) : lamq r a b q ≤ muSH r a b := by
  rw [lamq_eq r a b hb.ne']
  have := mul_nonneg hb.le (sq_nonneg (q - kstar2 a b))
  linarith

theorem lamq_eq_mu_iff (hb : 0 < b) (q : ℝ) : lamq r a b q = muSH r a b ↔ q = kstar2 a b := by
  rw [lamq_eq r a b hb.ne']
  constructor
  · intro h
    have : b * (q - kstar2 a b) ^ 2 = 0 := by linarith
    have := (mul_eq_zero.1 this).resolve_left hb.ne'
    linarith [pow_eq_zero_iff (n := 2) two_ne_zero |>.1 this]
  · intro h; rw [h]; ring

theorem kstar2_pos (ha : 0 < a) (hb : 0 < b) : 0 < kstar2 a b := by
  unfold kstar2; positivity

/-- **The preferred shell.** For `a, b > 0`, `q ↦ λ(q)` has the unique maximiser `q = k⋆²`, and
on `ℝ^d` the continuum symbol `λ(|k|²) = μ − b(|k|² − k⋆²)²` attains its maximum `μ` exactly on
the sphere `|k| = k⋆ > 0`. -/
theorem preferred_shell (ha : 0 < a) (hb : 0 < b) :
    IsMaxOn (lamq r a b) univ (kstar2 a b) ∧
    (∀ q, IsMaxOn (lamq r a b) univ q → q = kstar2 a b) ∧
    0 < Real.sqrt (kstar2 a b) ∧
    (∀ k : EuclideanSpace ℝ (Fin d), lamq r a b (‖k‖ ^ 2) ≤ muSH r a b) ∧
    (∀ k : EuclideanSpace ℝ (Fin d),
      lamq r a b (‖k‖ ^ 2) = muSH r a b ↔ ‖k‖ = Real.sqrt (kstar2 a b)) := by
  have hmax : lamq r a b (kstar2 a b) = muSH r a b := (lamq_eq_mu_iff r a b hb _).2 rfl
  have hk := kstar2_pos a b ha hb
  refine ⟨fun q _ => ?_, fun q hq => ?_, Real.sqrt_pos.2 hk, fun k => lamq_le r a b hb _,
    fun k => ?_⟩
  · rw [mem_setOf_eq, hmax]; exact lamq_le r a b hb q
  · have h1 : lamq r a b (kstar2 a b) ≤ lamq r a b q := hq (mem_univ _)
    rw [hmax] at h1
    exact (lamq_eq_mu_iff r a b hb q).1 (le_antisymm (lamq_le r a b hb q) h1)
  · rw [lamq_eq_mu_iff r a b hb]
    constructor
    · intro h; rw [← h, Real.sqrt_sq (norm_nonneg _)]
    · intro h; rw [h, Real.sq_sqrt hk.le]

/-- **The linearly growing band**: for `b > 0`, `λ(q) > 0 ⟺ |q − k⋆²| < √(μ/b)`; it is nonempty
(it contains `q = k⋆²`) exactly when `μ > 0`. -/
theorem growing_band (hb : 0 < b) (q : ℝ) :
    0 < lamq r a b q ↔ |q - kstar2 a b| < Real.sqrt (muSH r a b / b) := by
  rw [lamq_eq r a b hb.ne', Real.lt_sqrt (abs_nonneg _), sq_abs, lt_div_iff₀ hb]
  constructor <;> intro h <;> linarith [mul_comm b ((q - kstar2 a b) ^ 2)]

theorem growing_band_nonempty (hb : 0 < b) :
    0 < lamq r a b (kstar2 a b) ↔ 0 < muSH r a b := by
  rw [(lamq_eq_mu_iff r a b hb _).2 rfl]

/-- **Ultraviolet linear damping**: `λ(q) → −∞` as `q → ∞` (for `b > 0`). -/
theorem uv_damping (hb : 0 < b) : Tendsto (lamq r a b) atTop atBot := by
  have h1 : Tendsto (fun q : ℝ => b * (q - kstar2 a b) ^ 2) atTop atTop :=
    ((tendsto_pow_atTop two_ne_zero).comp (tendsto_atTop_add_const_right atTop (-kstar2 a b)
      tendsto_id)).const_mul_atTop hb
  have h2 := tendsto_atBot_add_const_left atTop (muSH r a b) (tendsto_neg_atTop_atBot.comp h1)
  refine h2.congr fun q => ?_
  simp only [Function.comp, lamq_eq r a b hb.ne', sub_eq_add_neg]

/-- **The opposite sign is UV-unstable**: with `+b(Δ + k⋆²)²` (`b > 0`) the symbol
`μ + b(q − k⋆²)²` tends to `+∞`, so high-frequency modes would grow. -/
theorem opposite_sign_growth (hb : 0 < b) :
    Tendsto (fun q : ℝ => muSH r a b + b * (q - kstar2 a b) ^ 2) atTop atTop :=
  tendsto_atTop_add_const_left atTop (muSH r a b)
    (((tendsto_pow_atTop two_ne_zero).comp (tendsto_atTop_add_const_right atTop (-kstar2 a b)
      tendsto_id)).const_mul_atTop hb |>.congr fun q => by
        simp only [Function.comp, id, sub_eq_add_neg])

theorem tendsto_xi2 : Tendsto (xi2 L : (Fin d → ℤ) → ℝ) cofinite atTop := by
  refine tendsto_atTop.2 fun M => eventually_cofinite.2 ?_
  have hc : 0 < 2 * π / L := div_pos Real.two_pi_pos hL.out
  set K : ℤ := ⌈M / (2 * π / L) ^ 2⌉
  refine (Set.Finite.pi (t := fun _ : Fin d => Icc (-K) K) fun _ => finite_Icc _ _).subset ?_
  intro n hn
  simp only [mem_setOf_eq, not_le] at hn
  simp only [Set.mem_pi, mem_univ, mem_Icc, true_implies]
  intro j
  have h1 := xi_sq_le_xi2 (L := L) n j
  have h2 : ((n j : ℤ) : ℝ) ^ 2 < M / (2 * π / L) ^ 2 := by
    rw [lt_div_iff₀ (by positivity)]
    have : xi L n j ^ 2 = (2 * π / L) ^ 2 * (n j : ℝ) ^ 2 := by rw [xi]; ring
    linarith
  have h3 : (n j) ^ 2 ≤ K := by
    have := h2.le.trans (Int.le_ceil _)
    exact_mod_cast this
  constructor
  · rcases le_or_gt 0 (n j) with h | h
    · nlinarith
    · nlinarith
  · rcases le_or_gt (n j) 0 with h | h
    · nlinarith
    · nlinarith

/-- **Discrete maximisers**: on the torus the fastest linear growth rate is attained at some lattice
wave number (for `b > 0`). -/
theorem lattice_maximiser (hb : 0 < b) :
    ∃ n₀ : Fin d → ℤ, ∀ n : Fin d → ℤ, lamq r a b (xi2 L n) ≤ lamq r a b (xi2 L n₀) :=
  ((uv_damping r a b hb).comp (tendsto_xi2 (L := L))).exists_forall_ge

/-- **An exact mode on the shell need not exist**: on `𝕋_{2π}¹` with `a = 4`, `b = 1`
(`k⋆² = 2`), no lattice wave number satisfies `|ξ_n|² = k⋆²`. -/
theorem shell_not_attained : ∀ n : Fin 1 → ℤ, xi2 (2 * π) n ≠ kstar2 4 1 := by
  intro n h
  have e : xi2 (2 * π) n = ((n 0 : ℤ) : ℝ) ^ 2 := by
    simp only [xi2, xi, Fin.sum_univ_one]
    rw [div_self Real.two_pi_pos.ne', one_mul]
  rw [e, kstar2] at h
  norm_num at h
  have h2 : (n 0) ^ 2 = 2 := by exact_mod_cast h
  have h3 : n 0 ≤ 1 := by nlinarith
  have h4 : -1 ≤ n 0 := by nlinarith
  interval_cases (n 0) <;> simp_all


/-! ### Linearisation at `A = 0` -/

theorem pmul_smul (s : (Fin d → ℤ) → ℂ) (z : ℂ) (A : L2 L d) : pmul s (z • A) = z • pmul s A := by
  classical
  by_cases h : Memℓp (fun n => s n * coef A n) 2
  · have h' : Memℓp (fun n => s n * coef (z • A) n) 2 := by
      have := h.const_smul z
      convert this using 1
      funext n; simp only [coef_smul, Pi.smul_apply, smul_eq_mul]; ring
    apply ext_coef; intro n
    rw [coef_pmul h', coef_smul, coef_smul, coef_pmul h]; ring
  · by_cases hz : z = 0
    · subst hz
      rw [zero_smul, zero_smul]
      have h0 : Memℓp (fun n => s n * coef (0 : L2 L d) n) 2 := by
        simp only [coef_zero, mul_zero]; exact zero_memℓp
      apply ext_coef; intro n; rw [coef_pmul h0, coef_zero, mul_zero]
    · have h' : ¬ Memℓp (fun n => s n * coef (z • A) n) 2 := by
        intro h'; apply h
        have := h'.const_smul z⁻¹
        convert this using 1
        funext n; simp only [coef_smul, Pi.smul_apply, smul_eq_mul]; field_simp
      rw [pmul, dif_neg h', pmul, dif_neg h, smul_zero]

theorem lap_smul (z : ℂ) (A : L2 L d) : lap (z • A) = z • lap A := pmul_smul _ z A

theorem cubic_smul (z : ℂ) (A : L2 L d) :
    cubic (z • A) = (((‖z‖ ^ 2 : ℝ) : ℂ) * z) • cubic A := by
  classical
  set w : ℂ := ((‖z‖ ^ 2 : ℝ) : ℂ) * z with hw
  have hae : (fun x => ((‖(z • A : L2 L d) x‖ ^ 2 : ℝ) : ℂ) * (z • A : L2 L d) x) =ᵐ[μ L d]
      fun x => w * (((‖A x‖ ^ 2 : ℝ) : ℂ) * A x) := by
    filter_upwards [Lp.coeFn_smul z A] with x hx
    rw [hx, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, hw]; push_cast; ring
  by_cases hz : z = 0
  · have hw0 : w = 0 := by rw [hw, hz, mul_zero]
    rw [hw0, zero_smul]
    have hae0 : (fun x => ((‖(z • A : L2 L d) x‖ ^ 2 : ℝ) : ℂ) * (z • A : L2 L d) x)
        =ᵐ[μ L d] 0 := by
      filter_upwards [hae] with x hx; rw [hx, hw0, zero_mul]; rfl
    have hm : MemLp (fun x => ((‖(z • A : L2 L d) x‖ ^ 2 : ℝ) : ℂ) * (z • A : L2 L d) x)
        2 (μ L d) := MemLp.zero.ae_eq hae0.symm
    rw [cubic, dif_pos hm, Lp.eq_zero_iff_ae_eq_zero]
    exact hm.coeFn_toLp.trans hae0
  · have hw0 : w ≠ 0 := by
      rw [hw]; exact mul_ne_zero (by exact_mod_cast (pow_pos (norm_pos_iff.2 hz) 2).ne') hz
    by_cases h : MemLp (fun x => ((‖A x‖ ^ 2 : ℝ) : ℂ) * A x) 2 (μ L d)
    · have h' : MemLp (fun x => ((‖(z • A : L2 L d) x‖ ^ 2 : ℝ) : ℂ) * (z • A : L2 L d) x)
          2 (μ L d) := (h.const_mul w).ae_eq hae.symm
      rw [cubic, dif_pos h', cubic, dif_pos h]
      refine Lp.ext ?_
      filter_upwards [h'.coeFn_toLp, Lp.coeFn_smul w (h.toLp _), h.coeFn_toLp, hae]
        with x h1 h2 h3 h4
      rw [h1, h2, Pi.smul_apply, h3, h4, smul_eq_mul]
    · have h' : ¬ MemLp (fun x => ((‖(z • A : L2 L d) x‖ ^ 2 : ℝ) : ℂ) * (z • A : L2 L d) x)
          2 (μ L d) := by
        intro h'; apply h
        refine (h'.const_mul w⁻¹).ae_eq ?_
        filter_upwards [hae] with x hx
        rw [hx, ← mul_assoc, inv_mul_cancel₀ hw0, one_mul]
      rw [cubic, dif_neg h', cubic, dif_neg h, smul_zero]

/-- Along rays the vector field splits exactly into its linear part and the cubic term:
`rhs(εA) = ε (r − aΔ − bΔ²)A − ε³ β|A|²A` for real `ε`. -/
theorem rhs_smul (ε : ℝ) (A : L2 L d) :
    rhs r a b β ((ε : ℂ) • A) =
      (ε : ℂ) • ((r : ℂ) • A - (a : ℂ) • lap A - (b : ℂ) • lap (lap A)) -
        ((ε ^ 3 : ℝ) : ℂ) • ((β : ℂ) • cubic A) := by
  have hc : cubic ((ε : ℂ) • A) = ((ε ^ 3 : ℝ) : ℂ) • cubic A := by
    rw [cubic_smul]; congr 1
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]; push_cast; ring
  rw [rhs, lap_smul, lap_smul, hc]
  module

/-- **Linearisation at `A = 0`**: `d/dε rhs(εA)|_{ε=0} = (r − aΔ − bΔ²)A`, which by `coef_linear`
acts on the Fourier modes as `∂ₜÂ_n = λ(|ξ_n|²) Â_n`. -/
theorem linearization (A : L2 L d) :
    HasDerivAt (fun ε : ℝ => rhs r a b β ((ε : ℂ) • A))
      ((r : ℂ) • A - (a : ℂ) • lap A - (b : ℂ) • lap (lap A)) 0 := by
  set V := (r : ℂ) • A - (a : ℂ) • lap A - (b : ℂ) • lap (lap A)
  set W := (β : ℂ) • cubic A
  have h1 : HasDerivAt (fun ε : ℝ => ε • V) V 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const V
  have h2 : HasDerivAt (fun ε : ℝ => ε ^ 3 • W) ((3 * (0 : ℝ) ^ 2) • W) 0 := by
    simpa using (hasDerivAt_pow 3 (0 : ℝ)).smul_const W
  have h3 := h1.sub h2
  rw [show (3 * (0 : ℝ) ^ 2) • W = 0 by simp, sub_zero] at h3
  refine h3.congr_of_eventuallyEq (Eventually.of_forall fun ε => ?_)
  show rhs r a b β ((ε : ℂ) • A) = ε • V - ε ^ 3 • W
  rw [rhs_smul, ← Complex.coe_smul ε V, ← Complex.coe_smul (ε ^ 3) W]


/-! ### Fourier shells are not invariant under the nonlinear flow -/


omit hL in
theorem emode_add (m n : Fin d → ℤ) (x : Tor L d) :
    emode (L := L) (m + n) x = emode m x * emode n x := by
  simp only [emode, ContinuousMap.coe_mk, Pi.add_apply, fourier_add, Finset.prod_mul_distrib]

omit hL in
theorem emode_neg (n : Fin d → ℤ) (x : Tor L d) : emode (L := L) (-n) x = conj (emode n x) := by
  simp only [emode, ContinuousMap.coe_mk, Pi.neg_apply, fourier_neg, map_prod]

theorem basis_ae_emode (m : Fin d → ℤ) :
    (basis L d m : Tor L d → ℂ) =ᵐ[μ L d] emode (L := L) m := by
  rw [basis_eq_toLp]
  exact ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (μ L d) (emode (L := L) m)

/-- `|A₀|²A₀` for the two-mode state `A₀ = e_n + e_{−n}` (`= 8 cos³`):
`e_{3n} + 3e_n + 3e_{−n} + e_{−3n}`. -/
theorem cubic_two_mode (n : Fin d → ℤ) :
    cubic (basis L d n + basis L d (-n)) = basis L d (3 • n) + (3 : ℂ) • basis L d n +
      (3 : ℂ) • basis L d (-n) + basis L d (-(3 • n)) := by
  have hA : ((basis L d n + basis L d (-n) : L2 L d) : Tor L d → ℂ) =ᵐ[μ L d]
      ⇑(emode (L := L) n + emode (L := L) (-n) : C(Tor L d, ℂ)) := by
    filter_upwards [Lp.coeFn_add (basis L d n) (basis L d (-n)), basis_ae_emode (L := L) n,
      basis_ae_emode (L := L) (-n)] with x h1 h2 h3
    rw [h1, Pi.add_apply, h2, h3, ContinuousMap.add_apply]
  refine Lp.ext ?_
  filter_upwards [cubic_ae_of_continuous hA,
    Lp.coeFn_add (basis L d (3 • n) + (3 : ℂ) • basis L d n + (3 : ℂ) • basis L d (-n))
      (basis L d (-(3 • n))),
    Lp.coeFn_add (basis L d (3 • n) + (3 : ℂ) • basis L d n) ((3 : ℂ) • basis L d (-n)),
    Lp.coeFn_add (basis L d (3 • n)) ((3 : ℂ) • basis L d n),
    Lp.coeFn_smul (3 : ℂ) (basis L d n), Lp.coeFn_smul (3 : ℂ) (basis L d (-n)),
    basis_ae_emode (L := L) (3 • n), basis_ae_emode (L := L) n, basis_ae_emode (L := L) (-n),
    basis_ae_emode (L := L) (-(3 • n))] with x h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  rw [h0, h1, Pi.add_apply, h2, Pi.add_apply, h3, Pi.add_apply, h4, h5, Pi.smul_apply,
    Pi.smul_apply, h6, h7, h8, h9, ContinuousMap.add_apply, smul_eq_mul, smul_eq_mul]
  set u := emode (L := L) n x with hu
  have hneg : emode (L := L) (-n) x = conj u := emode_neg n x
  have h3n : emode (L := L) (3 • n) x = u ^ 3 := by
    rw [show 3 • n = n + n + n by abel, emode_add, emode_add]; ring
  have hm3n : emode (L := L) (-(3 • n)) x = conj u ^ 3 := by
    rw [emode_neg, h3n, map_pow]
  have hnorm : ‖u‖ = 1 := norm_emode_apply n x
  have h1' : u * conj u = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm]; norm_num
  have hz : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = z * conj z := fun z => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hneg, h3n, hm3n, hz, map_add, Complex.conj_conj]
  linear_combination (3 * u + 3 * conj u) * h1'

theorem nsmul_ne_self {n : Fin d → ℤ} (hn : n ≠ 0) : (3 • n : Fin d → ℤ) ≠ n := by
  intro h; apply hn; funext j
  have := congrFun h j
  simp only [Pi.smul_apply, nsmul_eq_mul, Nat.cast_ofNat, Pi.zero_apply] at this ⊢; omega

theorem nsmul_ne_neg {n : Fin d → ℤ} (hn : n ≠ 0) : (3 • n : Fin d → ℤ) ≠ -n := by
  intro h; apply hn; funext j
  have := congrFun h j
  simp only [Pi.smul_apply, nsmul_eq_mul, Nat.cast_ofNat, Pi.neg_apply, Pi.zero_apply]
    at this ⊢
  omega

theorem nsmul_ne_neg_nsmul {n : Fin d → ℤ} (hn : n ≠ 0) :
    (3 • n : Fin d → ℤ) ≠ -(3 • n : Fin d → ℤ) := by
  intro h; apply hn; funext j
  have := congrFun h j
  simp only [Pi.neg_apply, Pi.smul_apply] at this
  rw [nsmul_eq_mul, Nat.cast_ofNat] at this
  simp only [Pi.zero_apply]
  omega

/-- The cubic term creates the off-shell mode `3n`: `(rhs A₀)^_{3n} = −β` for `A₀ = e_n + e_{−n}`,
`n ≠ 0`. -/
theorem coef_rhs_two_mode {n : Fin d → ℤ} (hn : n ≠ 0) :
    coef (rhs r a b β (basis L d n + basis L d (-n))) (3 • n) = -(β : ℂ) := by
  have h2 : InH 2 (basis L d n + basis L d (-n)) := inH_add (inH_basis 2 n) (inH_basis 2 (-n))
  have h0 : coef (basis L d n + basis L d (-n)) (3 • n) = 0 := by
    rw [coef_add, coef_basis, coef_basis, if_neg (nsmul_ne_self hn), if_neg (nsmul_ne_neg hn),
      add_zero]
  rw [rhs, coef_sub, coef_sub, coef_sub, coef_smul, coef_smul, coef_smul, coef_smul,
    coef_lap (inH_one_of_two h2), coef_lap_lap' h2, h0, cubic_two_mode, coef_add, coef_add,
    coef_add, coef_smul, coef_smul, coef_basis, coef_basis, coef_basis, coef_basis, if_pos rfl,
    if_neg (nsmul_ne_self hn), if_neg (nsmul_ne_neg hn), if_neg (nsmul_ne_neg_nsmul hn)]
  ring

omit hL in
theorem xi2_neg (n : Fin d → ℤ) : xi2 L (-n) = xi2 L n := by
  simp only [xi2, xi, Pi.neg_apply, Int.cast_neg, mul_neg, neg_sq]

omit hL in
theorem xi2_three_nsmul (n : Fin d → ℤ) : xi2 L (3 • n) = 9 * xi2 L n := by
  have h : ∀ j, (((3 • n : Fin d → ℤ) j : ℤ) : ℝ) = 3 * (n j : ℝ) := fun j => by
    rw [Pi.smul_apply, nsmul_eq_mul]; push_cast; ring
  simp only [xi2, xi, h, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem xi2_pos {n : Fin d → ℤ} (hn : n ≠ 0) : 0 < xi2 L n := by
  obtain ⟨j, hj⟩ : ∃ j, n j ≠ 0 := by
    by_contra h; push_neg at h; exact hn (funext h)
  have hc : 0 < 2 * π / L := div_pos Real.two_pi_pos hL.out
  have : 0 < xi L n j ^ 2 := by
    rw [xi]; exact sq_pos_iff.2 (mul_ne_zero hc.ne' (by exact_mod_cast hj))
  exact this.trans_le (xi_sq_le_xi2 n j)

theorem hasDerivWithinAt_coef {A : ℝ → L2 L d} {A' : L2 L d} {s : Set ℝ} {t : ℝ}
    (hA : HasDerivWithinAt A A' s t) (k : Fin d → ℤ) :
    HasDerivWithinAt (fun u => coef (A u) k) (coef A' k) s t := by
  have e : ∀ B : L2 L d, innerSL ℂ (basis L d k) B = coef B k := fun B => by
    rw [innerSL_apply, ← HilbertBasis.repr_apply_apply, repr_eq_coef]
  have h : HasDerivWithinAt (fun u => innerSL ℂ (basis L d k) (A u))
      (innerSL ℂ (basis L d k) A') s t :=
    (((innerSL ℂ (basis L d k)).hasFDerivAt (x := A t)).restrictScalars ℝ).comp_hasDerivWithinAt
      t hA
  simpa only [e] using h

/-- **The nonlinear equation does not preserve finite Fourier shells** (for `β ≠ 0`): for `n ≠ 0`
the shell `S = {m : |ξ_m|² = |ξ_n|²}` is finite and carries `A₀ = e_n + e_{−n}`, yet no solution of
E13 starting from `A₀` stays in the band-limited space `H_S` on any interval `[0, T]`. -/
theorem shell_not_invariant (hβ : β ≠ 0) {n : Fin d → ℤ} (hn : n ≠ 0) :
    {m : Fin d → ℤ | xi2 L m = xi2 L n}.Finite ∧
    basis L d n + basis L d (-n) ∈ H L d {m | xi2 L m = xi2 L n} ∧
    ∀ {T : ℝ}, 0 < T → ∀ A : ℝ → L2 L d, A 0 = basis L d n + basis L d (-n) →
      HasDerivWithinAt A (rhs r a b β (A 0)) (Icc 0 T) 0 →
      ¬ ∀ t ∈ Icc 0 T, A t ∈ H L d {m | xi2 L m = xi2 L n} := by
  refine ⟨?_, ?_, ?_⟩
  · refine (eventually_cofinite.1 (tendsto_atTop.1 (tendsto_xi2 (L := L)) (xi2 L n + 1))).subset
      fun m hm => ?_
    simp only [mem_setOf_eq] at hm ⊢
    linarith
  · rw [mem_H]
    intro k hk
    simp only [mem_setOf_eq] at hk
    rw [coef_add, coef_basis, coef_basis, if_neg (fun h => hk (by rw [h])),
      if_neg (fun h => hk (by rw [h, xi2_neg])), add_zero]
  · intro T hT A hA0 hder hinv
    have hS : 3 • n ∉ {m : Fin d → ℤ | xi2 L m = xi2 L n} := by
      simp only [mem_setOf_eq, xi2_three_nsmul]
      have := xi2_pos (L := L) hn
      intro h; linarith
    have hzero : ∀ t ∈ Icc 0 T, coef (A t) (3 • n) = 0 := fun t ht => mem_H.1 (hinv t ht) _ hS
    have h1 := hasDerivWithinAt_coef hder (3 • n)
    have h2 : HasDerivWithinAt (fun u => coef (A u) (3 • n)) 0 (Icc 0 T) 0 :=
      (hasDerivWithinAt_const (0 : ℝ) (Icc 0 T) (0 : ℂ)).congr (fun u hu => hzero u hu)
        (hzero 0 ⟨le_rfl, hT.le⟩)
    have h3 := (uniqueDiffOn_Icc hT 0 ⟨le_rfl, hT.le⟩).eq_deriv _ h1 h2
    rw [hA0, coef_rhs_two_mode r a b β hn, neg_eq_zero] at h3
    exact hβ (by exact_mod_cast h3)


/-! ### The lower bound for `β > 0` and finite total dissipation -/

theorem quad_lower (hβ : 0 < β) (m : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    -((max m 0) ^ 2 / (2 * β)) ≤ β / 2 * s ^ 2 - m * s := by
  have h1 : m * s ≤ max m 0 * s := mul_le_mul_of_nonneg_right (le_max_left _ _) hs
  have h2 : 0 ≤ β / 2 * (s - max m 0 / β) ^ 2 := by positivity
  have h3 : β / 2 * (s - max m 0 / β) ^ 2 - (max m 0) ^ 2 / (2 * β) =
      β / 2 * s ^ 2 - max m 0 * s := by
    field_simp; ring
  linarith

/-- **Energy lower bound**: for `b, β > 0` and `A ∈ H²`, `E[A] ≥ −(|Ω|/(2β)) (max{μ, 0})²`
with `|Ω| = L^d`. -/
theorem energy_lower (hd : d ≤ 3) (hb : 0 < b) (hβ : 0 < β) {A : L2 L d} (hA : InH 1 A) :
    -(L ^ d / (2 * β) * (max (muSH r a b) 0) ^ 2) ≤ energy r a b β A := by
  obtain ⟨c, rfl⟩ := (inH_iff 1 A).1 hA
  have hLd : 0 < L ^ d := pow_pos hL.out d
  rw [← energySH_eq r a b β hd hb.ne' hA, energySH, integral_volume_real]
  have hint : Integrable (fun x => -muSH r a b * ‖(iota L 1 c : L2 L d) x‖ ^ 2 +
      b * ‖(shiftOp a b (iota L 1 c) : L2 L d) x‖ ^ 2 +
      β / 2 * ‖(iota L 1 c : L2 L d) x‖ ^ 4) (μ L d) :=
    (((integrable_norm_sq (iota L 1 c)).const_mul _).add
      ((integrable_norm_sq (shiftOp a b (iota L 1 c))).const_mul _)).add
      ((integrable_norm_four_iota (L := L) hd c).const_mul _)
  have hmono := integral_mono (integrable_const (-((max (muSH r a b) 0) ^ 2 / (2 * β))))
    hint fun x => by
      have h1 := quad_lower β hβ (muSH r a b) (sq_nonneg ‖(iota L 1 c : L2 L d) x‖)
      have h2 := mul_nonneg hb.le (sq_nonneg ‖(shiftOp a b (iota L 1 c) : L2 L d) x‖)
      have e : (‖(iota L 1 c : L2 L d) x‖ ^ 2) ^ 2 = ‖(iota L 1 c : L2 L d) x‖ ^ 4 := by ring
      simp only
      linarith
  rw [integral_const, measureReal_univ_eq_one, one_smul] at hmono
  have := mul_le_mul_of_nonneg_left hmono hLd.le
  have e : L ^ d * -((max (muSH r a b) 0) ^ 2 / (2 * β)) =
      -(L ^ d / (2 * β) * (max (muSH r a b) 0) ^ 2) := by ring
  linarith

theorem rhs_eq_iota_deriv {s : Set ℝ} (hs : UniqueDiffOn ℝ s) {A : ℝ → L2 L d}
    {c c' : ℝ → ell2 d} (hAc : ∀ t ∈ s, A t = iota L 1 (c t))
    (hc : ∀ t ∈ s, HasDerivWithinAt c (c' t) s t)
    (hpde : ∀ t ∈ s, HasDerivWithinAt A (rhs r a b β (A t)) s t) :
    ∀ t ∈ s, rhs r a b β (A t) = iota L 1 (c' t) := by
  intro t ht
  have h1 : HasDerivWithinAt A (iota L 1 (c' t)) s t :=
    (hasDerivWithinAt_clm (iota L 1) (hc t ht)).congr (fun u hu => hAc u hu) (hAc t ht)
  exact (hs t ht).eq_deriv _ (hpde t ht) h1

theorem continuousOn_dissipation {s : Set ℝ} (hs : UniqueDiffOn ℝ s) {A : ℝ → L2 L d}
    {c c' : ℝ → ell2 d} (hAc : ∀ t ∈ s, A t = iota L 1 (c t))
    (hc : ∀ t ∈ s, HasDerivWithinAt c (c' t) s t) (hc' : ContinuousOn c' s)
    (hpde : ∀ t ∈ s, HasDerivWithinAt A (rhs r a b β (A t)) s t) :
    ContinuousOn (fun t => ∫ x, ‖rhs r a b β (A t) x‖ ^ 2) s := by
  have : ContinuousOn (fun t => L ^ d * ‖iota L 1 (c' t)‖ ^ 2) s :=
    continuousOn_const.mul ((continuous_norm.comp (iota L 1).continuous).continuousOn.comp hc'
      (mapsTo_univ _ _) |>.pow 2)
  refine this.congr fun t ht => ?_
  show ∫ x, ‖rhs r a b β (A t) x‖ ^ 2 = L ^ d * ‖iota L 1 (c' t)‖ ^ 2
  rw [rhs_eq_iota_deriv r a b β hs hAc hc hpde t ht, integral_norm_sq_vol]

/-- **Finite total dissipation**: for `b, β > 0`, a solution with the regularity of `e13` on every
`[0, T]` satisfies `∫₀^∞ ‖∂ₜA‖²_{L²(Ω)} dt ≤ ½ (E[A(0)] + (|Ω|/(2β)) (max{μ, 0})²) < ∞`. -/
theorem finite_dissipation (hd : d ≤ 3) (hb : 0 < b) (hβ : 0 < β) {A : ℝ → L2 L d}
    {c c' : ℝ → ell2 d} (hAc : ∀ t ∈ Ici (0 : ℝ), A t = iota L 1 (c t))
    (hc : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt c (c' t) (Ici 0) t)
    (hc' : ContinuousOn c' (Ici 0)) (h4 : ∀ t ∈ Ici (0 : ℝ), InH 2 (A t))
    (hpde : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt A (rhs r a b β (A t)) (Ici 0) t) :
    IntegrableOn (fun t => ∫ x, ‖rhs r a b β (A t) x‖ ^ 2) (Ioi 0) ∧
    ∫ t in Ioi (0 : ℝ), ∫ x, ‖rhs r a b β (A t) x‖ ^ 2 ≤
      (energy r a b β (A 0) + L ^ d / (2 * β) * (max (muSH r a b) 0) ^ 2) / 2 := by
  set f : ℝ → ℝ := fun t => ∫ x, ‖rhs r a b β (A t) x‖ ^ 2 with hf
  have hf0 : ∀ t, 0 ≤ f t := fun t => integral_nonneg fun x => by positivity
  have hcont : ContinuousOn f (Ici 0) :=
    continuousOn_dissipation r a b β (uniqueDiffOn_Ici 0) hAc hc hc' hpde
  have hfi : ∀ i : ℝ, IntegrableOn f (Ioc 0 i) := fun i =>
    ((hcont.mono Icc_subset_Ici_self).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  -- the bound on `[0, T]`
  have hbound : ∀ T : ℝ, 0 < T → ∫ t in (0 : ℝ)..T, f t ≤
      (energy r a b β (A 0) + L ^ d / (2 * β) * (max (muSH r a b) 0) ^ 2) / 2 := by
    intro T hT
    have sub : Icc 0 T ⊆ Ici 0 := Icc_subset_Ici_self
    obtain ⟨-, -, -, -, hbal, -⟩ := e13 r a b β hd hT (fun t ht => hAc t (sub ht))
      (fun t ht => (hc t (sub ht)).mono sub) (hc'.mono sub) (fun t ht => h4 t (sub ht))
      (fun t ht => (hpde t (sub ht)).mono sub)
    have hT' : InH 1 (A T) := (inH_iff 1 _).2 ⟨c T, hAc T hT.le⟩
    have hlow := energy_lower r a b β hd hb hβ hT'
    simp only [hf]
    linarith
  have hint : IntegrableOn f (Ioi 0) := by
    refine integrableOn_Ioi_of_intervalIntegral_norm_bounded
      ((energy r a b β (A 0) + L ^ d / (2 * β) * (max (muSH r a b) 0) ^ 2) / 2) 0 hfi tendsto_id ?_
    filter_upwards [eventually_gt_atTop 0] with i hi
    have : ∫ x in (0 : ℝ)..i, ‖f x‖ = ∫ x in (0 : ℝ)..i, f x :=
      intervalIntegral.integral_congr fun x _ => Real.norm_of_nonneg (hf0 x)
    rw [this]
    exact hbound i hi
  refine ⟨hint, ?_⟩
  refine le_of_tendsto (intervalIntegral_tendsto_integral_Ioi 0 hint tendsto_id) ?_
  filter_upwards [eventually_gt_atTop 0] with i hi
  exact hbound i hi

/-- **Periodic solutions are stationary**: if a solution as in `e13` returns to its initial
state, `A(T) = A(0)`, then `∂ₜA = 0` throughout `[0, T]`. -/
theorem periodic_stationary (hd : d ≤ 3) {T : ℝ} (hT : 0 < T) {A : ℝ → L2 L d}
    {c c' : ℝ → ell2 d} (hAc : ∀ t ∈ Icc 0 T, A t = iota L 1 (c t))
    (hc : ∀ t ∈ Icc 0 T, HasDerivWithinAt c (c' t) (Icc 0 T) t)
    (hc' : ContinuousOn c' (Icc 0 T)) (h4 : ∀ t ∈ Icc 0 T, InH 2 (A t))
    (hpde : ∀ t ∈ Icc 0 T, HasDerivWithinAt A (rhs r a b β (A t)) (Icc 0 T) t)
    (hper : A T = A 0) : ∀ t ∈ Icc 0 T, rhs r a b β (A t) = 0 := by
  obtain ⟨-, -, -, -, hbal, heq⟩ := e13 r a b β hd hT hAc hc hc' h4 hpde
  set f : ℝ → ℝ := fun t => ∫ x, ‖rhs r a b β (A t) x‖ ^ 2 with hf
  have hf0 : ∀ t, 0 ≤ f t := fun t => integral_nonneg fun x => by positivity
  have hcont : ContinuousOn f (Icc 0 T) :=
    continuousOn_dissipation r a b β (uniqueDiffOn_Icc hT) hAc hc hc' hpde
  have hzero : ∫ t in (0 : ℝ)..T, f t = 0 := by
    rw [hper] at hbal; simp only [hf]; linarith
  have hae := (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae hT.le
    (Eventually.of_forall fun t => hf0 t) (hcont.intervalIntegrable_of_Icc hT.le)).1 hzero
  have hae' : f =ᵐ[volume.restrict (Icc 0 T)] 0 := by
    rwa [← Measure.restrict_congr_set Ioc_ae_eq_Icc]
  have hEq := Measure.eqOn_Icc_of_ae_eq volume hT.ne hae' hcont continuousOn_const
  intro t ht
  have h0 : f t = 0 := hEq ht
  exact (heq t ht).1 (by simp only [hf] at h0; rw [h0]; ring)


/-- **The balance law on subintervals** (E14): under the hypotheses of `e13`,
`E[A(t₂)] + 2∫_{t₁}^{t₂} ‖∂ₜA‖²_{L²(Ω)} dt = E[A(t₁)]` for `0 ≤ t₁ ≤ t₂ ≤ T`. -/
theorem balance_interval (hd : d ≤ 3) {T : ℝ} (hT : 0 < T) {A : ℝ → L2 L d}
    {c c' : ℝ → ell2 d} (hAc : ∀ t ∈ Icc 0 T, A t = iota L 1 (c t))
    (hc : ∀ t ∈ Icc 0 T, HasDerivWithinAt c (c' t) (Icc 0 T) t)
    (hc' : ContinuousOn c' (Icc 0 T)) (h4 : ∀ t ∈ Icc 0 T, InH 2 (A t))
    (hpde : ∀ t ∈ Icc 0 T, HasDerivWithinAt A (rhs r a b β (A t)) (Icc 0 T) t)
    {t₁ t₂ : ℝ} (h01 : 0 ≤ t₁) (h12 : t₁ ≤ t₂) (h2T : t₂ ≤ T) :
    energy r a b β (A t₂) + 2 * ∫ t in t₁..t₂, ∫ x, ‖rhs r a b β (A t) x‖ ^ 2 =
      energy r a b β (A t₁) := by
  obtain ⟨-, -, hE, -⟩ := e13 r a b β hd hT hAc hc hc' h4 hpde
  have hsub : Icc t₁ t₂ ⊆ Icc 0 T := Icc_subset_Icc h01 h2T
  have hcont := continuousOn_dissipation r a b β (uniqueDiffOn_Icc hT) hAc hc hc' hpde
  have hftc := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le h12
    (f := fun s => energy r a b β (A s)) (f' := fun t => -2 * ∫ x, ‖rhs r a b β (A t) x‖ ^ 2)
    (fun t ht => ((hE t (hsub ht)).continuousWithinAt).mono hsub)
    (fun t ht => by
      have ht' : t ∈ Ioo 0 T := ⟨h01.trans_lt ht.1, ht.2.trans_le h2T⟩
      exact ((hE t (Ioo_subset_Icc_self ht')).hasDerivAt
        (Icc_mem_nhds ht'.1 ht'.2)).hasDerivWithinAt)
    ((continuousOn_const.mul (hcont.mono hsub)).intervalIntegrable_of_Icc h12)
  rw [intervalIntegral.integral_const_mul] at hftc
  linarith

end BandPass
end ReyesMath
