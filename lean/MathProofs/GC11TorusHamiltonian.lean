import MathProofs.GC11TorusInitial

/-!
# GC11: exact carrier-frame Hamiltonian, kinetic first variation

The actual torus L² multiplier and its square-root form on H² are
linked by Parseval. The nonlinear term is the exact cubic-quintic
chemical-potential subtraction, not a generic conservation axiom.
-/
noncomputable section
open MeasureTheory Complex
open scoped ComplexConjugate InnerProductSpace
namespace ReyesMath
namespace GC11TorusHamiltonian

open BandPass TorusL2 GC11Coercivity GC11TorusEnergy GC11TorusOrbit

variable (L : ℝ) [Fact (0 < L)]

theorem norm_g_le {k : ℝ} {K : Fin 2 → ℝ} (hq : k ^ 2 ≤ carrierSq K)
    (n : Fin 2 → ℤ) :
    ‖(g L k K n : ℂ)‖ ≤ (2 + 10 * carrierSq K) * wt L n ^ 2 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (g_nonneg L hq n)]
  exact g_upper L k K n

theorem norm_sqrt_g_le (k : ℝ) (K : Fin 2 → ℝ) (n : Fin 2 → ℤ) :
    ‖(Real.sqrt (g L k K n) : ℂ)‖ ≤ Real.sqrt (2 + 10 * carrierSq K) * wt L n ^ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), pow_one]
  have hC : 0 ≤ 2 + 10 * carrierSq K := by linarith [carrierSq_nonneg K]
  have h := Real.sqrt_le_sqrt (g_upper L k K n)
  rw [Real.sqrt_mul hC, Real.sqrt_sq (wt_pos (L := L) n).le] at h
  exact h

/-- Square-root operator of the nonnegative shifted kinetic multiplier. -/
def sqrtOp (k : ℝ) (K : Fin 2 → ℝ) : ell2 2 →L[ℂ] TorusL2.L2 L 2 :=
  opS 1 (fun n => (Real.sqrt (g L k K n) : ℂ)) (norm_sqrt_g_le L k K)

/-- Full fourth-order operator on the H⁴ domain. -/
def carrierOp (k : ℝ) (K : Fin 2 → ℝ) (A : TorusL2.L2 L 2) : TorusL2.L2 L 2 :=
  pmul (fun n => (g L k K n : ℂ)) A

theorem coef_sqrtOp (k : ℝ) (K : Fin 2 → ℝ) (c : ell2 2) (n : Fin 2 → ℤ) :
    coef (sqrtOp L k K c) n =
      (Real.sqrt (g L k K n) : ℂ) * coef (iota L 1 c) n := by
  rw [sqrtOp, coef_opS, coef_iota, mul_assoc]

theorem coef_carrierOp {k : ℝ} {K : Fin 2 → ℝ} (hq : k ^ 2 ≤ carrierSq K)
    {A : TorusL2.L2 L 2} (hA : InH 2 A) (n : Fin 2 → ℤ) :
    coef (carrierOp L k K A) n = (g L k K n : ℂ) * coef A n := by
  exact coef_pmul (memℓp_of_inH (norm_g_le L hq) hA) n

theorem kinetic_eq_norm {k : ℝ} {K : Fin 2 → ℝ} (hq : k ^ 2 ≤ carrierSq K)
    (c : ell2 2) :
    kinetic L k K (iota L 1 c) = ‖sqrtOp L k K c‖ ^ 2 := by
  rw [norm_sq_eq_tsum]
  unfold kinetic
  congr 1
  funext n
  rw [coef_sqrtOp, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (g_nonneg L hq n)]

/-- Exact form-operator correspondence, on the actual H⁴ domain. -/
theorem sqrtOp_inner {k : ℝ} {K : Fin 2 → ℝ} (hq : k ^ 2 ≤ carrierSq K)
    {c : ell2 2} (h4 : InH 2 (iota L 1 c)) (b : ell2 2) :
    ⟪sqrtOp L k K c, sqrtOp L k K b⟫_ℂ =
      ⟪carrierOp L k K (iota L 1 c), iota L 1 b⟫_ℂ := by
  refine (hasSum_inner (sqrtOp L k K c) (sqrtOp L k K b)).unique
    ((hasSum_inner (carrierOp L k K (iota L 1 c)) (iota L 1 b)).congr_fun fun n => ?_)
  rw [coef_sqrtOp, coef_sqrtOp, coef_carrierOp L hq h4]
  simp only [map_mul, Complex.conj_ofReal]
  have hsq : (Real.sqrt (g L k K n) : ℂ) ^ 2 = (g L k K n : ℂ) := by
    exact_mod_cast Real.sq_sqrt (g_nonneg L hq n)
  calc
    _ = (Real.sqrt (g L k K n) : ℂ) ^ 2 *
      conj (coef (iota L 1 c) n) * coef (iota L 1 b) n := by ring
    _ = _ := by rw [hsq]; ring

theorem carrier_inner_im {k : ℝ} {K : Fin 2 → ℝ} (hq : k ^ 2 ≤ carrierSq K)
    {c : ell2 2} (h4 : InH 2 (iota L 1 c)) :
    (⟪iota L 1 c, carrierOp L k K (iota L 1 c)⟫_ℂ).im = 0 := by
  rw [← inner_conj_symm]
  have h := sqrtOp_inner L hq h4 c
  rw [← h]
  simp

/-- Exact nonlinearity (f(|z|²)-f(ρ))z in the carrier frame. -/
def nonlinearMap (beta gamma rho : ℝ) (F : C(Tor L 2, ℂ)) : C(Tor L 2, ℂ) where
  toFun x := ((densitySlope beta gamma (‖F x‖ ^ 2) - densitySlope beta gamma rho : ℝ) : ℂ) * F x
  continuous_toFun := by unfold densitySlope; fun_prop

def nonlinear (beta gamma rho : ℝ) (c : ell2 2) : TorusL2.L2 L 2 :=
  ContinuousMap.toLp (E := ℂ) 2 (μ L 2) ℂ (nonlinearMap L beta gamma rho (Phi L (by decide : 2 ≤ 3) c))

theorem nonlinear_ae (beta gamma rho : ℝ) (c : ell2 2) :
    (nonlinear L beta gamma rho c : Tor L 2 → ℂ) =ᵐ[μ L 2] fun x =>
      ((densitySlope beta gamma (‖Phi L (by decide : 2 ≤ 3) c x‖ ^ 2) -
        densitySlope beta gamma rho : ℝ) : ℂ) * Phi L (by decide : 2 ≤ 3) c x := by
  exact ContinuousMap.coeFn_toLp _ _

theorem nonlinear_inner_im (beta gamma rho : ℝ) (c : ell2 2) :
    (⟪iota L 1 c, nonlinear L beta gamma rho c⟫_ℂ).im = 0 := by
  rw [MeasureTheory.L2.inner_def]
  let F := Phi L (by decide : 2 ≤ 3) c
  have he : (∫ x, inner ℂ (iota L 1 c x) (nonlinear L beta gamma rho c x) ∂(μ L 2)) =
      ∫ x, (((densitySlope beta gamma (‖F x‖ ^ 2) - densitySlope beta gamma rho) *
        ‖F x‖ ^ 2 : ℝ) : ℂ) ∂(μ L 2) := by
    apply integral_congr_ae
    filter_upwards [iota_ae_eq_Phi (L := L) (by decide : 2 ≤ 3) c,
      nonlinear_ae L beta gamma rho c] with x hx hy
    rw [hx, hy]
    simp only [RCLike.inner_apply]
    change conj (F x) * _ = _
    have hh : conj (F x) * F x = ((‖F x‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.conj_mul']; push_cast; ring
    push_cast
    calc _ = ((densitySlope beta gamma (‖F x‖ ^ 2) - densitySlope beta gamma rho : ℝ) : ℂ) *
        (conj (F x) * F x) := by ring
         _ = _ := by rw [hh]
  rw [he, integral_complex_ofReal, Complex.ofReal_im]

def gradient (k beta gamma rho : ℝ) (K : Fin 2 → ℝ) (c : ell2 2) : TorusL2.L2 L 2 :=
  carrierOp L k K (iota L 1 c) + nonlinear L beta gamma rho c

/-- A strong carrier-frame solution, differentiable in H² and H⁴-valued.
The stronger regularity is explicit; general mild solutions are not claimed. -/
def StrongSolution (k beta gamma rho : ℝ) (K : Fin 2 → ℝ) (u : ℝ → ell2 2) : Prop :=
  ∀ t : ℝ, InH 2 (iota L 1 (u t)) ∧
    ∃ du : ell2 2, HasDerivAt u du t ∧
      iota L 1 du = (-Complex.I) • gradient L k beta gamma rho K (u t)

theorem hasDerivAt_mass_strong {k beta gamma rho : ℝ} {K : Fin 2 → ℝ}
    (hq : k ^ 2 ≤ carrierSq K) {u : ℝ → ell2 2}
    (hu : StrongSolution L k beta gamma rho K u) (t : ℝ) :
    HasDerivAt (fun s => mass L (u s)) 0 t := by
  obtain ⟨h4, du, hd, he⟩ := hu t
  have h := (((iota L 1).hasFDerivAt (x := u t)).restrictScalars ℝ).comp_hasDerivAt t hd
  have hi := h.norm_sq
  have him : (⟪iota L 1 (u t), gradient L k beta gamma rho K (u t)⟫_ℂ).im = 0 := by
    unfold gradient
    rw [inner_add_right, Complex.add_im, carrier_inner_im L hq h4, nonlinear_inner_im, add_zero]
  have hz : (inner ℝ (iota L 1 (u t)) (iota L 1 du) : ℝ) = 0 := by
    rw [real_inner_eq_re, he, inner_smul_right]
    simp [Complex.mul_re, him]
  simpa [mass, hz] using hi

theorem mass_conserved_strong {k beta gamma rho : ℝ} {K : Fin 2 → ℝ}
    (hq : k ^ 2 ≤ carrierSq K) {u : ℝ → ell2 2}
    (hu : StrongSolution L k beta gamma rho K u) (t : ℝ) :
    mass L (u t) = mass L (u 0) :=
  is_const_of_deriv_eq_zero (f := fun s => mass L (u s))
    (fun s => (hasDerivAt_mass_strong L hq hu s).differentiableAt)
    (fun s => (hasDerivAt_mass_strong L hq hu s).deriv) t 0

theorem hasDerivAt_kinetic {k : ℝ} {K : Fin 2 → ℝ} (hq : k ^ 2 ≤ carrierSq K)
    {u : ℝ → ell2 2} {du : ell2 2} {t : ℝ}
    (h4 : InH 2 (iota L 1 (u t))) (hd : HasDerivAt u du t) :
    HasDerivAt (fun s => kinetic L k K (iota L 1 (u s)))
      (2 * (⟪carrierOp L k K (iota L 1 (u t)), iota L 1 du⟫_ℂ).re) t := by
  have h := (((sqrtOp L k K).hasFDerivAt (x := u t)).restrictScalars ℝ).comp_hasDerivAt t hd
  have hi := h.norm_sq
  have he : (fun s => kinetic L k K (iota L 1 (u s))) =
      fun s => ‖sqrtOp L k K (u s)‖ ^ 2 := by
    funext s
    exact kinetic_eq_norm L hq (u s)
  rw [he]
  simpa only [real_inner_eq_re, sqrtOp_inner L hq h4 du] using hi

end GC11TorusHamiltonian
end ReyesMath
