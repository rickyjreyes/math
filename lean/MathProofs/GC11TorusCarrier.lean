import MathProofs.GC11TorusConservation
import MathProofs.GC11SidebandClassification
import MathProofs.GC11StaticWave

/-!
# GC11: original periodic stationary equation and exact carrier symbol

This module connects the shifted operator to the original (Δ+k²)²
Fourier multiplier, and constructs two exact stationary fields on ONE
torus at identical parameters. The carrier-frame equilibrium is also a
global strong solution, so the earlier stability predicate is nonempty.
The full time-dependent conjugacy and general mild existence are separate.
-/
noncomputable section
open MeasureTheory Complex
namespace ReyesMath
namespace GC11TorusCarrier

open BandPass TorusL2 RemainingCores GC11Coercivity GC11TorusEnergy
  GC11TorusOrbit GC11TorusInitial GC11TorusHamiltonian GC11TorusConservation

variable (L : ℝ) [Fact (0 < L)]

def latticeCarrier (m : Fin 2 → ℤ) : Fin 2 → ℝ := xi L m

theorem latticeCarrier_sq (m : Fin 2 → ℤ) :
    carrierSq (latticeCarrier L m) = xi2 L m := by
  simp [carrierSq, latticeCarrier, xi2, Fin.sum_univ_two]

theorem xi_add (m n : Fin 2 → ℤ) (j : Fin 2) :
    xi L (m + n) j = xi L m j + xi L n j := by
  simp [xi, Pi.add_apply, Int.cast_add, mul_add]

theorem xi2_shift (m n : Fin 2 → ℤ) :
    xi2 L (m + n) = carrierSq (latticeCarrier L m) + xi2 L n +
      2 * carrierDot L (latticeCarrier L m) n := by
  simp only [xi2, Fin.sum_univ_two, carrierSq, carrierDot, latticeCarrier, xi_add]
  ring

/-- Exact symbol identity on the full lattice of the original equation. -/
theorem carrier_symbol_eq (k : ℝ) (m n : Fin 2 → ℤ) :
    g L k (latticeCarrier L m) n =
      shellSymbol k (xi2 L (m + n)) - shellSymbol k (xi2 L m) -
      4 * (xi2 L m - k ^ 2) * carrierDot L (latticeCarrier L m) n := by
  unfold g excess
  rw [← xi2_shift L m n, latticeCarrier_sq]

/-- The original fourth-order operator, using the maintained torus Laplacian. -/
def originalOp (k : ℝ) (A : TorusL2.L2 L 2) : TorusL2.L2 L 2 :=
  shiftOp (2 * k ^ 2) 1 (shiftOp (2 * k ^ 2) 1 A)

theorem originalOp_coef (k : ℝ) {A : TorusL2.L2 L 2} (hA : InH 2 A)
    (n : Fin 2 → ℤ) :
    coef (originalOp L k A) n = (shellSymbol k (xi2 L n) : ℂ) * coef A n := by
  unfold originalOp
  rw [coef_shiftOp_shiftOp _ _ hA]
  unfold kstar2 shellSymbol
  push_cast
  ring

def planeField (a : ℂ) (m : Fin 2 → ℤ) : C(Tor L 2, ℂ) := a • emode m

def fieldL2 (F : C(Tor L 2, ℂ)) : TorusL2.L2 L 2 :=
  ContinuousMap.toLp (E := ℂ) 2 (μ L 2) ℂ F

theorem planeField_norm (a : ℂ) (m : Fin 2 → ℤ) (x : Tor L 2) :
    ‖planeField L a m x‖ = ‖a‖ := by
  rw [planeField, ContinuousMap.smul_apply, smul_eq_mul, norm_mul, norm_emode_apply, mul_one]

theorem planeField_L2 (a : ℂ) (m : Fin 2 → ℤ) :
    fieldL2 L (planeField L a m) = a • basis L 2 m := by
  rw [fieldL2, planeField, map_smul, ← basis_eq_toLp]

theorem originalOp_plane (k : ℝ) (a : ℂ) (m : Fin 2 → ℤ) :
    originalOp L k (fieldL2 L (planeField L a m)) =
      (shellSymbol k (xi2 L m) : ℂ) • fieldL2 L (planeField L a m) := by
  rw [planeField_L2]
  have hA := inH_smul (inH_basis (L := L) 2 m) a
  apply ext_coef
  intro n
  rw [originalOp_coef L k hA, coef_smul, coef_smul, coef_basis]
  by_cases hn : n = m
  · subst n
    simp [mul_comm]
  · simp [hn]

/-- Original cubic-quintic nonlinearity, without carrier or chemical subtraction. -/
def originalNonlinearMap (beta gamma : ℝ) (F : C(Tor L 2, ℂ)) : C(Tor L 2, ℂ) where
  toFun x := (densitySlope beta gamma (‖F x‖ ^ 2) : ℂ) * F x
  continuous_toFun := by unfold densitySlope; fun_prop

def originalResidual (k beta gamma : ℝ) (F : C(Tor L 2, ℂ)) : TorusL2.L2 L 2 :=
  originalOp L k (fieldL2 L F) + fieldL2 L (originalNonlinearMap L beta gamma F)

theorem originalNonlinear_plane (beta gamma : ℝ) (a : ℂ) (m : Fin 2 → ℤ) :
    originalNonlinearMap L beta gamma (planeField L a m) =
      (densitySlope beta gamma (‖a‖ ^ 2) : ℂ) • planeField L a m := by
  ext x
  change (densitySlope beta gamma (‖planeField L a m x‖ ^ 2) : ℂ) *
    planeField L a m x = _
  rw [planeField_norm]
  rfl

/-- Actual stationary equation in L², not merely a frequency root. -/
theorem stationary_plane {k beta gamma : ℝ} {a : ℂ} {m : Fin 2 → ℤ}
    (hf : frequency k beta gamma (‖a‖ ^ 2) (xi2 L m) = 0) :
    originalResidual L k beta gamma (planeField L a m) = 0 := by
  unfold originalResidual
  have hn : fieldL2 L (originalNonlinearMap L beta gamma (planeField L a m)) =
      (densitySlope beta gamma (‖a‖ ^ 2) : ℂ) • fieldL2 L (planeField L a m) := by
    rw [originalNonlinear_plane]
    unfold fieldL2
    rw [map_smul]
  rw [originalOp_plane, hn, ← add_smul]
  have h : shellSymbol k (xi2 L m) + densitySlope beta gamma (‖a‖ ^ 2) = 0 := by
    unfold frequency at hf
    unfold densitySlope
    linarith
  have hc : (shellSymbol k (xi2 L m) : ℂ) +
      (densitySlope beta gamma (‖a‖ ^ 2) : ℂ) = 0 := by exact_mod_cast h
  rw [hc, zero_smul]

theorem constant_iota (a : ℂ) :
    iota L 1 (constantCoeff a) = a • basis L 2 0 := by
  apply ext_coef
  intro n
  rw [coef_iota, constantCoeff_apply, coef_smul, coef_basis]
  by_cases hn : n = 0
  · subst n
    simp [wt_zero]
  · simp [hn]

theorem strong_constant {k beta gamma rho : ℝ} {K : Fin 2 → ℝ}
    (hq : k ^ 2 ≤ carrierSq K) {a : ℂ} (ha : ‖a‖ ^ 2 = rho) :
    StrongSolution L k beta gamma rho K (fun _ => constantCoeff a) := by
  have h4 : InH 2 (iota L 1 (constantCoeff a)) := by
    rw [constant_iota]
    exact inH_smul (inH_basis 2 0) a
  have hk : carrierOp L k K (iota L 1 (constantCoeff a)) = 0 := by
    apply ext_coef
    intro n
    rw [coef_carrierOp L hq h4, constant_iota, coef_smul, coef_basis, coef_zero]
    by_cases hn : n = 0
    · subst n
      simp [g_zero]
    · simp [hn]
  have hp : nonlinear L beta gamma rho (constantCoeff a) = 0 := by
    apply MeasureTheory.Lp.ext
    filter_upwards [nonlinear_ae L beta gamma rho (constantCoeff a),
      MeasureTheory.Lp.coeFn_zero (p := 2) (μ := μ L 2) (E := ℂ)] with x hx hy
    rw [hx, Phi_constant, ha, sub_self, Complex.ofReal_zero, zero_mul, hy]
  intro t
  refine ⟨h4, 0, hasDerivAt_const t (constantCoeff a), ?_⟩
  simp [gradient, hk, hp]

/-- Common torus for the two different stable stationary wavelengths. -/
def commonLength : ℝ := 40 * Real.pi

instance commonLength_pos : Fact (0 < commonLength) :=
  ⟨mul_pos (by norm_num) Real.pi_pos⟩

def axialIndex (j : ℤ) : Fin 2 → ℤ := fun i => if i = 0 then j else 0

theorem common_xi2 (j : ℤ) :
    xi2 commonLength (axialIndex j) = (j : ℝ) ^ 2 / 400 := by
  have hp := Real.pi_pos
  have he : 2 * Real.pi / commonLength = 1 / 20 := by
    unfold commonLength
    field_simp [hp.ne']
    <;> ring
  simp [xi2, Fin.sum_univ_two, xi, he, axialIndex]
  <;> ring

def upperRho (q : ℝ) : ℝ := (1 + Real.sqrt (1 - 4 * (q - 1) ^ 2)) / 2

theorem upperRho_data {q : ℝ} (hlo : 1 < q)
    (hhi : (q - 1) ^ 2 < 3/16) :
    3/4 < upperRho q ∧ frequency 1 1 1 (upperRho q) q = 0 := by
  have hrad : 0 ≤ 1 - 4 * (q - 1) ^ 2 := by linarith
  have hs := Real.sq_sqrt hrad
  have hlt : (1/2 : ℝ) < Real.sqrt (1 - 4 * (q - 1) ^ 2) := by
    apply (Real.lt_sqrt (by norm_num : 0 ≤ (1/2 : ℝ))).2
    nlinarith
  constructor
  · unfold upperRho
    linarith
  · unfold upperRho frequency shellSymbol
    nlinarith [hs]

/-- Explicit different lattice radii at the same length and model parameters. -/
theorem common_torus_data :
    let q1 := xi2 commonLength (axialIndex 21)
    let q2 := xi2 commonLength (axialIndex 22)
    1 < q1 ∧ 1 < q2 ∧ q1 ≠ q2 ∧
      3/4 < upperRho q1 ∧ 3/4 < upperRho q2 ∧
      frequency 1 1 1 (upperRho q1) q1 = 0 ∧
      frequency 1 1 1 (upperRho q2) q2 = 0 := by
  dsimp
  rw [common_xi2, common_xi2]
  obtain ⟨h1, hf1⟩ := upperRho_data (q := (21 : ℝ)^2/400) (by norm_num) (by norm_num)
  obtain ⟨h2, hf2⟩ := upperRho_data (q := (22 : ℝ)^2/400) (by norm_num) (by norm_num)
  exact ⟨by norm_num, by norm_num, by norm_num, h1, h2, hf1, hf2⟩

theorem common_torus_stationary :
    ∃ m₁ m₂ : Fin 2 → ℤ, ∃ r₁ r₂ : ℝ,
      xi2 commonLength m₁ ≠ xi2 commonLength m₂ ∧
      1 < xi2 commonLength m₁ ∧ 1 < xi2 commonLength m₂ ∧
      3/4 < r₁ ∧ 3/4 < r₂ ∧
      originalResidual commonLength 1 1 1
        (planeField commonLength (Real.sqrt r₁ : ℂ) m₁) = 0 ∧
      originalResidual commonLength 1 1 1
        (planeField commonLength (Real.sqrt r₂ : ℂ) m₂) = 0 := by
  obtain ⟨hq1, hq2, hne, hr1, hr2, hf1, hf2⟩ := common_torus_data
  refine ⟨axialIndex 21, axialIndex 22,
    upperRho (xi2 commonLength (axialIndex 21)),
    upperRho (xi2 commonLength (axialIndex 22)),
    hne, hq1, hq2, hr1, hr2, ?_, ?_⟩
  · apply stationary_plane
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt (by linarith : 0 ≤ upperRho (xi2 commonLength (axialIndex 21)))]
    exact hf1
  · apply stationary_plane
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt (by linarith : 0 ≤ upperRho (xi2 commonLength (axialIndex 22)))]
    exact hf2


/-- Temporal phase in the transformation from a carrier-frame coefficient
to the laboratory Fourier coefficient at index m+n. -/
def carrierTheta (k beta gamma rho : ℝ) (m n : Fin 2 → ℤ) : ℝ :=
  frequency k beta gamma rho (xi2 L m) +
    4 * (xi2 L m - k ^ 2) * carrierDot L (latticeCarrier L m) n

theorem carrierTheta_balance (k beta gamma rho : ℝ) (m n : Fin 2 → ℤ) :
    g L k (latticeCarrier L m) n + carrierTheta L k beta gamma rho m n =
      shellSymbol k (xi2 L (m+n)) + densitySlope beta gamma rho := by
  rw [carrier_symbol_eq]
  unfold carrierTheta frequency densitySlope
  ring

/-- Exact coefficient-wise time-dependent transformation. The supplied
forcing is the coefficient of the chemical-potential-subtracted
nonlinearity in the moving frame. The conclusion recovers the original
linear dispersion and adds back the chemical term. A separate
function-space theorem must identify the transformed forcing with the
original nonlinear Fourier coefficient. -/
theorem coefficient_laboratory_deriv (k beta gamma rho : ℝ)
    (m n : Fin 2 → ℤ) {z : ℝ → ℂ} {dz N : ℂ} {t : ℝ}
    (hd : HasDerivAt z dz t)
    (he : Complex.I * dz = (g L k (latticeCarrier L m) n : ℂ) * z t + N) :
    let theta := carrierTheta L k beta gamma rho m n
    let phase := mode (-theta)
    ∃ dw : ℂ, HasDerivAt (fun s => phase s * z s) dw t ∧
      Complex.I * dw =
        (shellSymbol k (xi2 L (m+n)) : ℂ) * (phase t * z t) +
          phase t * (N + (densitySlope beta gamma rho : ℂ) * z t) := by
  let theta := carrierTheta L k beta gamma rho m n
  let phase := mode (-theta)
  have hp : HasDerivAt phase ((Complex.I * ((-theta : ℝ) : ℂ)) * phase t) t :=
    hasDerivAt_mode (-theta) t
  refine ⟨_, hp.mul hd, ?_⟩
  have hb : (g L k (latticeCarrier L m) n : ℂ) + (theta : ℂ) =
      (shellSymbol k (xi2 L (m+n)) : ℂ) + (densitySlope beta gamma rho : ℂ) := by
    exact_mod_cast carrierTheta_balance L k beta gamma rho m n
  calc
    _ = phase t * ((theta : ℂ) * z t + Complex.I * dz) := by
      push_cast
      calc
        _ = (- (Complex.I * Complex.I)) * (theta : ℂ) * phase t * z t +
          phase t * (Complex.I * dz) := by ring
        _ = _ := by rw [Complex.I_mul_I]; ring
    _ = _ := by rw [he]; linear_combination (phase t * z t) * hb

/-- Both exact static fields admit nonempty strong carrier-frame solution
classes and the previously proved conditional-on-existence stability
statement. This packages the two radii and all stability hypotheses. -/
theorem common_torus_carrier_stability :
    ∃ m₁ m₂ : Fin 2 → ℤ, ∃ r₁ r₂ : ℝ,
      xi2 commonLength m₁ ≠ xi2 commonLength m₂ ∧
      (∀ i : Bool, let m := if i then m₁ else m₂
        let rho := if i then r₁ else r₂
        originalResidual commonLength 1 1 1
          (planeField commonLength (Real.sqrt rho : ℂ) m) = 0 ∧
        StrongSolution commonLength 1 1 1 rho (latticeCarrier commonLength m)
          (fun _ => constantCoeff (Real.sqrt rho : ℂ)) ∧
        (∀ eps > 0, ∃ eta > 0, ∀ u : ℝ → ell2 2,
          StrongSolution commonLength 1 1 1 rho (latticeCarrier commonLength m) u →
          OrbitalStabilityCriterion.Near (phaseOrbit rho) (u 0) eta →
          ∀ t, OrbitalStabilityCriterion.Near (phaseOrbit rho) (u t) eps)) := by
  obtain ⟨m₁, m₂, r₁, r₂, hne, hq1, hq2, hr1, hr2, hs1, hs2⟩ :=
    common_torus_stationary
  refine ⟨m₁, m₂, r₁, r₂, hne, ?_⟩
  have aux : ∀ (m : Fin 2 → ℤ) (rho : ℝ), 1 < xi2 commonLength m →
      3/4 < rho →
      StrongSolution commonLength 1 1 1 rho (latticeCarrier commonLength m)
        (fun _ => constantCoeff (Real.sqrt rho : ℂ)) ∧
      (∀ eps > 0, ∃ eta > 0, ∀ u : ℝ → ell2 2,
        StrongSolution commonLength 1 1 1 rho (latticeCarrier commonLength m) u →
        OrbitalStabilityCriterion.Near (phaseOrbit rho) (u 0) eta →
        ∀ t, OrbitalStabilityCriterion.Near (phaseOrbit rho) (u t) eps) := by
    intro m rho hq hr
    have hq' : (1 : ℝ)^2 < carrierSq (latticeCarrier commonLength m) := by
      rw [latticeCarrier_sq]
      simpa using hq
    have hr' : 0 ≤ rho := by linarith
    have ha : ‖(Real.sqrt rho : ℂ)‖ ^ 2 = rho := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
        Real.sq_sqrt hr']
    exact ⟨strong_constant commonLength hq'.le ha,
      orbital_stability_strong commonLength hq' (by norm_num) (by linarith) hr'⟩
  intro i
  cases i
  · exact ⟨hs2, aux m₂ r₂ hq2 hr2⟩
  · exact ⟨hs1, aux m₁ r₁ hq1 hr1⟩

end GC11TorusCarrier
end ReyesMath
