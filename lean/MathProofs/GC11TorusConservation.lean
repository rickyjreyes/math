import MathProofs.GC11TorusHamiltonian

/-!
# GC11: nonlinear potential differentiation and strong conservation

The proof uses the continuous representative of the full H² Fourier
space. The potential is a polynomial on continuous complex maps,
and the integral of the real part is a bounded real-linear map.
It supplies conservation and nonlinear orbital stability for the
strong carrier-frame solution class, not existence of that class for
all H² data or its equivalence with the original unshifted evolution.
-/
noncomputable section
open MeasureTheory Complex
open scoped ComplexConjugate InnerProductSpace
namespace ReyesMath
namespace GC11TorusConservation

open BandPass TorusL2 GC11Coercivity GC11TorusEnergy GC11TorusOrbit
  GC11TorusInitial GC11TorusHamiltonian

variable (L : ℝ) [Fact (0 < L)]

abbrev CField := C(Tor L 2, ℂ)

/-- Complex conjugation as a bounded real-linear map on continuous fields. -/
def conjCLM : CField L →L[ℝ] CField L :=
  LinearMap.mkContinuous
    { toFun := fun F => ⟨fun x => conj (F x), Complex.continuous_conj.comp F.continuous⟩
      map_add' := by
        intro F G
        ext x
        simp
      map_smul' := by
        intro a F
        ext x
        simp [Complex.real_smul, map_mul] }
    1 (fun F => by
      rw [one_mul]
      apply (ContinuousMap.norm_le _ (norm_nonneg F)).2
      intro x
      change ‖conj (F x)‖ ≤ ‖F‖
      rw [Complex.norm_conj]
      exact ContinuousMap.norm_coe_le_norm F x)

theorem conjCLM_apply (F : CField L) (x : Tor L 2) :
    conjCLM L F x = conj (F x) := rfl

/-- The normalized integral of the real part. -/
def intRe : CField L →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun F => ∫ x, (F x).re ∂(μ L 2)
      map_add' := by
        intro F G
        change (∫ x, (F x + G x).re ∂(μ L 2)) = _
        simp only [Complex.add_re]
        exact integral_add
          (integrable_of_continuous (Complex.continuous_re.comp F.continuous))
          (integrable_of_continuous (Complex.continuous_re.comp G.continuous))
      map_smul' := by
        intro a F
        change (∫ x, (a • F x).re ∂(μ L 2)) = a * ∫ x, (F x).re ∂(μ L 2)
        simp only [Complex.real_smul, Complex.re_ofReal_mul]
        exact integral_const_mul _ _ }
    1 (fun F => by
      rw [one_mul]
      exact integral_le_of_le_const (L := L) fun x => by
        rw [Real.norm_eq_abs]
        exact (Complex.abs_re_le_norm _).trans (ContinuousMap.norm_coe_le_norm F x))

theorem intRe_apply (F : CField L) :
    intRe L F = ∫ x, (F x).re ∂(μ L 2) := rfl

def dMap (F : CField L) : CField L := conjCLM L F * F

def dMapDeriv (F G : CField L) : CField L := conjCLM L G * F + conjCLM L F * G

theorem dMap_apply (F : CField L) (x : Tor L 2) :
    dMap L F x = ((‖F x‖ ^ 2 : ℝ) : ℂ) := by
  change conj (F x) * F x = _
  rw [Complex.conj_mul']; push_cast; ring

theorem dMapDeriv_apply (F G : CField L) (x : Tor L 2) :
    dMapDeriv L F G x = ((2 * (conj (F x) * G x).re : ℝ) : ℂ) := by
  change conj (G x) * F x + conj (F x) * G x = _
  apply Complex.ext
  · simp [Complex.mul_re]; ring
  · simp [Complex.mul_im]; ring

theorem hasDerivAt_dMap {u : ℝ → CField L} {du : CField L} {t : ℝ}
    (h : HasDerivAt u du t) :
    HasDerivAt (fun s => dMap L (u s)) (dMapDeriv L (u t) du) t := by
  have hc := ((conjCLM L).hasFDerivAt (x := u t)).comp_hasDerivAt t h
  exact hc.mul h

/-- The exact renormalized potential as a polynomial of the density field. -/
def pMap (beta gamma rho : ℝ) (D : CField L) : CField L :=
  (-beta / 2) • (D * D) + (gamma / 3) • (D * D * D) -
    densitySlope beta gamma rho • D +
    ContinuousMap.const _ ((-potential beta gamma rho + densitySlope beta gamma rho * rho : ℝ) : ℂ)

def pMapDeriv (beta gamma rho : ℝ) (D H : CField L) : CField L :=
  (-beta / 2) • (H * D + D * H) +
    (gamma / 3) • ((H * D + D * H) * D + (D * D) * H) -
    densitySlope beta gamma rho • H

theorem hasDerivAt_pMap {beta gamma rho : ℝ} {u : ℝ → CField L}
    {du : CField L} {t : ℝ} (h : HasDerivAt u du t) :
    HasDerivAt (fun s => pMap L beta gamma rho (u s))
      (pMapDeriv L beta gamma rho (u t) du) t := by
  have h2 := h.mul h
  have h3 := h2.mul h
  exact (((h2.const_smul (-beta / 2)).add (h3.const_smul (gamma / 3))).sub
    (h.const_smul (densitySlope beta gamma rho))).add_const _

theorem pMap_apply (beta gamma rho : ℝ) (F : CField L) (x : Tor L 2) :
    pMap L beta gamma rho (dMap L F) x =
      (relativePotential beta gamma rho (‖F x‖ ^ 2) : ℂ) := by
  simp only [pMap, ContinuousMap.add_apply, ContinuousMap.sub_apply,
    ContinuousMap.smul_apply, ContinuousMap.mul_apply, ContinuousMap.const_apply,
    dMap_apply, Complex.real_smul]
  unfold relativePotential potential
  push_cast
  ring

theorem pMapDeriv_apply (beta gamma rho : ℝ) (F G : CField L) (x : Tor L 2) :
    pMapDeriv L beta gamma rho (dMap L F) (dMapDeriv L F G) x =
      ((2 * (densitySlope beta gamma (‖F x‖ ^ 2) - densitySlope beta gamma rho) *
        (conj (F x) * G x).re : ℝ) : ℂ) := by
  simp only [pMapDeriv, ContinuousMap.add_apply, ContinuousMap.sub_apply,
    ContinuousMap.smul_apply, ContinuousMap.mul_apply, dMap_apply, dMapDeriv_apply,
    Complex.real_smul]
  unfold densitySlope
  push_cast
  ring

theorem densityPotential_eq_intRe (beta gamma rho : ℝ) (c : ell2 2) :
    densityPotential L beta gamma rho c =
      intRe L (pMap L beta gamma rho (dMap L (Phi L (by decide : 2 ≤ 3) c))) := by
  rw [densityPotential, intRe_apply]
  apply integral_congr_ae
  filter_upwards with x
  rw [pMap_apply, Complex.ofReal_re]

theorem intRe_pMapDeriv (beta gamma rho : ℝ) (c b : ell2 2) :
    intRe L (pMapDeriv L beta gamma rho
      (dMap L (Phi L (by decide : 2 ≤ 3) c))
      (dMapDeriv L (Phi L (by decide : 2 ≤ 3) c) (Phi L (by decide : 2 ≤ 3) b))) =
      2 * (⟪nonlinear L beta gamma rho c, iota L 1 b⟫_ℂ).re := by
  rw [intRe_apply, MeasureTheory.L2.inner_def, ← RCLike.re_to_complex,
    ← integral_re (L2.integrable_inner (𝕜 := ℂ) _ _), ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [nonlinear_ae L beta gamma rho c,
    iota_ae_eq_Phi (L := L) (by decide : 2 ≤ 3) b] with x hx hy
  rw [pMapDeriv_apply, Complex.ofReal_re, RCLike.inner_apply, hx, hy, RCLike.re_to_complex]
  simp only [map_mul, Complex.conj_ofReal]
  rw [mul_comm (conj (((densitySlope beta gamma
    (‖Phi L (by decide : 2 ≤ 3) c x‖ ^ 2) - densitySlope beta gamma rho : ℝ) : ℂ)))]
  simp only [Complex.conj_ofReal]
  rw [mul_assoc, mul_comm (conj (Phi L (by decide : 2 ≤ 3) c x)), ← mul_assoc]
  -- The remaining equality is multiplication by a real scalar.
  simp [Complex.mul_re]
  <;> ring

theorem hasDerivAt_potential {beta gamma rho : ℝ} {u : ℝ → ell2 2}
    {du : ell2 2} {t : ℝ} (h : HasDerivAt u du t) :
    HasDerivAt (fun s => densityPotential L beta gamma rho (u s))
      (2 * (⟪nonlinear L beta gamma rho (u t), iota L 1 du⟫_ℂ).re) t := by
  have hF := (((Phi L (by decide : 2 ≤ 3)).hasFDerivAt (x := u t)).restrictScalars ℝ).comp_hasDerivAt t h
  have hD := hasDerivAt_dMap L hF
  have hP := hasDerivAt_pMap L (beta := beta) (gamma := gamma) (rho := rho) hD
  have hI := ((intRe L).hasFDerivAt (x := pMap L beta gamma rho
    (dMap L (Phi L (by decide : 2 ≤ 3) (u t))))).comp_hasDerivAt t hP
  simpa only [← densityPotential_eq_intRe, intRe_pMapDeriv] using hI

theorem hasDerivAt_energy_strong {k beta gamma rho : ℝ} {K : Fin 2 → ℝ}
    (hq : k ^ 2 ≤ carrierSq K) {u : ℝ → ell2 2}
    (hu : StrongSolution L k beta gamma rho K u) (t : ℝ) :
    HasDerivAt (fun s => relEnergy L k beta gamma rho K (u s)) 0 t := by
  obtain ⟨h4, du, hd, he⟩ := hu t
  have hk := hasDerivAt_kinetic L hq h4 hd
  have hp := hasDerivAt_potential L (beta := beta) (gamma := gamma) (rho := rho) hd
  have h := hk.add hp
  have hz : 2 * (⟪carrierOp L k K (iota L 1 (u t)), iota L 1 du⟫_ℂ).re +
      2 * (⟪nonlinear L beta gamma rho (u t), iota L 1 du⟫_ℂ).re = 0 := by
    rw [← mul_add, ← Complex.add_re, ← inner_add_left, ← gradient, he,
      inner_smul_right]
    have hi : (⟪gradient L k beta gamma rho K (u t),
      gradient L k beta gamma rho K (u t)⟫_ℂ).im = 0 := by simp
    simp [Complex.mul_re, hi]
  simpa only [relEnergy, hz] using h

theorem energy_conserved_strong {k beta gamma rho : ℝ} {K : Fin 2 → ℝ}
    (hq : k ^ 2 ≤ carrierSq K) {u : ℝ → ell2 2}
    (hu : StrongSolution L k beta gamma rho K u) (t : ℝ) :
    relEnergy L k beta gamma rho K (u t) = relEnergy L k beta gamma rho K (u 0) :=
  is_const_of_deriv_eq_zero (f := fun s => relEnergy L k beta gamma rho K (u s))
    (fun s => (hasDerivAt_energy_strong L hq hu s).differentiableAt)
    (fun s => (hasDerivAt_energy_strong L hq hu s).deriv) t 0

/-- Nonlinear orbital stability for all global strong solutions of the exact
carrier-frame PDE. Neither mass nor energy conservation is a hypothesis. -/
theorem orbital_stability_strong {k beta gamma rho : ℝ} {K : Fin 2 → ℝ}
    (hq : k ^ 2 < carrierSq K) (hg : 0 ≤ gamma)
    (hrho : 3 * beta < 4 * gamma * rho) (hr : 0 ≤ rho) :
    ∀ eps > 0, ∃ eta > 0, ∀ u : ℝ → ell2 2,
      StrongSolution L k beta gamma rho K u →
      OrbitalStabilityCriterion.Near (phaseOrbit rho) (u 0) eta →
      ∀ t, OrbitalStabilityCriterion.Near (phaseOrbit rho) (u t) eps := by
  intro eps heps
  obtain ⟨eta, heta, hstab⟩ :=
    orbital_stability_conserving L hq hg hrho hr eps heps
  refine ⟨eta, heta, ?_⟩
  intro u hu hnear
  exact hstab u (mass_conserved_strong L hq.le hu)
    (energy_conserved_strong L hq.le hu) hnear

end GC11TorusConservation
end ReyesMath
