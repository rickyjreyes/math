import MathProofs.GC11TorusOrbit

/-!
# GC11: initial H² proximity and conditional orbital stability

The energy and mass defects are controlled directly by the actual H²
distance to a constant phase representative. The last theorem quantifies
over nearby H² initial data and all mass/energy conserving trajectories.
The independent task of verifying conservation and existence for the
Hamiltonian PDE is not assumed to have been completed.
-/
noncomputable section
open MeasureTheory Complex
namespace ReyesMath
namespace GC11TorusInitial

open BandPass TorusL2 GC11Coercivity GC11TorusEnergy GC11TorusOrbit

variable (L : ℝ) [Fact (0 < L)]

theorem emode_zero_apply (x : Tor L 2) : emode (L := L) (0 : Fin 2 → ℤ) x = 1 := by
  have hf : ∀ y : AddCircle L, fourier (0 : ℤ) y = 1 := by
    intro y
    induction y using QuotientAddGroup.induction_on with
    | H z => rw [fourier_coe_apply]; simp
  simp [emode, hf]

theorem Phi_constant (z : ℂ) (x : Tor L 2) :
    Phi L (by decide : 2 ≤ 3) (constantCoeff z) x = z := by
  have h := (hasSum_Phi (L := L) (by decide : 2 ≤ 3) (constantCoeff z)).tsum_eq
  rw [← h, tsum_eq_single 0]
  · simp [constantCoeff_apply, wt_zero, emode_zero_apply]
  · intro n hn
    simp [constantCoeff_apply, hn]

theorem g_zero (k : ℝ) (K : Fin 2 → ℝ) :
    g L k K (0 : Fin 2 → ℤ) = 0 := by
  simp [g, excess_eq, xi2_zero, carrierDot, xi]

theorem kinetic_upper_near {k : ℝ} {K : Fin 2 → ℝ}
    (hq : k ^ 2 ≤ carrierSq K) (c : ell2 2) (z : ℂ) :
    kinetic L k K (iota L 1 c) ≤ (2 + 10 * carrierSq K) * ‖c - constantCoeff z‖ ^ 2 := by
  have hH : InH 1 (iota L 1 c) := (inH_iff 1 _).2 ⟨c, rfl⟩
  unfold kinetic
  rw [norm_sq_ell2, ← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun n => ?_) (summable_kinetic L hq hH)
    ((hasSum_sq_ell2 (c - constantCoeff z)).summable.mul_left _)
  by_cases hn : n = 0
  · subst n
    rw [g_zero, zero_mul]
    exact mul_nonneg (by linarith [carrierSq_nonneg K]) (sq_nonneg _)
  · have he : wt L n ^ 2 * ‖coef (iota L 1 c) n‖ ^ 2 = ‖c n‖ ^ 2 := by
      simpa using norm_coef_iota_sq (L := L) 1 c n
    rw [lp.coeFn_sub, Pi.sub_apply, constantCoeff_apply, if_neg hn, sub_zero, ← he, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (g_upper L k K n) (sq_nonneg _)

def S : ℝ := Real.sqrt (∑' n : Fin 2 → ℤ, ((wt L n)⁻¹) ^ 2)

theorem S_nonneg : 0 ≤ S L := Real.sqrt_nonneg _

theorem Phi_near_const (c : ell2 2) (z : ℂ) (x : Tor L 2) :
    ‖Phi L (by decide : 2 ≤ 3) c x - z‖ ≤ S L * ‖c - constantCoeff z‖ := by
  have he : Phi L (by decide : 2 ≤ 3) (c - constantCoeff z) x =
      Phi L (by decide : 2 ≤ 3) c x - z := by
    rw [map_sub, ContinuousMap.sub_apply, Phi_constant]
  rw [← he]
  exact (ContinuousMap.norm_coe_le_norm _ x).trans
    (norm_Phi_le (L := L) (by decide : 2 ≤ 3) (c - constantCoeff z))

def B (rho : ℝ) : ℝ := S L * (2 * Real.sqrt rho + S L)

theorem B_nonneg (rho : ℝ) : 0 ≤ B L rho := by
  unfold B
  have := S_nonneg L
  positivity

theorem pointwise_density_near {rho : ℝ} (hr : 0 ≤ rho) (c : ell2 2) {z : ℂ}
    (hz : ‖z‖ = Real.sqrt rho) (he : ‖c - constantCoeff z‖ ≤ 1) (x : Tor L 2) :
    |‖Phi L (by decide : 2 ≤ 3) c x‖ ^ 2 - rho| ≤
      B L rho * ‖c - constantCoeff z‖ := by
  let a := ‖Phi L (by decide : 2 ≤ 3) c x‖
  let R := Real.sqrt rho
  let e := ‖c - constantCoeff z‖
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have ha : 0 ≤ a := norm_nonneg _
  have hS := S_nonneg L
  have he0 : 0 ≤ e := norm_nonneg _
  have hdiff : |a - R| ≤ S L * e := by
    dsimp [a, R, e]
    rw [← hz]
    exact (abs_norm_sub_norm_le _ _).trans (Phi_near_const L c z x)
  have hsmall : S L * e ≤ S L := by
    simpa using mul_le_mul_of_nonneg_left he hS
  have hab : a + R ≤ 2 * R + S L := by
    linarith [le_abs_self (a - R)]
  have hR2 : R ^ 2 = rho := Real.sq_sqrt hr
  change |a ^ 2 - rho| ≤ B L rho * e
  calc
    |a ^ 2 - rho| = |a - R| * (a + R) := by
      rw [← hR2, show a ^ 2 - R ^ 2 = (a - R) * (a + R) by ring,
        abs_mul, abs_of_nonneg (add_nonneg ha hR)]
    _ ≤ (S L * e) * (2 * R + S L) :=
      mul_le_mul hdiff hab (add_nonneg ha hR) (mul_nonneg hS he0)
    _ = _ := by unfold B; dsimp [R]; ring

theorem mass_eq_integral (c : ell2 2) :
    mass L c = ∫ x, ‖Phi L (by decide : 2 ≤ 3) c x‖ ^ 2 ∂(μ L 2) := by
  unfold mass
  rw [norm_sq_eq_integral]
  apply integral_congr_ae
  filter_upwards [iota_ae_eq_Phi (L := L) (by decide : 2 ≤ 3) c] with x hx
  rw [hx]

theorem mass_defect_near {rho : ℝ} (hr : 0 ≤ rho) (c : ell2 2) {z : ℂ}
    (hz : ‖z‖ = Real.sqrt rho) (he : ‖c - constantCoeff z‖ ≤ 1) :
    |mass L c - rho| ≤ B L rho * ‖c - constantCoeff z‖ := by
  have hi : Integrable (fun x => ‖Phi L (by decide : 2 ≤ 3) c x‖ ^ 2) (μ L 2) :=
    integrable_of_continuous ((continuous_norm.comp (Phi L (by decide : 2 ≤ 3) c).continuous).pow 2)
  have h : mass L c - rho =
      ∫ x, (‖Phi L (by decide : 2 ≤ 3) c x‖ ^ 2 - rho) ∂(μ L 2) := by
    rw [integral_sub hi (integrable_const rho), mass_eq_integral, integral_const]
    simp
  rw [h, ← Real.norm_eq_abs]
  apply integral_le_of_le_const (L := L)
  intro x
  rw [Real.norm_eq_abs]
  exact pointwise_density_near L hr c hz he x

def Pbound (beta gamma rho : ℝ) : ℝ :=
  gamma / 3 * ((Real.sqrt rho + S L) ^ 2 + 2 * rho) + |beta| / 2

theorem Pbound_nonneg {beta gamma rho : ℝ} (hg : 0 ≤ gamma) (hr : 0 ≤ rho) :
    0 ≤ Pbound L beta gamma rho := by
  unfold Pbound
  positivity

theorem potential_near {beta gamma rho : ℝ} (hg : 0 ≤ gamma) (hr : 0 ≤ rho)
    (c : ell2 2) {z : ℂ} (hz : ‖z‖ = Real.sqrt rho)
    (he : ‖c - constantCoeff z‖ ≤ 1) :
    densityPotential L beta gamma rho c ≤
      Pbound L beta gamma rho * B L rho ^ 2 * ‖c - constantCoeff z‖ ^ 2 := by
  unfold densityPotential
  have hi : Integrable (fun x => relativePotential beta gamma rho
      (‖Phi L (by decide : 2 ≤ 3) c x‖ ^ 2)) (μ L 2) := by
    apply integrable_of_continuous
    unfold relativePotential potential densitySlope
    fun_prop
  let C := Pbound L beta gamma rho * B L rho ^ 2 * ‖c - constantCoeff z‖ ^ 2
  have hm := integral_mono hi (integrable_const C) (fun x => ?_)
  · simpa [C] using hm
  · let a := ‖Phi L (by decide : 2 ≤ 3) c x‖
    have ha : 0 ≤ a := norm_nonneg _
    have hR := Real.sqrt_nonneg rho
    have hS := S_nonneg L
    have hdist := abs_norm_sub_norm_le (Phi L (by decide : 2 ≤ 3) c x) z
    rw [hz] at hdist
    have hp := Phi_near_const L c z x
    have hsmall : S L * ‖c - constantCoeff z‖ ≤ S L := by
      simpa using mul_le_mul_of_nonneg_left he hS
    have hab : a ≤ Real.sqrt rho + S L := by
      dsimp [a]
      linarith [le_abs_self (‖Phi L (by decide : 2 ≤ 3) c x‖ - Real.sqrt rho)]
    have ha2 := pow_le_pow_left₀ ha hab 2
    have hcoef : gamma / 3 * (a ^ 2 + 2 * rho) - beta / 2 ≤ Pbound L beta gamma rho := by
      have hmul := mul_le_mul_of_nonneg_left ha2 (show 0 ≤ gamma / 3 by positivity)
      unfold Pbound
      linarith [neg_abs_le beta]
    have hden := pointwise_density_near L hr c hz he x
    have hd2 := pow_le_pow_left₀ (abs_nonneg _) hden 2
    rw [sq_abs, mul_pow] at hd2
    change relativePotential beta gamma rho (a ^ 2) ≤ C
    rw [relativePotential_eq]
    calc
      _ ≤ (a ^ 2 - rho) ^ 2 * Pbound L beta gamma rho :=
        mul_le_mul_of_nonneg_left hcoef (sq_nonneg _)
      _ ≤ (B L rho ^ 2 * ‖c - constantCoeff z‖ ^ 2) * Pbound L beta gamma rho :=
        mul_le_mul_of_nonneg_right hd2 (Pbound_nonneg L hg hr)
      _ = C := by dsimp [C]; ring

def Ebound (beta gamma rho : ℝ) (K : Fin 2 → ℝ) : ℝ :=
  2 + 10 * carrierSq K + Pbound L beta gamma rho * B L rho ^ 2

theorem energy_near {k beta gamma rho : ℝ} {K : Fin 2 → ℝ}
    (hq : k ^ 2 ≤ carrierSq K) (hg : 0 ≤ gamma) (hr : 0 ≤ rho)
    (c : ell2 2) {z : ℂ} (hz : ‖z‖ = Real.sqrt rho)
    (he : ‖c - constantCoeff z‖ ≤ 1) :
    relEnergy L k beta gamma rho K c ≤
      Ebound L beta gamma rho K * ‖c - constantCoeff z‖ ^ 2 := by
  have hk := kinetic_upper_near L hq c z
  have hp := potential_near L hg hr c hz he
  unfold relEnergy Ebound
  rw [add_mul]
  linarith

/-- Full initial-H² epsilon/delta orbital implication for all conserving
trajectories, rather than an assumption of small initial energy. -/
theorem orbital_stability_conserving {k beta gamma rho : ℝ} {K : Fin 2 → ℝ}
    (hq : k ^ 2 < carrierSq K) (hg : 0 ≤ gamma)
    (hrho : 3 * beta < 4 * gamma * rho) (hr : 0 ≤ rho) :
    ∀ eps > 0, ∃ eta > 0, ∀ u : ℝ → ell2 2,
      (∀ t, mass L (u t) = mass L (u 0)) →
      (∀ t, relEnergy L k beta gamma rho K (u t) =
        relEnergy L k beta gamma rho K (u 0)) →
      OrbitalStabilityCriterion.Near (phaseOrbit rho) (u 0) eta →
      ∀ t, OrbitalStabilityCriterion.Near (phaseOrbit rho) (u t) eps := by
  intro eps heps
  let A := 2 * Cgap L * Ckin k (carrierSq K)
  have hA : 0 < A := by
    dsimp [A]
    have := Cgap_pos L
    have := Ckin_pos hq
    positivity
  have hB := B_nonneg L rho
  have hE : 0 ≤ Ebound L beta gamma rho K := by
    unfold Ebound
    have := carrierSq_nonneg K
    have := Pbound_nonneg L (beta := beta) hg hr
    positivity
  let C := 1 + B L rho + A * Ebound L beta gamma rho K
  have hC : 0 < C := by dsimp [C]; positivity
  let eta := min 1 (eps ^ 2 / C)
  have heta : 0 < eta := lt_min (by norm_num) (div_pos (sq_pos_of_pos heps) hC)
  refine ⟨eta, heta, ?_⟩
  intro u hm hc hnear
  obtain ⟨v, hv, hd⟩ := hnear
  obtain ⟨z, hz, rfl⟩ := hv
  rw [dist_eq_norm] at hd
  let e := ‖u 0 - constantCoeff z‖
  have he : e < eta := hd
  have he0 : 0 ≤ e := norm_nonneg _
  have he1 : e ≤ 1 := he.le.trans (min_le_left _ _)
  have hm0 := mass_defect_near L hr (u 0) hz he1
  have hE0 := energy_near L hq.le hg hr (u 0) hz he1
  have hmul := mul_le_mul_of_nonneg_left hE0 hA.le
  have he2 : e ^ 2 ≤ e := by nlinarith [mul_nonneg he0 (sub_nonneg.mpr he1)]
  have hprod := mul_le_mul_of_nonneg_left he2 (mul_nonneg hA.le hE)
  have hcE : |mass L (u 0) - rho| + A * relEnergy L k beta gamma rho K (u 0) ≤ C * e := by
    change |mass L (u 0) - rho| + A * relEnergy L k beta gamma rho K (u 0) ≤ _
    change |mass L (u 0) - rho| ≤ B L rho * e at hm0
    change relEnergy L k beta gamma rho K (u 0) ≤ Ebound L beta gamma rho K * e ^ 2 at hE0
    have hh := mul_le_mul_of_nonneg_left hE0 hA.le
    dsimp [C]
    nlinarith [hh, hprod]
  have heps' : e < eps ^ 2 / C := he.trans_le (min_le_right _ _)
  have hsmall : C * e < eps ^ 2 := by
    have hh := (lt_div_iff₀ hC).1 heps'
    simpa [mul_comm] using hh
  exact orbit_near_of_small_mass_energy L hq hg hrho hr heps u hm hc
    (hcE.trans_lt hsmall)

end GC11TorusInitial
end ReyesMath
