import MathProofs.GC11TorusEnergy
import MathProofs.OrbitalStabilityCriterion

/-!
# GC11: quantitative fixed-mass phase-orbit estimate on the full torus

A constant in the carrier frame is a single Fourier coefficient at zero.
The torus spectral gap controls all other H² coefficients. At fixed mass,
the remaining modulus error is controlled by the nonzero-mode L² mass.
This is an actual Hilbert-space distance estimate, not a new stability
topology or a finite-mode truncation. Conservation is still explicit.
-/

noncomputable section
namespace ReyesMath
namespace GC11TorusOrbit

open BandPass TorusL2 GC11TorusEnergy GC11Coercivity

variable (L : ℝ) [Fact (0 < L)]

def latticeGap : ℝ := (2 * Real.pi / L) ^ 2

theorem latticeGap_pos : 0 < latticeGap L := by
  unfold latticeGap
  exact sq_pos_of_pos (div_pos Real.two_pi_pos (Fact.out : 0 < L))

theorem xi2_zero : xi2 L (0 : Fin 2 → ℤ) = 0 := by
  simp [xi2, xi]

theorem wt_zero : wt L (0 : Fin 2 → ℤ) = 1 := by
  simp [wt, xi2_zero]

theorem latticeGap_le {n : Fin 2 → ℤ} (hn : n ≠ 0) :
    latticeGap L ≤ xi2 L n := by
  classical
  have hj : ∃ j : Fin 2, n j ≠ 0 := by
    by_contra h
    push_neg at h
    apply hn
    funext j
    exact h j
  obtain ⟨j, hj⟩ := hj
  have hi : n j ≤ -1 ∨ 1 ≤ n j := by omega
  have hsq : (1 : ℝ) ≤ (n j : ℝ) ^ 2 := by
    rcases hi with h | h
    · have h' : (n j : ℝ) ≤ -1 := by exact_mod_cast h
      nlinarith [sq_nonneg ((n j : ℝ) + 1)]
    · have h' : (1 : ℝ) ≤ (n j : ℝ) := by exact_mod_cast h
      nlinarith [sq_nonneg ((n j : ℝ) - 1)]
  have hm := mul_le_mul_of_nonneg_left hsq (sq_nonneg (2 * Real.pi / L))
  have hb : latticeGap L ≤ xi L n j ^ 2 := by
    simpa [latticeGap, xi, mul_pow] using hm
  exact hb.trans (xi_sq_le_xi2 n j)

def Cgap : ℝ := 2 + (latticeGap L)⁻¹

theorem Cgap_pos : 0 < Cgap L := by
  unfold Cgap
  have h := latticeGap_pos L
  positivity

theorem weight_le_derivative {n : Fin 2 → ℤ} (hn : n ≠ 0) :
    wt L n ^ 2 ≤ Cgap L * (xi2 L n + xi2 L n ^ 2) := by
  have hd := latticeGap_pos L
  have hs := xi2_nonneg (L := L) n
  have h := latticeGap_le L hn
  have h1 : 1 ≤ (latticeGap L)⁻¹ * xi2 L n := by
    rw [← div_eq_inv_mul, le_div_iff₀ hd]
    simpa using h
  have h2 := mul_nonneg (inv_nonneg.mpr hd.le) (sq_nonneg (xi2 L n))
  unfold wt Cgap
  nlinarith [sq_nonneg (xi2 L n)]

/-- The Hilbert-space vector of a constant physical field. -/
def constantCoeff (z : ℂ) : ell2 2 :=
  ⟨fun n => if n = 0 then z else 0, by
    classical
    rw [memℓp_two_iff]
    refine summable_of_ne_finset_zero (s := {0}) fun n hn => ?_
    have hn' : n ≠ 0 := by simpa using hn
    simp [hn']⟩

theorem constantCoeff_apply (z : ℂ) (n : Fin 2 → ℤ) :
    constantCoeff z n = if n = 0 then z else 0 := rfl

def phaseOrbit (rho : ℝ) : Set (ell2 2) :=
  {c | ∃ z : ℂ, ‖z‖ = Real.sqrt rho ∧ c = constantCoeff z}

theorem phase_target (a : ℂ) {R : ℝ} (hR : 0 ≤ R) :
    ∃ z : ℂ, ‖z‖ = R ∧ ‖a - z‖ = |‖a‖ - R| := by
  by_cases ha : a = 0
  · subst a
    exact ⟨(R : ℂ), by simp [Complex.norm_real, abs_of_nonneg hR],
      by simp [Complex.norm_real, abs_of_nonneg hR]⟩
  · have hn : 0 < ‖a‖ := norm_pos_iff.mpr ha
    refine ⟨(R / ‖a‖) • a, ?_, ?_⟩
    · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hR hn.le)]
      exact div_mul_cancel₀ R hn.ne'
    · have he : a - (R / ‖a‖) • a = (1 - R / ‖a‖) • a := by
        rw [sub_smul, one_smul]
      rw [he, norm_smul, Real.norm_eq_abs]
      calc
        |1 - R / ‖a‖| * ‖a‖ = |(1 - R / ‖a‖) * ‖a‖| := by
          rw [abs_mul, abs_of_nonneg hn.le]
        _ = |‖a‖ - R| := by
          congr 1
          field_simp

/-- L² mass is measured in the repository's normalized Haar measure. -/
def mass (c : ell2 2) : ℝ := ‖iota L 1 c‖ ^ 2

def tailMass (c : ell2 2) : ℝ :=
  ∑' n : Fin 2 → ℤ, if n = 0 then 0 else ‖coef (iota L 1 c) n‖ ^ 2

def tailH2 (c : ell2 2) : ℝ :=
  ∑' n : Fin 2 → ℤ, if n = 0 then 0 else ‖c n‖ ^ 2

theorem summable_tailMass (c : ell2 2) :
    Summable (fun n : Fin 2 → ℤ => if n = 0 then 0 else ‖coef (iota L 1 c) n‖ ^ 2) := by
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) (summable_sq (iota L 1 c))
  · split_ifs <;> positivity
  · split_ifs <;> positivity

theorem summable_tailH2 (c : ell2 2) :
    Summable (fun n : Fin 2 → ℤ => if n = 0 then 0 else ‖c n‖ ^ 2) := by
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    (hasSum_sq_ell2 c).summable
  · split_ifs <;> positivity
  · split_ifs <;> positivity

theorem mass_split (c : ell2 2) : mass L c = ‖c 0‖ ^ 2 + tailMass L c := by
  have hz : coef (iota L 1 c) 0 = c 0 := by
    rw [coef_iota, wt_zero]
    simp
  have hs : Summable (fun n : Fin 2 → ℤ => if n = 0 then ‖c 0‖ ^ 2 else 0) := by
    classical
    refine summable_of_ne_finset_zero (s := {0}) fun n hn => ?_
    have hn' : n ≠ 0 := by simpa using hn
    simp [hn']
  have hsum : (∑' n : Fin 2 → ℤ, if n = 0 then ‖c 0‖ ^ 2 else 0) = ‖c 0‖ ^ 2 := by
    rw [tsum_eq_single 0]
    · simp
    · intro n hn
      simp [hn]
  unfold mass tailMass
  rw [norm_sq_eq_tsum, ← hsum, ← hs.tsum_add (summable_tailMass L c)]
  congr 1
  funext n
  by_cases hn : n = 0
  · subst n
    simp [hz]
  · simp [hn]

theorem tailMass_nonneg (c : ell2 2) : 0 ≤ tailMass L c := by
  unfold tailMass
  exact tsum_nonneg fun n => by split_ifs <;> positivity

theorem tailMass_le_tailH2 (c : ell2 2) : tailMass L c ≤ tailH2 c := by
  unfold tailMass tailH2
  refine Summable.tsum_le_tsum (fun n => ?_) (summable_tailMass L c) (summable_tailH2 c)
  by_cases hn : n = 0
  · simp [hn]
  · simp only [hn, if_false]
    have hw := one_le_wt (L := L) n
    have he : wt L n ^ 2 * ‖coef (iota L 1 c) n‖ ^ 2 = ‖c n‖ ^ 2 := by
      simpa using norm_coef_iota_sq (L := L) 1 c n
    have hm := mul_le_mul_of_nonneg_right
      (show (1 : ℝ) ≤ wt L n ^ 2 by nlinarith [sq_nonneg (wt L n - 1)])
      (sq_nonneg ‖coef (iota L 1 c) n‖)
    nlinarith

theorem tailH2_le_derivative (c : ell2 2) :
    tailH2 c ≤ Cgap L * derivativeEnergy L (iota L 1 c) := by
  have hH : InH 1 (iota L 1 c) := (inH_iff 1 _).2 ⟨c, rfl⟩
  unfold tailH2 derivativeEnergy
  rw [← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun n => ?_) (summable_tailH2 c)
    ((summable_derivative L hH).mul_left _)
  by_cases hn : n = 0
  · simp [hn, xi2_zero]
  · simp only [hn, if_false]
    have he : wt L n ^ 2 * ‖coef (iota L 1 c) n‖ ^ 2 = ‖c n‖ ^ 2 := by
      simpa using norm_coef_iota_sq (L := L) 1 c n
    rw [← he]
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (weight_le_derivative L hn) (sq_nonneg _)

theorem norm_sub_constant_sq (c : ell2 2) (z : ℂ) :
    ‖c - constantCoeff z‖ ^ 2 = ‖c 0 - z‖ ^ 2 + tailH2 c := by
  have hs : Summable (fun n : Fin 2 → ℤ => if n = 0 then ‖c 0 - z‖ ^ 2 else 0) := by
    classical
    refine summable_of_ne_finset_zero (s := {0}) fun n hn => ?_
    have hn' : n ≠ 0 := by simpa using hn
    simp [hn']
  have hsum : (∑' n : Fin 2 → ℤ, if n = 0 then ‖c 0 - z‖ ^ 2 else 0) = ‖c 0 - z‖ ^ 2 := by
    rw [tsum_eq_single 0]
    · simp
    · intro n hn
      simp [hn]
  rw [norm_sq_ell2, ← hsum]
  unfold tailH2
  rw [← hs.tsum_add (summable_tailH2 c)]
  congr 1
  funext n
  rw [lp.coeFn_sub, Pi.sub_apply, constantCoeff_apply]
  by_cases hn : n = 0
  · subst n
    simp
  · simp [hn]

/-- Fixed-mass phase-orbit bound in the actual H² Hilbert norm.
The witness is a constant coefficient with modulus sqrt(rho). -/
theorem orbit_bound_fixed_mass {rho : ℝ} (hrho : 0 ≤ rho)
    (c : ell2 2) (hmass : mass L c = rho) :
    ∃ v ∈ phaseOrbit rho,
      ‖c - v‖ ^ 2 ≤ 2 * Cgap L * derivativeEnergy L (iota L 1 c) := by
  obtain ⟨z, hz, hzdist⟩ := phase_target (c 0) (Real.sqrt_nonneg rho)
  refine ⟨constantCoeff z, ⟨z, hz, rfl⟩, ?_⟩
  have hs := mass_split L c
  rw [hmass] at hs
  have htail := tailMass_nonneg L c
  have hr := Real.sq_sqrt hrho
  have hn := norm_nonneg (c 0)
  have hR := Real.sqrt_nonneg rho
  have hle : ‖c 0‖ ≤ Real.sqrt rho := by nlinarith
  have hprod := mul_nonneg hn (sub_nonneg.mpr hle)
  have herror : ‖c 0 - z‖ ^ 2 ≤ tailMass L c := by
    rw [hzdist, sq_abs]
    nlinarith
  rw [norm_sub_constant_sq]
  have h1 := tailMass_le_tailH2 L c
  have h2 := tailH2_le_derivative L c
  nlinarith

/-- Quantified orbital bound for every trajectory conserving relative
energy and having the fixed prescribed mass. The PDE conservation law
is not built into the trajectory definition. -/
theorem conserving_orbit_bound {k beta gamma rho : ℝ} {K : Fin 2 → ℝ}
    (hq : k ^ 2 < carrierSq K) (hg : 0 ≤ gamma)
    (hrho : 3 * beta < 4 * gamma * rho) (hr : 0 ≤ rho)
    (u : ℝ → ell2 2)
    (hm : ∀ t, mass L (u t) = rho)
    (hc : ∀ t, relEnergy L k beta gamma rho K (u t) =
      relEnergy L k beta gamma rho K (u 0)) (t : ℝ) :
    ∃ v ∈ phaseOrbit rho,
      ‖u t - v‖ ^ 2 ≤
        2 * Cgap L * Ckin k (carrierSq K) * relEnergy L k beta gamma rho K (u 0) := by
  obtain ⟨v, hv, hb⟩ := orbit_bound_fixed_mass L hr (u t) (hm t)
  refine ⟨v, hv, hb.trans ?_⟩
  have h := conserved_energy_bound L hq hg hrho u hc t
  have hn := mul_nonneg (mul_nonneg (Ckin_pos hq).le (density_coercivity_pos hrho).le)
    (density_nonneg L rho (u t))
  have hder : derivativeEnergy L (iota L 1 (u t)) ≤
      Ckin k (carrierSq K) * relEnergy L k beta gamma rho K (u 0) := by linarith
  have hc0 := Cgap_pos L
  calc
    _ ≤ (2 * Cgap L) * (Ckin k (carrierSq K) * relEnergy L k beta gamma rho K (u 0)) :=
      mul_le_mul_of_nonneg_left hder (by positivity)
    _ = _ := by ring


/-- The same H² orbit estimate for arbitrary mass, with explicit mass defect. -/
theorem orbit_bound_mass_defect {rho : ℝ} (hrho : 0 ≤ rho) (c : ell2 2) :
    ∃ v ∈ phaseOrbit rho,
      ‖c - v‖ ^ 2 ≤ |mass L c - rho| +
        2 * Cgap L * derivativeEnergy L (iota L 1 c) := by
  obtain ⟨z, hz, hzdist⟩ := phase_target (c 0) (Real.sqrt_nonneg rho)
  refine ⟨constantCoeff z, ⟨z, hz, rfl⟩, ?_⟩
  have hs := mass_split L c
  have htail := tailMass_nonneg L c
  have hr := Real.sq_sqrt hrho
  have hn := norm_nonneg (c 0)
  have hR := Real.sqrt_nonneg rho
  have herror : ‖c 0 - z‖ ^ 2 ≤ |mass L c - rho| + tailMass L c := by
    rw [hzdist, sq_abs]
    by_cases h : ‖c 0‖ ≤ Real.sqrt rho
    · have hp := mul_nonneg hn (sub_nonneg.mpr h)
      nlinarith [neg_abs_le (mass L c - rho)]
    · have hp := mul_nonneg hR (sub_nonneg.mpr (le_of_not_ge h))
      nlinarith [le_abs_self (mass L c - rho)]
  rw [norm_sub_constant_sq]
  have h1 := tailMass_le_tailH2 L c
  have h2 := tailH2_le_derivative L c
  nlinarith

/-- Uniform-in-time H² orbital control for nearby masses, on a trajectory
with explicit mass and relative-energy conservation. -/
theorem conserving_orbit_bound_near_mass {k beta gamma rho : ℝ} {K : Fin 2 → ℝ}
    (hq : k ^ 2 < carrierSq K) (hg : 0 ≤ gamma)
    (hrho : 3 * beta < 4 * gamma * rho) (hr : 0 ≤ rho)
    (u : ℝ → ell2 2)
    (hm : ∀ t, mass L (u t) = mass L (u 0))
    (hc : ∀ t, relEnergy L k beta gamma rho K (u t) =
      relEnergy L k beta gamma rho K (u 0)) (t : ℝ) :
    ∃ v ∈ phaseOrbit rho,
      ‖u t - v‖ ^ 2 ≤ |mass L (u 0) - rho| +
        2 * Cgap L * Ckin k (carrierSq K) * relEnergy L k beta gamma rho K (u 0) := by
  obtain ⟨v, hv, hb⟩ := orbit_bound_mass_defect L hr (u t)
  rw [hm t] at hb
  refine ⟨v, hv, hb.trans ?_⟩
  have h := conserved_energy_bound L hq hg hrho u hc t
  have hn := mul_nonneg (mul_nonneg (Ckin_pos hq).le (density_coercivity_pos hrho).le)
    (density_nonneg L rho (u t))
  have hder : derivativeEnergy L (iota L 1 (u t)) ≤
      Ckin k (carrierSq K) * relEnergy L k beta gamma rho K (u 0) := by linarith
  have hc0 := Cgap_pos L
  have hmul := mul_le_mul_of_nonneg_left hder (show 0 ≤ 2 * Cgap L by positivity)
  calc
    _ ≤ |mass L (u 0) - rho| + (2 * Cgap L) *
        (Ckin k (carrierSq K) * relEnergy L k beta gamma rho K (u 0)) := by linarith
    _ = _ := by ring

/-- An epsilon-level orbital conclusion with a quantitative initial
mass-energy condition; no hidden compactness hypothesis. -/
theorem orbit_near_of_small_mass_energy {k beta gamma rho eps : ℝ}
    {K : Fin 2 → ℝ} (hq : k ^ 2 < carrierSq K) (hg : 0 ≤ gamma)
    (hrho : 3 * beta < 4 * gamma * rho) (hr : 0 ≤ rho) (heps : 0 < eps)
    (u : ℝ → ell2 2)
    (hm : ∀ t, mass L (u t) = mass L (u 0))
    (hc : ∀ t, relEnergy L k beta gamma rho K (u t) =
      relEnergy L k beta gamma rho K (u 0))
    (hsmall : |mass L (u 0) - rho| +
      2 * Cgap L * Ckin k (carrierSq K) * relEnergy L k beta gamma rho K (u 0) <
      eps ^ 2) :
    ∀ t, OrbitalStabilityCriterion.Near (phaseOrbit rho) (u t) eps := by
  intro t
  obtain ⟨v, hv, hb⟩ := conserving_orbit_bound_near_mass L hq hg hrho hr u hm hc t
  refine ⟨v, hv, ?_⟩
  rw [dist_eq_norm]
  have hlt := hb.trans_lt hsmall
  nlinarith [norm_nonneg (u t - v)]

end GC11TorusOrbit
end ReyesMath
