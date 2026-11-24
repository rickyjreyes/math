import MathProofs.OrbitalStability

/-!
# GC16: all positive masses when k = 0

Candidate extension of the exact F01 Hamiltonian on H²(ℝ²).
Use spatial stretching at fixed amplitude, rather than amplitude scaling alone.
The negative constrained infimum and the established sharp Fourier sup bound
give a uniform positive lower bound on the kinetic energy near the infimum.
No attainment, new axiom, or mass ceiling is assumed.
-/

namespace ReyesMath
namespace GC16ZeroShell

open Filter Topology
open Sobolev Sobolev.H2 StrictBinding
open OrbitalStability
open scoped Topology

/-- Stretch a field at fixed amplitude by a factor √t in two dimensions. -/
theorem exists_stretch (β γ : ℝ) (U : H2 2) {t : ℝ} (ht : 0 < t) :
    ∃ V : H2 2, M V = t * M U ∧
      energy β γ 0 V = t * energy β γ 0 U - (t - 1 / t) * D U := by
  let l := Real.sqrt (1 / t)
  have hl : 0 < l := Real.sqrt_pos.2 (div_pos (by norm_num) ht)
  have hl2 : l ^ 2 = 1 / t := Real.sq_sqrt (div_nonneg (by norm_num) ht.le)
  have hl4 : l ^ 4 = (1 / t) ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, hl2]
  obtain ⟨V, hM, hE⟩ := exists_scaled (β := β) (γ := γ) (k := 0)
    (dil hl U) (t := t) ht.le
  refine ⟨V, ?_, ?_⟩
  · rwa [M_dil] at hM
  · rw [T_eq, D_dil, Q_dil, S_dil, hl2, hl4] at hE
    rw [hE, energy_expand]
    simp only [zero_pow (by decide : (2 : ℕ) ≠ 0),
      zero_pow (by decide : (4 : ℕ) ≠ 0), zero_mul, sub_zero, zero_add, add_zero]
    field_simp
    <;> ring

/-- A negative-energy near minimizer has a uniformly nonzero kinetic term. -/
theorem kinetic_lower {β γ a J : ℝ} (hβ : 0 < β) (hγ : 0 < γ)
    (ha : 0 < a) (hJ : J < 0) (U : H2 2) (hM : M U = a)
    (hE : energy β γ 0 U < J / 2) :
    (-4 * J / (β * a)) ^ 2 / a ≤ D U := by
  have hq := Q_le_of_ae_bound U (ae_sup_bound_opt U)
  rw [hM] at hq
  have he := energy_eq β γ 0 U
  have ht := T_nonneg 0 U
  have hs : 0 ≤ γ / 3 * S U := mul_nonneg (by positivity) (S_nonneg U)
  have hqlo : -J < β * Q U := by linarith
  have hmul := mul_le_mul_of_nonneg_left hq hβ.le
  have hz : 0 < -4 * J / (β * a) :=
    div_pos (by linarith) (mul_pos hβ ha)
  have hsqrt : -4 * J / (β * a) < Real.sqrt (a * D U) := by
    apply (div_lt_iff₀ (mul_pos hβ ha)).2
    nlinarith only [hqlo, hmul]
  have hsq := pow_le_pow_left₀ hz.le hsqrt.le 2
  rw [Real.sq_sqrt (mul_nonneg ha.le (D_nonneg U))] at hsq
  exact (div_le_iff₀ ha).2 (by simpa [mul_comm] using hsq)

/-- The constrained infimum per mass decreases strictly at every positive mass,
in the exact k=0 focusing-cubic/defocusing-quintic model. -/
theorem energy_per_mass_strict {β γ a b : ℝ} (hβ : 0 < β) (hγ : 0 < γ)
    (ha : 0 < a) (hab : a < b) :
    Imin β γ 0 b / b < Imin β γ 0 a / a := by
  let t := b / a
  have ht : 1 < t := (one_lt_div ha).2 hab
  have ht0 : 0 < t := by linarith
  have hb : 0 < b := ha.trans hab
  have hta : t * a = b := by
    dsimp [t]
    field_simp [ha.ne']
  have hti : 1 / t < 1 := (div_lt_one ht0).2 ht
  have hd : 0 < t - 1 / t := by linarith
  let J := Imin β γ 0 a
  have hJ : J < 0 := (NegativeEnergy.negative_constrained_energy
    (k := 0) hβ hγ ha).2
  let c := (-4 * J / (β * a)) ^ 2 / a
  have hz : 0 < -4 * J / (β * a) :=
    div_pos (by linarith) (mul_pos hβ ha)
  have hc : 0 < c := div_pos (pow_pos hz 2) ha
  let e := min (-J / 2) ((t - 1 / t) * c / (2 * t))
  have he : 0 < e := lt_min (by linarith) (div_pos (mul_pos hd hc) (by positivity))
  obtain ⟨U, hUm, hUlt⟩ := exists_energy_lt (γ := γ) (k := 0) hβ ha he
  change energy β γ 0 U < J + e at hUlt
  have he1 : e ≤ -J / 2 := min_le_left _ _
  have he2 : e ≤ (t - 1 / t) * c / (2 * t) := min_le_right _ _
  have hD : c ≤ D U := kinetic_lower hβ hγ ha hJ U hUm (by linarith)
  obtain ⟨V, hVm, hVE⟩ := exists_stretch β γ U ht0
  have hIb : Imin β γ 0 b ≤ energy β γ 0 V :=
    Imin_le_energy hγ (by rw [hVm, hUm, hta])
  have hEU := mul_lt_mul_of_pos_left hUlt ht0
  have hgap := mul_le_mul_of_nonneg_left hD hd.le
  have hEe := mul_le_mul_of_nonneg_left he2 ht0.le
  have hcancel : t * ((t - 1 / t) * c / (2 * t)) = (t - 1 / t) * c / 2 := by
    field_simp
    <;> ring
  rw [hcancel] at hEe
  have hpos := mul_pos hd hc
  have hstrict : Imin β γ 0 b < t * J := by
    nlinarith only [hIb, hVE, hEU, hgap, hEe, hpos]
  calc Imin β γ 0 b / b < (t * J) / b := div_lt_div_of_pos_right hstrict hb
    _ = Imin β γ 0 a / a := by
      change t * J / b = J / a
      rw [← hta]
      field_simp [ht0.ne', ha.ne']

/-- GC16 is resolved in the k=0 subfamily, for all positive masses and splits. -/
theorem strict_binding_all_mass {β γ m a : ℝ} (hβ : 0 < β) (hγ : 0 < γ)
    (hm : 0 < m) (ha : 0 < a) (ham : a < m) :
    Imin β γ 0 m < Imin β γ 0 a + Imin β γ 0 (m - a) := by
  have hb : 0 < m - a := by linarith
  have e1 := energy_per_mass_strict hβ hγ ha ham
  have e2 := energy_per_mass_strict hβ hγ hb (show m - a < m by linarith)
  have f1 : a * (Imin β γ 0 m / m) < Imin β γ 0 a := by
    have h := mul_lt_mul_of_pos_left e1 ha
    rwa [mul_div_cancel₀ _ ha.ne'] at h
  have f2 : (m - a) * (Imin β γ 0 m / m) < Imin β γ 0 (m - a) := by
    have h := mul_lt_mul_of_pos_left e2 hb
    rwa [mul_div_cancel₀ _ hb.ne'] at h
  have hsum : a * (Imin β γ 0 m / m) + (m - a) * (Imin β γ 0 m / m) =
      Imin β γ 0 m := by
    field_simp
    <;> ring
  linarith

/-- Every minimizing sequence at positive mass has a strongly convergent
subsequence modulo translations, without a mass ceiling when k=0. -/
theorem compactness_all_mass {β γ m : ℝ} (hβ : 0 < β) (hγ : 0 < γ)
    (hm : 0 < m) {u : ℕ → H2 2} (hM : ∀ n, M (u n) = m)
    (hE : Tendsto (fun n => energy β γ 0 (u n)) atTop (𝓝 (Imin β γ 0 m))) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ y : ℕ → EuclideanSpace ℝ (Fin 2),
      ∃ U : H2 2, M U = m ∧ energy β γ 0 U = Imin β γ 0 m ∧
      Tendsto (fun n => distH2 (translate (y n) (u (φ n))) U) atTop (𝓝 0) :=
  WholeSpace.compactness_of_binding hβ hγ hm
    (fun a ha ham => strict_binding_all_mass hβ hγ hm ha ham) hM hE

/-- GC06: attainment at every positive mass in the exact k=0 subfamily. -/
theorem exists_minimizer_all_mass {β γ m : ℝ} (hβ : 0 < β) (hγ : 0 < γ)
    (hm : 0 < m) :
    ∃ U : H2 2, M U = m ∧ energy β γ 0 U = Imin β γ 0 m :=
  WholeSpace.exists_minimizer_of_binding hβ hγ hm
    (fun a ha ham => strict_binding_all_mass hβ hγ hm ha ham)

/-- GC01 milestone: stability of the entire constrained minimizing set,
not of every individual standing-wave orbit. -/
theorem orbital_stability_all_mass {β γ m ε : ℝ} (hβ : 0 < β) (hγ : 0 < γ)
    (hm : 0 < m) (hε : 0 < ε) :
    ∃ δ > 0, ∀ u : ℝ → H2 2, IsSolution β γ 0 u →
      distX (u 0) (Gset β γ 0 m) < δ →
      BddAbove (Set.range fun t => distX (u t) (Gset β γ 0 m)) ∧
      ⨆ t, distX (u t) (Gset β γ 0 m) < ε :=
  OrbitalStability.orbital_stability_of_binding hβ hγ hm
    (fun a ha ham => strict_binding_all_mass hβ hγ hm ha ham) hε

end GC16ZeroShell
end ReyesMath

#print axioms ReyesMath.GC16ZeroShell.strict_binding_all_mass
#print axioms ReyesMath.GC16ZeroShell.compactness_all_mass
#print axioms ReyesMath.GC16ZeroShell.exists_minimizer_all_mass
#print axioms ReyesMath.GC16ZeroShell.orbital_stability_all_mass
