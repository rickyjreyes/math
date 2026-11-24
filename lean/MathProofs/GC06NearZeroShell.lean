import MathProofs.GC06ShellBinding

/-!
GC06: a growing near-zero-selector all-split binding region. The exact
zero-selector constrained energy at a fixed seed mass controls the region.
No existence of seed minimizers is assumed.
Candidate proofs require kernel verification.
-/

open Filter Topology Complex InnerProductSpace MeasureTheory Set
open scoped Topology

namespace ReyesMath.GC06NearZeroShell
open Sobolev Sobolev.H2 StrictBinding GC06ShellBinding
variable {β γ k : ℝ}

theorem exists_stretch (β γ k : ℝ) (U : H2 2) {t : ℝ} (ht : 0 < t) :
    ∃ V : H2 2, M V = t * M U ∧
      energy β γ k V = t * energy β γ k U - (t - 1 / t) * D U +
        2 * k ^ 2 * (t - 1) * K U := by
  let l := Real.sqrt (1 / t)
  have hl : 0 < l := Real.sqrt_pos.2 (div_pos (by norm_num) ht)
  have hl2 : l ^ 2 = 1 / t := Real.sq_sqrt (div_nonneg (by norm_num) ht.le)
  have hl4 : l ^ 4 = (1 / t) ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, hl2]
  obtain ⟨V, hM, hE⟩ := exists_scaled (β := β) (γ := γ) (k := k)
    (dil hl U) (t := t) ht.le
  refine ⟨V, ?_, ?_⟩
  · rwa [M_dil] at hM
  · rw [T_eq, D_dil, K_dil, M_dil, Q_dil, S_dil, hl2, hl4] at hE
    rw [hE, energy_expand]
    field_simp [ht.ne']
    <;> ring

/-- A negative-energy seed at k=0 produces a uniform negative energy per mass
at all larger masses, for a small nonzero k. -/
theorem seed_upper (hβ : 0 < β) (hγ : 0 < γ) {a0 a η : ℝ}
    (ha0 : 0 < a0) (haa : a0 ≤ a) (hη : 0 < η)
    (hseed : Imin β γ 0 a0 < -2 * η * a0) (hk : k ^ 4 ≤ η) :
    Imin β γ k a ≤ -η * a := by
  have ha : 0 < a := ha0.trans_le haa
  let t := a / a0
  have ht : 1 ≤ t := (le_div_iff₀ ha0).2 (by simpa using haa)
  have ht0 : 0 < t := by linarith
  have hta : t * a0 = a := by
    dsimp [t]
    field_simp [ha0.ne']
  have heps : 0 < -2 * η * a0 - Imin β γ 0 a0 := sub_pos.mpr hseed
  obtain ⟨U, hUm, hUe⟩ := exists_energy_lt (γ := γ) (k := 0) hβ ha0 heps
  have hU : energy β γ 0 U < -2 * η * a0 := by linarith
  obtain ⟨V, hVm, hVE⟩ := exists_stretch β γ k U ht0
  have heq : energy β γ k U =
      energy β γ 0 U - 2 * k ^ 2 * K U + k ^ 4 * M U := by
    rw [energy_expand, energy_expand]
    ring
  have hVE' : energy β γ k V = t * energy β γ 0 U -
      (t - 1 / t) * D U - 2 * k ^ 2 * K U + t * k ^ 4 * M U := by
    rw [hVE, heq]
    ring
  have hti : 1 / t ≤ 1 := (div_le_one ht0).2 ht
  have hd := mul_nonneg (show 0 ≤ t - 1 / t by linarith) (D_nonneg U)
  have hK := mul_nonneg (show 0 ≤ 2 * k ^ 2 by positivity) (K_nonneg U)
  have hEVle : energy β γ k V ≤ t * (energy β γ 0 U + k ^ 4 * a0) := by
    rw [hVE', hUm]
    nlinarith only [hd, hK]
  have hbound0 : energy β γ 0 U + k ^ 4 * a0 < -η * a0 := by
    have hh := mul_le_mul_of_nonneg_right hk ha0.le
    linarith only [hh, hU]
  have hbound := mul_lt_mul_of_pos_left hbound0 ht0
  have hI : Imin β γ k a ≤ energy β γ k V :=
    Imin_le_energy hγ (by rw [hVm, hUm, hta])
  calc
    Imin β γ k a ≤ energy β γ k V := hI
    _ ≤ t * (energy β γ 0 U + k ^ 4 * a0) := hEVle
    _ ≤ t * (-η * a0) := hbound.le
    _ = -η * a := by rw [← hta]; ring

/-- A uniform positive kinetic stretching defect near the infimum. -/
theorem kinetic_gap (hβ : 0 < β) (hγ : 0 < γ) {a η : ℝ}
    (ha : 0 < a) (hη : 0 < η) (hk : 2 * k ^ 2 * a < 4 * η / β)
    (U : H2 2) (hM : M U = a) (hE : energy β γ k U < -η * a / 2) :
    (4 * η / β) * (4 * η / β - 2 * k ^ 2 * a) / a ≤ D U - 2 * k ^ 2 * K U := by
  let x := Real.sqrt (a * D U)
  let L := 4 * η / β
  have hL : 0 < L := by dsimp [L]; positivity
  have hx2 : x ^ 2 = a * D U := Real.sq_sqrt (mul_nonneg ha.le (D_nonneg U))
  have hq := Q_le_of_ae_bound U (ae_sup_bound_opt U)
  rw [hM] at hq
  change Q U ≤ x / 4 * a at hq
  have he := energy_eq β γ k U
  have hT := T_nonneg k U
  have hS := mul_nonneg (show 0 ≤ γ / 3 by positivity) (S_nonneg U)
  have hqlo : η * a < β * Q U := by linarith only [he, hE, hT, hS]
  have hqhi := mul_le_mul_of_nonneg_left hq hβ.le
  have hLX : L ≤ x := by
    change 4 * η / β ≤ x
    apply (div_le_iff₀ hβ).2
    by_contra! h
    have hh := mul_lt_mul_of_pos_right h ha
    nlinarith only [hh, hqlo, hqhi]
  have hK := K_le_sqrt U
  rw [hM] at hK
  change K U ≤ x at hK
  have hK' := mul_le_mul_of_nonneg_left hK (show 0 ≤ 2 * k ^ 2 * a by positivity)
  change 2 * k ^ 2 * a < L at hk
  have hxL := mul_nonneg (sub_nonneg.mpr hLX)
    (show 0 ≤ x + L - 2 * k ^ 2 * a by linarith only [hk, hL, hLX])
  change L * (L - 2 * k ^ 2 * a) / a ≤ D U - 2 * k ^ 2 * K U
  apply (div_le_iff₀ ha).2
  nlinarith only [hx2, hK', hxL]

/-- Binding comparison without a bound on the sextic-to-quartic ratio. -/
theorem energy_per_mass_strict (hβ : 0 < β) (hγ : 0 < γ) {a b η : ℝ}
    (ha : 0 < a) (hab : a < b) (hη : 0 < η)
    (hJ : Imin β γ k a ≤ -η * a) (hk : 2 * k ^ 2 * a < 4 * η / β) :
    Imin β γ k b / b < Imin β γ k a / a := by
  let t := b / a
  have ht : 1 < t := (one_lt_div ha).2 hab
  have ht0 : 0 < t := by linarith
  have hb : 0 < b := ha.trans hab
  have hta : t * a = b := by dsimp [t]; field_simp [ha.ne']
  let J := Imin β γ k a
  let c := (4 * η / β) * (4 * η / β - 2 * k ^ 2 * a) / a
  have hc : 0 < c := by
    dsimp [c]
    exact div_pos (mul_pos (by positivity) (sub_pos.mpr hk)) ha
  let e := min (η * a / 2) ((t - 1) * c / (2 * t))
  have he : 0 < e := lt_min (by positivity)
    (div_pos (mul_pos (sub_pos.mpr ht) hc) (by positivity))
  obtain ⟨U, hUm, hUlt⟩ := exists_energy_lt (γ := γ) (k := k) hβ ha he
  change energy β γ k U < J + e at hUlt
  have he1 : e ≤ η * a / 2 := min_le_left _ _
  have he2 : e ≤ (t - 1) * c / (2 * t) := min_le_right _ _
  have hD : c ≤ D U - 2 * k ^ 2 * K U :=
    kinetic_gap hβ hγ ha hη hk U hUm (by
      change J ≤ -η * a at hJ
      linarith only [hJ, hUlt, he1])
  obtain ⟨V, hVm, hVE⟩ := exists_stretch β γ k U ht0
  have hIb : Imin β γ k b ≤ energy β γ k V :=
    Imin_le_energy hγ (by rw [hVm, hUm, hta])
  have hti : 1 / t < 1 := (div_lt_one ht0).2 ht
  have hrem := mul_nonneg (show 0 ≤ 1 - 1 / t by linarith) (D_nonneg U)
  have hEU := mul_lt_mul_of_pos_left hUlt ht0
  have hgap := mul_le_mul_of_nonneg_left hD (sub_nonneg.mpr ht.le)
  have hEe := mul_le_mul_of_nonneg_left he2 ht0.le
  have hcancel : t * ((t - 1) * c / (2 * t)) = (t - 1) * c / 2 := by
    field_simp [ht0.ne']
    <;> ring
  rw [hcancel] at hEe
  have hpos := mul_pos (sub_pos.mpr ht) hc
  have hstrict : Imin β γ k b < t * J := by
    nlinarith only [hIb, hVE, hEU, hgap, hEe, hpos, hrem]
  calc Imin β γ k b / b < (t * J) / b := div_lt_div_of_pos_right hstrict hb
    _ = Imin β γ k a / a := by
      change t * J / b = J / a
      rw [← hta]
      field_simp [ht0.ne', ha.ne']

/-- All smaller masses have strictly higher energy per mass at the target m.
The seed lies in the refined region; the target need not lie in that region. -/
theorem comparison_near_zero (hβ : 0 < β) (hγ : 0 < γ) {a0 a m η : ℝ}
    (ha0 : 0 < a0) (ha0R : a0 ≤ mR β γ k) (ha0m : a0 ≤ m)
    (ha : 0 < a) (ham : a < m) (hη : 0 < η)
    (hseed : Imin β γ 0 a0 < -2 * η * a0) (hk4 : k ^ 4 ≤ η)
    (hk : 2 * k ^ 2 * m < 4 * η / β) :
    Imin β γ k m / m < Imin β γ k a / a := by
  have hcmp : ∀ x : ℝ, a0 ≤ x → x < m →
      Imin β γ k m / m < Imin β γ k x / x := by
    intro x hx hxm
    have hxx := mul_le_mul_of_nonneg_left hxm.le (show 0 ≤ 2 * k ^ 2 by positivity)
    exact energy_per_mass_strict hβ hγ (ha0.trans_le hx) hxm hη
      (seed_upper hβ hγ ha0 hx hη hseed hk4) (hxx.trans_lt hk)
  by_cases h : a0 ≤ a
  · exact hcmp a h ham
  · have haa0 : a < a0 := lt_of_not_ge h
    have hg := gap_refined (k := k) hβ hγ ha haa0 (by linarith)
    have he : Imin β γ k a0 / a0 < Imin β γ k a / a := by linarith [hg.1, hg.2]
    rcases lt_or_eq_of_le ha0m with hlt | heq
    · exact (hcmp a0 le_rfl hlt).trans he
    · rwa [← heq]

theorem strict_binding_near_zero (hβ : 0 < β) (hγ : 0 < γ) {a0 m μ η : ℝ}
    (ha0 : 0 < a0) (ha0R : a0 ≤ mR β γ k) (ha0m : a0 ≤ m)
    (hη : 0 < η) (hseed : Imin β γ 0 a0 < -2 * η * a0)
    (hk4 : k ^ 4 ≤ η) (hk : 2 * k ^ 2 * m < 4 * η / β)
    (hμ : 0 < μ) (hμm : μ < m) :
    Imin β γ k m < Imin β γ k μ + Imin β γ k (m - μ) := by
  have hm : 0 < m := ha0.trans_le ha0m
  have hmμ : 0 < m - μ := by linarith
  have e1 := comparison_near_zero hβ hγ ha0 ha0R ha0m hμ hμm hη hseed hk4 hk
  have e2 := comparison_near_zero hβ hγ ha0 ha0R ha0m hmμ
    (show m - μ < m by linarith) hη hseed hk4 hk
  have f1 : μ * (Imin β γ k m / m) < Imin β γ k μ := by
    have h := mul_lt_mul_of_pos_left e1 hμ
    rwa [mul_div_cancel₀ _ hμ.ne'] at h
  have f2 : (m - μ) * (Imin β γ k m / m) < Imin β γ k (m - μ) := by
    have h := mul_lt_mul_of_pos_left e2 hmμ
    rwa [mul_div_cancel₀ _ hmμ.ne'] at h
  have hsum : μ * (Imin β γ k m / m) + (m - μ) * (Imin β γ k m / m) =
      Imin β γ k m := by field_simp; ring
  linarith

theorem compactness_near_zero (hβ : 0 < β) (hγ : 0 < γ) {a0 m η : ℝ}
    (ha0 : 0 < a0) (ha0R : a0 ≤ mR β γ k) (ha0m : a0 ≤ m)
    (hη : 0 < η) (hseed : Imin β γ 0 a0 < -2 * η * a0)
    (hk4 : k ^ 4 ≤ η) (hk : 2 * k ^ 2 * m < 4 * η / β)
    {u : ℕ → H2 2} (hM : ∀ n, M (u n) = m)
    (hE : Tendsto (fun n => energy β γ k (u n)) atTop (𝓝 (Imin β γ k m))) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ y : ℕ → EuclideanSpace ℝ (Fin 2),
      ∃ U : H2 2, M U = m ∧ energy β γ k U = Imin β γ k m ∧
      Tendsto (fun n => distH2 (translate (y n) (u (φ n))) U) atTop (𝓝 0) :=
  WholeSpace.compactness_of_binding hβ hγ (ha0.trans_le ha0m)
    (fun a ha ham => strict_binding_near_zero hβ hγ ha0 ha0R ha0m hη hseed hk4 hk ha ham) hM hE

theorem exists_minimizer_near_zero (hβ : 0 < β) (hγ : 0 < γ) {a0 m η : ℝ}
    (ha0 : 0 < a0) (ha0R : a0 ≤ mR β γ k) (ha0m : a0 ≤ m)
    (hη : 0 < η) (hseed : Imin β γ 0 a0 < -2 * η * a0)
    (hk4 : k ^ 4 ≤ η) (hk : 2 * k ^ 2 * m < 4 * η / β) :
    ∃ U : H2 2, M U = m ∧ energy β γ k U = Imin β γ k m :=
  WholeSpace.exists_minimizer_of_binding hβ hγ (ha0.trans_le ha0m)
    (fun a ha ham => strict_binding_near_zero hβ hγ ha0 ha0R ha0m hη hseed hk4 hk ha ham)

end ReyesMath.GC06NearZeroShell

#print axioms ReyesMath.GC06NearZeroShell.exists_stretch
#print axioms ReyesMath.GC06NearZeroShell.seed_upper
#print axioms ReyesMath.GC06NearZeroShell.kinetic_gap
#print axioms ReyesMath.GC06NearZeroShell.strict_binding_near_zero
#print axioms ReyesMath.GC06NearZeroShell.compactness_near_zero
#print axioms ReyesMath.GC06NearZeroShell.exists_minimizer_near_zero
