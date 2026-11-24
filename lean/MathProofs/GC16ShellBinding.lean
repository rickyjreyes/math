import MathProofs.GC16ShellFourier

/-! GC16 nonzero-shell extension: actual H² energy and Imin, without attainment.
Candidate proof, verification pending on the pinned Mathlib toolchain. -/

open Filter Topology MeasureTheory Set
namespace ReyesMath
namespace GC16Shell

open Sobolev Sobolev.H2 StrictBinding

variable {β γ k : ℝ}

noncomputable def bulk (β γ : ℝ) : ℝ := 3 * β ^ 2 / (16 * γ)
noncomputable def sigmaShell (β γ : ℝ) : ℝ := 2 * Real.sqrt (bulk β γ)
noncomputable def mShell (β γ : ℝ) : ℝ := 3 * β / (γ * sigmaShell β γ)

theorem bulk_pos (hβ : 0 < β) (hγ : 0 < γ) : 0 < bulk β γ := by
  unfold bulk
  positivity

theorem sigmaShell_pos (hβ : 0 < β) (hγ : 0 < γ) : 0 < sigmaShell β γ := by
  unfold sigmaShell
  exact mul_pos two_pos (Real.sqrt_pos.2 (bulk_pos hβ hγ))

theorem mShell_pos (hβ : 0 < β) (hγ : 0 < γ) : 0 < mShell β γ := by
  unfold mShell
  exact div_pos (by positivity) (mul_pos hγ (sigmaShell_pos hβ hγ))

/-- Exact fixed-amplitude spatial stretch for arbitrary k. -/
theorem exists_stretch_general (β γ k : ℝ) (U : H2 2) {t : ℝ} (ht : 0 < t) :
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

/-- Uniform amplitude bound on every negative-energy H² field. -/
theorem ae_bound_of_negative (hβ : 0 < β) (hγ : 0 < γ) (U : H2 2)
    (hE : energy β γ k U < 0) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin 2))),
      ‖U.val x‖ ^ 2 ≤ sigmaShell β γ / 4 * M U := by
  let C := bulk β γ
  have hC : 0 < C := bulk_pos hβ hγ
  have hs : 0 < Real.sqrt C := Real.sqrt_pos.2 hC
  have hT := energy_ge β γ k hγ U
  change T k U - C * M U ≤ energy β γ k U at hT
  have hT' : T k U ≤ C * M U := by linarith
  filter_upwards [ae_sup_bound_shell U k hC] with x hx
  refine hx.trans ?_
  change (T k U + C * M U) / (4 * Real.sqrt C) ≤ (2 * Real.sqrt C) / 4 * M U
  apply (div_le_iff₀ (by positivity : 0 < 4 * Real.sqrt C)).2
  have he : (2 * Real.sqrt C / 4 * M U) * (4 * Real.sqrt C) = 2 * C * M U := by
    calc
      _ = 2 * (Real.sqrt C) ^ 2 * M U := by ring
      _ = _ := by rw [Real.sq_sqrt hC.le]
  rw [he]
  linarith

theorem S_le_of_negative (hβ : 0 < β) (hγ : 0 < γ) (U : H2 2)
    (hE : energy β γ k U < 0) :
    S U ≤ sigmaShell β γ / 4 * M U * Q U := by
  unfold S Q
  rw [← integral_const_mul]
  refine integral_mono_ae (integrable_S U) ((integrable_Q U).const_mul _) ?_
  filter_upwards [ae_bound_of_negative hβ hγ U hE] with x hx
  calc
    ‖U.val x‖ ^ 6 = ‖U.val x‖ ^ 2 * ‖U.val x‖ ^ 4 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hx (by positivity)

/-- The new mass bound is independent of the preferred wavenumber. -/
theorem mShell_eq (hβ : 0 < β) (hγ : 0 < γ) :
    mShell β γ = 2 * Real.sqrt 3 / Real.sqrt γ := by
  have hroot : Real.sqrt (bulk β γ) = Real.sqrt 3 * β / (4 * Real.sqrt γ) := by
    apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).2
    unfold bulk
    field_simp [Real.sqrt_ne_zero'.2 hγ]
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sq_sqrt hγ.le]
    <;> ring
  unfold mShell sigmaShell
  rw [hroot]
  have hg : Real.sqrt γ ≠ 0 := (Real.sqrt_pos.2 hγ).ne'
  have h3 : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 3)).ne'
  field_simp [hβ.ne', hγ.ne', hg, h3]
  nlinarith [Real.sq_sqrt hγ.le, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]

theorem gap_shell (hβ : 0 < β) (hγ : 0 < γ) {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hsum : a + b < 2 * mShell β γ) :
    (b - a) * (1 - (a + b) / (2 * mShell β γ)) / a ^ 2 * (-Imin β γ k a) ≤
      Imin β γ k a / a - Imin β γ k b / b ∧
    0 < (b - a) * (1 - (a + b) / (2 * mShell β γ)) / a ^ 2 * (-Imin β γ k a) := by
  have hmB := mShell_pos hβ hγ
  have hσ := sigmaShell_pos hβ hγ
  have hmBeq : mShell β γ * (γ * sigmaShell β γ) = 3 * β := by
    unfold mShell
    field_simp
  have hneg := (NegativeEnergy.negative_constrained_energy (k := k) hβ hγ ha).2
  obtain ⟨h, hh⟩ : ∃ h, h = 1 - (a + b) / (2 * mShell β γ) := ⟨_, rfl⟩
  have hhpos : 0 < h := by
    rw [hh, sub_pos, div_lt_one (by positivity)]
    exact hsum
  obtain ⟨t, ht⟩ : ∃ t, t = b / a := ⟨_, rfl⟩
  have hta : t * a = b := by
    rw [ht]
    field_simp
  have htpos : 1 < t := by
    rw [ht, one_lt_div ha]
    exact hab
  obtain ⟨Ia, hIa⟩ : ∃ I, I = Imin β γ k a := ⟨_, rfl⟩
  obtain ⟨Ib, hIb⟩ : ∃ I, I = Imin β γ k b := ⟨_, rfl⟩
  rw [← hh, ← hIa, ← hIb]
  rw [← hIa] at hneg
  obtain ⟨c, hc⟩ : ∃ c, c = 1 + (t - 1) * h := ⟨_, rfl⟩
  have hcpos : 0 < c := by
    rw [hc]
    nlinarith
  have hkey : Ib / t ≤ c * Ia := by
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    let δ := min (-Ia / 2) (ε / (2 * c))
    have hδ : 0 < δ := lt_min (by linarith) (by positivity)
    obtain ⟨W, hWm, hWlt⟩ := exists_energy_lt (γ := γ) (k := k) hβ ha
      (ε := δ) hδ
    rw [← hIa] at hWlt
    have hδ1 : δ ≤ -Ia / 2 := min_le_left _ _
    have hδ2 : δ ≤ ε / (2 * c) := min_le_right _ _
    have hWneg : energy β γ k W < 0 := by linarith
    obtain ⟨V, hVm, hEV⟩ := exists_scaled (β := β) (γ := γ) (k := k) W (t := t) (by linarith)
    have hSQ := S_le_of_negative hβ hγ W hWneg
    rw [hWm] at hSQ
    have hstep : energy β γ k V / t ≤ c * energy β γ k W := by
      rw [hc]
      exact scaling_arith hβ hγ ha hmB hta htpos hh hmBeq hhpos hEV (energy_eq β γ k W) hSQ
        (T_nonneg k W) (S_nonneg W)
    have hIbV : Ib ≤ energy β γ k V := by
      rw [hIb]
      exact Imin_le_energy hγ (by rw [hVm, hWm, hta])
    have e1 : Ib / t ≤ energy β γ k V / t := div_le_div_of_nonneg_right hIbV (by linarith)
    have e2 : c * energy β γ k W ≤ c * (Ia + ε / (2 * c)) :=
      mul_le_mul_of_nonneg_left (by linarith) hcpos.le
    have e3 : c * (Ia + ε / (2 * c)) = c * Ia + ε / 2 := by
      field_simp
    linarith
  have hpos : 0 < (b - a) * h / a ^ 2 * (-Ia) := by
    have : 0 < b - a := by linarith
    have : 0 < -Ia := by linarith
    positivity
  refine ⟨?_, hpos⟩
  have heb : Ib / b ≤ c * (Ia / a) := by
    have e : Ib / b = Ib / t / a := by
      rw [← hta, div_div]
    rw [e, div_le_iff₀ ha]
    calc Ib / t ≤ c * Ia := hkey
      _ = c * (Ia / a) * a := by field_simp
  have e : (b - a) * h / a ^ 2 * (-Ia) = -((t - 1) * h * (Ia / a)) := by
    rw [← hta]
    field_simp
  rw [e]
  rw [hc] at heb
  nlinarith [heb]

/-- **Theorem (uniform shell strict-binding range).**  For `β, γ > 0`, every `k`, every
`0 < m ≤ m_B` and every `0 < μ < m`: `I(m) < I(μ) + I(m − μ)`. -/
theorem strict_binding_shell (hβ : 0 < β) (hγ : 0 < γ) {m μ : ℝ} (hm : 0 < m) (hmB : m ≤ mShell β γ)
    (hμ : 0 < μ) (hμm : μ < m) :
    Imin β γ k m < Imin β γ k μ + Imin β γ k (m - μ) := by
  have h1 := gap_shell (k := k) hβ hγ hμ hμm (by linarith)
  have h2 := gap_shell (k := k) hβ hγ (show 0 < m - μ by linarith) (show m - μ < m by linarith)
    (by linarith)
  have e1 : Imin β γ k m / m < Imin β γ k μ / μ := by linarith [h1.1, h1.2]
  have e2 : Imin β γ k m / m < Imin β γ k (m - μ) / (m - μ) := by linarith [h2.1, h2.2]
  have hmμ : 0 < m - μ := by linarith
  have f1 : μ * (Imin β γ k m / m) < Imin β γ k μ := by
    have := mul_lt_mul_of_pos_left e1 hμ
    rwa [mul_div_cancel₀ _ hμ.ne'] at this
  have f2 : (m - μ) * (Imin β γ k m / m) < Imin β γ k (m - μ) := by
    have := mul_lt_mul_of_pos_left e2 hmμ
    rwa [mul_div_cancel₀ _ hmμ.ne'] at this
  have : μ * (Imin β γ k m / m) + (m - μ) * (Imin β γ k m / m) = Imin β γ k m := by
    field_simp
    ring
  linarith


end GC16Shell
end ReyesMath

#print axioms ReyesMath.GC16Shell.exists_stretch_general
#print axioms ReyesMath.GC16Shell.gap_shell
#print axioms ReyesMath.GC16Shell.strict_binding_shell
