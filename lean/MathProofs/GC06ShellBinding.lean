import MathProofs.WholeSpaceMinimizers

/-!
GC06: sharpened stationary-dilation confinement region for the original F01
Hamiltonian, without a symmetry assumption. Candidate proof pending CI.
-/

open Filter Topology Complex InnerProductSpace MeasureTheory Set
open scoped Topology

namespace ReyesMath.GC06ShellBinding

open Sobolev Sobolev.H2 StrictBinding
variable {β γ k : ℝ}

noncomputable def sigmaR (β γ k : ℝ) : ℝ :=
  (k ^ 2 + Real.sqrt (k ^ 4 + 2 * (3 * β ^ 2 / (32 * γ)))) / 2

noncomputable def mR (β γ k : ℝ) : ℝ := 3 * β / (γ * sigmaR β γ k)

theorem sigmaR_gt (hβ : 0 < β) (hγ : 0 < γ) :
    k ^ 2 < sigmaR β γ k := by
  have hc : 0 < 3 * β ^ 2 / (32 * γ) := by positivity
  let r := Real.sqrt (k ^ 4 + 2 * (3 * β ^ 2 / (32 * γ)))
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = k ^ 4 + 2 * (3 * β ^ 2 / (32 * γ)) :=
    Real.sq_sqrt (by positivity)
  change k ^ 2 < (k ^ 2 + r) / 2
  by_contra! h
  have hprod := mul_nonneg (show 0 ≤ k ^ 2 - r by linarith)
    (show 0 ≤ k ^ 2 + r by positivity)
  nlinarith only [hprod, hr2, hc]

theorem sigmaR_pos (hβ : 0 < β) (hγ : 0 < γ) :
    0 < sigmaR β γ k := (sq_nonneg k).trans_lt (sigmaR_gt hβ hγ)

theorem sigmaR_eq (hγ : 0 < γ) :
    2 * sigmaR β γ k ^ 2 - 2 * k ^ 2 * sigmaR β γ k =
      3 * β ^ 2 / (32 * γ) := by
  have hr := Real.sq_sqrt
    (show 0 ≤ k ^ 4 + 2 * (3 * β ^ 2 / (32 * γ)) by positivity)
  unfold sigmaR
  nlinarith only [hr]

theorem mR_pos (hβ : 0 < β) (hγ : 0 < γ) : 0 < mR β γ k := by
  unfold mR
  have := sigmaR_pos (k := k) hβ hγ
  positivity

/-- The improvement is strict for every allowed coefficient tuple. -/
theorem sigmaR_lt_sigmaB (hβ : 0 < β) (hγ : 0 < γ) :
    sigmaR β γ k < sigmaB β γ k := by
  have hgt := sigmaR_gt (k := k) hβ hγ
  have he := sigmaR_eq (β := β) (k := k) hγ
  have hb : sigmaB β γ k ^ 2 = k ^ 4 + 3 * β ^ 2 / (32 * γ) := by
    unfold sigmaB rho
    exact Real.sq_sqrt (by positivity)
  have hp := mul_pos (sub_pos.mpr hgt) (sub_pos.mpr hgt)
  have hs := sigmaB_pos (k := k) hβ hγ
  by_contra! h
  have hprod := mul_nonneg (sub_nonneg.mpr h)
    (show 0 ≤ sigmaR β γ k + sigmaB β γ k by linarith)
  nlinarith only [hprod, hp, he, hb]

theorem mB_lt_mR (hβ : 0 < β) (hγ : 0 < γ) :
    mB β γ k < mR β γ k := by
  unfold mB mR
  have hs := sigmaR_pos (k := k) hβ hγ
  have hb := sigmaB_pos (k := k) hβ hγ
  rw [div_lt_div_iff₀ (mul_pos hγ hb) (mul_pos hγ hs)]
  exact mul_lt_mul_of_pos_left
    (mul_lt_mul_of_pos_left (sigmaR_lt_sigmaB hβ hγ) hγ) (by positivity)

/-- Retain the gradient Cauchy bound in the stationary virial identity.
This is a bound on the actual Sobolev field, not an abstract surrogate. -/
theorem sqrt_MD_refined (hβ : 0 < β) (hγ : 0 < γ) {W : H2 2}
    (hW : IsStationary β γ k W) :
    Real.sqrt (M W * D W) ≤ sigmaR β γ k * M W := by
  have hM := M_nonneg W
  have hD0 := D_nonneg W
  have hx0 := Real.sqrt_nonneg (M W * D W)
  have hx2 := Real.sq_sqrt (mul_nonneg hM hD0)
  have hK := K_le_sqrt W
  have hK' := mul_le_mul_of_nonneg_left hK (show 0 ≤ 2 * k ^ 2 by positivity)
  have hnn := sextic_quartic_mass_nonneg (β := β) hγ W
  have hD : 2 * D W ≤
      2 * k ^ 2 * Real.sqrt (M W * D W) + 3 * β ^ 2 / (32 * γ) * M W := by
    unfold IsStationary at hW
    linarith only [hW, hnn, hK']
  have hmul := mul_le_mul_of_nonneg_right hD hM
  have hσ := sigmaR_eq (β := β) (k := k) hγ
  have hσM := congrArg (fun z : ℝ => z * M W ^ 2) hσ
  have hσge := mul_le_mul_of_nonneg_right (sigmaR_gt (k := k) hβ hγ).le hM
  have hσ0 := mul_nonneg (sigmaR_pos (k := k) hβ hγ).le hM
  by_contra! h
  have hxp : 0 < Real.sqrt (M W * D W) := hσ0.trans_lt h
  have hp := mul_pos (sub_pos.mpr h)
    (show 0 < Real.sqrt (M W * D W) + sigmaR β γ k * M W - k ^ 2 * M W by
      linarith only [hxp, hσge])
  nlinarith only [hmul, hx2, hσM, hp]

theorem S_le_of_stationary_refined (hβ : 0 < β) (hγ : 0 < γ) {W : H2 2}
    (hW : IsStationary β γ k W) :
    S W ≤ sigmaR β γ k / 4 * M W * Q W := by
  calc
    S W ≤ Real.sqrt (M W * D W) / 4 * Q W := S_le W
    _ ≤ sigmaR β γ k * M W / 4 * Q W := by
      gcongr
      exact sqrt_MD_refined hβ hγ hW
    _ = sigmaR β γ k / 4 * M W * Q W := by ring

theorem gap_refined (hβ : 0 < β) (hγ : 0 < γ) {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hsum : a + b < 2 * mR β γ k) :
    (b - a) * (1 - (a + b) / (2 * mR β γ k)) / a ^ 2 * (-Imin β γ k a) ≤
      Imin β γ k a / a - Imin β γ k b / b ∧
    0 < (b - a) * (1 - (a + b) / (2 * mR β γ k)) / a ^ 2 * (-Imin β γ k a) := by
  have hmB := mR_pos (k := k) hβ hγ
  have hσ := sigmaR_pos (k := k) hβ hγ
  have hmBeq : mR β γ k * (γ * sigmaR β γ k) = 3 * β := by
    unfold mR
    field_simp
  have hneg := (NegativeEnergy.negative_constrained_energy (k := k) hβ hγ ha).2
  obtain ⟨h, hh⟩ : ∃ h, h = 1 - (a + b) / (2 * mR β γ k) := ⟨_, rfl⟩
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
    obtain ⟨U, hUm, hUlt⟩ := exists_energy_lt (γ := γ) (k := k) hβ ha
      (ε := ε / (2 * c)) (by positivity)
    rw [← hIa] at hUlt
    obtain ⟨W, hWm, hWle, hWst⟩ := exists_stationary_dil k hβ hγ U (by rw [hUm]; exact ha)
    rw [hUm] at hWm
    obtain ⟨V, hVm, hEV⟩ := exists_scaled (β := β) (γ := γ) (k := k) W (t := t) (by linarith)
    have hSQ := S_le_of_stationary_refined hβ hγ hWst
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

/-- **Theorem (explicit strict-binding range).**  For `β, γ > 0`, every `k`, every
`0 < m ≤ m_B` and every `0 < μ < m`: `I(m) < I(μ) + I(m − μ)`. -/
theorem strict_binding_refined (hβ : 0 < β) (hγ : 0 < γ) {m μ : ℝ} (hm : 0 < m) (hmB : m ≤ mR β γ k)
    (hμ : 0 < μ) (hμm : μ < m) :
    Imin β γ k m < Imin β γ k μ + Imin β γ k (m - μ) := by
  have h1 := gap_refined (k := k) hβ hγ hμ hμm (by linarith)
  have h2 := gap_refined (k := k) hβ hγ (show 0 < m - μ by linarith) (show m - μ < m by linarith)
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


/-- Full-sequence compactness in the strictly enlarged explicit interval. -/
theorem compactness_refined (hβ : 0 < β) (hγ : 0 < γ) {m : ℝ}
    (hm : 0 < m) (hmR : m ≤ mR β γ k) {u : ℕ → H2 2}
    (hM : ∀ n, M (u n) = m)
    (hE : Tendsto (fun n => energy β γ k (u n)) atTop (𝓝 (Imin β γ k m))) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ y : ℕ → EuclideanSpace ℝ (Fin 2),
      ∃ U : H2 2, M U = m ∧ energy β γ k U = Imin β γ k m ∧
      Tendsto (fun n => distH2 (translate (y n) (u (φ n))) U) atTop (𝓝 0) :=
  WholeSpace.compactness_of_binding hβ hγ hm
    (fun a ha ham => strict_binding_refined hβ hγ hm hmR ha ham) hM hE

theorem exists_minimizer_refined (hβ : 0 < β) (hγ : 0 < γ) {m : ℝ}
    (hm : 0 < m) (hmR : m ≤ mR β γ k) :
    ∃ U : H2 2, M U = m ∧ energy β γ k U = Imin β γ k m :=
  WholeSpace.exists_minimizer_of_binding hβ hγ hm
    (fun a ha ham => strict_binding_refined hβ hγ hm hmR ha ham)

end ReyesMath.GC06ShellBinding

#print axioms ReyesMath.GC06ShellBinding.mB_lt_mR
#print axioms ReyesMath.GC06ShellBinding.strict_binding_refined
#print axioms ReyesMath.GC06ShellBinding.compactness_refined
#print axioms ReyesMath.GC06ShellBinding.exists_minimizer_refined
