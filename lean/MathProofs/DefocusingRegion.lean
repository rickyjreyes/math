import Mathlib
import MathProofs.StrictBinding

/-!
# GC06: exact nonconfinement in the defocusing, zero-selector whole-space regime

For the SAME fourth-order F01 cubic-quintic Hamiltonian on H²(R²; C),
  H(u) = ||(Delta+k²)u||² - (beta/2) Q(u) + (gamma/3) S(u),
we prove:
* H(u) >= 0 for all beta <= 0, gamma >= 0;
* at k=0 and fixed mass m>0, I(m)=0. A mass-preserving dilation
  drives all three positive energy terms to zero;
* when beta<0 or gamma>0, no positive-mass field attains that infimum.

This is a genuine model-specific EXCLUDED region for ground-state
confinement, not a universal nonattainment theorem for other k,
not a statement about A2, and not a proof of instability of an
unrelated periodic stationary state.
-/

open Filter Topology Complex InnerProductSpace MeasureTheory Set

namespace ReyesMath.DefocusingRegion

open Sobolev Sobolev.H2

/-- Repulsive quartic and nonnegative sextic terms cannot make the
F01 whole-space energy negative. No strict positivity of gamma is needed. -/
theorem energy_nonnegative (beta gamma k : ℝ)
    (hb : beta ≤ 0) (hg : 0 ≤ gamma) (U : H2 2) :
    0 ≤ energy beta gamma k U := by
  rw [energy_eq]
  have hT := T_nonneg k U
  have hQ := Q_nonneg U
  have hS := S_nonneg U
  have hquad : 0 ≤ -(beta / 2) * Q U :=
    mul_nonneg (by linarith) hQ
  have hsextic : 0 ≤ gamma / 3 * S U :=
    mul_nonneg (by linarith) hS
  linarith

/-- Strictly defocusing quartic term yields strictly positive energy
at every nonzero mass, even if gamma=0. -/
theorem energy_pos_of_negative_beta (beta gamma k : ℝ)
    (hb : beta < 0) (hg : 0 ≤ gamma) (U : H2 2)
    (hm : 0 < M U) :
    0 < energy beta gamma k U := by
  rw [energy_eq]
  have hT := T_nonneg k U
  have hQ := Q_pos U hm
  have hS := S_nonneg U
  have hquad : 0 < -(beta / 2) * Q U :=
    mul_pos (by linarith) hQ
  have hsextic : 0 ≤ gamma / 3 * S U :=
    mul_nonneg (by linarith) hS
  linarith

/-- At beta=0, a positive sextic coupling also rules out zero
energy for every nonzero mass. -/
theorem energy_pos_of_zero_beta_positive_gamma (gamma k : ℝ)
    (hg : 0 < gamma) (U : H2 2) (hm : 0 < M U) :
    0 < energy 0 gamma k U := by
  rw [energy_eq]
  have hT := T_nonneg k U
  have hS := S_pos U hm
  have hsextic : 0 < gamma / 3 * S U :=
    mul_pos (by positivity) hS
  linarith

/-- A fixed-mass test field exists independent of the coefficients:
the existing negative-energy trial at auxiliary beta=gamma=1 supplies
a bona fide nonzero H² function of prescribed positive mass. -/
theorem exists_mass_state (m : ℝ) (hm : 0 < m) :
    ∃ U : H2 2, M U = m := by
  obtain ⟨U, hU, _⟩ :=
    NegativeEnergy.exists_negative (β := (1 : ℝ))
      (γ := (1 : ℝ)) (k := 0) (m := m) (by norm_num) hm
  exact ⟨U, hU⟩

/-- The exact defocusing constrained infimum is bounded below by zero. -/
theorem infimum_nonnegative (beta gamma k m : ℝ)
    (hb : beta ≤ 0) (hg : 0 ≤ gamma) (hm : 0 < m) :
    0 ≤ Imin beta gamma k m := by
  obtain ⟨U, hU⟩ := exists_mass_state m hm
  have hn : (energy beta gamma k '' {V : H2 2 | M V = m}).Nonempty :=
    ⟨energy beta gamma k U, U, hU, rfl⟩
  apply le_csInf hn
  rintro e ⟨V, -, rfl⟩
  exact energy_nonnegative beta gamma k hb hg V

/-- Exact constrained infimum at k=0. The proof uses the *same*
Hamiltonian, exact mass-preserving dilation and convergence of
lambda^2,lambda^4 to zero. -/
theorem infimum_zero_at_zero_selector (beta gamma m : ℝ)
    (hb : beta ≤ 0) (hg : 0 ≤ gamma) (hm : 0 < m) :
    Imin beta gamma 0 m = 0 := by
  obtain ⟨U, hU⟩ := exists_mass_state m hm
  have hbelow : BddBelow
      (energy beta gamma 0 '' {V : H2 2 | M V = m}) := by
    refine ⟨0, ?_⟩
    rintro e ⟨V, -, rfl⟩
    exact energy_nonnegative beta gamma 0 hb hg V
  let lam : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hlam : ∀ n, 0 < lam n := by
    intro n
    dsimp [lam]
    positivity
  have hlambda : Tendsto lam atTop (𝓝 (0 : ℝ)) := by
    simpa only [lam] using tendsto_one_div_add_atTop_nhds_zero_nat
  have henergy_formula (n : ℕ) :
      energy beta gamma 0 (dil (hlam n) U) =
      (lam n) ^ 4 * (D U + gamma / 3 * S U) -
        (lam n) ^ 2 * (beta / 2 * Q U) := by
    have h := energy_dil beta gamma 0 (hlam n) U
    convert h using 1 <;> ring
  have henergy : Tendsto
      (fun n => energy beta gamma 0 (dil (hlam n) U))
      atTop (𝓝 (0 : ℝ)) := by
    have h4 := (hlambda.pow 4).mul_const (D U + gamma / 3 * S U)
    have h2 := (hlambda.pow 2).mul_const (beta / 2 * Q U)
    have h := h4.sub h2
    have h0 : (0 : ℝ) ^ 4 * (D U + gamma / 3 * S U) -
        (0 : ℝ) ^ 2 * (beta / 2 * Q U) = 0 := by ring
    rw [h0] at h
    convert h using 1 <;>
      simp only [henergy_formula]
  have hnonneg := infimum_nonnegative beta gamma 0 m hb hg hm
  have hnonpos : Imin beta gamma 0 m ≤ 0 := by
    by_contra hn
    have hp : 0 < Imin beta gamma 0 m := lt_of_not_ge hn
    obtain ⟨n, hn⟩ :=
      (henergy.eventually (gt_mem_nhds hp)).exists
    have hmass : M (dil (hlam n) U) = m := by
      rw [M_dil]
      exact hU
    have hupper : Imin beta gamma 0 m ≤
        energy beta gamma 0 (dil (hlam n) U) :=
      csInf_le hbelow ⟨_, hmass, rfl⟩
    linarith
  exact le_antisymm hnonpos hnonneg

/-- An explicit entire excluded regime: for k=0, beta<0, gamma>=0,
positive-mass constrained minimizers do not exist. -/
theorem no_minimizer_negative_beta (beta gamma m : ℝ)
    (hb : beta < 0) (hg : 0 ≤ gamma) (hm : 0 < m) :
    ¬ ∃ U : H2 2, M U = m ∧
        energy beta gamma 0 U = Imin beta gamma 0 m := by
  intro ⟨U, hU, hE⟩
  have hp := energy_pos_of_negative_beta beta gamma 0 hb hg U
    (by rw [hU]; exact hm)
  have hI := infimum_zero_at_zero_selector beta gamma m hb.le hg hm
  linarith

/-- The same nonattainment conclusion when beta=0, gamma>0. -/
theorem no_minimizer_positive_sextic (gamma m : ℝ)
    (hg : 0 < gamma) (hm : 0 < m) :
    ¬ ∃ U : H2 2, M U = m ∧
        energy 0 gamma 0 U = Imin 0 gamma 0 m := by
  intro ⟨U, hU, hE⟩
  have hp := energy_pos_of_zero_beta_positive_gamma gamma 0 hg U
    (by rw [hU]; exact hm)
  have hI := infimum_zero_at_zero_selector 0 gamma m (le_refl _) hg.le hm
  linarith

/-! ## Stronger obstruction: absence of virial/dilation stationary states -/

/-- When k=0 and beta<0, the exact F01 dilation-stationarity
identity cannot hold on any positive-mass H² state. This rules out
ALL dilation-critical states in this regime, not only minimizers.
It does not silently assert that a generic weak PDE solution has
the regularity needed to satisfy the virial identity. -/
theorem no_dilation_stationary_negative_beta
    (beta gamma : ℝ) (hb : beta < 0) (hg : 0 ≤ gamma)
    (U : H2 2) (hm : 0 < M U) :
    ¬ IsStationary beta gamma 0 U := by
  intro hstat
  have hD := D_nonneg U
  have hQ := Q_pos U hm
  have hS := S_nonneg U
  have hrepulsive : 0 < -(beta / 4) * Q U :=
    mul_pos (by linarith) hQ
  have hsextic : 0 ≤ gamma / 3 * S U :=
    mul_nonneg (by linarith) hS
  unfold IsStationary at hstat
  norm_num at hstat
  nlinarith

/-- When k=beta=0 and gamma>0, every positive-mass H² state
also violates the exact dilation-stationarity identity. -/
theorem no_dilation_stationary_sextic
    (gamma : ℝ) (hg : 0 < gamma)
    (U : H2 2) (hm : 0 < M U) :
    ¬ IsStationary 0 gamma 0 U := by
  intro hstat
  have hD := D_nonneg U
  have hS := S_pos U hm
  have hsextic : 0 < gamma / 3 * S U :=
    mul_pos (by positivity) hS
  unfold IsStationary at hstat
  norm_num at hstat
  nlinarith

/-- Explicit union of strictly defocusing mass-parameter sectors
with no positive-mass dilation-stationary state at k=0. -/
theorem no_dilation_stationary_defocusing
    (beta gamma : ℝ) (hb : beta ≤ 0) (hg : 0 ≤ gamma)
    (hstrict : beta < 0 ∨ 0 < gamma)
    (U : H2 2) (hm : 0 < M U) :
    ¬ IsStationary beta gamma 0 U := by
  rcases hstrict with hbeta | hgamma
  · exact no_dilation_stationary_negative_beta beta gamma hbeta hg U hm
  · have hz : beta = 0 := by linarith
    subst beta
    exact no_dilation_stationary_sextic gamma hgamma U hm

end ReyesMath.DefocusingRegion
