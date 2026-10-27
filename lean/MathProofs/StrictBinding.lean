import Mathlib
import MathProofs.NegativeEnergy

/-!
# Strict binding for the fourth-order cubic–quintic Hamiltonian (F01/T1)

Formalization of `papers/strict-subadditivity-fourth-order-cubic-quintic/main.tex` on the
Sobolev space `H²(ℝ²; ℂ)` of `MathProofs.SobolevH2`, with
`H(u) = ‖(Δ + k²)u‖² − (β/2)‖u‖⁴_{L⁴} + (γ/3)‖u‖⁶_{L⁶}` and
`I(m) = inf {H(u) : ‖u‖²₂ = m}` (`Sobolev.H2.energy`, `Sobolev.H2.Imin`).

* Scalings: `Sobolev.H2.smul` (amplitude) with `M_smul`, `K_smul`, `D_smul`, `Q_smul`,
  `S_smul`, `T_smul`; the mass-preserving dilation `u_λ(x) = λu(λx)` with `Q_dil`, `S_dil`
  and `energy_dil` (`H(u_λ) = λ⁴P − λ²B + k⁴M`).
* `Sobolev.H2.T_eq`: `T = D − 2k²K + k⁴M ≥ 0`.
* Lemma (coercive lower bound): `Sobolev.H2.energy_ge`, `StrictBinding.bounded_of_energy_le`.
* Lemma (strict negativity): `NegativeEnergy.negative_constrained_energy`.
* Lemma (dilation-stationary minimizing sequences): `Sobolev.H2.exists_stationary_dil` and
  `StrictBinding.exists_stationary_minimizing_seq`, with the identity
  `IsStationary : D − k²K − (β/4)Q + (γ/3)S = 0`.
* Lemma (square completion on the stationary dilation): `Sobolev.H2.stationary_square` (the
  exact identity `D + T + (2γ/3)∫|w|²(|w|² − 3β/(8γ))² = ρM`) and `D_le_of_stationary`.
* Lemma (Fourier sup-norm estimate): `Sobolev.H2.ae_sup_bound`, `Sobolev.H2.ae_sup_bound_opt`.
* Proposition (stationary sextic/quartic ratio): `Sobolev.H2.ae_sq_le_of_stationary`
  (`‖w‖²_∞ ≤ (σ/4)M`) and `Sobolev.H2.S_le_of_stationary` (`S ≤ (σ/4) M Q`).
* Proposition (strict decrease at the infimum): `StrictBinding.gap`.
* Theorem (explicit strict-binding range): `StrictBinding.strict_binding` — for `β, γ > 0`,
  every `k`, every `0 < m ≤ m_B = 3β/(γ√(k⁴ + 3β²/(32γ)))` and every `0 < μ < m`,
  `I(m) < I(μ) + I(m − μ)`.  No attainment of any infimum is used.
* Corollary (exact frozen-parameter check): `StrictBinding.frozen_parameters`.
-/

open Filter Topology Complex InnerProductSpace MeasureTheory Set
open scoped ContDiff

namespace ReyesMath

namespace Sobolev

namespace H2

variable {d : ℕ}

/-- Amplitude scaling `c • u` on `H²`. -/
noncomputable def smul (c : ℂ) (U : H2 d) : H2 d where
  val := c • U.val
  grad := fun i => c • U.grad i
  lap := c • U.lap
  approx := by
    obtain ⟨φ, h0, h1, h2⟩ := U.approx
    refine ⟨fun n => c • φ n, ?_, fun i => ?_, ?_⟩
    · simpa only [map_smul] using h0.const_smul c
    · simpa only [map_smul] using (h1 i).const_smul c
    · simpa only [map_smul] using h2.const_smul c

theorem M_smul (c : ℂ) (U : H2 d) : M (smul c U) = ‖c‖ ^ 2 * M U := by
  simp only [M, smul, norm_smul, mul_pow]

theorem K_smul (c : ℂ) (U : H2 d) : K (smul c U) = ‖c‖ ^ 2 * K U := by
  simp only [K, smul, norm_smul, mul_pow, Finset.mul_sum]

theorem D_smul (c : ℂ) (U : H2 d) : D (smul c U) = ‖c‖ ^ 2 * D U := by
  simp only [D, smul, norm_smul, mul_pow]

theorem integral_pow_smul (c : ℂ) (U : H2 d) (n : ℕ) :
    ∫ x, ‖(smul c U).val x‖ ^ n = ‖c‖ ^ n * ∫ x, ‖U.val x‖ ^ n := by
  rw [← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_smul c U.val] with x hx
  simp only [smul]
  rw [hx, Pi.smul_apply, norm_smul, mul_pow]

theorem Q_smul (c : ℂ) (U : H2 d) : Q (smul c U) = ‖c‖ ^ 4 * Q U := integral_pow_smul c U 4

theorem S_smul (c : ℂ) (U : H2 d) : S (smul c U) = ‖c‖ ^ 6 * S U := integral_pow_smul c U 6

/-- The kinetic term `T(u) = ‖(Δ + k²)u‖²`. -/
noncomputable def T (k : ℝ) (U : H2 d) : ℝ := ‖U.lap + ((k ^ 2 : ℝ) : ℂ) • U.val‖ ^ 2

theorem T_smul (k : ℝ) (c : ℂ) (U : H2 d) : T k (smul c U) = ‖c‖ ^ 2 * T k U := by
  simp only [T, smul]
  rw [smul_comm, ← smul_add, norm_smul, mul_pow]

theorem T_eq (k : ℝ) (U : H2 d) : T k U = D U - 2 * k ^ 2 * K U + k ^ 4 * M U :=
  normSq_shift U k

theorem T_nonneg (k : ℝ) (U : H2 d) : 0 ≤ T k U := sq_nonneg _

theorem energy_eq (β γ k : ℝ) (U : H2 2) : energy β γ k U = T k U - β / 2 * Q U + γ / 3 * S U :=
  rfl

theorem Q_nonneg (U : H2 d) : 0 ≤ Q U := integral_nonneg fun _ => by positivity

theorem S_nonneg (U : H2 d) : 0 ≤ S U := integral_nonneg fun _ => by positivity

/-- A nonzero `L²` function has positive `‖u‖^{2n}` integral. -/
theorem integral_pow_pos (U : H2 d) (hM : 0 < M U) {n : ℕ} (hn : n ≠ 0)
    (hint : Integrable fun x => ‖U.val x‖ ^ (2 * n)) : 0 < ∫ x, ‖U.val x‖ ^ (2 * n) := by
  rw [integral_pos_iff_support_of_nonneg (fun x => by positivity) hint]
  by_contra h
  push_neg at h
  have h0 : volume (Function.support fun x => ‖U.val x‖ ^ (2 * n)) = 0 := le_antisymm h (zero_le _)
  have hae : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), ‖U.val x‖ ^ 2 = 0 := by
    have := measure_eq_zero_iff_ae_notMem.1 h0
    filter_upwards [this] with x hx
    rw [Function.mem_support, not_not] at hx
    have : ‖U.val x‖ = 0 := by
      have := pow_eq_zero_iff (n := 2 * n) (by omega) |>.1 hx
      exact this
    rw [this]
    simp
  have : M U = 0 := by
    rw [M_eq_integral, integral_eq_zero_of_ae hae]
  linarith

theorem Q_pos (U : H2 2) (hM : 0 < M U) : 0 < Q U := by
  have := integral_pow_pos U hM (n := 2) two_ne_zero (integrable_Q U)
  simpa [Q] using this

theorem S_pos (U : H2 2) (hM : 0 < M U) : 0 < S U := by
  have := integral_pow_pos U hM (n := 3) (by norm_num) (integrable_S U)
  simpa [S] using this

end H2

end Sobolev

end ReyesMath

namespace ReyesMath

namespace Sobolev

namespace H2

local notation "R2" => EuclideanSpace ℝ (Fin 2)

variable {lam : ℝ}

theorem Q_dil (hlam : 0 < lam) (U : H2 2) : Q (dil hlam U) = lam ^ 2 * Q U := by
  have h := integral_dil hlam U (fun r => r ^ 2)
  simp only [← pow_mul] at h
  unfold Q
  rw [h]
  simp_rw [mul_pow, ← pow_mul]
  rw [integral_const_mul]
  field_simp

theorem S_dil (hlam : 0 < lam) (U : H2 2) : S (dil hlam U) = lam ^ 4 * S U := by
  have h := integral_dil hlam U (fun r => r ^ 3)
  simp only [← pow_mul] at h
  unfold S
  rw [h]
  simp_rw [mul_pow, ← pow_mul]
  rw [integral_const_mul]
  field_simp

/-- The energy along the mass-preserving dilation:
`H(u_λ) = λ⁴ P − λ² B + k⁴ M`, `P = D + (γ/3)S`, `B = 2k²K + (β/2)Q`. -/
theorem energy_dil (β γ k : ℝ) (hlam : 0 < lam) (U : H2 2) :
    energy β γ k (dil hlam U) =
      lam ^ 4 * (D U + γ / 3 * S U) - lam ^ 2 * (2 * k ^ 2 * K U + β / 2 * Q U) + k ^ 4 * M U := by
  rw [energy_eq, T_eq, D_dil, K_dil, M_dil, Q_dil, S_dil]
  ring

theorem energy_expand (β γ k : ℝ) (U : H2 2) :
    energy β γ k U = (D U + γ / 3 * S U) - (2 * k ^ 2 * K U + β / 2 * Q U) + k ^ 4 * M U := by
  rw [energy_eq, T_eq]
  ring

/-- The dilation-stationarity identity `D − k²K − (β/4)Q + (γ/3)S = 0`. -/
def IsStationary (β γ k : ℝ) (W : H2 2) : Prop :=
  D W - k ^ 2 * K W - β / 4 * Q W + γ / 3 * S W = 0

/-- **Exact dilation adjustment.**  Every `u ≠ 0` has a dilation `w` with the same mass, no
larger energy, and the stationarity identity. -/
theorem exists_stationary_dil {β γ : ℝ} (k : ℝ) (hβ : 0 < β) (hγ : 0 < γ) (U : H2 2)
    (hM : 0 < M U) :
    ∃ W : H2 2, M W = M U ∧ energy β γ k W ≤ energy β γ k U ∧ IsStationary β γ k W := by
  have hS := S_pos U hM
  have hQ := Q_pos U hM
  have hK := K_nonneg U
  have hD := D_nonneg U
  set P := D U + γ / 3 * S U with hP
  set B := 2 * k ^ 2 * K U + β / 2 * Q U with hB
  have hPpos : 0 < P := by positivity
  have hBpos : 0 < B := by positivity
  set z := B / (2 * P) with hz
  have hzpos : 0 < z := by positivity
  have hlam : 0 < Real.sqrt z := Real.sqrt_pos.2 hzpos
  have hl2 : Real.sqrt z ^ 2 = z := Real.sq_sqrt hzpos.le
  have hl4 : Real.sqrt z ^ 4 = z ^ 2 := by rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, hl2]
  refine ⟨dil hlam U, M_dil hlam U, ?_, ?_⟩
  · rw [energy_dil, energy_expand, hl2, hl4]
    have : P * z ^ 2 - z * B + k ^ 4 * M U ≤ P - B + k ^ 4 * M U := by
      have h2 : 2 * P * z = B := by rw [hz]; field_simp
      have h3 : P * z ^ 2 - z * B = -(P * z ^ 2) := by rw [← h2]; ring
      have h4 : P - B = P - 2 * P * z := by rw [← h2]
      rw [h3, h4]
      nlinarith [mul_nonneg hPpos.le (sq_nonneg (z - 1))]
    rw [← hP, ← hB]
    linarith
  · unfold IsStationary
    rw [D_dil, K_dil, Q_dil, S_dil, hl2, hl4]
    have h2 : 2 * P * z = B := by rw [hz]; field_simp
    have : z ^ 2 * D U - k ^ 2 * (z * K U) - β / 4 * (z * Q U) + γ / 3 * (z ^ 2 * S U) =
        z * (z * P - B / 2) := by rw [hP, hB]; ring
    rw [this]
    have : z * P - B / 2 = 0 := by linarith
    rw [this, mul_zero]

/-- `(2γ/3)S − (β/2)Q + (3β²/(32γ))M = (2γ/3)∫|u|²(|u|² − 3β/(8γ))² ≥ 0`. -/
theorem sextic_quartic_mass_nonneg {β γ : ℝ} (hγ : 0 < γ) (U : H2 2) :
    0 ≤ 2 * γ / 3 * S U - β / 2 * Q U + 3 * β ^ 2 / (32 * γ) * M U := by
  have hQ := integrable_Q U
  have hS := integrable_S U
  have h2 := integrable_sq_val U
  have hint : Integrable fun x => 2 * γ / 3 * ‖U.val x‖ ^ 6 - β / 2 * ‖U.val x‖ ^ 4 +
      3 * β ^ 2 / (32 * γ) * ‖U.val x‖ ^ 2 :=
    ((hS.const_mul _).sub (hQ.const_mul _)).add (h2.const_mul _)
  have hnn : 0 ≤ ∫ x, (2 * γ / 3 * ‖U.val x‖ ^ 6 - β / 2 * ‖U.val x‖ ^ 4 +
      3 * β ^ 2 / (32 * γ) * ‖U.val x‖ ^ 2) := by
    refine integral_nonneg fun x => ?_
    have hid : 2 * γ / 3 * ‖U.val x‖ ^ 6 - β / 2 * ‖U.val x‖ ^ 4 +
        3 * β ^ 2 / (32 * γ) * ‖U.val x‖ ^ 2 =
        2 * γ / 3 * ‖U.val x‖ ^ 2 * (‖U.val x‖ ^ 2 - 3 * β / (8 * γ)) ^ 2 := by
      field_simp
      ring
    rw [hid]
    positivity
  have hA : Integrable fun x => 2 * γ / 3 * ‖U.val x‖ ^ 6 - β / 2 * ‖U.val x‖ ^ 4 :=
    (hS.const_mul _).sub (hQ.const_mul _)
  rw [integral_add hA (h2.const_mul _), integral_sub (hS.const_mul _) (hQ.const_mul _),
    integral_const_mul, integral_const_mul, integral_const_mul, ← M_eq_integral] at hnn
  unfold Q S
  linarith

/-- **Square completion on the stationary dilation:** `D(w) ≤ ρ M(w)`,
`ρ = k⁴ + 3β²/(32γ)`. -/
theorem D_le_of_stationary {β γ k : ℝ} (hγ : 0 < γ) {W : H2 2} (hW : IsStationary β γ k W) :
    D W ≤ (k ^ 4 + 3 * β ^ 2 / (32 * γ)) * M W := by
  have hT := T_nonneg k W
  rw [T_eq] at hT
  have hnn := sextic_quartic_mass_nonneg (β := β) hγ W
  unfold IsStationary at hW
  nlinarith

/-- On a stationary dilation, `√(M D) ≤ √ρ M`. -/
theorem sqrt_MD_le_of_stationary {β γ k : ℝ} (hγ : 0 < γ) {W : H2 2}
    (hW : IsStationary β γ k W) :
    Real.sqrt (M W * D W) ≤ Real.sqrt (k ^ 4 + 3 * β ^ 2 / (32 * γ)) * M W := by
  have h2 := D_le_of_stationary hγ hW
  have hM := M_nonneg W
  calc Real.sqrt (M W * D W) ≤ Real.sqrt (M W * ((k ^ 4 + 3 * β ^ 2 / (32 * γ)) * M W)) :=
        Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left h2 hM)
    _ = Real.sqrt (k ^ 4 + 3 * β ^ 2 / (32 * γ)) * M W := by
        rw [show M W * ((k ^ 4 + 3 * β ^ 2 / (32 * γ)) * M W) =
          (k ^ 4 + 3 * β ^ 2 / (32 * γ)) * M W ^ 2 by ring,
          Real.sqrt_mul (by positivity), Real.sqrt_sq hM]

/-- **Stationary sup-norm bound:** `‖w‖²_∞ ≤ (σ/4) M(w)`, `σ = √ρ`. -/
theorem ae_sq_le_of_stationary {β γ k : ℝ} (hγ : 0 < γ) {W : H2 2}
    (hW : IsStationary β γ k W) :
    ∀ᵐ x, ‖W.val x‖ ^ 2 ≤ Real.sqrt (k ^ 4 + 3 * β ^ 2 / (32 * γ)) / 4 * M W := by
  have h := sqrt_MD_le_of_stationary hγ hW
  filter_upwards [ae_sup_bound_opt W] with x hx
  linarith

/-- **Stationary sextic/quartic ratio:** `S(w) ≤ (σ/4) M(w) Q(w)`, `σ = √ρ`. -/
theorem S_le_of_stationary {β γ k : ℝ} (hγ : 0 < γ) {W : H2 2} (hW : IsStationary β γ k W) :
    S W ≤ Real.sqrt (k ^ 4 + 3 * β ^ 2 / (32 * γ)) / 4 * M W * Q W := by
  have h1 := S_le W
  have hQ := Q_nonneg W
  have h3 := sqrt_MD_le_of_stationary hγ hW
  calc S W ≤ Real.sqrt (M W * D W) / 4 * Q W := h1
    _ ≤ Real.sqrt (k ^ 4 + 3 * β ^ 2 / (32 * γ)) * M W / 4 * Q W := by gcongr
    _ = Real.sqrt (k ^ 4 + 3 * β ^ 2 / (32 * γ)) / 4 * M W * Q W := by ring

/-- **Square completion on the stationary dilation (exact identity):**
`D(w) + T(w) + (2γ/3)∫|w|²(|w|² − 3β/(8γ))² = ρ M(w)`. -/
theorem stationary_square {β γ k : ℝ} (hγ : 0 < γ) {W : H2 2} (hW : IsStationary β γ k W) :
    D W + T k W + 2 * γ / 3 * ∫ x, ‖W.val x‖ ^ 2 * (‖W.val x‖ ^ 2 - 3 * β / (8 * γ)) ^ 2 =
      (k ^ 4 + 3 * β ^ 2 / (32 * γ)) * M W := by
  have hQ := integrable_Q W
  have hS := integrable_S W
  have h2 := integrable_sq_val W
  have hid : ∀ x, ‖W.val x‖ ^ 2 * (‖W.val x‖ ^ 2 - 3 * β / (8 * γ)) ^ 2 =
      ‖W.val x‖ ^ 6 - 3 * β / (4 * γ) * ‖W.val x‖ ^ 4 + (3 * β / (8 * γ)) ^ 2 * ‖W.val x‖ ^ 2 :=
    fun x => by ring
  have hA : Integrable fun x => ‖W.val x‖ ^ 6 - 3 * β / (4 * γ) * ‖W.val x‖ ^ 4 :=
    hS.sub (hQ.const_mul _)
  simp_rw [hid]
  rw [integral_add hA (h2.const_mul _), integral_sub hS (hQ.const_mul _), integral_const_mul,
    integral_const_mul, ← M_eq_integral, T_eq]
  have hc1 : 2 * γ / 3 * (3 * β / (4 * γ)) = β / 2 := by
    field_simp
    ring
  have hc2 : 2 * γ / 3 * (3 * β / (8 * γ)) ^ 2 = 3 * β ^ 2 / (32 * γ) := by
    field_simp
    ring
  unfold IsStationary at hW
  unfold Q S at hW
  linear_combination 2 * hW - (∫ x, ‖W.val x‖ ^ 4) * hc1 + M W * hc2

end H2

end Sobolev

end ReyesMath

namespace ReyesMath

namespace StrictBinding

open Sobolev Sobolev.H2

variable {β γ k : ℝ}

/-- `ρ = k⁴ + 3β²/(32γ)`. -/
noncomputable def rho (β γ k : ℝ) : ℝ := k ^ 4 + 3 * β ^ 2 / (32 * γ)

/-- `σ = √ρ`. -/
noncomputable def sigmaB (β γ k : ℝ) : ℝ := Real.sqrt (rho β γ k)

/-- The explicit strict-binding mass `m_B = 3β/(γσ)`. -/
noncomputable def mB (β γ k : ℝ) : ℝ := 3 * β / (γ * sigmaB β γ k)

theorem sigmaB_pos (hβ : 0 < β) (hγ : 0 < γ) : 0 < sigmaB β γ k := by
  unfold sigmaB rho
  apply Real.sqrt_pos.2
  positivity

theorem mB_pos (hβ : 0 < β) (hγ : 0 < γ) : 0 < mB β γ k := by
  unfold mB
  have := sigmaB_pos (k := k) hβ hγ
  positivity

theorem bddBelow_energy (hγ : 0 < γ) (m : ℝ) :
    BddBelow (energy β γ k '' {U | M U = m}) := by
  refine ⟨-(3 * β ^ 2 / (16 * γ)) * m, ?_⟩
  rintro _ ⟨V, hV, rfl⟩
  have := energy_ge_mass β γ k hγ V
  rwa [hV] at this

theorem Imin_le_energy (hγ : 0 < γ) {m : ℝ} {U : H2 2} (hU : M U = m) :
    Imin β γ k m ≤ energy β γ k U :=
  csInf_le (bddBelow_energy hγ m) ⟨U, hU, rfl⟩

theorem exists_energy_lt (hβ : 0 < β) {m : ℝ} (hm : 0 < m) {ε : ℝ} (hε : 0 < ε) :
    ∃ U : H2 2, M U = m ∧ energy β γ k U < Imin β γ k m + ε := by
  obtain ⟨U, hUm, -⟩ := NegativeEnergy.exists_negative (β := β) (γ := γ) (k := k) hβ hm
  have hne : (energy β γ k '' {U | M U = m}).Nonempty := ⟨_, U, hUm, rfl⟩
  obtain ⟨_, ⟨V, hV, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt hne (lt_add_of_pos_right _ hε)
  exact ⟨V, hV, hlt⟩

/-- **Coercive lower bound, boundedness part.**  A mass-`m` state with energy at most `C₀` has
`‖Δu‖₂ ≤ √(C₀ + 3β²m/(16γ)) + k²√m` and `K(u) ≤ √(m D(u))`; in particular fixed-mass
sequences with energies bounded above are bounded in `H²`. -/
theorem bounded_of_energy_le (hγ : 0 < γ) {U : H2 2} {m C₀ : ℝ} (hM : M U = m)
    (hE : energy β γ k U ≤ C₀) :
    D U ≤ (Real.sqrt (C₀ + 3 * β ^ 2 / (16 * γ) * m) + k ^ 2 * Real.sqrt m) ^ 2 ∧
      K U ≤ Real.sqrt (m * D U) := by
  have hT := energy_ge β γ k hγ U
  rw [hM] at hT
  have h1 : ‖U.lap + ((k ^ 2 : ℝ) : ℂ) • U.val‖ ≤ Real.sqrt (C₀ + 3 * β ^ 2 / (16 * γ) * m) :=
    Real.le_sqrt_of_sq_le (by linarith)
  have hk : ‖((k ^ 2 : ℝ) : ℂ) • U.val‖ = k ^ 2 * Real.sqrt m := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity), ← hM, M,
      Real.sqrt_sq (norm_nonneg _)]
  have h2 : ‖U.lap‖ ≤ ‖U.lap + ((k ^ 2 : ℝ) : ℂ) • U.val‖ + k ^ 2 * Real.sqrt m := by
    calc ‖U.lap‖ = ‖(U.lap + ((k ^ 2 : ℝ) : ℂ) • U.val) - ((k ^ 2 : ℝ) : ℂ) • U.val‖ := by
          rw [add_sub_cancel_right]
      _ ≤ ‖U.lap + ((k ^ 2 : ℝ) : ℂ) • U.val‖ + ‖((k ^ 2 : ℝ) : ℂ) • U.val‖ := norm_sub_le _ _
      _ = _ := by rw [hk]
  refine ⟨?_, ?_⟩
  · rw [D]
    exact pow_le_pow_left₀ (norm_nonneg _) (h2.trans (by linarith)) 2
  · rw [← hM]
    exact K_le_sqrt U

/-- **Dilation-stationary minimizing sequences.**  For every `a > 0` there is a minimizing
sequence at mass `a` each of whose members satisfies the stationarity identity. -/
theorem exists_stationary_minimizing_seq (hβ : 0 < β) (hγ : 0 < γ) {a : ℝ} (ha : 0 < a) :
    ∃ w : ℕ → H2 2, (∀ n, M (w n) = a) ∧
      Tendsto (fun n => energy β γ k (w n)) atTop (𝓝 (Imin β γ k a)) ∧
      ∀ n, IsStationary β γ k (w n) := by
  have hU : ∀ n : ℕ, ∃ U : H2 2, M U = a ∧ energy β γ k U < Imin β γ k a + 1 / ((n : ℝ) + 1) :=
    fun n => exists_energy_lt hβ ha (by positivity)
  choose U hUm hUlt using hU
  have hW : ∀ n, ∃ W : H2 2, M W = a ∧ energy β γ k W ≤ energy β γ k (U n) ∧
      IsStationary β γ k W := fun n => by
    obtain ⟨W, hWm, hWle, hWst⟩ := exists_stationary_dil k hβ hγ (U n) (by rw [hUm n]; exact ha)
    exact ⟨W, hWm.trans (hUm n), hWle, hWst⟩
  choose w hwm hwle hwst using hW
  refine ⟨w, hwm, ?_, hwst⟩
  have hlim : Tendsto (fun n : ℕ => Imin β γ k a + 1 / ((n : ℝ) + 1)) atTop
      (𝓝 (Imin β γ k a)) := by
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_add (Imin β γ k a)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun n => Imin_le_energy hγ (hwm n)) (fun n => (hwle n).trans (hUlt n).le)

/-- Amplitude scaling `u ↦ √t u` multiplies the mass by `t`, the kinetic term by `t`, the
quartic term by `t²` and the sextic term by `t³`. -/
theorem exists_scaled (W : H2 2) {t : ℝ} (ht : 0 ≤ t) :
    ∃ V : H2 2, M V = t * M W ∧
      energy β γ k V = t * T k W - β / 2 * (t ^ 2 * Q W) + γ / 3 * (t ^ 3 * S W) := by
  have hst : ‖((Real.sqrt t : ℝ) : ℂ)‖ = Real.sqrt t := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hs2 : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht
  have hs4 : Real.sqrt t ^ 4 = t ^ 2 := by rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, hs2]
  have hs6 : Real.sqrt t ^ 6 = t ^ 3 := by rw [show (6 : ℕ) = 2 * 3 by rfl, pow_mul, hs2]
  refine ⟨smul ((Real.sqrt t : ℝ) : ℂ) W, ?_, ?_⟩
  · rw [M_smul, hst, hs2]
  · rw [energy_eq, T_smul, Q_smul, S_smul, hst, hs2, hs4, hs6]

/-- The real-arithmetic core of the mass-scaling comparison: if `w` has mass `a`, satisfies
`S ≤ (σ/4) a Q`, and `v = √t w` with `t a = b`, then `H(v)/t ≤ (1 + (t − 1)h) H(w)`,
`h = 1 − (a+b)/(2m_B)`, `m_B γ σ = 3β`. -/
theorem scaling_arith {σ m a b t h EV EW T Q S : ℝ} (hβ : 0 < β) (hγ : 0 < γ) (ha : 0 < a)
    (hm : 0 < m) (hta : t * a = b) (htpos : 1 < t) (hh : h = 1 - (a + b) / (2 * m))
    (hmeq : m * (γ * σ) = 3 * β) (hhpos : 0 < h)
    (hEV : EV = t * T - β / 2 * (t ^ 2 * Q) + γ / 3 * (t ^ 3 * S))
    (hEW : EW = T - β / 2 * Q + γ / 3 * S) (hSQ : S ≤ σ / 4 * a * Q) (hT : 0 ≤ T)
    (hS : 0 ≤ S) :
    EV / t ≤ (1 + (t - 1) * h) * EW := by
  have hm0 : m ≠ 0 := hm.ne'
  have htt : 0 ≤ t * (t - 1) := by nlinarith
  have h1 : γ * (t + 1) / 3 * S ≤ γ * (t + 1) / 3 * (σ / 4 * a * Q) :=
    mul_le_mul_of_nonneg_left hSQ (by positivity)
  have hβ' : β = m * (γ * σ) / 3 := by linarith
  have h2 : γ * (t + 1) / 3 * (σ / 4 * a * Q) = β * (a + b) / (4 * m) * Q := by
    rw [hβ', ← hta]
    field_simp
    ring
  have h3 : -(β * h / 2) * Q = -β / 2 * Q + β * (a + b) / (4 * m) * Q := by
    rw [hh]
    field_simp
    ring
  have hbound : -β / 2 * Q + γ * (t + 1) / 3 * S ≤ -(β * h / 2) * Q := by linarith
  have hEW' : -β / 2 * Q ≤ EW := by
    rw [hEW]
    have : 0 ≤ γ / 3 * S := by positivity
    linarith
  have e1 : EV - t * EW = t * (t - 1) * (-β / 2 * Q + γ * (t + 1) / 3 * S) := by
    rw [hEV, hEW]
    ring
  have e2 := mul_le_mul_of_nonneg_left hbound htt
  have e3 : -(β * h / 2) * Q ≤ h * EW := by
    have := mul_le_mul_of_nonneg_left hEW' hhpos.le
    linarith
  have e4 := mul_le_mul_of_nonneg_left e3 htt
  rw [div_le_iff₀ (by linarith)]
  linarith

/-- **Proposition (strict decrease at the infimum).**  For `0 < a < b` with `a + b < 2m_B` and
`h = 1 − (a+b)/(2m_B)`, the energy per mass `e(s) = I(s)/s` satisfies
`e(a) − e(b) ≥ ((b − a)h/a²)(−I(a)) > 0`. -/
theorem gap (hβ : 0 < β) (hγ : 0 < γ) {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hsum : a + b < 2 * mB β γ k) :
    (b - a) * (1 - (a + b) / (2 * mB β γ k)) / a ^ 2 * (-Imin β γ k a) ≤
      Imin β γ k a / a - Imin β γ k b / b ∧
    0 < (b - a) * (1 - (a + b) / (2 * mB β γ k)) / a ^ 2 * (-Imin β γ k a) := by
  have hmB := mB_pos (k := k) hβ hγ
  have hσ := sigmaB_pos (k := k) hβ hγ
  have hmBeq : mB β γ k * (γ * sigmaB β γ k) = 3 * β := by
    unfold mB
    field_simp
  have hneg := (NegativeEnergy.negative_constrained_energy (k := k) hβ hγ ha).2
  obtain ⟨h, hh⟩ : ∃ h, h = 1 - (a + b) / (2 * mB β γ k) := ⟨_, rfl⟩
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
    have hSQ := S_le_of_stationary hγ hWst
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
theorem strict_binding (hβ : 0 < β) (hγ : 0 < γ) {m μ : ℝ} (hm : 0 < m) (hmB : m ≤ mB β γ k)
    (hμ : 0 < μ) (hμm : μ < m) :
    Imin β γ k m < Imin β γ k μ + Imin β γ k (m - μ) := by
  have h1 := gap (k := k) hβ hγ hμ hμm (by linarith)
  have h2 := gap (k := k) hβ hγ (show 0 < m - μ by linarith) (show m - μ < m by linarith)
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

/-- **Corollary (exact frozen-parameter check).**  For `k = 1`, `β = γ = b₀`, and `m₀` given
by the exactly represented binary64 values, `m₀ < m_B`; hence strict binding holds at `m₀`. -/
theorem frozen_parameters :
    let b₀ : ℝ := 4608178181141995 / 1125899906842624
    let m₀ : ℝ := 1432536998431173 / 562949953421312
    m₀ < mB b₀ b₀ 1 ∧
      ∀ μ : ℝ, 0 < μ → μ < m₀ → Imin b₀ b₀ 1 m₀ < Imin b₀ b₀ 1 μ + Imin b₀ b₀ 1 (m₀ - μ) := by
  intro b₀ m₀
  have hb : (0 : ℝ) < b₀ := by norm_num [b₀]
  have hm : (0 : ℝ) < m₀ := by norm_num [m₀]
  have hrho : rho b₀ b₀ 1 = 1 + 3 * b₀ / 32 := by
    unfold rho
    field_simp
  have hlt : m₀ < mB b₀ b₀ 1 := by
    unfold mB sigmaB
    rw [hrho, show 3 * b₀ / (b₀ * Real.sqrt (1 + 3 * b₀ / 32)) = 3 / Real.sqrt (1 + 3 * b₀ / 32) by
      field_simp]
    have hpos : 0 < 1 + 3 * b₀ / 32 := by positivity
    rw [lt_div_iff₀ (Real.sqrt_pos.2 hpos)]
    have hsq : (m₀ * Real.sqrt (1 + 3 * b₀ / 32)) ^ 2 < 3 ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hpos.le]
      norm_num [b₀, m₀]
    exact (pow_lt_pow_iff_left₀ (by positivity) (by norm_num) two_ne_zero).1 hsq
  exact ⟨hlt, fun μ hμ hμm => strict_binding hb hb hm hlt.le hμ hμm⟩

end StrictBinding

end ReyesMath
