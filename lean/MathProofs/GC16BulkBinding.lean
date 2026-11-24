import MathProofs.GC16ShellBinding
import MathProofs.WholeSpaceMinimizers

/-! Quantitative bulk gap and mass-addition comparison for the exact GC06/GC16
Hamiltonian. Candidate Lean implementation; pinned build and audit required.
Neither attainment nor an asymptotic trial theorem is assumed in these roots. -/

open Filter Topology MeasureTheory Set
namespace ReyesMath.GC16BulkBinding
open Sobolev Sobolev.H2 StrictBinding GC16Shell
variable {β γ k : ℝ}

/-- Explicit positive separation from the bulk energy at every bounded mass. -/
theorem field_bulk_gap (hβ : 0 < β) (hγ : 0 < γ)
    {a s : ℝ} (ha : 0 < a) (hs : 0 < s)
    (hsmall : β * s * a ≤ 2 * bulk β γ)
    (U : H2 2) (hM : M U = a) :
    (-bulk β γ + min (s ^ 2) (bulk β γ / 2)) * a ≤ energy β γ k U := by
  have hC := bulk_pos hβ hγ
  have hE := energy_ge β γ k hγ U
  change T k U - bulk β γ * M U ≤ energy β γ k U at hE
  rw [hM] at hE
  by_cases hT : s ^ 2 * a ≤ T k U
  · have hh := mul_le_mul_of_nonneg_right
      (min_le_left (s ^ 2) (bulk β γ / 2)) ha.le
    nlinarith only [hE, hT, hh]
  · have hη : 0 < s ^ 2 := by positivity
    have hb := ae_sup_bound_shell U k hη
    rw [Real.sqrt_sq hs.le, hM] at hb
    have hL : (T k U + s ^ 2 * a) / (4 * s) ≤ s * a / 2 := by
      apply (div_le_iff₀ (by positivity : 0 < 4 * s)).2
      nlinarith only [le_of_not_ge hT]
    have hQ := Q_le_of_ae_bound U (show ∀ᵐ x ∂(volume : Measure
        (EuclideanSpace ℝ (Fin 2))), ‖U.val x‖ ^ 2 ≤ s * a / 2 from
        hb.mono fun x hx => hx.trans hL)
    rw [hM] at hQ
    have hβQ := mul_le_mul_of_nonneg_left hQ (show 0 ≤ β / 2 by positivity)
    have hsmall' := mul_le_mul_of_nonneg_right hsmall ha.le
    have he := energy_eq β γ k U
    have hT0 := T_nonneg k U
    have hS0 := mul_nonneg (show 0 ≤ γ / 3 by positivity) (S_nonneg U)
    have hh := mul_le_mul_of_nonneg_right
      (min_le_right (s ^ 2) (bulk β γ / 2)) ha.le
    nlinarith only [hβQ, hsmall', he, hT0, hS0, hh]

theorem inf_bulk_gap (hβ : 0 < β) (hγ : 0 < γ)
    {a s : ℝ} (ha : 0 < a) (hs : 0 < s)
    (hsmall : β * s * a ≤ 2 * bulk β γ) :
    (-bulk β γ + min (s ^ 2) (bulk β γ / 2)) * a ≤ Imin β γ k a := by
  obtain ⟨U, hUm, _⟩ := NegativeEnergy.exists_negative (β := β) (γ := γ) (k := k) hβ ha
  have hne : (energy β γ k '' {U | M U = a}).Nonempty := ⟨_, U, hUm, rfl⟩
  apply le_csInf hne
  rintro _ ⟨V, hVm, rfl⟩
  exact field_bulk_gap hβ hγ ha hs hsmall V hVm

/-- Changing the attractive coupling gives a sharp limiting upper bound
on the quartic moment of near-bulk fields, without a Cauchy-Schwarz step. -/
theorem quartic_shift_bound (hγ : 0 < γ) (δ : ℝ) (U : H2 2) :
    δ / 2 * Q U ≤ energy β γ k U + bulk (β + δ) γ * M U := by
  have h := energy_ge_mass (β + δ) γ k hγ U
  change -bulk (β + δ) γ * M U ≤ energy (β + δ) γ k U at h
  rw [energy_eq (β + δ) γ k U] at h
  have he := energy_eq β γ k U
  nlinarith only [h, he]

/-- Exact finite mass addition comparison, valid for all t ≥ 1. -/
theorem scaled_field_upper (hβ : 0 < β) (hγ : 0 < γ)
    {δ t : ℝ} (hδ : 0 < δ) (ht : 1 ≤ t) (U : H2 2) :
    ∃ V : H2 2, M V = t * M U ∧
      energy β γ k V ≤
        (t ^ 3 + (t - 1) * t ^ 2 * (β / δ)) * energy β γ k U +
        (t - 1) * t ^ 2 * (β / δ) * bulk (β + δ) γ * M U := by
  have ht0 : 0 ≤ t := by linarith
  let L := (t - 1) * t ^ 2 * (β / δ)
  have hL : 0 ≤ L := by
    dsimp [L]
    exact mul_nonneg (mul_nonneg (sub_nonneg.mpr ht) (sq_nonneg t)) (div_nonneg hβ.le hδ.le)
  obtain ⟨V, hVm, hVE⟩ := exists_scaled (β := β) (γ := γ) (k := k) U (t := t) ht0
  refine ⟨V, hVm, ?_⟩
  have hQ := mul_le_mul_of_nonneg_left (quartic_shift_bound (β := β) (k := k) hγ δ U) hL
  have hLQ : L * (δ / 2 * Q U) = β / 2 * (t - 1) * t ^ 2 * Q U := by
    dsimp [L]
    field_simp [hδ.ne']
    <;> ring
  rw [hLQ] at hQ
  have htn : 0 ≤ t ^ 3 - t := by
    rw [show t ^ 3 - t = t * (t - 1) * (t + 1) by ring]
    exact mul_nonneg (mul_nonneg ht0 (sub_nonneg.mpr ht)) (by linarith)
  have hK := mul_nonneg htn (T_nonneg k U)
  have he : energy β γ k V =
      t ^ 3 * energy β γ k U - (t ^ 3 - t) * T k U +
        β / 2 * (t - 1) * t ^ 2 * Q U := by
    rw [hVE, energy_eq β γ k U]
    ring
  change energy β γ k V ≤ (t ^ 3 + L) * energy β γ k U +
    L * bulk (β + δ) γ * M U
  nlinarith only [hQ, hK, he]

/-- Pass the finite addition comparison to the actual infimum. -/
theorem inf_scaled_upper (hβ : 0 < β) (hγ : 0 < γ)
    {b δ t : ℝ} (hb : 0 < b) (hδ : 0 < δ) (ht : 1 ≤ t) :
    Imin β γ k (t * b) ≤
      (t ^ 3 + (t - 1) * t ^ 2 * (β / δ)) * Imin β γ k b +
      (t - 1) * t ^ 2 * (β / δ) * bulk (β + δ) γ * b := by
  let L := (t - 1) * t ^ 2 * (β / δ)
  let c := t ^ 3 + L
  have ht0 : 0 < t := by linarith
  have hL : 0 ≤ L := by
    dsimp [L]
    exact mul_nonneg (mul_nonneg (sub_nonneg.mpr ht) (sq_nonneg t)) (div_nonneg hβ.le hδ.le)
  have hc : 0 < c := add_pos_of_pos_of_nonneg (pow_pos ht0 3) hL
  change Imin β γ k (t * b) ≤ c * Imin β γ k b + L * bulk (β + δ) γ * b
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨U, hUm, hUe⟩ := exists_energy_lt (γ := γ) (k := k) hβ hb
    (ε := ε / (2 * c)) (by positivity)
  obtain ⟨V, hVm, hVE⟩ := scaled_field_upper (β := β) (γ := γ) (k := k) hβ hγ hδ ht U
  change energy β γ k V ≤ c * energy β γ k U +
    L * bulk (β + δ) γ * M U at hVE
  rw [hUm] at hVE
  have hI : Imin β γ k (t * b) ≤ energy β γ k V :=
    Imin_le_energy hγ (by rw [hVm, hUm])
  have hU := mul_le_mul_of_nonneg_left hUe.le hc.le
  have herr : c * (ε / (2 * c)) = ε / 2 := by field_simp [hc.ne']
  nlinarith only [hVE, hI, hU, herr, hε]

/-- Explicit, finite numerical certificate for binding of a specific split.
All quantities are the original Imin and couplings. This is a sufficient
criterion, not a classification of all splits. -/
theorem strict_split_of_certificate (hβ : 0 < β) (hγ : 0 < γ)
    {a b s δ t : ℝ} (ha : 0 < a) (hb : 0 < b) (hs : 0 < s)
    (hδ : 0 < δ) (ht : 1 ≤ t) (hmass : t * b = a + b)
    (hsmall : β * s * a ≤ 2 * bulk β γ)
    (hcert : (t ^ 3 + (t - 1) * t ^ 2 * (β / δ)) * Imin β γ k b +
      (t - 1) * t ^ 2 * (β / δ) * bulk (β + δ) γ * b <
      Imin β γ k b + (-bulk β γ + min (s ^ 2) (bulk β γ / 2)) * a) :
    Imin β γ k (a + b) < Imin β γ k a + Imin β γ k b := by
  have hI := inf_scaled_upper (β := β) (γ := γ) (k := k) hβ hγ hb hδ ht
  rw [hmass] at hI
  have hgap := inf_bulk_gap (β := β) (γ := γ) (k := k) hβ hγ ha hs hsmall
  linarith only [hI, hgap, hcert]

end ReyesMath.GC16BulkBinding

#print axioms ReyesMath.GC16BulkBinding.field_bulk_gap
#print axioms ReyesMath.GC16BulkBinding.inf_bulk_gap
#print axioms ReyesMath.GC16BulkBinding.quartic_shift_bound
#print axioms ReyesMath.GC16BulkBinding.scaled_field_upper
#print axioms ReyesMath.GC16BulkBinding.inf_scaled_upper
#print axioms ReyesMath.GC16BulkBinding.strict_split_of_certificate
