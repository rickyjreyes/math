import MathProofs.StrictBinding

/-!
# GC01: zero-shell angular-sector variational estimates

These are exact H² scalar estimates used by the analytical vortex construction.
The angular-equivariant subspace, polar integration identities, full stationary
equation and constrained Hessian identification are not yet encoded here.
-/
namespace ReyesMath
namespace GC01VortexEstimates

open Sobolev Sobolev.H2
variable {β γ : ℝ}

/-- In the zero-shell case the virial identity and the stationary equation
tested against the profile force strictly positive frequency. -/
theorem frequency_pos (hγ : 0 < γ) {U : H2 2} {ω : ℝ}
    (hM : 0 < M U) (hvir : IsStationary β γ 0 U)
    (htest : D U + ω * M U = β * Q U - γ * S U) :
    0 < ω := by
  unfold IsStationary at hvir
  norm_num at hvir
  have hs : 0 < γ * S U := mul_pos hγ (S_pos U hM)
  have hd := D_nonneg U
  have hp : 0 < ω * M U := by linarith
  exact pos_of_mul_pos_left hp hM.le

/-- Explicit nonlinear gap for a positive-mass zero-shell virial profile.
The smallness premise is an algebraic sufficient mass bound, not a
spectral assumption. -/
theorem nonlinear_gap (hγ : 0 < γ) {U : H2 2}
    (hM : 0 < M U) (hvir : IsStationary β γ 0 U)
    (hsmall : γ * Real.sqrt (3 * β ^ 2 / (32 * γ)) * M U < 2 * β) :
    -β * Q U + 2 * γ * S U < 0 := by
  have hs := S_le_of_stationary hγ hvir
  norm_num at hs
  have hq := Q_pos U hM
  have h1 := mul_le_mul_of_nonneg_left hs (show 0 ≤ 2 * γ by positivity)
  have h2 := mul_lt_mul_of_pos_right hsmall hq
  nlinarith only [h1, h2]

/-- Any lower kinetic-energy competitor with the same mass and nonlinear
integrals excludes global minimization in the zero-shell Hamiltonian. -/
theorem not_minimizer_of_kinetic_competitor (hγ : 0 < γ)
    {U V : H2 2} (hM : M V = M U) (hQ : Q V = Q U)
    (hS : S V = S U) (hD : D V < D U) :
    Imin β γ 0 (M U) < energy β γ 0 U := by
  have h := StrictBinding.Imin_le_energy (β := β) (γ := γ) (k := 0) hγ hM
  have hE : energy β γ 0 V < energy β γ 0 U := by
    rw [energy_eq, energy_eq, T_eq, T_eq, hQ, hS]
    norm_num
    linarith
  exact h.trans_lt hE

/-- Algebraic core of the polar kinetic comparison. A and B denote the
nonnegative weighted radial derivative and amplitude integrals. -/
theorem angular_kinetic_gap_pos {l j A B : ℝ}
    (hl : 4 ≤ l ^ 2) (hj : j ^ 2 < l ^ 2)
    (hA : 0 < A) (hB : 0 ≤ B) :
    0 < (l ^ 2 - j ^ 2) * (2 * A + (l ^ 2 + j ^ 2 - 4) * B) := by
  apply mul_pos (sub_pos.mpr hj)
  have hcoef : 0 ≤ l ^ 2 + j ^ 2 - 4 := by nlinarith [sq_nonneg j]
  have hp := mul_nonneg hcoef hB
  linarith

/-- For every lower angular sector, a nonpositive kinetic difference plus
the explicit nonlinear gap gives a strictly negative scalar coefficient.
The equality identifying this coefficient with the actual Hessian is
proved analytically in the ledger, not formalized by this lemma. -/
theorem angular_coefficient_negative (hγ : 0 < γ) {U : H2 2}
    (hM : 0 < M U) (hvir : IsStationary β γ 0 U)
    (hsmall : γ * Real.sqrt (3 * β ^ 2 / (32 * γ)) * M U < 2 * β)
    {d : ℝ} (hd : d ≤ D U) :
    d - D U - β * Q U + 2 * γ * S U < 0 := by
  have h := nonlinear_gap hγ hM hvir hsmall
  linarith

end GC01VortexEstimates
end ReyesMath
