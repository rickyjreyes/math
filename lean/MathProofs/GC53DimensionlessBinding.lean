import Mathlib
import MathProofs.StrictBinding

/-!
# GC53: exact dimensionless form of the existing strict-binding threshold

The GC06/GC16 fourth-order cubic-quintic Hamiltonian has the certified
sufficient strict-binding mass mB. For beta,gamma > 0, define the
dimensionless wavenumber parameter lambda = gamma*k^4/beta^2 and rescaled
mass mu = gamma*k^2*m/beta.

The existing threshold obeys the *exact* algebraic relation
  muB^2 * (lambda + 3/32) = 9*lambda.
This is a parameter-reduction identity for a proven sufficient threshold.
It is NOT an assertion that the threshold is sharp, universal, or necessary
for attainment, and does not resolve the full GC53 classification.
-/

namespace ReyesMath
namespace GC53

/-- The dimensionless fourth-order wavenumber parameter. -/
noncomputable def normalizedWaveParameter (beta gamma k : ℝ) : ℝ :=
  gamma * k ^ 4 / beta ^ 2

/-- Rescaled mass for k > 0. -/
noncomputable def normalizedMass (beta gamma k m : ℝ) : ℝ :=
  gamma * k ^ 2 * m / beta

/-- The parameter-dependent denominator square in mB. -/
theorem sigmaB_sq (beta gamma k : ℝ) (hbeta : 0 < beta) (hgamma : 0 < gamma) :
    (StrictBinding.sigmaB beta gamma k) ^ 2 =
      StrictBinding.rho beta gamma k := by
  have hrho : 0 ≤ StrictBinding.rho beta gamma k := by
    unfold StrictBinding.rho
    positivity
  unfold StrictBinding.sigmaB
  exact Real.sq_sqrt hrho

/-- Exact dimensionless expression for the proven sufficient mass bound.
    This identity does not establish the threshold's optimality. -/
theorem normalized_binding_threshold_identity
    (beta gamma k : ℝ) (hbeta : 0 < beta) (hgamma : 0 < gamma) :
    (normalizedMass beta gamma k (StrictBinding.mB beta gamma k)) ^ 2 *
        (normalizedWaveParameter beta gamma k + 3 / 32) =
      9 * normalizedWaveParameter beta gamma k := by
  have hsigma :
      (StrictBinding.sigmaB beta gamma k) ^ 2 =
        StrictBinding.rho beta gamma k :=
    sigmaB_sq beta gamma k hbeta hgamma
  have hsigma_pos : 0 < StrictBinding.sigmaB beta gamma k :=
    StrictBinding.sigmaB_pos (k := k) hbeta hgamma
  have hscalar :
      gamma * k ^ 4 / beta ^ 2 + 3 / 32 =
        (gamma / beta ^ 2) * (StrictBinding.sigmaB beta gamma k) ^ 2 := by
    rw [hsigma]
    unfold StrictBinding.rho
    field_simp [ne_of_gt hbeta, ne_of_gt hgamma]
    ring
  unfold normalizedMass normalizedWaveParameter
  rw [hscalar]
  unfold StrictBinding.mB
  field_simp [ne_of_gt hbeta, ne_of_gt hgamma, ne_of_gt hsigma_pos]
  ring

end GC53
end ReyesMath
