import Mathlib
import MathProofs.OrbitalStability

/-!
# GC06: radical-free parameter region for the verified F01 binding theorem

The maintained F01 theorem proves strict binding, attainment and orbital
stability for beta > 0, gamma > 0 and 0 < m <=
  3 beta / (gamma sqrt(k^4 + 3 beta^2/(32 gamma))).

Here that region is characterized exactly by a polynomial inequality in
(m,beta,gamma,k), with no approximate sqrt or floating-point threshold.
This makes it possible to certify entire parameter intervals by rational
inequalities and to reuse the existing whole-space theorems.

IMPORTANT: this is an exact reparameterization of the EXISTING sufficient
region, not a classification of every mass above the threshold, and not a
ghost-free derivation from the literal covariant S004 action.
-/

namespace ReyesMath.ParameterRegion

open Sobolev Sobolev.H2

/-- The exact squared-mass test for the existing explicit sufficient
strict-binding interval; gamma > 0 is required when using this formula. -/
def squaredBindingRegion (beta gamma k m : ℝ) : Prop :=
  (m * gamma) ^ 2 * StrictBinding.rho beta gamma k ≤ (3 * beta) ^ 2

/-- Removing the square root is logically equivalent to the original
binding threshold when mass is nonnegative and beta, gamma are positive.
The positivity conditions are essential before squaring an inequality. -/
theorem m_le_mB_iff_squaredBindingRegion
    (beta gamma k m : ℝ) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hm : 0 ≤ m) :
    m ≤ StrictBinding.mB beta gamma k ↔
      squaredBindingRegion beta gamma k m := by
  have hrho : 0 ≤ StrictBinding.rho beta gamma k := by
    unfold StrictBinding.rho
    positivity
  have hsigma :
      (StrictBinding.sigmaB beta gamma k) ^ 2 =
        StrictBinding.rho beta gamma k := by
    unfold StrictBinding.sigmaB
    exact Real.sq_sqrt hrho
  have hsigmaPos : 0 < StrictBinding.sigmaB beta gamma k :=
    StrictBinding.sigmaB_pos (k := k) hbeta hgamma
  have hden : 0 < gamma * StrictBinding.sigmaB beta gamma k :=
    mul_pos hgamma hsigmaPos
  have hlinear :
      (m ≤ StrictBinding.mB beta gamma k) ↔
        m * (gamma * StrictBinding.sigmaB beta gamma k) ≤
          3 * beta := by
    change m ≤ 3 * beta / (gamma * StrictBinding.sigmaB beta gamma k) ↔
      m * (gamma * StrictBinding.sigmaB beta gamma k) ≤ 3 * beta
    exact le_div_iff₀ hden
  have hnon : 0 ≤ m * gamma * StrictBinding.sigmaB beta gamma k := by
    positivity
  constructor
  · intro hbound
    have hlin : m * gamma * StrictBinding.sigmaB beta gamma k ≤ 3 * beta := by
      simpa only [mul_assoc] using hlinear.mp hbound
    have hfactor : 0 ≤
        (3 * beta - m * gamma * StrictBinding.sigmaB beta gamma k) *
          (3 * beta + m * gamma * StrictBinding.sigmaB beta gamma k) :=
      mul_nonneg (by linarith) (by positivity)
    have hsq :
        (m * gamma * StrictBinding.sigmaB beta gamma k) ^ 2 ≤
          (3 * beta) ^ 2 := by nlinarith
    unfold squaredBindingRegion
    calc
      (m * gamma) ^ 2 * StrictBinding.rho beta gamma k =
          (m * gamma * StrictBinding.sigmaB beta gamma k) ^ 2 := by
            rw [← hsigma]
            ring
      _ ≤ (3 * beta) ^ 2 := hsq
  · intro hregion
    have hsq :
        (m * gamma * StrictBinding.sigmaB beta gamma k) ^ 2 ≤
          (3 * beta) ^ 2 := by
      calc
        (m * gamma * StrictBinding.sigmaB beta gamma k) ^ 2 =
            (m * gamma) ^ 2 * StrictBinding.rho beta gamma k := by
              rw [← hsigma]
              ring
        _ ≤ (3 * beta) ^ 2 := hregion
    have hlin : m * gamma * StrictBinding.sigmaB beta gamma k ≤ 3 * beta := by
      by_contra hn
      have hneg : 3 * beta -
          m * gamma * StrictBinding.sigmaB beta gamma k < 0 := by
        linarith
      have hpos : 0 <
          3 * beta + m * gamma * StrictBinding.sigmaB beta gamma k := by
        positivity
      have hproduct := mul_neg_of_neg_of_pos hneg hpos
      nlinarith
    apply hlinear.mpr
    simpa only [mul_assoc] using hlin

/-- Strict subadditivity for EVERY positive mass in the exact squared
parameter region, with the full whole-space infimum (not a surrogate). -/
theorem strict_binding_of_squared_region
    (beta gamma k m : ℝ) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hm : 0 < m) (hregion : squaredBindingRegion beta gamma k m)
    (a : ℝ) (ha : 0 < a) (ham : a < m) :
    Sobolev.H2.Imin beta gamma k m <
      Sobolev.H2.Imin beta gamma k a +
        Sobolev.H2.Imin beta gamma k (m - a) := by
  have hmB :=
    (m_le_mB_iff_squaredBindingRegion beta gamma k m
      hbeta hgamma hm.le).mpr hregion
  exact StrictBinding.strict_binding (k := k) hbeta hgamma hm hmB ha ham

/-- Whole-space H2 minimizers exist throughout the polynomially specified
sufficient region. No inference about the complementary region is made. -/
theorem exists_minimizer_of_squared_region
    (beta gamma k m : ℝ) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hm : 0 < m) (hregion : squaredBindingRegion beta gamma k m) :
    ∃ U : H2 2,
      M U = m ∧ energy beta gamma k U = Imin beta gamma k m := by
  have hmB :=
    (m_le_mB_iff_squaredBindingRegion beta gamma k m
      hbeta hgamma hm.le).mpr hregion
  exact WholeSpace.exists_minimizer (k := k) hbeta hgamma hm hmB

/-- Every positive (beta,gamma) and every real k has a nonempty
fixed-mass region admitting a whole-space constrained minimizer.
This is a theorem for the independent cubic-quintic F01 Hamiltonian. -/
theorem exists_some_positive_confined_mass
    (beta gamma k : ℝ) (hbeta : 0 < beta) (hgamma : 0 < gamma) :
    ∃ m : ℝ, 0 < m ∧
      ∃ U : H2 2, M U = m ∧ energy beta gamma k U = Imin beta gamma k m := by
  have hmb : 0 < StrictBinding.mB beta gamma k :=
    StrictBinding.mB_pos (k := k) hbeta hgamma
  refine ⟨StrictBinding.mB beta gamma k / 2, by linarith, ?_⟩
  exact WholeSpace.exists_minimizer (k := k) hbeta hgamma
    (by linarith) (by linarith)

end ReyesMath.ParameterRegion
