import Mathlib

/-!
# Quantitative UV growth of the exact nonreal dispersion branch

For q = |ξ|², the growing temporal exponent has
σ(q)² = (sqrt(2q²+q)-q-1/2)/2.
The following is a *uniform quantitative high-frequency bound*:
σ(q) ≥ sqrt(q)/4 for q ≥ 4.
This is not by itself the unbounded operator-norm claim between
Sobolev four-jet spaces; the Fourier multiplier estimate is still open.
-/

namespace ReyesMath

noncomputable def uvGrowthSquared (q : ℝ) : ℝ :=
  (Real.sqrt (2 * q ^ 2 + q) - q - 1 / 2) / 2

noncomputable def uvGrowth (q : ℝ) : ℝ :=
  Real.sqrt (uvGrowthSquared q)

/-- An exact positive lower bound, linear in q, for the square of the
unstable growth rate above the explicit high-frequency threshold q=4. -/
theorem uv_growth_squared_lower (q : ℝ) (hq : 4 ≤ q) :
    q / 16 ≤ uvGrowthSquared q := by
  have hrad : 0 ≤ 2 * q ^ 2 + q := by positivity
  have hsquare :
      (Real.sqrt (2 * q ^ 2 + q)) ^ 2 = 2 * q ^ 2 + q :=
    Real.sq_sqrt hrad
  have hsqrt : 0 ≤ Real.sqrt (2 * q ^ 2 + q) :=
    Real.sqrt_nonneg _
  have haux : 0 ≤ (5 / 4 : ℝ) * q := by positivity
  have hdiff : (5 / 4 * q) ^ 2 ≤ 2 * q ^ 2 + q := by
    nlinarith [sq_nonneg q]
  have hbound : 5 / 4 * q ≤ Real.sqrt (2 * q ^ 2 + q) := by
    nlinarith [hsquare]
  unfold uvGrowthSquared
  nlinarith

/-- Therefore the physical temporal exponential growth rate is at least
one quarter of the wavenumber amplitude for |ξ|² ≥ 4. -/
theorem uv_growth_linear_in_wavenumber (k : ℝ) (hk : 4 ≤ k ^ 2) :
    |k| / 4 ≤ uvGrowth (k ^ 2) := by
  have hlow := uv_growth_squared_lower (k ^ 2) hk
  have hqnonneg : 0 ≤ k ^ 2 := sq_nonneg _
  have hR : 0 ≤ uvGrowth (k ^ 2) :=
    Real.sqrt_nonneg _
  have hkmag : 0 ≤ |k| := abs_nonneg _
  have hkmagsq : |k| ^ 2 = k ^ 2 := sq_abs k
  have hsq : (uvGrowth (k ^ 2)) ^ 2 = uvGrowthSquared (k ^ 2) := by
    unfold uvGrowth
    exact Real.sq_sqrt (le_trans (by positivity : (0 : ℝ) ≤ k ^ 2 / 16) hlow)
  nlinarith

end ReyesMath
