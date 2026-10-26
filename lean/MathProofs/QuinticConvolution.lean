import Mathlib

/-!
# Universal extremal quintic-convolution uniqueness

For any real separating linear-functional values, a five-frequency
combination attaining the maximal quintic escape value can arise ONLY
from three maximal p and two minimal q modes. Consequently the
extremal frequency receives exactly one quintic convolution summand.
This does not yet prove local PDE well-posedness or Fourier-coefficient
differentiability for the full torus evolution.
-/

namespace ReyesMath

/-- The extremal five-mode quintic convolution term is unique at its
maximum value of any separating real functional. -/
theorem quintic_extremal_convolution_unique
    (Lp Lq L1 L2 L3 M1 M2 : ℝ)
    (hpq : Lq < Lp)
    (h1 : L1 ≤ Lp) (h2 : L2 ≤ Lp) (h3 : L3 ≤ Lp)
    (hm1 : Lq ≤ M1) (hm2 : Lq ≤ M2)
    (hfrequency :
      L1 + L2 + L3 - M1 - M2 = 3 * Lp - 2 * Lq) :
    L1 = Lp ∧ L2 = Lp ∧ L3 = Lp ∧
      M1 = Lq ∧ M2 = Lq := by
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  · linarith

/-- No cubic combination of modes bounded by the same extremes can
reach the quintic escaped frequency when the extremes are distinct. -/
theorem cubic_cannot_reach_quintic_extreme
    (Lp Lq L1 L2 M : ℝ)
    (hpq : Lq < Lp)
    (h1 : L1 ≤ Lp) (h2 : L2 ≤ Lp) (hm : Lq ≤ M) :
    L1 + L2 - M < 3 * Lp - 2 * Lq := by
  linarith

/-- The nonzero escaped coefficient of the extremal quintic convolution
has the product form a³ (conj b)². -/
theorem quintic_extremal_coefficient_nonzero
    (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) :
    a ^ 3 * (star b) ^ 2 ≠ 0 := by
  exact mul_ne_zero (pow_ne_zero _ ha)
    (pow_ne_zero _ (star_ne_zero.mpr hb))

end ReyesMath
