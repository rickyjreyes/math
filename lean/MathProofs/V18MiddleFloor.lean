import MathProofs.V18FullForward

/-!
# F09: rigorous inactive floor for all five frozen middle observables

The historical middle-sector outputs are clipped below at 10⁻¹².
The five source outputs n=12,19,53,73,91 are strictly above the floor,
independently of the fitted suppression parameters. Thus the exact
middleRaw analytic partial derivatives already proved in the Lean
repository coincide with derivatives of the clipped observed map in a
neighborhood of the frozen parameters.

This module uses only rational bounds on pi and the exact universal
|sin t| ≤ |t| inequality, not a numerical sine evaluation.
-/

noncomputable section
namespace ReyesMath.V18MiddleFloor

open ReyesMath

/-- Integer multiples of pi control the magnitude of the sine. -/
theorem abs_sin_le_distance_to_nat_pi (x : ℝ) (k : ℕ) :
    |Real.sin x| ≤ |x - k * Real.pi| := by
  have h := Real.sin_add_nat_mul_pi (x - k * Real.pi) k
  have hx : x - k * Real.pi + k * Real.pi = x := by ring
  rw [hx] at h
  rw [h, abs_mul] 
  simpa using (Real.abs_sin_le_abs (x := x - k * Real.pi))

/-- Exact rational reduction of source frequencies modulo pi. -/
theorem frozen_middle_sine_lower_12 :
    (-43 / 100 : ℝ) ≤ Real.sin ((5.0632 : ℝ) * 12 + 1.6469) := by
  let x : ℝ := (5.0632 : ℝ) * 12 + 1.6469
  have hr : |x - 20 * Real.pi| ≤ (43 / 100 : ℝ) := by
    apply abs_le.mpr
    constructor <;> dsimp [x] <;>
      nlinarith [Real.pi_gt_d6, Real.pi_lt_d6]
  have h := abs_sin_le_distance_to_nat_pi x 20
  have hn := (abs_le.mp h).1
  have hc := neg_le_neg hr
  convert le_trans hc hn using 1 <;> norm_num [x]

theorem frozen_middle_sine_lower_19 :
    (-46 / 100 : ℝ) ≤ Real.sin ((5.0632 : ℝ) * 19 + 1.6469) := by
  let x : ℝ := (5.0632 : ℝ) * 19 + 1.6469
  have hr : |x - 31 * Real.pi| ≤ (46 / 100 : ℝ) := by
    apply abs_le.mpr
    constructor <;> dsimp [x] <;>
      nlinarith [Real.pi_gt_d6, Real.pi_lt_d6]
  have h := abs_sin_le_distance_to_nat_pi x 31
  convert ((neg_le_neg hr).trans (abs_le.mp h).1) using 1 <;> norm_num [x]

theorem frozen_middle_sine_lower_53 :
    (-19 / 100 : ℝ) ≤ Real.sin ((5.0632 : ℝ) * 53 + 1.6469) := by
  let x : ℝ := (5.0632 : ℝ) * 53 + 1.6469
  have hr : |x - 86 * Real.pi| ≤ (19 / 100 : ℝ) := by
    apply abs_le.mpr
    constructor <;> dsimp [x] <;>
      nlinarith [Real.pi_gt_d6, Real.pi_lt_d6]
  have h := abs_sin_le_distance_to_nat_pi x 86
  exact (neg_le_neg hr).trans (abs_le.mp h).1

/-- Source middle values exceed the actual piecewise clipping floor. -/
theorem middle_12_strict (alpha epsilon : ℝ) :
    (1e-12 : ℝ) < V18Forward.middleRaw (V18Forward.frozen alpha epsilon) 12 := by
  have h1 := frozen_middle_sine_lower_12
  have h2 := Real.neg_one_le_sin ((9.4062 : ℝ) * 12)
  change (1e-12 : ℝ) <
    (998.7 : ℝ) + 0.2427 * (12 : ℝ)^2 +
      0.2092 * Real.sin ((9.4062 : ℝ) * 12) +
      2241.1 * Real.sin ((5.0632 : ℝ) * 12 + 1.6469)
  nlinarith

theorem middle_19_strict (alpha epsilon : ℝ) :
    (1e-12 : ℝ) < V18Forward.middleRaw (V18Forward.frozen alpha epsilon) 19 := by
  have h1 := frozen_middle_sine_lower_19
  have h2 := Real.neg_one_le_sin ((9.4062 : ℝ) * 19)
  change (1e-12 : ℝ) <
    (998.7 : ℝ) + 0.2427 * (19 : ℝ)^2 +
      0.2092 * Real.sin ((9.4062 : ℝ) * 19) +
      2241.1 * Real.sin ((5.0632 : ℝ) * 19 + 1.6469)
  nlinarith

theorem middle_53_strict (alpha epsilon : ℝ) :
    (1e-12 : ℝ) < V18Forward.middleRaw (V18Forward.frozen alpha epsilon) 53 := by
  have h1 := frozen_middle_sine_lower_53
  have h2 := Real.neg_one_le_sin ((9.4062 : ℝ) * 53)
  change (1e-12 : ℝ) <
    (998.7 : ℝ) + 0.2427 * (53 : ℝ)^2 +
      0.2092 * Real.sin ((9.4062 : ℝ) * 53) +
      2241.1 * Real.sin ((5.0632 : ℝ) * 53 + 1.6469)
  nlinarith

theorem middle_73_strict (alpha epsilon : ℝ) :
    (1e-12 : ℝ) < V18Forward.middleRaw (V18Forward.frozen alpha epsilon) 73 := by
  have h1 := Real.neg_one_le_sin ((5.0632 : ℝ) * 73 + 1.6469)
  have h2 := Real.neg_one_le_sin ((9.4062 : ℝ) * 73)
  change (1e-12 : ℝ) <
    (998.7 : ℝ) + 0.2427 * (73 : ℝ)^2 +
      0.2092 * Real.sin ((9.4062 : ℝ) * 73) +
      2241.1 * Real.sin ((5.0632 : ℝ) * 73 + 1.6469)
  nlinarith

theorem middle_91_strict (alpha epsilon : ℝ) :
    (1e-12 : ℝ) < V18Forward.middleRaw (V18Forward.frozen alpha epsilon) 91 := by
  have h1 := Real.neg_one_le_sin ((5.0632 : ℝ) * 91 + 1.6469)
  have h2 := Real.neg_one_le_sin ((9.4062 : ℝ) * 91)
  change (1e-12 : ℝ) <
    (998.7 : ℝ) + 0.2427 * (91 : ℝ)^2 +
      0.2092 * Real.sin ((9.4062 : ℝ) * 91) +
      2241.1 * Real.sin ((5.0632 : ℝ) * 91 + 1.6469)
  nlinarith

/-- All five middle observations are locally on the differentiable branch
of the frozen model rather than on the nonlinear max floor. -/
theorem every_middle_observable_unclipped (alpha epsilon : ℝ)
    (i : Fin 5) :
    (1e-12 : ℝ) <
      V18Forward.middleRaw (V18Forward.frozen alpha epsilon)
        ((![12, 19, 53, 73, 91] : Fin 5 → ℕ) i) := by
  fin_cases i
  · exact middle_12_strict alpha epsilon
  · exact middle_19_strict alpha epsilon
  · exact middle_53_strict alpha epsilon
  · exact middle_73_strict alpha epsilon
  · exact middle_91_strict alpha epsilon

end ReyesMath.V18MiddleFloor
