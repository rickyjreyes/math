import MathProofs.V18Regularity

/-!
# The complete Fréchet derivative on the verified frozen branch

Every active parameter occurs in the derivative formulas below. In particular,
the two middle frequencies, the two suppression parameters, the heavy powers,
and the W/Z phase and frequency have not been frozen in differentiation.
-/

noncomputable section
namespace ReyesMath.V18Forward
open Filter
open scoped Topology
set_option maxHeartbeats 1000000

def coord (j : Fin 31) : Params →L[ℝ] ℝ := ContinuousLinearMap.proj j

theorem hasFDerivAt_coord (p : Params) (j : Fin 31) :
    HasFDerivAt (fun q : Params => q j) (coord j) p :=
  (coord j).hasFDerivAt

def lightBaseSmooth (p : Params) (n : ℕ) : ℝ :=
  let x : ℝ := n
  let ratio := if n = 0 then 0 else x / (x + 1)
  let chirality := if n = 0 then (1 : ℝ) else x^2
  p 0 * ratio + p 1 * topo n + p 2 * Real.log (1 + x) +
    p 3 * x^2 + p 4 * x^3 + p 5 * Real.exp (p 6 * x) + p 7 / chirality

def lightSuppression (p : Params) (n : ℕ) : ℝ :=
  (1 + Real.exp (p 29 * ((n : ℝ) - p 30)))⁻¹

def lightBaseD (p : Params) (n : ℕ) : Params →L[ℝ] ℝ :=
  let x : ℝ := n
  let ratio := if n = 0 then 0 else x / (x + 1)
  let chirality := if n = 0 then (1 : ℝ) else x^2
  ratio • coord 0 + topo n • coord 1 + Real.log (1 + x) • coord 2 +
    x^2 • coord 3 + x^3 • coord 4 +
    (p 5 • (Real.exp (p 6 * x) • (x • coord 6)) + Real.exp (p 6 * x) • coord 5) +
    chirality⁻¹ • coord 7

def lightSuppressionD (p : Params) (n : ℕ) : Params →L[ℝ] ℝ :=
  let a := p 29 * ((n : ℝ) - p 30)
  (-(1 + Real.exp a)^2)⁻¹ •
    (Real.exp a • (p 29 • (-coord 30) + ((n : ℝ) - p 30) • coord 29))

def lightD (p : Params) (n : ℕ) : Params →L[ℝ] ℝ :=
  let d := lightBaseSmooth p n • lightSuppressionD p n + lightSuppression p n • lightBaseD p n
  if n = 3 then
    (lightBaseSmooth p n * lightSuppression p n) • coord 8 + p 8 • d
  else d

def middleD (p : Params) (n : ℕ) : Params →L[ℝ] ℝ :=
  coord 14 + (n : ℝ)^2 • coord 15 +
    (p 13 • (Real.cos (p 11 * n) • ((n : ℝ) • coord 11)) +
      Real.sin (p 11 * n) • coord 13) +
    (p 9 • (Real.cos (p 10 * n + p 12) • ((n : ℝ) • coord 10 + coord 12)) +
      Real.sin (p 10 * n + p 12) • coord 9)

def wzD (p : Params) (n : ℕ) : Params →L[ℝ] ℝ :=
  if n = 95 ∨ n = 96 then
    p 24 • (Real.cos (p 25 * n + p 26) • ((n : ℝ) • coord 25 + coord 26)) +
      Real.sin (p 25 * n + p 26) • coord 24
  else 0

def higgsD (n : ℕ) : Params →L[ℝ] ℝ :=
  if n = 123 then ((n : ℝ) / (n + 1)) • coord 27 + coord 28 else 0

def heavyD (p : Params) (n : ℕ) : Params →L[ℝ] ℝ :=
  let r := (n : ℝ) / 100
  (p 17 • ((r ^ p 19 * Real.log r) • coord 19) + r ^ p 19 • coord 17) +
    (p 20 • ((r ^ p 21 * Real.log r) • coord 21) + r ^ p 21 • coord 20) +
    (p 22 • ((r ^ p 23 * Real.log r) • coord 23) + r ^ p 23 • coord 22) +
    wzD p n + higgsD n

def observedD (p : Params) : Params →L[ℝ] (Fin 11 → ℝ) :=
  ContinuousLinearMap.pi
    ![lightD p 1, lightD p 2, lightD p 3,
      middleD p 12, middleD p 19, middleD p 53, middleD p 73, middleD p 91,
      heavyD p 95, heavyD p 96, heavyD p 123]

theorem hasFDerivAt_lightBaseSmooth (p : Params) (n : ℕ) :
    HasFDerivAt (fun q => lightBaseSmooth q n) (lightBaseD p n) p := by
  have h (j : Fin 31) := hasFDerivAt_coord p j
  have he := ((h 6).mul_const (n : ℝ)).exp
  have hb := ((((((h 0).mul_const (if n = 0 then 0 else (n : ℝ) / (n + 1))).add
    ((h 1).mul_const (topo n))).add ((h 2).mul_const (Real.log (1 + (n : ℝ))))).add
    ((h 3).mul_const ((n : ℝ)^2))).add ((h 4).mul_const ((n : ℝ)^3))).add ((h 5).mul he)
  convert hb.add ((h 7).mul_const ((if n = 0 then (1 : ℝ) else (n : ℝ)^2)⁻¹)) using 1 <;>
    simp only [lightBaseSmooth, lightBaseD, div_eq_mul_inv]

theorem hasFDerivAt_lightSuppression (p : Params) (n : ℕ) :
    HasFDerivAt (fun q => lightSuppression q n) (lightSuppressionD p n) p := by
  have h29 := hasFDerivAt_coord p 29
  have h30 := hasFDerivAt_coord p 30
  have ha := h29.mul ((hasFDerivAt_const (n : ℝ) p).sub h30)
  have hd := ha.exp.const_add 1
  have hn : 1 + Real.exp (p 29 * ((n : ℝ) - p 30)) ≠ 0 := by positivity
  convert (hasDerivAt_inv hn).comp_hasFDerivAt p hd using 1 <;>
    simp only [lightSuppression, lightSuppressionD, zero_sub, inv_neg, Pi.mul_apply, Pi.sub_apply]

theorem hasFDerivAt_lightSmooth (p : Params) (n : ℕ) :
    HasFDerivAt (fun q => lightSmooth q n) (lightD p n) p := by
  have h := (hasFDerivAt_lightBaseSmooth p n).mul (hasFDerivAt_lightSuppression p n)
  by_cases hn : n = 3
  · convert h.mul (hasFDerivAt_coord p 8) using 1 <;>
      simp only [lightD, if_pos hn, lightSmooth, lightBaseSmooth, lightSuppression, Pi.mul_def]
  · convert h using 1 <;>
      simp only [lightD, if_neg hn, lightSmooth, lightBaseSmooth, lightSuppression, Pi.mul_def]

theorem hasFDerivAt_middleRaw (p : Params) (n : ℕ) :
    HasFDerivAt (fun q => middleRaw q n) (middleD p n) p := by
  have h (j : Fin 31) := hasFDerivAt_coord p j
  convert (((h 14).add ((h 15).mul_const ((n : ℝ)^2))).add
    ((h 13).mul (((h 11).mul_const (n : ℝ)).sin))).add
    ((h 9).mul ((((h 10).mul_const (n : ℝ)).add (h 12)).sin)) using 1 <;>
    simp only [middleRaw, middleD]

theorem hasFDerivAt_wz (p : Params) (n : ℕ) :
    HasFDerivAt
      (fun q : Params => if n = 95 ∨ n = 96 then q 24 * Real.sin (q 25 * n + q 26) else 0)
      (wzD p n) p := by
  by_cases hn : n = 95 ∨ n = 96
  · simp only [if_pos hn, wzD]
    exact (hasFDerivAt_coord p 24).mul
      ((((hasFDerivAt_coord p 25).mul_const (n : ℝ)).add (hasFDerivAt_coord p 26)).sin)
  · simp only [if_neg hn, wzD]
    exact hasFDerivAt_const _ _

theorem hasFDerivAt_higgs (p : Params) (n : ℕ) :
    HasFDerivAt
      (fun q : Params => if n = 123 then q 27 * ((n : ℝ) / (n + 1)) + q 28 else 0)
      (higgsD n) p := by
  by_cases hn : n = 123
  · simp only [if_pos hn, higgsD]
    exact ((hasFDerivAt_coord p 27).mul_const ((n : ℝ) / (n + 1))).add (hasFDerivAt_coord p 28)
  · simp only [if_neg hn, higgsD]
    exact hasFDerivAt_const _ _

theorem hasFDerivAt_heavySmooth (p : Params) (n : ℕ) (hn : 0 < n) :
    HasFDerivAt (fun q => heavySmooth q n) (heavyD p n) p := by
  have hr : (0 : ℝ) < (n : ℝ) / 100 := by positivity
  have h (j : Fin 31) := hasFDerivAt_coord p j
  have hb := (((h 17).mul ((h 19).const_rpow hr)).add
    ((h 20).mul ((h 21).const_rpow hr))).add ((h 22).mul ((h 23).const_rpow hr))
  convert ((hb.add (hasFDerivAt_wz p n)).add (hasFDerivAt_higgs p n)).const_add (1e-12 : ℝ)
    using 1 <;> simp only [heavySmooth, bosonSmooth, heavyD]

theorem hasFDerivAt_observedSmooth (p : Params) :
    HasFDerivAt observedSmooth (observedD p) p := by
  apply hasFDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact hasFDerivAt_lightSmooth p 1
  · exact hasFDerivAt_lightSmooth p 2
  · exact hasFDerivAt_lightSmooth p 3
  · exact hasFDerivAt_middleRaw p 12
  · exact hasFDerivAt_middleRaw p 19
  · exact hasFDerivAt_middleRaw p 53
  · exact hasFDerivAt_middleRaw p 73
  · exact hasFDerivAt_middleRaw p 91
  · exact hasFDerivAt_heavySmooth p 95 (by norm_num)
  · exact hasFDerivAt_heavySmooth p 96 (by norm_num)
  · exact hasFDerivAt_heavySmooth p 123 (by norm_num)

/-- Full Fréchet derivative of the actual clipped map, with all 31 input
coordinates retained. -/
theorem hasFDerivAt_observed_frozen (alpha : ℝ) (ha : 0 ≤ alpha) :
    HasFDerivAt observed (observedD (frozen alpha 5)) (frozen alpha 5) :=
  (hasFDerivAt_observedSmooth _).congr_of_eventuallyEq
    (observed_eq_smooth_near_frozen alpha ha)

theorem jacobian_frozen_eq (alpha : ℝ) (ha : 0 ≤ alpha) :
    jacobian (frozen alpha 5) = observedD (frozen alpha 5) :=
  (hasFDerivAt_observed_frozen alpha ha).fderiv

/-- The same explicit derivative formula holds throughout a neighborhood,
with the parameters free to vary in every coordinate. -/
theorem hasFDerivAt_observed_near_frozen (alpha : ℝ) (ha : 0 ≤ alpha) :
    ∀ᶠ p in 𝓝 (frozen alpha 5), HasFDerivAt observed (observedD p) p := by
  have h := (observed_eq_smooth_near_frozen alpha ha).eventually_nhds
  filter_upwards [h] with p hp
  exact (hasFDerivAt_observedSmooth p).congr_of_eventuallyEq hp

end ReyesMath.V18Forward
