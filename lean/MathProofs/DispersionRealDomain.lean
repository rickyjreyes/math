import Mathlib
import MathProofs.DispersionMinimizer

/-!
# Exact right endpoint of the real-frequency dispersion interval

For s,B>0, G≥0 and q≥0, the quadratic discriminant
  d(q) = s² + 2Gq - Bq²
is nonnegative precisely when
  0 ≤ q ≤ (G + sqrt(G² + B s²))/B.
This gives the full physical nonnegative real-root domain.
-/

namespace ReyesMath

/-- The exact upper real-frequency-domain endpoint exists and is
strictly positive; the radicand vanishes at the endpoint. -/
theorem dispersion_real_domain_endpoint
    (s G B : ℝ) (hs : 0 < s) (hG : 0 ≤ G) (hB : 0 < B) :
    let qmax := (G + Real.sqrt (G ^ 2 + B * s ^ 2)) / B
    0 < qmax ∧ radicand s G B qmax = 0 ∧
      ∀ q : ℝ, 0 ≤ q →
        (0 ≤ radicand s G B q ↔ q ≤ qmax) := by
  let t : ℝ := Real.sqrt (G ^ 2 + B * s ^ 2)
  have hrad : 0 ≤ G ^ 2 + B * s ^ 2 := by positivity
  have ht2 : t ^ 2 = G ^ 2 + B * s ^ 2 := Real.sq_sqrt hrad
  have ht : 0 ≤ t := Real.sqrt_nonneg _
  have hdiff : 0 < t ^ 2 - G ^ 2 := by
    rw [ht2]
    nlinarith [sq_pos_of_pos hs, mul_pos hB (sq_pos_of_pos hs)]
  have htG : G < t := by nlinarith
  let qmax : ℝ := (G + t) / B
  have hqmax : 0 < qmax := div_pos (by linarith) hB
  have hfactor (q : ℝ) :
      B * radicand s G B q =
        (t + B * q - G) * (t - B * q + G) := by
    dsimp [radicand]
    nlinarith [ht2]
  have hqend : t - B * qmax + G = 0 := by
    dsimp [qmax]
    field_simp [ne_of_gt hB]
    ring
  have hz : radicand s G B qmax = 0 := by
    have hprod := hfactor qmax
    rw [hqend, mul_zero] at hprod
    have hbne : B ≠ 0 := ne_of_gt hB
    exact (mul_eq_zero.mp hprod).resolve_left hbne
  change 0 < qmax ∧ radicand s G B qmax = 0 ∧
    ∀ q : ℝ, 0 ≤ q → (0 ≤ radicand s G B q ↔ q ≤ qmax)
  refine ⟨hqmax, hz, ?_⟩
  intro q hq
  have hfront : 0 < t + B * q - G := by
    have hmul : 0 ≤ B * q := mul_nonneg (le_of_lt hB) hq
    linarith
  have hsecond : (0 ≤ t - B * q + G) ↔ q ≤ qmax := by
    dsimp [qmax]
    constructor
    · intro h
      apply (le_div_iff₀ hB).2
      linarith
    · intro h
      have hh := (le_div_iff₀ hB).1 h
      linarith
  constructor
  · intro h
    have hbd : 0 ≤ B * radicand s G B q :=
      mul_nonneg (le_of_lt hB) h
    rw [hfactor] at hbd
    have hback : 0 ≤ t - B * q + G := by
      by_contra hn
      have neg : t - B * q + G < 0 := lt_of_not_ge hn
      have hp := mul_neg_of_pos_of_neg hfront neg
      linarith
    exact hsecond.mp hback
  · intro h
    have hb := hsecond.mpr h
    have hbd : 0 ≤ B * radicand s G B q := by
      rw [hfactor]
      exact mul_nonneg (le_of_lt hfront) hb
    by_contra hn
    have hneg : radicand s G B q < 0 := lt_of_not_ge hn
    have hp := mul_neg_of_pos_of_neg hB hneg
    linarith

end ReyesMath
