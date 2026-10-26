import Mathlib
import MathProofs.DispersionMinimizer

/-!
# Explicit positive interior critical point of the finite-wavenumber branch

This removes the arbitrary stationary-point *existence* assumption from the
previous dispersion lemma, using the original strict small-scale criterion
G(1-s) > 2Ks, with a = 2K+G and B>0.

The argument is polynomial except for one rigorously controlled positive
real square root. It does not make any ghost-stability claim.
-/

namespace ReyesMath

set_option maxHeartbeats 1800000

private def finiteScaleRadicand (s G B q : ℝ) : ℝ :=
  s ^ 2 + 2 * G * q - B * q ^ 2

/-- The critical wavenumber formula satisfies the original (unsquared)
stationary equation and lies strictly between zero and G/B. -/
theorem finite_scale_positive_stationary_exists
    (K G B s : ℝ)
    (hK : 0 < K) (hB : 0 < B)
    (hs : 0 < s) (hsone : s < 1)
    (hcriterion : G * (1 - s) > 2 * K * s) :
    ∃ q : ℝ,
      0 < q ∧ q < G / B ∧
      0 < finiteScaleRadicand s G B q ∧
      G - B * q = (2 * K + G) * Real.sqrt (finiteScaleRadicand s G B q) ∧
      0 < Real.sqrt (finiteScaleRadicand s G B q) - (2 * K + G) * q ∧
      q = (G - (2 * K + G) *
        Real.sqrt ((G ^ 2 + B * s ^ 2) / ((2 * K + G) ^ 2 + B))) / B := by
  let a : ℝ := 2 * K + G
  have hGs : G > a * s := by
    dsimp [a]
    nlinarith [hcriterion]
  have hG : 0 < G := by
    have has : 0 < a * s := by
      have hzero : 0 < 1 - s := by linarith
      have hKst : 0 < 2 * K * s := by positivity
      have hGpos : 0 < G := by
        by_contra h
        have hn : G ≤ 0 := le_of_not_gt h
        have hn2 : G * (1 - s) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hn (le_of_lt hzero)
        linarith
      dsimp [a]
      positivity
    linarith
  have ha : 0 < a := by dsimp [a]; linarith
  let D : ℝ := a ^ 2 + B
  let H : ℝ := G ^ 2 + B * s ^ 2
  have hD : 0 < D := by dsimp [D]; positivity
  have hH : 0 < H := by dsimp [H]; positivity
  let t : ℝ := Real.sqrt (H / D)
  have ht : 0 < t := Real.sqrt_pos.2 (div_pos hH hD)
  have ht2 : D * t ^ 2 = H := by
    have hsq : t ^ 2 = H / D := Real.sq_sqrt (le_of_lt (div_pos hH hD))
    rw [hsq]
    field_simp [ne_of_gt hD]
  have hgsq : 0 < G ^ 2 - (a * s) ^ 2 := by
    have hz : 0 < (G - a * s) * (G + a * s) := by
      apply mul_pos (sub_pos.mpr hGs)
      positivity
    nlinarith
  have hrel :
      D * (G ^ 2 - (a * t) ^ 2) =
      B * (G ^ 2 - (a * s) ^ 2) := by
    calc
      _ = D * G ^ 2 - a ^ 2 * (D * t ^ 2) := by ring
      _ = D * G ^ 2 - a ^ 2 * H := by rw [ht2]
      _ = B * (G ^ 2 - (a * s) ^ 2) := by dsimp [D, H]; ring
  have hposdiff : 0 < G ^ 2 - (a * t) ^ 2 := by
    have hprod : 0 < D * (G ^ 2 - (a * t) ^ 2) := by
      rw [hrel]
      exact mul_pos hB hgsq
    by_contra hn
    have hh : G ^ 2 - (a * t) ^ 2 ≤ 0 := le_of_not_gt hn
    have hh2 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hD) hh
    linarith
  have hGt : a * t < G := by
    have hat : 0 ≤ a * t := le_of_lt (mul_pos ha ht)
    nlinarith [hposdiff]
  let q : ℝ := (G - a * t) / B
  have hqpos : 0 < q := div_pos (sub_pos.mpr hGt) hB
  have hqmax : q < G / B :=
    div_lt_div_of_pos_right (by nlinarith [mul_pos ha ht]) hB
  have hshift : G - B * q = a * t := by
    dsimp [q]
    field_simp [ne_of_gt hB]
    ring
  have hdiscr :
      B * finiteScaleRadicand s G B q =
        B * s ^ 2 + G ^ 2 - (G - B * q) ^ 2 := by
    dsimp [finiteScaleRadicand]
    ring
  have hmul : B * finiteScaleRadicand s G B q = B * t ^ 2 := by
    calc
      _ = B * s ^ 2 + G ^ 2 - (G - B * q) ^ 2 := hdiscr
      _ = B * s ^ 2 + G ^ 2 - (a * t) ^ 2 := by rw [hshift]
      _ = B * t ^ 2 := by
        dsimp [D, H] at ht2
        nlinarith [ht2]
  have hrad : finiteScaleRadicand s G B q = t ^ 2 := by
    have hz : B * (finiteScaleRadicand s G B q - t ^ 2) = 0 := by
      nlinarith [hmul]
    have hzero : finiteScaleRadicand s G B q - t ^ 2 = 0 :=
      (mul_eq_zero.mp hz).resolve_left (ne_of_gt hB)
    linarith
  have hradpos : 0 < finiteScaleRadicand s G B q := by
    rw [hrad]
    positivity
  have hsqrt : Real.sqrt (finiteScaleRadicand s G B q) = t := by
    rw [hrad, Real.sqrt_sq (le_of_lt ht)]
  have hrel2 :
      (D * t) ^ 2 - (a * G) ^ 2 =
        B * (G ^ 2 + D * s ^ 2) := by
    calc
      _ = D * (D * t ^ 2) - a ^ 2 * G ^ 2 := by ring
      _ = D * H - a ^ 2 * G ^ 2 := by rw [ht2]
      _ = B * (G ^ 2 + D * s ^ 2) := by dsimp [D, H]; ring
  have hposDt : a * G < D * t := by
    have hpos : 0 < (D * t) ^ 2 - (a * G) ^ 2 := by
      rw [hrel2]
      positivity
    have hl : 0 ≤ D * t := le_of_lt (mul_pos hD ht)
    have hr : 0 ≤ a * G := le_of_lt (mul_pos ha hG)
    nlinarith
  have hshift2 : B * (t - a * q) = D * t - a * G := by
    dsimp [q, D]
    field_simp [ne_of_gt hB]
    ring
  have hT0 : 0 < t - a * q := by
    have hprod : 0 < B * (t - a * q) := by
      rw [hshift2]
      linarith
    by_contra hn
    have hnonpos : t - a * q ≤ 0 := le_of_not_gt hn
    have hnonposprod := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hB) hnonpos
    linarith
  refine ⟨q, hqpos, hqmax, hradpos, ?_, ?_, ?_⟩
  · rw [hsqrt]
    change G - B * q = a * t
    exact hshift
  · rw [hsqrt]
    change 0 < t - a * q
    exact hT0
  · dsimp [q, t, D, H, a]

/-- The explicit positive critical point is the unique global minimum of
the lower *squared-frequency branch* over the complete real-pole domain at
nonnegative squared wavenumbers. The hypotheses are the precise reduced
parameters s = sqrt(1-4Km²), B = 4KT-G², a = 2K+G. -/
theorem finite_scale_explicit_global_minimum
    (K G B s : ℝ)
    (hK : 0 < K) (hB : 0 < B)
    (hs : 0 < s) (hsone : s < 1)
    (hcriterion : G * (1 - s) > 2 * K * s) :
    ∃ qstar : ℝ,
      0 < qstar ∧
      qstar = (G - (2 * K + G) *
        Real.sqrt ((G ^ 2 + B * s ^ 2) / ((2 * K + G) ^ 2 + B))) / B ∧
      ∀ q : ℝ, 0 ≤ q → 0 ≤ radicand s G B q → q ≠ qstar →
        lowerBranch K s G B (2 * K + G) qstar <
          lowerBranch K s G B (2 * K + G) q := by
  obtain ⟨qstar, hqpos, hqmax, hradpos, hstat, ht0, hformula⟩ :=
    finite_scale_positive_stationary_exists K G B s hK hB hs hsone hcriterion
  refine ⟨qstar, hqpos, hformula, ?_⟩
  have hG : 0 < G := by
    have hsm : 0 < 1 - s := by linarith
    have hp : 0 < 2 * K * s := by positivity
    by_contra hn
    have hnG : G ≤ 0 := le_of_not_gt hn
    have hbad := mul_nonpos_of_nonpos_of_nonneg hnG (le_of_lt hsm)
    linarith
  have ha : 0 < 2 * K + G := by linarith
  have hrad0 : 0 ≤ radicand s G B qstar := by
    simpa only [radicand, finiteScaleRadicand] using (le_of_lt hradpos)
  have hstat0 :
      G - B * qstar = (2 * K + G) * Real.sqrt (radicand s G B qstar) := by
    simpa only [radicand, finiteScaleRadicand] using hstat
  have ht0' :
      0 < Real.sqrt (radicand s G B qstar) - (2 * K + G) * qstar := by
    simpa only [radicand, finiteScaleRadicand] using ht0
  intro q hq hrad hneq
  have htangent :
      0 ≤ Real.sqrt (radicand s G B qstar) +
        (2 * K + G) * (q - qstar) := by
    have hm : 0 ≤ (2 * K + G) * q := mul_nonneg (le_of_lt ha) hq
    nlinarith [ht0']
  exact dispersion_unique_minimum_at_stationary
    K s G B (2 * K + G) q qstar hK hB
    hrad0 hrad hstat0 htangent hneq


end ReyesMath
