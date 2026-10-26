import Mathlib

/-!
# Explicit positive interior critical point of the finite-wavenumber branch

This removes the arbitrary stationary-point *existence* assumption from the
previous dispersion lemma, using the original strict small-scale criterion
G(1-s) > 2Ks, with a = 2K+G and B>0.

The argument is polynomial except for one rigorously controlled positive
real square root. It does not make any ghost-stability claim.
-/

namespace ReyesMath

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
  refine ⟨q, hqpos, hqmax, hradpos, ?_, ?_⟩
  · rw [hsqrt]
    change G - B * q = a * t
    exact hshift
  · dsimp [q, t, D, H, a]

end ReyesMath
