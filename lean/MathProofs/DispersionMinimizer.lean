import Mathlib

/-!
# Convex geometry of the real-frequency dispersion branch

These declarations prove an exact supporting-tangent inequality and the
uniqueness of a positive-parameter stationary minimizer on a real-root
interval. The existence/explicit closed formula for that stationary point
under the original manuscript parameter restrictions remains a separate
formalization obligation.
-/

namespace ReyesMath

private def radicand (s G B q : ℝ) : ℝ :=
  s ^ 2 + 2 * G * q - B * q ^ 2

private noncomputable def lowerBranch (K s G B a q : ℝ) : ℝ :=
  (1 + a * q - Real.sqrt (radicand s G B q)) / (2 * K)

/-- Exact discriminant identity underlying a strict supporting tangent. -/
theorem dispersion_tangent_square_identity
    (s G B a q q₀ : ℝ)
    (h₀ : 0 ≤ radicand s G B q₀)
    (hq : 0 ≤ radicand s G B q)
    (hstat : G - B * q₀ = a * Real.sqrt (radicand s G B q₀)) :
    (Real.sqrt (radicand s G B q₀) + a * (q - q₀)) ^ 2 -
        (Real.sqrt (radicand s G B q)) ^ 2 =
      (a ^ 2 + B) * (q - q₀) ^ 2 := by
  have hs0 : (Real.sqrt (radicand s G B q₀)) ^ 2 =
      radicand s G B q₀ := Real.sq_sqrt h₀
  have hsq : (Real.sqrt (radicand s G B q)) ^ 2 =
      radicand s G B q := Real.sq_sqrt hq
  calc
    (Real.sqrt (radicand s G B q₀) + a * (q - q₀)) ^ 2 -
        (Real.sqrt (radicand s G B q)) ^ 2 =
      2 * (a * Real.sqrt (radicand s G B q₀) -
        (G - B * q₀)) * (q - q₀) +
        (a ^ 2 + B) * (q - q₀) ^ 2 := by
          calc
            _ = (Real.sqrt (radicand s G B q₀)) ^ 2 +
                  2 * Real.sqrt (radicand s G B q₀) *
                    (a * (q - q₀)) + (a * (q - q₀)) ^ 2 -
                  (Real.sqrt (radicand s G B q)) ^ 2 := by ring
            _ = _ := by
              rw [hs0, hsq]
              dsimp [radicand]
              ring
    _ = (a ^ 2 + B) * (q - q₀) ^ 2 := by
      rw [show a * Real.sqrt (radicand s G B q₀) -
        (G - B * q₀) = 0 from by rw [← hstat]; ring]
      ring

/-- Every admissible point other than the positive-tangent stationary
point has strictly larger lower-branch value. -/
theorem dispersion_unique_minimum_at_stationary
    (K s G B a q q₀ : ℝ)
    (hK : 0 < K) (hB : 0 < B)
    (h₀ : 0 ≤ radicand s G B q₀)
    (hq : 0 ≤ radicand s G B q)
    (hstat : G - B * q₀ = a * Real.sqrt (radicand s G B q₀))
    (htangent : 0 ≤ Real.sqrt (radicand s G B q₀) + a * (q - q₀))
    (hne : q ≠ q₀) :
    lowerBranch K s G B a q₀ < lowerBranch K s G B a q := by
  have hsquare : 0 < (q - q₀) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
  have hcoeff : 0 < a ^ 2 + B := by nlinarith [sq_nonneg a]
  have hstrict :
      0 < (a ^ 2 + B) * (q - q₀) ^ 2 :=
    mul_pos hcoeff hsquare
  have hsqrt0 : 0 ≤ Real.sqrt (radicand s G B q₀) :=
    Real.sqrt_nonneg _
  have hsqrtq : 0 ≤ Real.sqrt (radicand s G B q) :=
    Real.sqrt_nonneg _
  have hdiff := dispersion_tangent_square_identity s G B a q q₀ h₀ hq hstat
  have hbound :
      Real.sqrt (radicand s G B q) <
        Real.sqrt (radicand s G B q₀) + a * (q - q₀) := by
    nlinarith
  unfold lowerBranch
  apply div_lt_div_of_pos_right _ (by positivity : 0 < 2 * K)
  nlinarith

end ReyesMath
