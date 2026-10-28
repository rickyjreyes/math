import Mathlib
import MathProofs.M6BCurvature

/-!
# M6B nonzero-field regularization limit of the *exact* complex quotient.
-/

noncomputable section
namespace ReyesMath.M6B

/-- At ε=0 and any nonzero complex field value, the actual
M6B curvature jet equals the unregularized quotient -Δψ/ψ. -/
theorem curvature_zero_epsilon (α lam S : ℝ) (z w : ℂ) (hz : z ≠ 0) :
    curvature 0 α lam S z w = -(w / z) := by
  have hconj : (starRingEnd ℂ) z ≠ 0 := by
    simpa using hz
  have hnorm : ((Complex.normSq z : ℝ) : ℂ) =
      z * (starRingEnd ℂ) z := by
    rw [Complex.normSq_eq_conj_mul_self]
    ring
  unfold curvature
  simp only [denominator, zero_pow (by norm_num : (2:ℕ) ≠ 0),
    zero_mul, add_zero]
  rw [hnorm]
  field_simp [hz, hconj]

/-- The *full complex quotient* converges at nonzero field values,
not merely the real regularizing denominator.  We use unrestricted
ε→0; hence the manuscript's one-sided ε↓0 follows immediately. -/
theorem curvature_nonzero_limit (α lam S : ℝ)
    (z w : ℂ) (hz : z ≠ 0) :
    Filter.Tendsto (fun ε : ℝ => curvature ε α lam S z w)
      (nhds 0) (nhds (-(w / z))) := by
  have hn : Complex.normSq z ≠ 0 := (Complex.normSq_pos.mpr hz).ne'
  have hden : denominator 0 α lam S (Complex.normSq z) ≠ 0 := by
    simpa [denominator] using hn
  have hcont : ContinuousAt
      (fun ε : ℝ => curvature ε α lam S z w) 0 := by
    unfold curvature
    have hdenCont : ContinuousAt
        (fun ε : ℝ =>
          ((denominator ε α lam S (Complex.normSq z) : ℝ) : ℂ)) 0 := by
      unfold denominator
      fun_prop
    exact continuousAt_const.div hdenCont (by exact_mod_cast hden)
  convert hcont.tendsto using 1
  exact congrArg nhds ((curvature_zero_epsilon α lam S z w hz).symm)

/-- The one-sided ε↓0 limit, as stated in the manuscript. -/
theorem curvature_downarrow_zero (α lam S : ℝ)
    (z w : ℂ) (hz : z ≠ 0) :
    Filter.Tendsto (fun ε : ℝ => curvature ε α lam S z w)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (-(w / z))) :=
  (curvature_nonzero_limit α lam S z w hz).mono_left nhdsWithin_le_nhds

end ReyesMath.M6B
