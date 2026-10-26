import Mathlib
import MathProofs.DispersionCriticalPoint

/-!
# Original physical parameter specialization of the finite-scale minimum

The squared-frequency lower branch of the manuscript is formalized at
B = 4KT-G² and s = sqrt(1-4Km²). The theorem states a unique positive
global minimizer throughout the nonnegative real-frequency domain.
It makes no assertion about healthy Hamiltonian degrees of freedom.
-/

namespace ReyesMath

/-- The original positive-parameter finite-wavenumber hypothesis,
with *no assumed critical point*, implies an explicit unique global
minimum of the exact lower squared-frequency branch. -/
theorem finite_scale_physical_unique_global_minimum
    (K G T mass : ℝ)
    (hK : 0 < K) (hT : 0 < T)
    (hB : 0 < 4 * K * T - G ^ 2)
    (hm0 : 0 < 4 * K * mass ^ 2)
    (hm1 : 4 * K * mass ^ 2 < 1)
    (hscale : G * (1 - Real.sqrt (1 - 4 * K * mass ^ 2)) >
        2 * K * Real.sqrt (1 - 4 * K * mass ^ 2)) :
    ∃ qstar : ℝ,
      0 < qstar ∧
      qstar = (G - (2 * K + G) *
        Real.sqrt ((G ^ 2 + (4 * K * T - G ^ 2) *
          (Real.sqrt (1 - 4 * K * mass ^ 2)) ^ 2) /
          ((2 * K + G) ^ 2 + (4 * K * T - G ^ 2)))) /
        (4 * K * T - G ^ 2) ∧
      ∀ q : ℝ, 0 ≤ q →
        0 ≤ radicand (Real.sqrt (1 - 4 * K * mass ^ 2))
          G (4 * K * T - G ^ 2) q →
        q ≠ qstar →
        lowerBranch K (Real.sqrt (1 - 4 * K * mass ^ 2))
          G (4 * K * T - G ^ 2) (2 * K + G) qstar <
        lowerBranch K (Real.sqrt (1 - 4 * K * mass ^ 2))
          G (4 * K * T - G ^ 2) (2 * K + G) q := by
  let s : ℝ := Real.sqrt (1 - 4 * K * mass ^ 2)
  let B : ℝ := 4 * K * T - G ^ 2
  have hdisc : 0 < 1 - 4 * K * mass ^ 2 := by linarith
  have hs0 : 0 < s := Real.sqrt_pos.2 hdisc
  have hsquare : s ^ 2 = 1 - 4 * K * mass ^ 2 :=
    Real.sq_sqrt (le_of_lt hdisc)
  have hsone : s < 1 := by
    nlinarith [hm0, hsquare]
  have hmin := finite_scale_explicit_global_minimum
    K G B s hK hB hs0 hsone hscale
  simpa only [s, B] using hmin

end ReyesMath
