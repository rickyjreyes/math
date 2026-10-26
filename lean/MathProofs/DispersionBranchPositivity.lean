import Mathlib
import MathProofs.PhysicalDispersionMinimum
import MathProofs.ModelAlgebra

/-!
# Positivity of both physical squared-frequency branches

Under K,T>0, G≥0 and 0<4K m²<1, both physical branches
z±(q) are strictly positive at every nonnegative q in the real-root
domain. This closes the *branch-positivity corollary* left outside
the original finite-scale minimum proof. No conclusion about
Ostrogradsky ghosts or a healthy Hamiltonian is made.
-/

namespace ReyesMath

noncomputable def physicalUpperBranch (K G T mass q : ℝ) : ℝ :=
  (1 + (2 * K + G) * q +
    Real.sqrt (radicand (Real.sqrt (1 - 4 * K * mass ^ 2))
      G (4 * K * T - G ^ 2) q)) / (2 * K)

/-- With positive mass and positive coefficients, both real-frequency
solutions have strictly positive squared frequency. -/
theorem physical_dispersion_both_branches_positive
    (K G T mass q : ℝ)
    (hK : 0 < K) (hG : 0 ≤ G) (hT : 0 < T)
    (hM : 0 < 4 * K * mass ^ 2)
    (hMtop : 4 * K * mass ^ 2 < 1)
    (hq : 0 ≤ q)
    (hreal : 0 ≤ radicand (Real.sqrt (1 - 4 * K * mass ^ 2))
      G (4 * K * T - G ^ 2) q) :
    0 < lowerBranch K (Real.sqrt (1 - 4 * K * mass ^ 2))
          G (4 * K * T - G ^ 2) (2 * K + G) q ∧
      0 < physicalUpperBranch K G T mass q := by
  let C : ℝ := 1 + (2 * K + G) * q
  let D : ℝ := radicand (Real.sqrt (1 - 4 * K * mass ^ 2))
    G (4 * K * T - G ^ 2) q
  have hcoeff : 0 ≤ K + G + T := by linarith
  have hmass : 0 < mass ^ 2 := by
    have hp : 0 < 4 * K * mass ^ 2 := hM
    nlinarith [sq_nonneg mass]
  have hpotential : 0 < mass ^ 2 + q + (K + G + T) * q ^ 2 := by
    have hnonneg : 0 ≤ (K + G + T) * q ^ 2 :=
      mul_nonneg hcoeff (sq_nonneg q)
    linarith
  have hdisc0 : 0 ≤ 1 - 4 * K * mass ^ 2 := by linarith
  have hdiscSq : (Real.sqrt (1 - 4 * K * mass ^ 2)) ^ 2 =
      1 - 4 * K * mass ^ 2 := Real.sq_sqrt hdisc0
  have hD :
      D = (1 - 4 * K * mass ^ 2) + 2 * G * q -
        (4 * K * T - G ^ 2) * q ^ 2 := by
    dsimp [D, radicand]
    rw [hdiscSq]
  have hsqrt : (Real.sqrt D) ^ 2 = D :=
    Real.sq_sqrt hreal
  have hquad : C ^ 2 - (Real.sqrt D) ^ 2 =
      4 * K * (mass ^ 2 + q + (K + G + T) * q ^ 2) := by
    rw [hsqrt, hD]
    dsimp [C]
    ring
  have hpositive : 0 < C ^ 2 - (Real.sqrt D) ^ 2 := by
    rw [hquad]
    exact mul_pos (by positivity) hpotential
  have hC : 0 < C := by
    dsimp [C]
    have hca : 0 ≤ (2 * K + G) * q :=
      mul_nonneg (by linarith) hq
    linarith
  have hroot : 0 ≤ Real.sqrt D := Real.sqrt_nonneg _
  have hstrict : Real.sqrt D < C := by
    nlinarith only [hpositive, hC, hroot]
  constructor
  · unfold lowerBranch
    change 0 < (C - Real.sqrt D) / (2 * K)
    exact div_pos (sub_pos.mpr hstrict) (by positivity)
  · unfold physicalUpperBranch
    change 0 < (C + Real.sqrt D) / (2 * K)
    exact div_pos (by linarith) (by positivity)

end ReyesMath
