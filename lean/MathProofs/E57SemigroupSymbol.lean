import MathProofs.RemainingCores

/-!
# E57: exact semigroup law for the fourth-order Fourier-shell symbol

These identities hold at every real squared-frequency coordinate and
every real time. They provide the algebraic time-composition foundation
for the genuine L² contraction implemented in E57WholeSpaceDamping.
The strong operator-semigroup equation on L² still requires a
coefficient-level identity and transfer through the Fourier isometry.
-/

namespace ReyesMath
namespace E57SemigroupSymbol

open RemainingCores

/-- Zero elapsed time leaves every Fourier-shell mode unchanged. -/
theorem damping_at_zero_time (a kStar q : ℝ) :
    shellDamping a 0 kStar q = 1 := by
  simp [shellDamping]

/-- The exact fourth-order Fourier-shell multiplier composes under
time addition, without a discretization or an assumed exponential law. -/
theorem damping_semigroup (a s t kStar q : ℝ) :
    shellDamping a (s + t) kStar q =
      shellDamping a s kStar q * shellDamping a t kStar q := by
  have h :
      -(a * (s + t) * shellSymbol kStar q) =
        -(a * s * shellSymbol kStar q) -
          a * t * shellSymbol kStar q := by ring
  simp only [shellDamping]
  rw [h, sub_eq_add_neg, Real.exp_add]

/-- Damping at any nonnegative time is strictly positive and at most one. -/
theorem damping_positive_and_contractive (a t kStar q : ℝ)
    (ha : 0 ≤ a) (ht : 0 ≤ t) :
    0 < shellDamping a t kStar q ∧ shellDamping a t kStar q ≤ 1 :=
  shellDamping_bounds a t kStar q ha ht

end E57SemigroupSymbol
end ReyesMath
