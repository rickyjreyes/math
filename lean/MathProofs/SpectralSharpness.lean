import MathProofs.RemainingCores

/-!
# E61 and M3/E57: sharp shell equality and strict off-shell damping

Algebraic pointwise consequences of the manuscript dispersion and
semigroup symbols, without claiming a continuum differential-operator
spectral theorem or complete PDE well-posedness.
-/

namespace ReyesMath
namespace SpectralSharpness

open RemainingCores

/-- For positive stiffness, the growth symbol reaches its upper
bound exactly at the selected squared frequency. -/
theorem linearGrowth_eq_max_iff (r a kStar q : ℝ)
    (ha : 0 < a) :
    linearGrowth r a kStar q = r ↔ q = kStar ^ 2 := by
  constructor
  · intro h
    have hmul : a * shellSymbol kStar q = 0 := by
      dsimp [linearGrowth] at h
      linarith
    have hz : shellSymbol kStar q = 0 :=
      (mul_eq_zero.mp hmul).resolve_left (ne_of_gt ha)
    have hsq : (q - kStar ^ 2) ^ 2 = 0 := by
      simpa [shellSymbol] using hz
    nlinarith [sq_nonneg (q - kStar ^ 2)]
  · intro h
    rw [h]
    exact linearGrowth_at_shell r a kStar

theorem linearGrowth_strict_off_shell (r a kStar q : ℝ)
    (ha : 0 < a) (hq : q ≠ kStar ^ 2) :
    linearGrowth r a kStar q < r := by
  have hb : linearGrowth r a kStar q ≤ r :=
    linearGrowth_le r a kStar q (le_of_lt ha)
  have hn : linearGrowth r a kStar q ≠ r := by
    intro heq
    exact hq ((linearGrowth_eq_max_iff r a kStar q ha).mp heq)
  exact lt_of_le_of_ne hb hn

/-- With positive time and stiffness, the semigroup damps every
strictly off-shell mode by a factor smaller than one. -/
theorem shellDamping_strict_off_shell (a t kStar q : ℝ)
    (ha : 0 < a) (ht : 0 < t) (hq : q ≠ kStar ^ 2) :
    shellDamping a t kStar q < 1 := by
  have hsq : 0 < shellSymbol kStar q := by
    unfold shellSymbol
    exact sq_pos_of_ne_zero (sub_ne_zero.mpr hq)
  have hp : 0 < a * t * shellSymbol kStar q :=
    mul_pos (mul_pos ha ht) hsq
  unfold shellDamping
  rw [← Real.exp_zero]
  exact Real.exp_lt_exp.mpr (by linarith)

/-- The selected shell is exactly undamped. -/
theorem shellDamping_at_shell (a t kStar : ℝ) :
    shellDamping a t kStar (kStar ^ 2) = 1 := by
  simp [shellDamping, shellSymbol]

end SpectralSharpness
end ReyesMath
