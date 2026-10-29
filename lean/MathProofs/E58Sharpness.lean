import MathProofs.RemainingCores

/-!
# E58: sharpness and shell equality for the Green multiplier

These are exact algebraic spectral-symbol theorems. They do not
assert that the continuum L² multiplier has already been constructed
or that its operator norm has been certified.
-/

namespace ReyesMath
namespace E58Sharpness

open RemainingCores

/-- When the fourth-order coefficient is strictly positive, the Green
symbol reaches its upper bound only at the specified squared frequency. -/
theorem greenMultiplier_eq_bound_iff (r a kStar q : ℝ)
    (hr : 0 < r) (ha : 0 < a) :
    greenMultiplier r a kStar q = 1 / r ↔ q = kStar ^ 2 := by
  have hnonneg : 0 ≤ a * shellSymbol kStar q :=
    mul_nonneg (le_of_lt ha) (shellSymbol_nonneg kStar q)
  have hd : 0 < r + a * shellSymbol kStar q := by linarith
  constructor
  · intro h
    have hcross : (1 : ℝ) * r =
        (1 : ℝ) * (r + a * shellSymbol kStar q) := by
      apply (div_eq_div_iff₀ hd hr).mp
      simpa [greenMultiplier] using h
    have hmul : a * shellSymbol kStar q = 0 := by linarith
    have hs : shellSymbol kStar q = 0 :=
      (mul_eq_zero.mp hmul).resolve_left (ne_of_gt ha)
    have hsq : (q - kStar ^ 2) ^ 2 = 0 := by
      simpa [shellSymbol] using hs
    exact sub_eq_zero.mp (pow_eq_zero hsq)
  · intro h
    rw [h]
    exact greenMultiplier_at_shell r a kStar (ne_of_gt hr)

/-- Away from the shell, the pointwise estimate is strict for a > 0. -/
theorem greenMultiplier_lt_bound_off_shell (r a kStar q : ℝ)
    (hr : 0 < r) (ha : 0 < a) (hq : q ≠ kStar ^ 2) :
    greenMultiplier r a kStar q < 1 / r := by
  have hb := (greenMultiplier_bounds r a kStar q hr (le_of_lt ha)).2
  have hn : greenMultiplier r a kStar q ≠ 1 / r := by
    intro heq
    exact hq ((greenMultiplier_eq_bound_iff r a kStar q hr ha).mp heq)
  exact lt_of_le_of_ne hb hn

/-- Without the fourth-order term, the Fourier multiplier is constant. -/
theorem greenMultiplier_at_zero_coupling (r kStar q : ℝ) :
    greenMultiplier r 0 kStar q = 1 / r := by
  simp [greenMultiplier]

/-- The shell equality stated in terms of the Euclidean wavenumber norm. -/
theorem greenMultiplier_norm_eq_bound_iff {d : ℕ}
    (r a kStar : ℝ) (ξ : EuclideanSpace ℝ (Fin (d + 1)))
    (hr : 0 < r) (ha : 0 < a) (hk : 0 ≤ kStar) :
    greenMultiplier r a kStar (‖ξ‖ ^ 2) = 1 / r ↔ ‖ξ‖ = kStar := by
  rw [greenMultiplier_eq_bound_iff r a kStar (‖ξ‖ ^ 2) hr ha]
  constructor
  · intro h
    exact (sq_eq_sq₀ (norm_nonneg ξ) hk).mp h
  · intro h
    rw [h]

/-- The pointwise supremum is exactly 1/r, because the selected
    squared frequency is actually in the continuous frequency domain. -/
theorem greenMultiplier_sup (r a kStar : ℝ)
    (hr : 0 < r) (ha : 0 ≤ a) :
    sSup (Set.range (greenMultiplier r a kStar)) = 1 / r := by
  apply le_antisymm
  · apply csSup_le
    · exact ⟨_, ⟨kStar ^ 2, rfl⟩⟩
    · rintro _ ⟨q, rfl⟩
      exact (greenMultiplier_bounds r a kStar q hr ha).2
  · apply le_csSup
    · refine ⟨1 / r, ?_⟩
      rintro _ ⟨q, rfl⟩
      exact (greenMultiplier_bounds r a kStar q hr ha).2
    · exact ⟨kStar ^ 2, greenMultiplier_at_shell r a kStar (ne_of_gt hr)⟩

end E58Sharpness
end ReyesMath
