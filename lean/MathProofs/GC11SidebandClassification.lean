import MathProofs.GC11Coercivity

/-!
# GC11: sharp transverse sideband discriminant classification

The algebraic classification quantifies over every real squared sideband
radius s ≥ 0. On R² each s is realizable perpendicular to a nonzero carrier.
This does not by itself formalize the full Bloch operator or nonlinear
instability. A fixed torus only has discrete realizable sidebands.
-/
noncomputable section
namespace ReyesMath
namespace GC11Coercivity

def transverse (delta s : ℝ) : ℝ := s ^ 2 + 2 * delta * s

theorem transverse_eq (k q s : ℝ) :
    evenPart k q s 0 = transverse (q - k ^ 2) s := by
  unfold evenPart transverse
  ring

/-- Every positive value of the transverse polynomial is attained at s>0. -/
theorem transverse_attains_pos (delta y : ℝ) (hy : 0 < y) :
    ∃ s > 0, transverse delta s = y := by
  have hr : 0 ≤ delta ^ 2 + y := by linarith [sq_nonneg delta]
  have hs := Real.sq_sqrt hr
  let s := -delta + Real.sqrt (delta ^ 2 + y)
  have hp : 0 < s := by
    by_cases hd : delta < 0
    · dsimp [s]
      linarith [Real.sqrt_nonneg (delta ^ 2 + y)]
    · have hd0 : 0 ≤ delta := le_of_not_gt hd
      have hlt : delta < Real.sqrt (delta ^ 2 + y) := by
        have h := Real.sqrt_lt_sqrt (sq_nonneg delta)
          (show delta ^ 2 < delta ^ 2 + y by linarith)
        simpa [Real.sqrt_sq hd0] using h
      dsimp [s]
      linarith
  refine ⟨s, hp, ?_⟩
  unfold transverse
  dsimp [s]
  nlinarith [hs]

/-- Every negative value strictly above the transverse minimum is attained
at a positive sideband radius when the carrier lies below the shell. -/
theorem transverse_attains_neg (delta a : ℝ) (hd : delta < 0)
    (ha : 0 < a) (ha' : a ≤ delta ^ 2) :
    ∃ s > 0, transverse delta s = -a := by
  have hr : 0 ≤ delta ^ 2 - a := sub_nonneg.mpr ha'
  have hs := Real.sq_sqrt hr
  have hlt : Real.sqrt (delta ^ 2 - a) < -delta := by
    have h := Real.sqrt_lt_sqrt hr
      (show delta ^ 2 - a < (-delta) ^ 2 by nlinarith)
    simpa [Real.sqrt_sq (neg_nonneg.mpr hd.le)] using h
  refine ⟨-delta - Real.sqrt (delta ^ 2 - a), by linarith, ?_⟩
  unfold transverse
  nlinarith [hs]

theorem negative_c_unstable (delta c : ℝ) (hc : c < 0) :
    ∃ s > 0, transverse delta s * (transverse delta s + 2 * c) < 0 := by
  obtain ⟨s, hs, he⟩ := transverse_attains_pos delta (-c) (by linarith)
  refine ⟨s, hs, ?_⟩
  rw [he]
  exact mul_neg_of_pos_of_neg (by linarith) (by linarith)

theorem below_shell_unstable (delta c : ℝ) (hd : delta < 0) (hc : 0 < c) :
    ∃ s > 0, transverse delta s * (transverse delta s + 2 * c) < 0 := by
  let a := min c (delta ^ 2)
  have ha : 0 < a := lt_min hc (sq_pos_of_neg hd)
  have hac : a ≤ c := min_le_left _ _
  have had : a ≤ delta ^ 2 := min_le_right _ _
  obtain ⟨s, hs, he⟩ := transverse_attains_neg delta a hd ha had
  refine ⟨s, hs, ?_⟩
  rw [he]
  exact mul_neg_of_neg_of_pos (by linarith) (by linarith)

/-- Exact continuum transverse no-growth criterion, including c=0. -/
theorem transverse_no_growth_iff (delta c : ℝ) :
    (∀ s : ℝ, 0 ≤ s → 0 ≤ transverse delta s * (transverse delta s + 2 * c)) ↔
      c = 0 ∨ (0 ≤ delta ∧ 0 < c) := by
  constructor
  · intro h
    by_cases hc : c = 0
    · exact Or.inl hc
    · have hcp : 0 < c := by
        by_contra hn
        have hn' : c < 0 := lt_of_le_of_ne (le_of_not_gt hn) hc
        obtain ⟨s, hs, he⟩ := negative_c_unstable delta c hn'
        exact (not_lt_of_ge (h s hs.le)) he
      refine Or.inr ⟨?_, hcp⟩
      by_contra hn
      obtain ⟨s, hs, he⟩ := below_shell_unstable delta c (lt_of_not_ge hn) hcp
      exact (not_lt_of_ge (h s hs.le)) he
  · rintro (rfl | ⟨hd, hc⟩) s hs
    · simp only [mul_zero, add_zero]
      exact mul_self_nonneg _
    · have he : 0 ≤ transverse delta s := by unfold transverse; positivity
      exact mul_nonneg he (by linarith)

/-- Sharp all-sideband discriminant theorem: sufficiency for every
dot product t, necessity already on transverse modes t=0. -/
theorem all_sidebands_no_growth_iff (k q c : ℝ) :
    (∀ s t : ℝ, 0 ≤ s →
      0 ≤ evenPart k q s t * (evenPart k q s t + 2 * c)) ↔
      c = 0 ∨ (k ^ 2 ≤ q ∧ 0 < c) := by
  constructor
  · intro h
    have ht : ∀ s : ℝ, 0 ≤ s →
      0 ≤ transverse (q - k ^ 2) s * (transverse (q - k ^ 2) s + 2 * c) := by
      intro s hs
      simpa only [transverse_eq] using h s 0 hs
    rcases (transverse_no_growth_iff (q - k ^ 2) c).1 ht with hc | ⟨hd, hc⟩
    · exact Or.inl hc
    · exact Or.inr ⟨by linarith, hc⟩
  · rintro (rfl | ⟨hq, hc⟩) s t hs
    · simp only [mul_zero, add_zero]
      exact mul_self_nonneg _
    · exact sideband_discriminant_nonneg hq hs hc.le

end GC11Coercivity
end ReyesMath
