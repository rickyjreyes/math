import Mathlib

/-!
# E68: exact scaling obstructions

These are the universal real-variable contradictions forced by the
*actual exponents* in the E68 manuscript for smooth concentration
families.  The symbols A, B, etc. are explicitly the base profile's
squared Sobolev seminorms, as calculated in the paper.

The full issue additionally requires constructing the smooth family in
`H¹(ℝⁿ)`, proving change-of-variable formulas for the actual integrals,
and establishing the fixed singular `H¹` counterexample.  The present
file does not assert those missing analytic bridges.
-/

noncomputable section

namespace ReyesMath.E68

/-- No positive constant can be uniformly bounded above along all
positive radii by a function continuous at zero and vanishing there. -/
theorem obstruction_of_vanishing
    (F : ℝ → ℝ) (A : ℝ) (hA : 0 < A)
    (hc : ContinuousAt F 0) (hF : F 0 = 0)
    (hbound : ∀ R : ℝ, 0 < R → A ≤ F R) : False := by
  have ht : Filter.Tendsto F (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa [hF] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hsmall : ∀ᶠ R in nhdsWithin 0 (Set.Ioi 0), F R < A :=
    ht.eventually (isOpen_Iio.mem_nhds hA)
  have hpositive : ∀ᶠ R : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < R := by
    filter_upwards [self_mem_nhdsWithin] with R hR
    exact hR
  obtain ⟨R, hR, hlt⟩ := (hpositive.and hsmall).exists
  exact (not_le_of_gt hlt) (hbound R hR)

/-- For n>2 the unmodified E68 smooth-concentration scaling law
A ≤ C R^(n-2) (A+R²B) cannot hold for every R>0 when A>0.
This is the exact algebraic contradiction of Proposition 3.1,
not a claim that an H¹ concentration family has already been built. -/
theorem smooth_concentration_scaling_obstruction (n : ℕ)
    (hn : 2 < n) (A B : ℝ) (hA : 0 < A) :
    ¬ ∃ C : ℝ, ∀ R : ℝ, 0 < R →
      A ≤ C * R ^ (n - 2) * (A + R ^ 2 * B) := by
  rintro ⟨C, h⟩
  let F : ℝ → ℝ := fun R => C * R ^ (n - 2) * (A + R ^ 2 * B)
  have hc : ContinuousAt F 0 := by
    dsimp [F]
    fun_prop
  have hn2 : 0 < n - 2 := Nat.sub_pos_of_lt hn
  have hz : F 0 = 0 := by simp [F, Nat.ne_of_gt hn2]
  exact obstruction_of_vanishing F A hA hc hz h

/-- The dimension-one large-radius obstruction: a fixed nonzero
compactly supported gradient energy A cannot obey A ≤ C H / R
uniformly as R grows. -/
theorem large_radius_one_dimensional_obstruction
    (A H : ℝ) (hA : 0 < A) :
    ¬ ∃ C : ℝ, ∀ R : ℝ, 1 ≤ R → A ≤ C * H / R := by
  rintro ⟨C, h⟩
  let R : ℝ := max 1 (C * H / A + 1)
  have hR : 1 ≤ R := le_max_left _ _
  have hRpos : 0 < R := by linarith
  have hRlower : C * H / A + 1 ≤ R := le_max_right _ _
  have hbound := h R hR
  have hproduct : A * R ≤ C * H :=
    (le_div_iff₀ hRpos).mp hbound
  have hlower : A * (C * H / A + 1) ≤ A * R :=
    mul_le_mul_of_nonneg_left hRlower (le_of_lt hA)
  have hcancel : A * (C * H / A) = C * H := by
    field_simp [ne_of_gt hA]
  nlinarith

/-- Above dimension four, the exact H² rescaling leads to
R² A ≤ C R^(n-2) (R⁴ B₀ + R² B₁ + B₂).  This is impossible for
positive A.  The Sobolev identification of A,Bᵢ is a separate step. -/
theorem high_dimensional_H2_scaling_obstruction (n : ℕ)
    (hn : 4 < n) (A B₀ B₁ B₂ : ℝ) (hA : 0 < A) :
    ¬ ∃ C : ℝ, ∀ R : ℝ, 0 < R →
      R ^ 2 * A ≤ C * R ^ (n - 2) *
        (R ^ 4 * B₀ + R ^ 2 * B₁ + B₂) := by
  rintro ⟨C, h⟩
  let F : ℝ → ℝ := fun R =>
    C * R ^ (n - 4) * (R ^ 4 * B₀ + R ^ 2 * B₁ + B₂)
  have hc : ContinuousAt F 0 := by
    dsimp [F]
    fun_prop
  have hn4 : 0 < n - 4 := Nat.sub_pos_of_lt hn
  have hz : F 0 = 0 := by simp [F, Nat.ne_of_gt hn4]
  apply obstruction_of_vanishing F A hA hc hz
  intro R hR
  have he : n - 2 = (n - 4) + 2 := by omega
  have hr2 : 0 < R ^ 2 := pow_pos hR 2
  have hh := h R hR
  rw [he, pow_add] at hh
  have hscaled : R ^ 2 * A ≤ R ^ 2 * F R := by
    simpa [F, mul_assoc, mul_comm, mul_left_comm] using hh
  exact (mul_le_mul_iff_right₀ hr2).mp hscaled

/-- The n=2 portion of E68 with C₂=1, for the actual (strong)
derivative and the inhomogeneous whole-space H¹ energy integral.
Both the center and the positive radius are universally quantified.
In particular this theorem covers smooth H¹ fields. -/
theorem two_dimensional_local_gradient_energy
    (ψ : EuclideanSpace ℝ (Fin 2) → ℂ)
    (_hψ : MeasureTheory.Integrable (fun x => ‖ψ x‖ ^ 2))
    (hgrad : MeasureTheory.Integrable (fun x => ‖fderiv ℝ ψ x‖ ^ 2))
    (center : EuclideanSpace ℝ (Fin 2)) (R : ℝ) (_hR : 0 < R) :
    (∫ x in Metric.ball center R, ‖fderiv ℝ ψ x‖ ^ 2) ≤
      (∫ x, ‖ψ x‖ ^ 2) + (∫ x, ‖fderiv ℝ ψ x‖ ^ 2) := by
  have hlocal : (∫ x in Metric.ball center R, ‖fderiv ℝ ψ x‖ ^ 2) ≤
      (∫ x, ‖fderiv ℝ ψ x‖ ^ 2) :=
    MeasureTheory.setIntegral_le_integral hgrad
      (Filter.Eventually.of_forall (fun x => sq_nonneg (‖fderiv ℝ ψ x‖)))
  have hpositive : 0 ≤ (∫ x, ‖ψ x‖ ^ 2) :=
    MeasureTheory.integral_nonneg (fun x => sq_nonneg (‖ψ x‖))
  linarith

end ReyesMath.E68
