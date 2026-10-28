import Mathlib

/-!
# M6B: exact regularized curvature at a complex two-jet

The second jet of a C² complex field at a point is represented by the
value `z` and the value `w = Δψ`.  This is the *actual* pointwise
nonlinear expression from the manuscript, not a substitute polynomial.

These lemmas establish strict denominator positivity, behavior at nodes,
the canonical lam=0 specialization, global U(1) invariance, and identical
curvature for eigenjets of equal intensity.  The full C² Dirichlet,
mass-integral and smooth-operator nonuniqueness statements are separate
obligations; none is assumed here.
-/

noncomputable section

namespace ReyesMath.M6B

/-- The family of regularized M6B denominators, for intensity `s ≥ 0`. -/
def denominator (ε α lam S s : ℝ) : ℝ :=
  s + ε ^ 2 * Real.exp (-2 * α * s) * (1 + lam * s / (S + s))

/-- The exact nonlinear regularized curvature applied to the field value
and the Laplacian value of a complex field at a point. -/
def curvature (ε α lam S : ℝ) (z w : ℂ) : ℂ :=
  -(w * (starRingEnd ℂ) z) /
    ((denominator ε α lam S (Complex.normSq z) : ℝ) : ℂ)

/-- Positivity holds at every nonnegative intensity, with no sign
assumption on the exponential parameter α. -/
theorem denominator_pos (ε α lam S s : ℝ)
    (hε : 0 < ε) (hlam : 0 ≤ lam) (hS : 0 < S) (hs : 0 ≤ s) :
    0 < denominator ε α lam S s := by
  have hsum : 0 < S + s := by linarith
  have hfrac : 0 ≤ lam * s / (S + s) :=
    div_nonneg (mul_nonneg hlam hs) (le_of_lt hsum)
  have hfac : 0 < 1 + lam * s / (S + s) := by linarith
  have hbase : 0 < ε ^ 2 * Real.exp (-2 * α * s) := by positivity
  unfold denominator
  have hterm : 0 < ε ^ 2 * Real.exp (-2 * α * s) *
      (1 + lam * s / (S + s)) := mul_pos hbase hfac
  linarith

/-- The denominator at a node is exactly ε². -/
theorem denominator_at_node (ε α lam S : ℝ) :
    denominator ε α lam S 0 = ε ^ 2 := by
  simp [denominator]

/-- lam=0 gives the canonical manuscript denominator. -/
theorem denominator_canonical (ε α S s : ℝ) :
    denominator ε α 0 S s = s + ε ^ 2 * Real.exp (-2 * α * s) := by
  simp [denominator]

/-- The curvature image is zero at nodes, regardless of the Laplacian. -/
theorem curvature_at_node (ε α lam S : ℝ) (w : ℂ) :
    curvature ε α lam S 0 w = 0 := by
  simp [curvature]

/-- The pointwise denominator has the correct unregularized limit. -/
theorem denominator_unregularized_limit (α lam S s : ℝ) :
    Filter.Tendsto (fun ε : ℝ => denominator ε α lam S s)
      (nhds 0) (nhds s) := by
  have hc : Continuous (fun ε : ℝ => denominator ε α lam S s) := by
    unfold denominator
    fun_prop
  convert hc.continuousAt.tendsto using 1
  simp [denominator]

/-- Every constant unit complex phase leaves the curvature unchanged
provided it rotates both the value and the Laplacian. -/
theorem curvature_phase_invariant (ε α lam S : ℝ)
    (u z w : ℂ) (hu : ‖u‖ = 1) :
    curvature ε α lam S (u * z) (u * w) =
      curvature ε α lam S z w := by
  have husq : Complex.normSq u = 1 := by
    rw [Complex.normSq_eq_norm_sq, hu]
    norm_num
  have hnorm : Complex.normSq (u * z) = Complex.normSq z := by
    rw [Complex.normSq_mul, husq, one_mul]
  have hmul : (u * w) * (starRingEnd ℂ) (u * z) =
      w * (starRingEnd ℂ) z := by
    rw [map_mul]
    calc
      (u * w) * ((starRingEnd ℂ) u * (starRingEnd ℂ) z) =
          (u * (starRingEnd ℂ) u) * (w * (starRingEnd ℂ) z) := by ring
      _ = w * (starRingEnd ℂ) z := by
        rw [Complex.mul_conj']
        simp [hu]
  simp only [curvature, hnorm, hmul]

/-- The eigenjet equation w=-5z yields the same real curvature for any
two complex values with the same squared modulus. -/
theorem equal_intensity_eigenjets (ε α lam S : ℝ)
    (z₁ z₂ : ℂ) (h : Complex.normSq z₁ = Complex.normSq z₂) :
    curvature ε α lam S z₁ (-5 * z₁) =
      curvature ε α lam S z₂ (-5 * z₂) := by
  have eigen_formula (z : ℂ) :
      curvature ε α lam S z (-5 * z) =
        ((5 * Complex.normSq z : ℝ) : ℂ) /
          ((denominator ε α lam S (Complex.normSq z) : ℝ) : ℂ) := by
    unfold curvature
    calc
      -((-5 * z) * (starRingEnd ℂ) z) /
          ((denominator ε α lam S (Complex.normSq z) : ℝ) : ℂ) =
        (5 * (z * (starRingEnd ℂ) z)) /
          ((denominator ε α lam S (Complex.normSq z) : ℝ) : ℂ) := by ring
      _ = _ := by
        rw [Complex.mul_conj']
        push_cast
        rw [Complex.normSq_eq_norm_sq]
        push_cast
  rw [eigen_formula z₁, eigen_formula z₂, h]

/-- The family denominators are injectively parametrized by lam even
when examined at the single, physically admissible intensity s=1. -/
theorem denominator_injective_at_one (ε α S : ℝ)
    (hε : 0 < ε) (hS : 0 < S) :
    Function.Injective (fun lam : ℝ => denominator ε α lam S 1) := by
  intro lam μ heq
  have hs : S + 1 ≠ 0 := ne_of_gt (by linarith)
  have he : ε ^ 2 * Real.exp (-2 * α) ≠ 0 := ne_of_gt (by positivity)
  have hh : 1 + (ε ^ 2 * Real.exp (-2 * α)) *
        (1 + lam / (S + 1)) =
      1 + (ε ^ 2 * Real.exp (-2 * α)) *
        (1 + μ / (S + 1)) := by
    simpa [denominator] using heq
  have hm : (ε ^ 2 * Real.exp (-2 * α)) *
        (1 + lam / (S + 1)) =
      (ε ^ 2 * Real.exp (-2 * α)) *
        (1 + μ / (S + 1)) := add_left_cancel hh
  have hfac : 1 + lam / (S + 1) = 1 + μ / (S + 1) :=
    mul_left_cancel₀ he hm
  have hdiv : lam / (S + 1) = μ / (S + 1) := by linarith
  have hfinal := congrArg (fun a : ℝ => a * (S + 1)) hdiv
  field_simp [hs] at hfinal
  exact hfinal

/-- Actual curvature closures indexed by different lam give different
outputs already at the nonzero jet (ψ,Δψ)=(1,1). -/
theorem curvature_family_pairwise_distinct (ε α S lam μ : ℝ)
    (hε : 0 < ε) (hS : 0 < S) (hne : lam ≠ μ) :
    curvature ε α lam S 1 1 ≠ curvature ε α μ S 1 1 := by
  intro heq
  have hinv :
      (((denominator ε α lam S 1 : ℝ) : ℂ)⁻¹) =
        (((denominator ε α μ S 1 : ℝ) : ℂ)⁻¹) := by
    simpa [curvature, div_eq_mul_inv] using heq
  have hdenC : ((denominator ε α lam S 1 : ℝ) : ℂ) =
      ((denominator ε α μ S 1 : ℝ) : ℂ) := by
    have h := congrArg (fun z : ℂ => z⁻¹) hinv
    simpa using h
  have hdenR : denominator ε α lam S 1 =
      denominator ε α μ S 1 := by exact_mod_cast hdenC
  exact hne (denominator_injective_at_one ε α S hε hS hdenR)

end ReyesMath.M6B
