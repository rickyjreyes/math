import Mathlib
import MathProofs.M6BJetSmooth
import MathProofs.M6BLimit

/-!
# M6B: nonuniqueness of the exact smooth regularized closure

All structural axioms of the manuscript are quantified over the full
continuum of complex jets. The family contains canonical parameter
λ=0 and a different admissible λ=1 member, indeed all λ≥0.
-/

noncomputable section
namespace ReyesMath.M6B

/-- Every λ≥0 is admissible: the jet operator is C∞, denominator
strictly positive at every complex value, nodes are safe, global
constant unit complex phases cancel and the full complex quotient
converges to -Δψ/ψ off nodes. -/
theorem every_closure_is_admissible (ε α S : ℝ)
    (hε : 0 < ε) (hS : 0 < S) :
    ∀ lam : ℝ, 0 ≤ lam →
      ContDiff ℝ ⊤ (fun p : ℂ × ℂ =>
        curvature ε α lam S p.1 p.2) ∧
      (∀ s : ℝ, 0 ≤ s → 0 < denominator ε α lam S s) ∧
      denominator ε α lam S 0 = ε ^ 2 ∧
      (∀ w : ℂ, curvature ε α lam S 0 w = 0) ∧
      (∀ u z w : ℂ, ‖u‖ = 1 →
        curvature ε α lam S (u * z) (u * w) =
          curvature ε α lam S z w) ∧
      (∀ z w : ℂ, z ≠ 0 →
        Filter.Tendsto (fun δ : ℝ => curvature δ α lam S z w)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds (-(w / z)))) := by
  intro lam hlam
  exact ⟨curvature_contDiff ε α lam S hε hlam hS,
    fun s hs => denominator_pos ε α lam S s hε hlam hS hs,
    denominator_at_node ε α lam S,
    fun w => curvature_at_node ε α lam S w,
    fun u z w hu => curvature_phase_invariant ε α lam S u z w hu,
    fun z w hz => curvature_downarrow_zero α lam S z w hz⟩

/-- The canonical λ=0 and alternative λ=1 are genuinely distinct
constitutive maps, not merely differently named denominator formulas.
Both satisfy all the enumerated structural axioms. -/
theorem two_distinct_admissible_closures (ε α S : ℝ)
    (hε : 0 < ε) (hS : 0 < S) :
    ContDiff ℝ ⊤ (fun p : ℂ × ℂ =>
      curvature ε α 0 S p.1 p.2) ∧
    ContDiff ℝ ⊤ (fun p : ℂ × ℂ =>
      curvature ε α 1 S p.1 p.2) ∧
    curvature ε α 0 S 1 1 ≠ curvature ε α 1 S 1 1 := by
  exact ⟨curvature_contDiff ε α 0 S hε (by norm_num) hS,
    curvature_contDiff ε α 1 S hε (by norm_num) hS,
    curvature_family_pairwise_distinct ε α S 0 1 hε hS (by norm_num)⟩

/-- Infinitely many pairwise distinct regularizations are represented
by the natural-number subfamily of the actual continuum of λ values. -/
theorem infinitely_many_distinct_closures (ε α S : ℝ)
    (hε : 0 < ε) (hS : 0 < S) :
    Set.Infinite (Set.range
      (fun k : ℕ => (fun p : ℂ × ℂ =>
        curvature ε α (k : ℝ) S p.1 p.2))) := by
  apply Set.infinite_range_of_injective
  intro k l h
  have heq : curvature ε α (k : ℝ) S 1 1 =
      curvature ε α (l : ℝ) S 1 1 := by
    exact congrArg (fun f : ℂ × ℂ → ℂ => f (1, 1)) h
  have hcast : (k : ℝ) = (l : ℝ) := by
    by_contra hne
    exact curvature_family_pairwise_distinct ε α S
      (k : ℝ) (l : ℝ) hε hS hne heq
  exact_mod_cast hcast

end ReyesMath.M6B
