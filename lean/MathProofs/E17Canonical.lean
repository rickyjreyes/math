import MathProofs.M6BClosureTheorem
import MathProofs.M6BDimensionalField
import MathProofs.RemainingCores

/-!
# M2/E17: canonical regularized reciprocal, genuine complex C-infinity jet

The canonical corrected WCT operator is exactly the λ=0 member
of the previously kernel-checked M6B family, with S=1. This file
proves the parameter-matched identity and reuses the established
smoothness and singular-limit theorems for the original E17 operator.

These are genuine continuum complex-jet statements. The quantitative
uniform-away-from-nodes error, global multiplier bound and full
L² limit are separate manuscript obligations.
-/

noncomputable section
namespace ReyesMath
namespace E17Canonical

/-- Exactly the corrected denominator |z|² + ε² exp(-2α|z|²). -/
def denominator (ε α : ℝ) (z : ℂ) : ℝ :=
  M6B.denominator ε α 0 1 (Complex.normSq z)

/-- The original corrected E17 reciprocal, written as the λ=0
specialization of the already proved nonlinear complex-jet closure. -/
def reciprocal (ε α : ℝ) (z : ℂ) : ℂ :=
  -(M6B.curvature ε α 0 1 z 1)

/-- E17's corrected denominator agrees literally with the
independent symbolic positivity model in RemainingCores. -/
theorem denominator_eq_corrected (ε α : ℝ) (z : ℂ) :
    denominator ε α z = RemainingCores.correctedDenominator ε α z := by
  simp [denominator, M6B.denominator_canonical,
    RemainingCores.correctedDenominator, Complex.normSq_eq_norm_sq]

/-- The corrected denominator is positive at every complex field value. -/
theorem denominator_positive (ε α : ℝ) (z : ℂ) (hε : 0 < ε) :
    0 < denominator ε α z := by
  rw [denominator_eq_corrected]
  exact RemainingCores.correctedDenominator_pos ε α z hε

/-- Exactly the standard conjugate-over-modulus-squared formula,
including at field nodes where regularization keeps it defined. -/
theorem reciprocal_eq_explicit (ε α : ℝ) (z : ℂ) :
    reciprocal ε α z =
      (starRingEnd ℂ) z / ((denominator ε α z : ℝ) : ℂ) := by
  simp [reciprocal, denominator, M6B.curvature, neg_div]

/-- At a field node, the corrected reciprocal vanishes. -/
theorem reciprocal_at_node (ε α : ℝ) : reciprocal ε α 0 = 0 := by
  simp [reciprocal, M6B.curvature_at_node]

/-- The corrected regularized reciprocal is an actual smooth
map of the two real components of the complex field. -/
theorem reciprocal_contDiff (ε α : ℝ) (hε : 0 < ε) :
    ContDiff ℝ ⊤ (reciprocal ε α) := by
  have hjet : ContDiff ℝ ⊤
      (fun p : ℂ × ℂ => M6B.curvature ε α 0 1 p.1 p.2) :=
    M6B.curvature_contDiff ε α 0 1 hε (by norm_num) (by norm_num)
  have hp : ContDiff ℝ ⊤ (fun z : ℂ => (z, (1 : ℂ))) := by fun_prop
  have hcomp := hjet.comp hp
  simpa only [reciprocal, Function.comp_def] using hcomp.neg

/-- Exact pointwise singular-regularization limit off field nodes,
in the one-sided physical regime ε ↓ 0. -/
theorem reciprocal_downarrow_zero (α : ℝ) (z : ℂ) (hz : z ≠ 0) :
    Filter.Tendsto (fun ε : ℝ => reciprocal ε α z)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 / z)) := by
  have h := (M6B.curvature_downarrow_zero α 0 1 z 1 hz).neg
  simpa only [reciprocal, neg_neg] using h

/-- The canonical regularized curvature for an actual complex jet
is invariant under every global unit U(1) phase. -/
theorem curvature_phase_invariant (ε α : ℝ)
    (u z w : ℂ) (hu : ‖u‖ = 1) :
    M6B.curvature ε α 0 1 (u * z) (u * w) =
      M6B.curvature ε α 0 1 z w :=
  M6B.curvature_phase_invariant ε α 0 1 u z w hu

/-- The canonical exact quotient -Δψ/ψ is recovered off nodes. -/
theorem curvature_limit (α : ℝ) (z w : ℂ) (hz : z ≠ 0) :
    Filter.Tendsto
      (fun ε : ℝ => M6B.curvature ε α 0 1 z w)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (-(w / z))) :=
  M6B.curvature_downarrow_zero α 0 1 z w hz

/-- The original E17 phase-invariance property also holds for the
*actual Cartesian Laplacian* of every C² complex field on ℝᵈ. -/
theorem physical_curvature_phase_invariant (d : ℕ)
    (ψ : EuclideanSpace ℝ (Fin d) → ℂ)
    (hψ : ContDiff ℝ 2 ψ)
    (u : ℂ) (hu : ‖u‖ = 1)
    (ε α : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    M6B.fieldCurvatureD d ε α 0 1 (fun y => u * ψ y) x =
      M6B.fieldCurvatureD d ε α 0 1 ψ x :=
  M6B.fieldCurvatureD_phase_invariant d ψ hψ u hu ε α 0 1 x

/-- The corrected E17 curvature has the exact nonzero-field
singular-regulation limit for genuine d-dimensional Laplacians. -/
theorem physical_curvature_downarrow_zero (d : ℕ)
    (α : ℝ)
    (ψ : EuclideanSpace ℝ (Fin d) → ℂ)
    (x : EuclideanSpace ℝ (Fin d)) (hψx : ψ x ≠ 0) :
    Filter.Tendsto
      (fun ε : ℝ => M6B.fieldCurvatureD d ε α 0 1 ψ x)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (-(M6B.laplacianD d ψ x / ψ x))) :=
  M6B.fieldCurvatureD_downarrow_zero d α 0 1 ψ x hψx


end E17Canonical
end ReyesMath
