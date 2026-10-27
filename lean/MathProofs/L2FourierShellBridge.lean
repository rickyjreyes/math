import Mathlib
import MathProofs.SphereNull
import MathProofs.SobolevH2

/-!
# Fourier-shell exclusion on L²: explicit Plancherel bridge

The pinned Mathlib v4.23.0 release does not yet ship the L² Fourier
linear isometry equivalence that was subsequently introduced in
Mathlib.Analysis.Fourier.LpSpace.

Here the theorem is formulated for ANY specified complex-linear
isometric Fourier realization on genuine L²(ℝ^d; ℂ).  This proves the
measure-theoretic/exact inverse step, and cleanly isolates the remaining
construction and identification of the canonical L² Fourier transform.

This is a conditional bridge, not an end-to-end Fourier formalization.
-/

namespace ReyesMath

open MeasureTheory Metric

/-- A Plancherel Fourier realization cannot have a nonzero L² state
whose transformed representative is supported on one null sphere. -/
theorem l2_fourier_shell_no_bound_state_of_isometry
    (d : ℕ) (k : ℝ)
    (F₂ : Sobolev.L2 (d + 1) ≃ₗᵢ[ℂ] Sobolev.L2 (d + 1))
    (u : Sobolev.L2 (d + 1))
    (hsupport : ∀ ξ : EuclideanSpace ℝ (Fin (d + 1)),
      ξ ∉ sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) k →
        (F₂ u : EuclideanSpace ℝ (Fin (d + 1)) → ℂ) ξ = 0) :
    u = 0 := by
  have hFourierZero :
      (F₂ u : EuclideanSpace ℝ (Fin (d + 1)) → ℂ) =ᵐ[volume]
        (fun _ => 0) :=
    euclidean_frequency_shell_ae_zero d k (⇑(F₂ u)) hsupport
  have hZero : F₂ u = 0 :=
    (Lp.eq_zero_iff_ae_eq_zero).2 hFourierZero
  exact F₂.injective (by simpa using hZero)

end ReyesMath
