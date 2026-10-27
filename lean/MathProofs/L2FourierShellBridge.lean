import Mathlib
import MathProofs.SphereNull
import MathProofs.SobolevH2

/-!
# L² Fourier-shell exclusion: Plancherel bridge

Mathlib v4.23.0 (the repository-pinned release) does not yet contain
the later `Analysis/Fourier/LpSpace.lean` isometric L² Fourier equivalence.
For any supplied complex-linear L² Fourier isometric equivalence, a
state whose transformed representative is supported on a sphere is zero.

This is an exact infinite-dimensional L² theorem for a supplied Fourier
operator.  The canonical Plancherel transform, built from Schwartz-space
density and identified with the Fourier integral on `L¹ ∩ L²`, and the full
F10 theorem are in `MathProofs.FourierShellL2`.
-/

namespace ReyesMath

open MeasureTheory Metric

/-- A Plancherel isometry excludes nonzero L² states concentrated on
a single zero-measure frequency sphere. -/
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
