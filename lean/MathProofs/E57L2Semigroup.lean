import MathProofs.FourierMultiplierL2
import MathProofs.E57WholeSpaceDamping
import MathProofs.E57SemigroupSymbol

/-!
# E57: exact whole-space L² Fourier semigroup law

This module upgrades the pointwise shell-damping composition identity to an
identity of bounded continuous linear maps on the *actual* Plancherel L² space.
The Fourier multiplier is constructed with the repository's unitary Fourier
equivalence, and its defining symbol uses the pinned frequency normalization.

The generated semigroup identity is independent of a choice of representatives
of the L² equivalence classes. This is the operator-composition part of the
E57 manuscript; it does not, by itself, establish generator-domain
identification or strong continuity.
-/

open MeasureTheory

noncomputable section

namespace ReyesMath
namespace E57L2Semigroup

open E57WholeSpaceDamping E57SemigroupSymbol RemainingCores

variable {d : ℕ}
local notation "Rd" => EuclideanSpace ℝ (Fin d)

/-- The genuine bounded whole-space Fourier-shell evolution at time t ≥ 0. -/
def S (a kStar t : ℝ) (ha : 0 ≤ a) (ht : 0 ≤ t) :
    Sobolev.L2 d →L[ℂ] Sobolev.L2 d :=
  (Sobolev.fourierL2 (d := d)).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((SpectralConc.mulL2 (symbol a t kStar)
      (symbol_measurable a t kStar).aestronglyMeasurable
      (symbol_norm_le_one a t kStar ha ht)).comp
      (Sobolev.fourierL2 (d := d)).toContinuousLinearEquiv.toContinuousLinearMap)

/-- Fourier characterisation of the bounded operator, including L² classes. -/
theorem fourier_S (a kStar t : ℝ) (ha : 0 ≤ a) (ht : 0 ≤ t)
    (f : Sobolev.L2 d) :
    (Sobolev.fourierL2 (S a kStar t ha ht f) : Rd → ℂ) =ᵐ[volume]
      fun ξ => symbol a t kStar ξ * Sobolev.fourierL2 f ξ :=
by
  change (Sobolev.fourierL2
      ((Sobolev.fourierL2).symm
        (SpectralConc.mulL2 (symbol a t kStar)
          (symbol_measurable a t kStar).aestronglyMeasurable
          (symbol_norm_le_one a t kStar ha ht) (Sobolev.fourierL2 f))) : Rd → ℂ) =ᵐ[volume] _
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact SpectralConc.coeFn_mulL2
    (symbol_measurable a t kStar).aestronglyMeasurable
    (symbol_norm_le_one a t kStar ha ht) (Sobolev.fourierL2 f)

theorem symbol_at_zero (a kStar : ℝ) (ξ : Rd) :
    symbol a 0 kStar ξ = 1 := by
  change ((shellDamping a 0 kStar (Sobolev.qS ξ) : ℝ) : ℂ) = 1
  rw [damping_at_zero_time]
  norm_num

theorem symbol_add (a kStar s t : ℝ) (ξ : Rd) :
    symbol a (s + t) kStar ξ =
      symbol a s kStar ξ * symbol a t kStar ξ := by
  change ((shellDamping a (s + t) kStar (Sobolev.qS ξ) : ℝ) : ℂ) =
    (shellDamping a s kStar (Sobolev.qS ξ) : ℂ) *
      (shellDamping a t kStar (Sobolev.qS ξ) : ℂ)
  rw [damping_semigroup]
  push_cast
  rfl

/-- The zero-time operator is exactly the identity map on physical L². -/
theorem S_zero (a kStar : ℝ) (ha : 0 ≤ a) :
    S (d := d) a kStar 0 ha le_rfl = ContinuousLinearMap.id ℂ (Sobolev.L2 d) := by
  apply ContinuousLinearMap.ext
  intro f
  apply (Sobolev.fourierL2 (d := d)).injective
  change Sobolev.fourierL2 (S a kStar 0 ha le_rfl f) = Sobolev.fourierL2 f
  apply Lp.ext
  filter_upwards [fourier_S a kStar 0 ha le_rfl f] with ξ hξ
  simpa [symbol_at_zero] using hξ

/-- On physical L², the flow at s+t is composition of the two flows.
This is an operator equality, not merely a pointwise scalar identity. -/
theorem S_add (a kStar s t : ℝ) (ha : 0 ≤ a)
    (hs : 0 ≤ s) (ht : 0 ≤ t) :
    S (d := d) a kStar (s + t) ha (add_nonneg hs ht) =
      (S a kStar s ha hs).comp (S a kStar t ha ht) := by
  apply ContinuousLinearMap.ext
  intro f
  apply (Sobolev.fourierL2 (d := d)).injective
  change Sobolev.fourierL2 (S a kStar (s + t) ha (add_nonneg hs ht) f) =
    Sobolev.fourierL2 (S a kStar s ha hs (S a kStar t ha ht f))
  apply Lp.ext
  filter_upwards
    [fourier_S a kStar (s + t) ha (add_nonneg hs ht) f,
     fourier_S a kStar s ha hs (S a kStar t ha ht f),
     fourier_S a kStar t ha ht f] with ξ hadd hsξ htξ
  calc
    (Sobolev.fourierL2 (S a kStar (s + t) ha (add_nonneg hs ht) f) : Rd → ℂ) ξ =
        symbol a (s + t) kStar ξ * Sobolev.fourierL2 f ξ := hadd
    _ = symbol a s kStar ξ * (symbol a t kStar ξ * Sobolev.fourierL2 f ξ) := by
      rw [symbol_add]
      ring
    _ = (Sobolev.fourierL2 (S a kStar s ha hs (S a kStar t ha ht f)) : Rd → ℂ) ξ := by
      rw [hsξ, htξ]

end E57L2Semigroup
end ReyesMath
