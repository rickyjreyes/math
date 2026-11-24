import Mathlib

/-!
# GC21: affine canonical momentum obstruction (exact finite-dimensional statement)

A regular higher-time-derivative Legendre transform has an Ostrogradsky
momentum that enters the reduced canonical Hamiltonian affinely. This module
isolates the corresponding elementary but unconditional algebraic obstruction:
a nonzero coefficient of an unrestricted real canonical momentum prevents
a lower bound.

This does NOT classify all higher-derivative Lagrangians or prove that every
constrained or degenerate parent theory has a ghost. In particular, a physical
constraint can remove the unrestricted momentum assumed here.
-/

namespace ReyesMath
namespace GC21

/-- A fixed-slice Hamiltonian with an unrestricted linear canonical momentum. -/
def affineMomentumHamiltonian (velocity remainder momentum : ℝ) : ℝ :=
  velocity * momentum + remainder

/-- Every lower bound can be violated when the canonical velocity is nonzero. -/
theorem affine_unbounded_below (velocity remainder : ℝ)
    (hv : velocity ≠ 0) (threshold : ℝ) :
    ∃ momentum : ℝ,
      affineMomentumHamiltonian velocity remainder momentum < threshold := by
  refine ⟨(threshold - remainder - 1) / velocity, ?_⟩
  have hcancel :
      velocity * ((threshold - remainder - 1) / velocity) =
        threshold - remainder - 1 := by
    field_simp [hv]
  dsimp [affineMomentumHamiltonian]
  linarith

/-- The same fixed slice is unbounded above. -/
theorem affine_unbounded_above (velocity remainder : ℝ)
    (hv : velocity ≠ 0) (threshold : ℝ) :
    ∃ momentum : ℝ,
      threshold < affineMomentumHamiltonian velocity remainder momentum := by
  refine ⟨(threshold - remainder + 1) / velocity, ?_⟩
  have hcancel :
      velocity * ((threshold - remainder + 1) / velocity) =
        threshold - remainder + 1 := by
    field_simp [hv]
  dsimp [affineMomentumHamiltonian]
  linarith

/-- A globally lower-bounded unrestricted affine-momentum slice exists
    exactly when its linear momentum coefficient vanishes. -/
theorem affine_bounded_below_iff (velocity remainder : ℝ) :
    (∃ lower : ℝ, ∀ momentum : ℝ,
      lower ≤ affineMomentumHamiltonian velocity remainder momentum) ↔
      velocity = 0 := by
  constructor
  · rintro ⟨lower, hbound⟩
    by_contra hv
    obtain ⟨momentum, hlt⟩ :=
      affine_unbounded_below velocity remainder hv lower
    exact (not_lt_of_ge (hbound momentum)) hlt
  · intro hv
    refine ⟨remainder, ?_⟩
    intro momentum
    simp [affineMomentumHamiltonian, hv]

/-- Likewise, a globally upper-bounded unrestricted affine-momentum slice
    exists exactly when the coefficient vanishes. -/
theorem affine_bounded_above_iff (velocity remainder : ℝ) :
    (∃ upper : ℝ, ∀ momentum : ℝ,
      affineMomentumHamiltonian velocity remainder momentum ≤ upper) ↔
      velocity = 0 := by
  constructor
  · rintro ⟨upper, hbound⟩
    by_contra hv
    obtain ⟨momentum, hlt⟩ :=
      affine_unbounded_above velocity remainder hv upper
    exact (not_lt_of_ge (hbound momentum)) hlt
  · intro hv
    refine ⟨remainder, ?_⟩
    intro momentum
    simp [affineMomentumHamiltonian, hv]

end GC21
end ReyesMath
