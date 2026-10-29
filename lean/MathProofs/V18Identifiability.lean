import MathProofs.V18Rank
import MathProofs.LocalLevelSet

/-!
# F09: exact derivative rank and C¹ local non-identifiability

The fiber statement below is the ambient-chart formulation of a C¹ embedded
submanifold. Its chart and inverse are C¹ on open sets; its image is exactly
the vertical slice with the eleven observed outputs fixed. The fiber
coordinate space is the kernel of the actual observation derivative, of
dimension twenty. This concerns the open ambient parameter space, including
the specified center epsilon = 5, not an optimizer's closed constraint box.
-/

noncomputable section
namespace ReyesMath.V18Forward
open Filter
open scoped Topology

/-- Precise local coordinate statement for the actual nonlinear fiber.
The model space is the kernel of its actual Fréchet derivative. -/
def HasTwentyDimensionalLocalFiber (alpha : ℝ) : Prop :=
  Module.finrank ℝ (LinearMap.ker (jacobian (frozen alpha 5)).toLinearMap) = 20 ∧
  ∃ e : PartialHomeomorph Params
      ((Fin 11 → ℝ) × LinearMap.ker (jacobian (frozen alpha 5)).toLinearMap),
    frozen alpha 5 ∈ e.source ∧ e (frozen alpha 5) = (observed (frozen alpha 5), 0) ∧
    ContDiffOn ℝ 1 e e.source ∧ ContDiffOn ℝ 1 e.symm e.target ∧
    (∀ p, (e p).1 = observed p) ∧
    e '' {p | p ∈ e.source ∧ observed p = observed (frozen alpha 5)} =
      {y | y ∈ e.target ∧ y.1 = observed (frozen alpha 5)}

theorem observed_local_level_set (alpha : ℝ) (ha : 0 ≤ alpha) :
    HasTwentyDimensionalLocalFiber alpha := by
  have hd : HasFDerivAt observed (jacobian (frozen alpha 5)) (frozen alpha 5) := by
    rw [jacobian_frozen_eq alpha ha]
    exact hasFDerivAt_observed_frozen alpha ha
  obtain ⟨e, he, he0, hce, hci, hef⟩ :=
    exists_c1_level_set_chart observed (frozen alpha 5) (jacobian (frozen alpha 5))
      (contDiffAt_observed_frozen alpha ha) hd (jacobian_surjective alpha ha)
  exact ⟨jacobian_nullity alpha ha, e, he, he0, hce, hci, hef,
    level_set_chart_image observed (frozen alpha 5) e hef⟩

/-- Genuine nonlinear local non-identifiability, stronger than a vanishing
first directional derivative. Every ambient neighborhood contains another
parameter vector with exactly the same eleven observations. -/
theorem observed_locally_nonidentifiable (alpha : ℝ) (ha : 0 ≤ alpha)
    (U : Set Params) (hU : U ∈ 𝓝 (frozen alpha 5)) :
    ∃ p ∈ U, p ≠ frozen alpha 5 ∧ observed p = observed (frozen alpha 5) := by
  obtain ⟨hdim, e, he, he0, _, _, hef, _⟩ := observed_local_level_set alpha ha
  letI : Nontrivial (LinearMap.ker (jacobian (frozen alpha 5)).toLinearMap) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  exact level_set_not_isolated observed (frozen alpha 5) e he he0 hef U hU

/-- The complete F09 theorem chain, under the manuscript's alpha interval.
No determinant, rank, clipping branch, or regularity assumption is supplied
by the caller. All of these refer to the original 31-parameter clipped map. -/
theorem f09_completion (alpha : ℝ) (ha : alpha ∈ Set.Icc 5.172 5.173) :
    ((18000000 : ℝ) < V18MiddleJacobian.middle.det ∧
      V18MiddleJacobian.middle.det < 24000000) ∧
    HasFDerivAt observed (observedD (frozen alpha 5)) (frozen alpha 5) ∧
    (∀ᶠ p in 𝓝 (frozen alpha 5), HasFDerivAt observed (observedD p) p) ∧
    (selectedMinor (frozen alpha 5)).det ≠ 0 ∧
    Module.finrank ℝ (LinearMap.range (jacobian (frozen alpha 5)).toLinearMap) = 11 ∧
    Module.finrank ℝ (LinearMap.ker (jacobian (frozen alpha 5)).toLinearMap) = 20 ∧
    Function.Surjective (jacobian (frozen alpha 5)) ∧
    HasTwentyDimensionalLocalFiber alpha := by
  have h : 0 ≤ alpha := by linarith [ha.1]
  exact ⟨V18MiddleJacobian.middle_det_bounds,
    hasFDerivAt_observed_frozen alpha h, hasFDerivAt_observed_near_frozen alpha h,
    selectedMinor_det_ne_zero alpha h, jacobian_rank alpha h, jacobian_nullity alpha h,
    jacobian_surjective alpha h, observed_local_level_set alpha h⟩

end ReyesMath.V18Forward
