import MathProofs.LocalIdentifiability

/-!
# Full-row-rank refinement of the 31-to-11 sensitivity theorem (F09)

The main F09 theorem, nullity >= 20 for any 11-observable / 31-parameter
differentiable model, is formalized in LocalIdentifiability. This file
formalizes the manuscript's exact-nullity corollary if the *actual*
Jacobian has full row rank. It is conditional on verified surjectivity:
the separate source-pinned interval determinant checker verifies that
condition for the frozen v18 fit computationally, but the transcendental
Jacobian determinant has not yet been re-proved inside Lean.
-/

namespace ReyesMath

/-- Corollary: full row rank of an actual 31-to-11 Fréchet derivative
implies its linearized parameter nullspace is exactly 20-dimensional. -/
theorem exact_sensitivity_nullity_of_full_row_rank
    (F : (Fin 31 → ℝ) → (Fin 11 → ℝ))
    (θ : Fin 31 → ℝ)
    (J : (Fin 31 → ℝ) →L[ℝ] (Fin 11 → ℝ))
    (_hF : HasFDerivAt F J θ)
    (hfull : Function.Surjective J) :
    Module.finrank ℝ (LinearMap.ker J.toLinearMap) = 20 := by
  have hR : LinearMap.range J.toLinearMap = ⊤ :=
    LinearMap.range_eq_top.mpr hfull
  have hr : Module.finrank ℝ (LinearMap.range J.toLinearMap) = 11 := by
    rw [hR]
    simp
  have hdim := LinearMap.finrank_range_add_finrank_ker J.toLinearMap
  have hdomain : Module.finrank ℝ (Fin 31 → ℝ) = 31 := by simp
  omega

/-- The exact 20-dimensional conclusion combined with the
unconditional >=20 obstruction, in the same coordinates. -/
theorem sensitivity_rank_nullity_dichotomy
    (F : (Fin 31 → ℝ) → (Fin 11 → ℝ))
    (θ : Fin 31 → ℝ)
    (J : (Fin 31 → ℝ) →L[ℝ] (Fin 11 → ℝ))
    (hF : HasFDerivAt F J θ) :
    20 ≤ Module.finrank ℝ (LinearMap.ker J.toLinearMap) ∧
    (Function.Surjective J →
      Module.finrank ℝ (LinearMap.ker J.toLinearMap) = 20) := by
  exact ⟨differential_local_identifiability_obstruction F θ J hF,
    fun h => exact_sensitivity_nullity_of_full_row_rank F θ J hF h⟩

end ReyesMath
