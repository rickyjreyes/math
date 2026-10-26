import Mathlib

/-!
# Structural local identifiability for nonlinear observation maps

The derivative of ANY differentiable map from 31 real coefficient
coordinates into 11 real observables has at least 20 kernel dimensions.
The computed numerical rank of a particular physical model is not claimed.
-/

namespace ReyesMath

/-- The precise linearized local identifiability obstruction, stated
for the Fréchet derivative of a nonlinear differentiable observation map.
This makes no global non-identifiability claim. -/
theorem differential_local_identifiability_obstruction
    (f : (Fin 31 → ℝ) → (Fin 11 → ℝ))
    (x : Fin 31 → ℝ)
    (J : (Fin 31 → ℝ) →L[ℝ] (Fin 11 → ℝ))
    (_hder : HasFDerivAt f J x) :
    20 ≤ Module.finrank ℝ (LinearMap.ker J.toLinearMap) := by
  have hrange :
      Module.finrank ℝ (LinearMap.range J.toLinearMap) ≤ 11 := by
    calc
      Module.finrank ℝ (LinearMap.range J.toLinearMap)
          ≤ Module.finrank ℝ (Fin 11 → ℝ) := Submodule.finrank_le _
      _ = 11 := by simp
  have hnull :=
    LinearMap.finrank_range_add_finrank_ker J.toLinearMap
  have hdomain : Module.finrank ℝ (Fin 31 → ℝ) = 31 := by simp
  omega

end ReyesMath
