import Mathlib

/-!
# Algebraic certificates for higher-derivative model diagnostics

The exact S004 acceleration-Hessian determinant and the quadratic
dispersion discriminant are checked. This does NOT formalize Dirac constraint
classification, Ostrogradsky ghosts, dispersion convexity, or PDE evolution.
-/

namespace ReyesMath

/-- The two-real-component acceleration Hessian in the regular nonzero
fixed-background S004 scalar sector. -/
def s004AccelerationHessian (κ F : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => if i = j then -2 * κ * F else 0

/-- The physical acceleration Hessian has determinant 4 κ² F². -/
theorem s004_acceleration_hessian_det (κ F : ℝ) :
    (s004AccelerationHessian κ F).det = 4 * κ ^ 2 * F ^ 2 := by
  simp [s004AccelerationHessian, Matrix.det_fin_two]
  ring

/-- If both parameters are positive, the acceleration Hessian is
nondegenerate (nonzero determinant). -/
theorem s004_acceleration_hessian_det_pos
    (κ F : ℝ) (hκ : 0 < κ) (hF : 0 < F) :
    0 < (s004AccelerationHessian κ F).det := by
  rw [s004_acceleration_hessian_det]
  positivity

/-- The radicand used for the exact quadratic dispersion branches is
the discriminant of the original equation, with no approximations. -/
theorem dispersion_discriminant_identity (K G T mass q : ℝ) :
    (1 + (2 * K + G) * q) ^ 2 -
        4 * K * (mass ^ 2 + q + (K + G + T) * q ^ 2) =
      (1 - 4 * K * mass ^ 2) +
        2 * G * q - (4 * K * T - G ^ 2) * q ^ 2 := by
  ring

end ReyesMath
