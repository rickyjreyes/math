import Mathlib
import MathProofs.ChartedScalarMetric

/-!
# Intrinsic scalar-gradient metric: tensor and chart covariance

A complex scalar differential at a point has two real linear covectors.
Their real positive-sign tensor is built directly on each tangent vector
space, without coordinates or a preferred chart.  The tensor is positive
semidefinite, annihilates the common kernel and has nullity at least two
on every four-dimensional tangent fiber.  Its definition is natural
under *any* invertible linear change of coordinates.

This is the global *fiberwise algebraic* obstruction. The covector
fields are supplied; construction as smooth sections of the cotangent
bundle from a global smooth complex function remains separate.
-/

namespace ReyesMath
namespace IntrinsicScalarMetric

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Assemble the two real scalar differentials into one linear map. -/
def differentialPair (da db : V →ₗ[ℝ] ℝ) : V →ₗ[ℝ] (ℝ × ℝ) where
  toFun v := (da v, db v)
  map_add' x y := by
    ext <;> simp
  map_smul' c v := by
    ext <;> simp

/-- The intrinsic positive-sign scalar-gradient tensor. -/
def tensor (da db : V →ₗ[ℝ] ℝ) (v w : V) : ℝ :=
  da v * da w + db v * db w

theorem tensor_symmetric (da db : V →ₗ[ℝ] ℝ) (v w : V) :
    tensor da db v w = tensor da db w v := by
  unfold tensor
  ring

/-- Coordinate-free positivity of the scalar-gradient tensor. -/
theorem tensor_nonnegative (da db : V →ₗ[ℝ] ℝ) (v : V) :
    0 ≤ tensor da db v v := by
  unfold tensor
  exact add_nonneg (mul_self_nonneg (da v)) (mul_self_nonneg (db v))

/-- Each vector annihilating both differentials is a tensor null vector. -/
theorem tensor_zero_of_pair_kernel (da db : V →ₗ[ℝ] ℝ) (v w : V)
    (hv : differentialPair da db v = 0) :
    tensor da db v w = 0 := by
  have ha : da v = 0 := congrArg Prod.fst hv
  have hb : db v = 0 := congrArg Prod.snd hv
  simp [tensor, ha, hb, differentialPair] at *

/-- Exact covariant transformation under an invertible frame change. -/
theorem tensor_change_frame {W : Type*} [AddCommGroup W] [Module ℝ W]
    (e : W ≃ₗ[ℝ] V) (da db : V →ₗ[ℝ] ℝ) (v w : W) :
    tensor (da.comp e.toLinearMap) (db.comp e.toLinearMap) v w =
      tensor da db (e v) (e w) := rfl

variable [FiniteDimensional ℝ V]

theorem differential_pair_range_dim_le_two (da db : V →ₗ[ℝ] ℝ) :
    Module.finrank ℝ (LinearMap.range (differentialPair da db)) ≤ 2 := by
  calc
    Module.finrank ℝ (LinearMap.range (differentialPair da db))
        ≤ Module.finrank ℝ (ℝ × ℝ) := Submodule.finrank_le _
    _ = 2 := by simp

/-- Intrinsic rank obstruction in a four-dimensional tangent space. -/
theorem four_dimensional_kernel_bound (da db : V →ₗ[ℝ] ℝ)
    (hV : Module.finrank ℝ V = 4) :
    2 ≤ Module.finrank ℝ (LinearMap.ker (differentialPair da db)) := by
  have hr := differential_pair_range_dim_le_two da db
  have hdim := LinearMap.finrank_range_add_finrank_ker (differentialPair da db)
  omega

/-- Global fiber family: no choice of a coordinate chart is involved. -/
theorem at_every_tangent_fiber
    {B : Type*} (T : B → Type*)
    [∀ p, AddCommGroup (T p)] [∀ p, Module ℝ (T p)]
    [∀ p, FiniteDimensional ℝ (T p)]
    (da db : (p : B) → T p →ₗ[ℝ] ℝ)
    (h4 : ∀ p, Module.finrank ℝ (T p) = 4) :
    ∀ p : B,
      (∀ v : T p, 0 ≤ tensor (da p) (db p) v v) ∧
      2 ≤ Module.finrank ℝ
        (LinearMap.ker (differentialPair (da p) (db p))) := by
  intro p
  exact ⟨tensor_nonnegative (da p) (db p),
    four_dimensional_kernel_bound (da p) (db p) (h4 p)⟩

end IntrinsicScalarMetric
end ReyesMath
