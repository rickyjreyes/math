import Mathlib

/-!
# Intrinsic scalar-gradient obstruction (coordinate-free fiberwise form)

The input derivatives here are genuine linear covectors on an arbitrary
real tangent vector space V, not coordinate arrays.  For an arbitrary
family of four-dimensional tangent spaces, the conclusions hold at
every point without selecting a chart.

This module proves the coordinate-independent *algebraic obstruction*.
Constructing the differential from a globally smooth manifold map and
a smooth section of the covariant tensor bundle is a separate
differential-geometric integration task.
-/

namespace ReyesMath
namespace IntrinsicScalarMetric

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The two real scalar differentials assembled into a linear map. -/
def differentialPair (da db : V →ₗ[ℝ] ℝ) : V →ₗ[ℝ] ℝ × ℝ where
  toFun v := (da v, db v)
  map_add' x y := by
    ext <;> simp
  map_smul' c v := by
    ext <;> simp

/-- The intrinsic positive-sign tensor built from two scalar covectors. -/
def tensor (da db : V →ₗ[ℝ] ℝ) (v w : V) : ℝ :=
  da v * da w + db v * db w

/-- Its evaluation on any tangent vector is a sum of two real squares. -/
theorem tensor_nonnegative (da db : V →ₗ[ℝ] ℝ) (v : V) :
    0 ≤ tensor da db v v := by
  unfold tensor
  positivity

/-- Every vector annihilated by the two scalar differentials is a
null vector of the induced bilinear tensor. -/
theorem tensor_zero_of_pair_kernel (da db : V →ₗ[ℝ] ℝ) (v w : V)
    (hv : differentialPair da db v = 0) :
    tensor da db v w = 0 := by
  have ha : da v = 0 := congrArg Prod.fst hv
  have hb : db v = 0 := congrArg Prod.snd hv
  simp [tensor, ha, hb]

variable [FiniteDimensional ℝ V]

/-- A pair of scalar covectors carries at most two independent
tangent directions into its value space. -/
theorem differential_pair_range_dim_le_two (da db : V →ₗ[ℝ] ℝ) :
    Module.finrank ℝ (LinearMap.range (differentialPair da db)) ≤ 2 := by
  calc
    Module.finrank ℝ (LinearMap.range (differentialPair da db))
        ≤ Module.finrank ℝ (ℝ × ℝ) := Submodule.finrank_le _
    _ = 2 := by simp

/-- In four dimensions the induced tensor has a null subspace of
dimension at least two, intrinsically and independently of charts. -/
theorem four_dimensional_kernel_bound (da db : V →ₗ[ℝ] ℝ)
    (hV : Module.finrank ℝ V = 4) :
    2 ≤ Module.finrank ℝ (LinearMap.ker (differentialPair da db)) := by
  have hr := differential_pair_range_dim_le_two da db
  have hdim := LinearMap.finrank_range_add_finrank_ker (differentialPair da db)
  omega

/-- Every four-dimensional tangent fiber has two or more null directions
and a nonnegative quadratic form, for arbitrary globally supplied
differential covectors. This statement is independent of a trivialization. -/
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
