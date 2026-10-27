import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import MathProofs.IntrinsicScalarMetric

/-!
# Actual scalar differentials on a smooth four-manifold (F08)

This constructs the positive-sign tensor directly from the manifold
differential of a globally defined complex scalar (two real components).
It is a genuine intrinsic family of bilinear forms on tangent fibers,
not a coordinate-matrix surrogate. The chain rule proves naturality
under differentiable coordinate changes, and the rank/nullity and
signature obstructions hold at every differentiability point.

A proof that this family is a smooth section of the symmetric covariant
2-tensor bundle for C¹ or smoother scalar fields remains a separate
regularity/interface obligation; none of the pointwise obstructions
requires this additional smoothness.
-/

namespace ReyesMath
namespace GlobalScalarTensor

open ChartedSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin 4 → ℝ) M]

private abbrev I4 : ModelWithCorners ℝ (Fin 4 → ℝ) (Fin 4 → ℝ) :=
  𝓘(ℝ, Fin 4 → ℝ)

private abbrev IR : ModelWithCorners ℝ ℝ ℝ :=
  𝓘(ℝ, ℝ)

/-- The real differential of an actual globally defined complex scalar. -/
noncomputable def da (ψ : M → ℂ) (p : M) :
    TangentSpace I4 p →L[ℝ] ℝ :=
  mfderiv I4 IR (fun x : M => (ψ x).re) p

/-- The imaginary differential of an actual globally defined complex scalar. -/
noncomputable def db (ψ : M → ℂ) (p : M) :
    TangentSpace I4 p →L[ℝ] ℝ :=
  mfderiv I4 IR (fun x : M => (ψ x).im) p

/-- The globally defined, intrinsically covariant scalar gradient tensor. -/
noncomputable def g (ψ : M → ℂ) (p : M)
    (v w : TangentSpace I4 p) : ℝ :=
  da ψ p v * da ψ p w + db ψ p v * db ψ p w

theorem g_eq_intrinsic (ψ : M → ℂ) (p : M) (v w : TangentSpace I4 p) :
    g ψ p v w =
      IntrinsicScalarMetric.tensor (da ψ p).toLinearMap (db ψ p).toLinearMap v w :=
  rfl

theorem g_symmetric (ψ : M → ℂ) (p : M) (v w : TangentSpace I4 p) :
    g ψ p v w = g ψ p w v := by
  rw [g_eq_intrinsic, g_eq_intrinsic]
  exact IntrinsicScalarMetric.tensor_symmetric _ _ _ _

theorem g_nonnegative (ψ : M → ℂ) (p : M) (v : TangentSpace I4 p) :
    0 ≤ g ψ p v v := by
  rw [g_eq_intrinsic]
  exact IntrinsicScalarMetric.tensor_nonnegative _ _ _

/-- The derivative pair has a two-dimensional or larger common kernel
on each four-dimensional tangent fiber. -/
theorem kernel_dimension (ψ : M → ℂ) (p : M) :
    2 ≤ Module.finrank ℝ
      (LinearMap.ker (IntrinsicScalarMetric.differentialPair
        (da ψ p).toLinearMap (db ψ p).toLinearMap)) := by
  exact IntrinsicScalarMetric.four_dimensional_kernel_bound
    (da ψ p).toLinearMap (db ψ p).toLinearMap (by simp [I4])

/-- Every four-manifold point has a positive-semidefinite tensor with at
least two independent null directions. This theorem uses the *actual*
manifold derivatives of a single scalar. -/
theorem manifold_obstruction (ψ : M → ℂ) :
    ∀ p : M,
      (∀ v : TangentSpace I4 p, 0 ≤ g ψ p v v) ∧
      2 ≤ Module.finrank ℝ
        (LinearMap.ker (IntrinsicScalarMetric.differentialPair
          (da ψ p).toLinearMap (db ψ p).toLinearMap)) := by
  intro p
  exact ⟨g_nonnegative ψ p, kernel_dimension ψ p⟩

/-- Naturality under arbitrary differentiable maps between four-manifolds.
In particular, a diffeomorphism changes the coordinates but does not
change the underlying scalar tensor. -/
theorem g_natural
    {N : Type*} [TopologicalSpace N] [ChartedSpace (Fin 4 → ℝ) N]
    (f : N → M) (ψ : M → ℂ) (q : N)
    (hf : MDifferentiableAt I4 I4 f q)
    (ha : MDifferentiableAt I4 IR (fun x : M => (ψ x).re) (f q))
    (hb : MDifferentiableAt I4 IR (fun x : M => (ψ x).im) (f q))
    (v w : TangentSpace I4 q) :
    g (ψ ∘ f) q v w =
      g ψ (f q) (mfderiv I4 I4 f q v) (mfderiv I4 I4 f q w) := by
  have hda : da (ψ ∘ f) q =
      (da ψ (f q)).comp (mfderiv I4 I4 f q) := by
    unfold da
    exact mfderiv_comp ha hf
  have hdb : db (ψ ∘ f) q =
      (db ψ (f q)).comp (mfderiv I4 I4 f q) := by
    unfold db
    exact mfderiv_comp hb hf
  simp only [g, hda, hdb, ContinuousLinearMap.comp_apply]

end GlobalScalarTensor
end ReyesMath
