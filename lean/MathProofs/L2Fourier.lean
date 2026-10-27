import MathProofs.SobolevH2
import MathProofs.SphereNull

/-!
# Canonical Fourier transform on genuine L² equivalence classes

The actual Schwartz Fourier transform is extended by density and Parseval on
Mathlib v4.23.0. No Fourier equivalence or density assumption is supplied by
the caller. The dense domain carries the induced L² norm. The resulting
complex-linear isometric equivalence agrees with the Schwartz transform in
Mathlib's `2π` convention.
-/

noncomputable section
open MeasureTheory Filter Topology

namespace ReyesMath.L2Fourier
open Sobolev
variable {d : ℕ}
local notation "Rd" => EuclideanSpace ℝ (Fin d)

theorem toL2_injective : Function.Injective (toL2 (d := d)) := by
  intro f g h
  have hae : (f : Rd → ℂ) =ᵐ[volume] g :=
    (coeFn_toL2 f).symm.trans (h ▸ coeFn_toL2 g)
  exact DFunLike.ext' (MeasureTheory.Measure.eq_of_ae_eq hae f.continuous g.continuous)

/-- Schwartz functions with the inherited L² norm. -/
def schwartzRange (d : ℕ) : Submodule ℂ (L2 d) :=
  LinearMap.range (toL2 (d := d)).toLinearMap

/-- Density follows from the proved separation by Schwartz tests. -/
theorem schwartzRange_dense : Dense (schwartzRange d : Set (L2 d)) := by
  apply (dense_iff_closure_eq).2
  have htop : (schwartzRange d).topologicalClosure = ⊤ := by
    apply (Submodule.topologicalClosure_eq_top_iff).2
    apply le_antisymm ?_ bot_le
    intro w hw
    apply Submodule.mem_bot.2
    apply eq_zero_of_inner_schwartz
    intro f
    exact (Submodule.mem_orthogonal _ _).1 hw (toL2 f) ⟨f, rfl⟩
  calc
    closure (schwartzRange d : Set (L2 d)) =
        ((schwartzRange d).topologicalClosure : Set (L2 d)) := by
          exact (Submodule.topologicalClosure_coe _).symm
    _ = Set.univ := by rw [htop]; rfl


def schwartzEquiv : SchwartzMap Rd ℂ ≃ₗ[ℂ] schwartzRange d :=
  LinearEquiv.ofInjective toL2.toLinearMap toL2_injective

theorem fourier_schwartz_norm (f : SchwartzMap Rd ℂ) :
    ‖toL2 (SchwartzMap.fourierTransformCLE ℂ f)‖ = ‖toL2 f‖ := by
  have h : ‖toL2 (SchwartzMap.fourierTransformCLE ℂ f)‖ ^ 2 = ‖toL2 f‖ ^ 2 := by
    rw [norm_toL2_sq, norm_toL2_sq_fourier]
    rfl
  nlinarith [norm_nonneg (toL2 f), norm_nonneg (toL2 (SchwartzMap.fourierTransformCLE ℂ f))]

/-- Fourier transform on the dense Schwartz image in L². -/
def onSchwartzRange : schwartzRange d →ₗᵢ[ℂ] L2 d where
  toLinearMap := toL2.toLinearMap.comp
    ((SchwartzMap.fourierTransformCLE ℂ).toLinearMap.comp schwartzEquiv.symm.toLinearMap)
  norm_map' f := by
    obtain ⟨g, rfl⟩ := schwartzEquiv.surjective f
    simpa [schwartzEquiv] using fourier_schwartz_norm g

theorem dense_subtype : DenseRange (schwartzRange d).subtypeL := by
  simpa [DenseRange, Submodule.coe_subtype, Subtype.range_coe] using
    (schwartzRange_dense (d := d))

/-- Continuous extension in the L² norm without any regularity restriction. -/
def transform : L2 d →L[ℂ] L2 d :=
  onSchwartzRange.toContinuousLinearMap.extend (schwartzRange d).subtypeL
    dense_subtype isometry_subtype_coe.isUniformInducing

@[simp] theorem transform_toL2 (f : SchwartzMap Rd ℂ) :
    transform (toL2 f) = toL2 (SchwartzMap.fourierTransformCLE ℂ f) := by
  change transform ((schwartzRange d).subtypeL (schwartzEquiv f)) = _
  rw [transform, ContinuousLinearMap.extend_eq]
  change toL2 (SchwartzMap.fourierTransformCLE ℂ (schwartzEquiv.symm (schwartzEquiv f))) = _
  rw [LinearEquiv.symm_apply_apply]

/-- Plancherel for arbitrary L² equivalence classes. -/
@[simp] theorem transform_norm (u : L2 d) : ‖transform u‖ = ‖u‖ := by
  refine dense_subtype.induction_on u ?_ ?_
  · exact isClosed_eq transform.continuous.norm continuous_norm
  · intro f
    rw [transform, ContinuousLinearMap.extend_eq]
    exact onSchwartzRange.norm_map f

def isometry : L2 d →ₗᵢ[ℂ] L2 d where
  toLinearMap := transform.toLinearMap
  norm_map' := transform_norm

theorem transform_surjective : Function.Surjective (transform (d := d)) := by
  have hdense : DenseRange (transform (d := d)) := by
    apply schwartzRange_dense.mono
    rintro _ ⟨f, rfl⟩
    refine ⟨toL2 ((SchwartzMap.fourierTransformCLE ℂ).symm f), ?_⟩
    rw [transform_toL2, ContinuousLinearEquiv.apply_symm_apply]
    rfl
  have hc : IsClosed (Set.range (transform (d := d))) :=
    (isometry (d := d)).isometry.isClosedEmbedding.isClosed_range
  exact Set.range_eq_univ.mp (hc.closure_eq.symm.trans hdense.closure_range)

/-- Canonical L² Fourier equivalence constructed from Schwartz Fourier inversion. -/
def equivalence (d : ℕ) : L2 d ≃ₗᵢ[ℂ] L2 d :=
  LinearIsometryEquiv.ofSurjective isometry transform_surjective

@[simp] theorem equivalence_toL2 (f : SchwartzMap Rd ℂ) :
    equivalence d (toL2 f) = toL2 (SchwartzMap.fourierTransformCLE ℂ f) :=
  transform_toL2 f

/-- Exact-shell exclusion for genuine L² classes with an a.e. support premise,
in every positive finite spatial dimension and for every real radius. -/
theorem shell_exclusion (d : ℕ) (k : ℝ) (u : L2 (d + 1))
    (h : ∀ᵐ ξ ∂volume, ξ ∉ Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) k →
      (equivalence (d + 1) u : EuclideanSpace ℝ (Fin (d + 1)) → ℂ) ξ = 0) :
    u = 0 := by
  have hnull := euclidean_frequency_shell_measure_zero d k
  have hv : equivalence (d + 1) u = 0 := by
    apply Lp.eq_zero_iff_ae_eq_zero.2
    have hoff : ∀ᵐ ξ ∂volume, ξ ∉ Metric.sphere
        (0 : EuclideanSpace ℝ (Fin (d + 1))) k := by
      apply ae_iff.mpr
      simpa only [not_not, Metric.sphere, dist_zero_right] using hnull
    filter_upwards [h, hoff] with ξ hξ hn
    exact hξ hn
  apply (equivalence (d + 1)).injective
  simpa using hv

end ReyesMath.L2Fourier
