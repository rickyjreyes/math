import Mathlib
import MathProofs.M6BClosureTheorem

/-!
# M6B: genuine n-dimensional real-inner-product Laplacian

This module uses Mathlib's `InnerProductSpace.laplacian` on the actual
EuclideanSpace ℝ (Fin d), not a symbolic curvature jet or grid.

The Laplacian phase identity is a direct consequence of the second
Fréchet derivative and continuous ℝ-linear complex multiplication.

The quadratic test profile is a globally C∞ field. Its derived jet
is computed by the exact Hessian of the squared norm and the trace
over the standard orthonormal basis, not assumed.
-/

noncomputable section
open scoped RealInnerProductSpace
namespace ReyesMath.M6B

/-- Cartesian Laplacian in dimension d, genuinely given by Mathlib's
canonical covariant tensor and the second Fréchet derivative. -/
def laplacianD (d : ℕ)
    (ψ : EuclideanSpace ℝ (Fin d) → ℂ) :
    EuclideanSpace ℝ (Fin d) → ℂ :=
  InnerProductSpace.laplacian ψ

/-- The d-dimensional curvature operator acts on the *actual*
Cartesian Laplacian of a complex C² field. -/
def fieldCurvatureD (d : ℕ) (ε α lam S : ℝ)
    (ψ : EuclideanSpace ℝ (Fin d) → ℂ)
    (x : EuclideanSpace ℝ (Fin d)) : ℂ :=
  curvature ε α lam S (ψ x) (laplacianD d ψ x)

/-- Full C² phase covariance of the genuine finite-dimensional
Laplacian, with no stationary-eigenfield assumption. -/
theorem laplacianD_phase (d : ℕ)
    (ψ : EuclideanSpace ℝ (Fin d) → ℂ)
    (hψ : ContDiff ℝ 2 ψ) (u : ℂ)
    (x : EuclideanSpace ℝ (Fin d)) :
    laplacianD d (fun y => u * ψ y) x =
      u * laplacianD d ψ x := by
  let L : ℂ →L[ℝ] ℂ := (ContinuousLinearMap.lsmul ℝ ℂ) u
  have h := (hψ.contDiffAt x).laplacian_CLM_comp_left (l := L)
  simpa only [laplacianD, Function.comp_def, L,
    ContinuousLinearMap.lsmul_apply, smul_eq_mul] using h

/-- Local C² version of constant-phase Laplacian covariance:
only differentiability at the evaluated point is needed. -/
theorem laplacianD_phase_at (d : ℕ)
    (ψ : EuclideanSpace ℝ (Fin d) → ℂ)
    (x : EuclideanSpace ℝ (Fin d))
    (hψ : ContDiffAt ℝ 2 ψ x) (u : ℂ) :
    laplacianD d (fun y => u * ψ y) x =
      u * laplacianD d ψ x := by
  let L : ℂ →L[ℝ] ℂ := (ContinuousLinearMap.lsmul ℝ ℂ) u
  have h := hψ.laplacian_CLM_comp_left (l := L)
  simpa only [laplacianD, Function.comp_def, L,
    ContinuousLinearMap.lsmul_apply, smul_eq_mul] using h

/-- The real C² hypothesis may hold only on an arbitrary open domain.
No global smoothness or boundary condition is required for phase
invariance at an interior point. -/
theorem laplacianD_phase_on_open (d : ℕ)
    (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (hΩ : IsOpen Ω)
    (ψ : EuclideanSpace ℝ (Fin d) → ℂ)
    (hψ : ContDiffOn ℝ 2 ψ Ω)
    (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ Ω) (u : ℂ) :
    laplacianD d (fun y => u * ψ y) x =
      u * laplacianD d ψ x :=
  laplacianD_phase_at d ψ x
    ((hψ x hx).contDiffAt (hΩ.mem_nhds hx)) u

/-- A constant unit phase preserves the actual d-dimensional
regularized curvature operator on every C² field and every point. -/
theorem fieldCurvatureD_phase_invariant (d : ℕ)
    (ψ : EuclideanSpace ℝ (Fin d) → ℂ)
    (hψ : ContDiff ℝ 2 ψ) (u : ℂ) (hu : ‖u‖ = 1)
    (ε α lam S : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    fieldCurvatureD d ε α lam S (fun y => u * ψ y) x =
      fieldCurvatureD d ε α lam S ψ x := by
  unfold fieldCurvatureD
  rw [laplacianD_phase d ψ hψ u x]
  exact curvature_phase_invariant ε α lam S u (ψ x) (laplacianD d ψ x) hu

/-- Full U(1) invariance on an arbitrary open Ω⊆ℝᵈ for
complex fields that are C² on Ω, with no global C² hypothesis. -/
theorem fieldCurvatureD_phase_invariant_on_open (d : ℕ)
    (Ω : Set (EuclideanSpace ℝ (Fin d))) (hΩ : IsOpen Ω)
    (ψ : EuclideanSpace ℝ (Fin d) → ℂ)
    (hψ : ContDiffOn ℝ 2 ψ Ω)
    (u : ℂ) (hu : ‖u‖ = 1)
    (ε α lam S : ℝ) (x : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ Ω) :
    fieldCurvatureD d ε α lam S (fun y => u * ψ y) x =
      fieldCurvatureD d ε α lam S ψ x := by
  unfold fieldCurvatureD
  rw [laplacianD_phase_on_open d Ω hΩ ψ hψ x hx u]
  exact curvature_phase_invariant ε α lam S u (ψ x) (laplacianD d ψ x) hu

/-- The actual d-dimensional quadratic test field, on Euclidean
space, has smooth real components everywhere. -/
def quadraticFieldD (d : ℕ) :
    EuclideanSpace ℝ (Fin d) → ℂ :=
  fun x => (((1 : ℝ) + ‖x‖ ^ 2 : ℝ) : ℂ)

/-- The differentiating quadratic witness is genuinely C∞. -/
theorem quadraticFieldD_smooth (d : ℕ) :
    ContDiff ℝ ⊤ (quadraticFieldD d) := by
  let E := EuclideanSpace ℝ (Fin d)
  have hnorm : ContDiff ℝ ⊤ (fun x : E => ‖x‖ ^ 2) :=
    (contDiff_id (E := E)).norm_sq ℝ
  have hsum : ContDiff ℝ ⊤ (fun x : E => (1 : ℝ) + ‖x‖ ^ 2) :=
    (contDiff_const (c := (1 : ℝ))).add hnorm
  simpa [quadraticFieldD, Function.comp_def] using
    (Complex.ofRealCLM.contDiff.comp hsum)

/-- The raw real squared norm has the exact Hessian trace 2d on
the d-dimensional Euclidean vector space. -/
theorem squared_norm_laplacian_D (d : ℕ)
    (x : EuclideanSpace ℝ (Fin d)) :
    InnerProductSpace.laplacian
      (fun y : EuclideanSpace ℝ (Fin d) => ‖y‖ ^ 2) x =
      2 * (d : ℝ) := by
  let E := EuclideanSpace ℝ (Fin d)
  let L : E →L[ℝ] (E →L[ℝ] ℝ) := innerSL ℝ
  have hd (y : E) :
      fderiv ℝ (fun z : E => ‖z‖ ^ 2) y = (2 : ℝ) • L y := by
    simpa [L] using (fderiv_norm_sq_apply y)
  have hfun :
      fderiv ℝ (fun z : E => ‖z‖ ^ 2) =
        fun y => (2 : ℝ) • L y := funext hd
  have htwo (y : E) :
      fderiv ℝ (fderiv ℝ (fun z : E => ‖z‖ ^ 2)) y =
        (2 : ℝ) • L := by
    rw [hfun]
    simpa using (fderiv_const_smul (L.differentiableAt) (2 : ℝ))
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis
    (fun y : E => ‖y‖ ^ 2)]
  simp only [iteratedFDeriv_two_apply]
  simp_rw [htwo]
  simp [L, innerSL_apply, real_inner_self_eq_norm_sq,
    OrthonormalBasis.norm_eq_one, finrank_euclideanSpace]


/-- The polynomial witness has the nonzero field value one at the
origin in every Euclidean spatial dimension. -/
theorem quadraticFieldD_at_origin (d : ℕ) :
    quadraticFieldD d (0 : EuclideanSpace ℝ (Fin d)) = 1 := by
  simp [quadraticFieldD]

/-- The global complex quadratic test has the *actual* Laplacian
2d, as obtained by the Mathlib second-Fréchet-derivative trace. -/
theorem quadraticFieldD_laplacian_at_origin (d : ℕ) :
    laplacianD d (quadraticFieldD d)
      (0 : EuclideanSpace ℝ (Fin d)) = ((2 * (d : ℝ) : ℝ) : ℂ) := by
  let E := EuclideanSpace ℝ (Fin d)
  let f : E → ℝ := fun y => 1 + ‖y‖ ^ 2
  have hnorm : ContDiff ℝ 2 (fun y : E => ‖y‖ ^ 2) :=
    (contDiff_id (E := E)).norm_sq ℝ
  have hf : ContDiff ℝ 2 f := by
    dsimp [f]
    exact (contDiff_const (c := (1 : ℝ))).add hnorm
  have hconst : ContDiffAt ℝ 2 (fun _ : E => (1 : ℝ)) 0 :=
    (contDiff_const (c := (1 : ℝ))).contDiffAt 0
  have hsq : ContDiffAt ℝ 2 (fun y : E => ‖y‖ ^ 2) 0 :=
    hnorm.contDiffAt 0
  have hreal : InnerProductSpace.laplacian f (0 : E) = 2 * (d : ℝ) := by
    have h := hconst.laplacian_add hsq
    change InnerProductSpace.laplacian f 0 =
      InnerProductSpace.laplacian (fun _ : E => (1 : ℝ)) 0 +
        InnerProductSpace.laplacian (fun y : E => ‖y‖ ^ 2) 0 at h
    have hzero :
        InnerProductSpace.laplacian (fun _ : E => (1 : ℝ)) 0 = 0 := by
      rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
      simp [iteratedFDeriv_const_of_ne two_ne_zero]
    rw [hzero, zero_add, squared_norm_laplacian_D] at h
    exact h
  have hc := (hf.contDiffAt (0 : E)).laplacian_CLM_comp_left
    (l := Complex.ofRealCLM)
  simpa [laplacianD, quadraticFieldD, f, Function.comp_def,
    hreal] using hc

/-- The manuscript's infinite family is genuinely nonunique on
actual C-infinity complex fields for *every* spatial d >= 1.

The distinguishing jet is derived, not assumed: ψ(0)=1 and
Δψ(0)=2d, and 2d ≠ 0 in any permitted dimension. -/
theorem distinct_closures_on_actual_fields_all_dimensions
    (d : ℕ) (hd : 1 ≤ d)
    (ε α S lam mu : ℝ)
    (hε : 0 < ε) (hS : 0 < S) (hne : lam ≠ mu) :
    ∃ ψ : EuclideanSpace ℝ (Fin d) → ℂ,
      ContDiff ℝ ⊤ ψ ∧
      ∃ x : EuclideanSpace ℝ (Fin d),
        fieldCurvatureD d ε α lam S ψ x ≠
          fieldCurvatureD d ε α mu S ψ x := by
  let a : ℂ := ((2 * (d : ℝ) : ℝ) : ℂ)
  have ha : a ≠ 0 := by
    have hdpos : (0 : ℝ) < (d : ℝ) := by
      exact_mod_cast (by omega : 0 < d)
    have hr : 2 * (d : ℝ) ≠ 0 :=
      ne_of_gt (mul_pos (by norm_num) hdpos)
    exact_mod_cast hr
  have hlinear (k : ℝ) :
      curvature ε α k S 1 a = a * curvature ε α k S 1 1 := by
    unfold curvature
    ring
  have hdistinct :
      curvature ε α lam S 1 a ≠ curvature ε α mu S 1 a := by
    intro he
    rw [hlinear lam, hlinear mu] at he
    exact (curvature_family_pairwise_distinct ε α S lam mu hε hS hne)
      (mul_left_cancel₀ ha he)
  refine ⟨quadraticFieldD d, quadraticFieldD_smooth d, 0, ?_⟩
  simpa only [fieldCurvatureD, quadraticFieldD_at_origin,
    quadraticFieldD_laplacian_at_origin, a] using hdistinct


/-- All five structural properties in the original closure theorem,
stated literally for the exact nonlinear complex-jet quotient. -/
def IsAdmissibleRegularization (ε α lam S : ℝ) : Prop :=
  ContDiff ℝ ⊤ (fun p : ℂ × ℂ =>
    curvature ε α lam S p.1 p.2) ∧
  (∀ s : ℝ, 0 ≤ s → 0 < denominator ε α lam S s) ∧
  denominator ε α lam S 0 = ε ^ 2 ∧
  (∀ w : ℂ, curvature ε α lam S 0 w = 0) ∧
  (∀ u z w : ℂ, ‖u‖ = 1 →
    curvature ε α lam S (u * z) (u * w) =
      curvature ε α lam S z w) ∧
  (∀ z w : ℂ, z ≠ 0 →
    Filter.Tendsto (fun δ : ℝ => curvature δ α lam S z w)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (-(w / z))))

/-- The dimension-uniform original closure nonuniqueness theorem:
every λ≥0 satisfies all enumerated analytic axioms; the closures
form an infinite set; and distinct λ are separated by evaluation
on an *actual smooth Cartesian field* in every d≥1. -/
theorem manuscript_closure_nonuniqueness_all_dimensions
    (d : ℕ) (hd : 1 ≤ d)
    (ε α S : ℝ) (hε : 0 < ε) (hS : 0 < S) :
    (∀ lam : ℝ, 0 ≤ lam → IsAdmissibleRegularization ε α lam S) ∧
    Set.Infinite (Set.range
      (fun k : ℕ => fun p : ℂ × ℂ =>
        curvature ε α (k : ℝ) S p.1 p.2)) ∧
    (∀ lam mu : ℝ, 0 ≤ lam → 0 ≤ mu → lam ≠ mu →
      ∃ ψ : EuclideanSpace ℝ (Fin d) → ℂ,
        ContDiff ℝ ⊤ ψ ∧
        ∃ x : EuclideanSpace ℝ (Fin d),
          fieldCurvatureD d ε α lam S ψ x ≠
            fieldCurvatureD d ε α mu S ψ x) := by
  refine ⟨?_, infinitely_many_distinct_closures ε α S hε hS, ?_⟩
  · intro lam hlam
    exact every_closure_is_admissible ε α S hε hS lam hlam
  · intro lam mu _ _ hne
    exact distinct_closures_on_actual_fields_all_dimensions
      d hd ε α S lam mu hε hS hne

end ReyesMath.M6B
