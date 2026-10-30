import Mathlib
import MathProofs.E68WeakH1
import MathProofs.RegularizedCurvatureL2
import MathProofs.SobolevH2

/-!
# E68: the Sobolev space `H¹(ℝⁿ; ℂ)` by weak derivatives

`IsH1 ψ g` says that `ψ ∈ L²(ℝⁿ; ℂ)`, `g ∈ L²(ℝⁿ; ℂⁿ)` and `g` is the weak gradient of `ψ`:
`∫ ψ ∂ᵢφ = -∫ gᵢ φ` for every coordinate `i` and every real `φ ∈ C_c^∞(ℝⁿ)`. This is the
standard definition of `H¹ = W^{1,2}`. The pointwise gradient energy is the Euclidean norm
`|∇ψ|² = Σᵢ |∂ᵢψ|²` of the gradient vector, as in the manuscript.

* `IsH1.ae_eq_grad`: the weak gradient is unique up to a.e. equality.
* `IsH1.congr_ae`, `h1sq_congr_ae`: membership and the `H¹` energies depend only on the
  a.e. classes of the field and of its gradient.
* `isH1_of_contDiff`: every `C¹` compactly supported field is in `H¹`, and its classical
  gradient is the weak gradient; `norm_gradVec_ofReal` identifies the gradient energy of a
  real field with `‖fderiv‖²`.
* `WeakH1Field.isH1`, `IsH1.toWeakH1Field`: correspondence with the directional
  distributional structure `WeakH1Field` of `E68WeakH1`.
* `isH1_iff_isWeakDeriv`: equivalence with `E26.IsWeakDeriv` on `Ω = ℝⁿ`.
* `isH1_of_H2`: every element of `Sobolev.H2` gives an `H¹` field with its strong gradient.
* `IsH1.smul_test`: the product rule with a smooth compactly supported multiplier.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ContDiff

namespace ReyesMath.E68

variable {n : ℕ}

/-- The coordinate vector `eᵢ` of `ℝⁿ`. -/
def ev (i : Fin n) : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single i 1

/-- `ψ ∈ H¹(ℝⁿ; ℂ)` with weak gradient `g`: both are in `L²`, and `∫ ψ ∂ᵢφ = -∫ gᵢ φ` for
every coordinate `i` and every real `φ ∈ C_c^∞(ℝⁿ)`. -/
structure IsH1 (ψ : EuclideanSpace ℝ (Fin n) → ℂ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)) : Prop where
  memLp : MemLp ψ 2 volume
  memLp_grad : MemLp g 2 volume
  weak : ∀ (i : Fin n) (φ : EuclideanSpace ℝ (Fin n) → ℝ), ContDiff ℝ ∞ φ →
    HasCompactSupport φ →
    ∫ x, ψ x * ((fderiv ℝ φ x (ev i) : ℝ) : ℂ) = -∫ x, g x i * ((φ x : ℝ) : ℂ)

/-- `ψ ∈ H¹(ℝⁿ; ℂ)`. -/
def MemH1 (ψ : EuclideanSpace ℝ (Fin n) → ℂ) : Prop :=
  ∃ g, IsH1 ψ g

/-- The squared inhomogeneous norm `‖ψ‖²_{H¹} = ‖ψ‖²_{L²} + ‖∇ψ‖²_{L²}`. -/
def h1sq (ψ : EuclideanSpace ℝ (Fin n) → ℂ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)) : ℝ :=
  (∫ x, ‖ψ x‖ ^ 2) + ∫ x, ‖g x‖ ^ 2

theorem h1sq_nonneg (ψ : EuclideanSpace ℝ (Fin n) → ℂ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)) : 0 ≤ h1sq ψ g :=
  add_nonneg (integral_nonneg fun _ => sq_nonneg _) (integral_nonneg fun _ => sq_nonneg _)

namespace IsH1

variable {ψ : EuclideanSpace ℝ (Fin n) → ℂ} {g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)}

theorem integrable_sq (h : IsH1 ψ g) : Integrable (fun x => ‖ψ x‖ ^ 2) volume :=
  (memLp_two_iff_integrable_sq_norm h.memLp.1).1 h.memLp

theorem integrable_grad_sq (h : IsH1 ψ g) : Integrable (fun x => ‖g x‖ ^ 2) volume :=
  (memLp_two_iff_integrable_sq_norm h.memLp_grad.1).1 h.memLp_grad

theorem locallyIntegrable (h : IsH1 ψ g) : LocallyIntegrable ψ volume :=
  h.memLp.locallyIntegrable (by norm_num)

theorem memLp_comp (h : IsH1 ψ g) (i : Fin n) : MemLp (fun x => g x i) 2 volume :=
  h.memLp_grad.eval_piLp i

theorem locallyIntegrable_comp (h : IsH1 ψ g) (i : Fin n) :
    LocallyIntegrable (fun x => g x i) volume :=
  (h.memLp_comp i).locallyIntegrable (by norm_num)

end IsH1

/-- A locally integrable complex function times a continuous compactly supported real function
is integrable. -/
theorem integrable_mul_ofReal_of_compact {f : EuclideanSpace ℝ (Fin n) → ℂ}
    (hf : LocallyIntegrable f volume) {c : EuclideanSpace ℝ (Fin n) → ℝ} (hc : Continuous c)
    (hcs : HasCompactSupport c) : Integrable (fun x => f x * ((c x : ℝ) : ℂ)) volume := by
  have h := hf.integrable_smul_left_of_hasCompactSupport
    (g := fun x => ((c x : ℝ) : ℂ)) (Complex.continuous_ofReal.comp hc)
    (hcs.comp_left Complex.ofReal_zero)
  refine h.congr (Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul]
  ring

/-- **Uniqueness of the weak gradient** up to a.e. equality. -/
theorem IsH1.ae_eq_grad {ψ : EuclideanSpace ℝ (Fin n) → ℂ}
    {g g' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)} (h : IsH1 ψ g)
    (h' : IsH1 ψ g') : g =ᵐ[volume] g' := by
  have hcomp : ∀ i : Fin n, ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      g x i - g' x i = 0 := by
    intro i
    apply ae_eq_zero_of_integral_contDiff_smul_eq_zero
      ((h.locallyIntegrable_comp i).sub (h'.locallyIntegrable_comp i))
    intro φ hφ hφc
    simp only [Pi.sub_apply]
    have h1 := h.weak i φ hφ hφc
    have h2 := h'.weak i φ hφ hφc
    have hi1 := integrable_mul_ofReal_of_compact (h.locallyIntegrable_comp i) hφ.continuous hφc
    have hi2 := integrable_mul_ofReal_of_compact (h'.locallyIntegrable_comp i) hφ.continuous hφc
    have : ∫ x, φ x • (g x i - g' x i) =
        (∫ x, g x i * ((φ x : ℝ) : ℂ)) - ∫ x, g' x i * ((φ x : ℝ) : ℂ) := by
      rw [← integral_sub hi1 hi2]
      congr 1
      funext x
      rw [Complex.real_smul]
      ring
    rw [this]
    have : (∫ x, g x i * ((φ x : ℝ) : ℂ)) = ∫ x, g' x i * ((φ x : ℝ) : ℂ) := by
      rw [← neg_neg (∫ x, g x i * ((φ x : ℝ) : ℂ)), ← h1, h2, neg_neg]
    rw [this, sub_self]
  rw [← ae_all_iff] at hcomp
  filter_upwards [hcomp] with x hx
  exact PiLp.ext fun i => sub_eq_zero.1 (hx i)

/-- `H¹` membership depends only on the a.e. classes of the field and the gradient. -/
theorem IsH1.congr_ae {ψ ψ' : EuclideanSpace ℝ (Fin n) → ℂ}
    {g g' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)} (h : IsH1 ψ g)
    (hψ : ψ =ᵐ[volume] ψ') (hg : g =ᵐ[volume] g') : IsH1 ψ' g' where
  memLp := h.memLp.ae_eq hψ
  memLp_grad := h.memLp_grad.ae_eq hg
  weak i φ hφ hφc := by
    have e1 : (∫ x, ψ' x * ((fderiv ℝ φ x (ev i) : ℝ) : ℂ)) =
        ∫ x, ψ x * ((fderiv ℝ φ x (ev i) : ℝ) : ℂ) := by
      apply integral_congr_ae
      filter_upwards [hψ] with x hx
      rw [hx]
    have e2 : (∫ x, g' x i * ((φ x : ℝ) : ℂ)) = ∫ x, g x i * ((φ x : ℝ) : ℂ) := by
      apply integral_congr_ae
      filter_upwards [hg] with x hx
      rw [hx]
    rw [e1, e2]
    exact h.weak i φ hφ hφc

/-- The `H¹` energy is a function of the a.e. classes. -/
theorem h1sq_congr_ae {ψ ψ' : EuclideanSpace ℝ (Fin n) → ℂ}
    {g g' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)}
    (hψ : ψ =ᵐ[volume] ψ') (hg : g =ᵐ[volume] g') : h1sq ψ g = h1sq ψ' g' := by
  unfold h1sq
  congr 1
  · apply integral_congr_ae
    filter_upwards [hψ] with x hx
    rw [hx]
  · apply integral_congr_ae
    filter_upwards [hg] with x hx
    rw [hx]

/-- Ball energies of the gradient are a function of the a.e. class of the gradient. -/
theorem setIntegral_grad_congr_ae {g g' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)}
    (hg : g =ᵐ[volume] g') (s : Set (EuclideanSpace ℝ (Fin n))) :
    (∫ x in s, ‖g x‖ ^ 2) = ∫ x in s, ‖g' x‖ ^ 2 := by
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae hg] with x hx
  rw [hx]

/-! ### Smooth compactly supported fields -/

/-- The coordinate vector `(L e₁, …, L eₙ)` of a real-linear map `L : ℝⁿ → ℂ`. -/
def coordVec : (EuclideanSpace ℝ (Fin n) →L[ℝ] ℂ) →L[ℝ] EuclideanSpace ℂ (Fin n) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun L => WithLp.toLp 2 fun i => L (ev i)
      map_add' := fun L M => by ext i; simp
      map_smul' := fun c L => by ext i; simp }

theorem coordVec_apply (L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℂ) (i : Fin n) :
    coordVec L i = L (ev i) := rfl

/-- The classical gradient vector `(∂₁f, …, ∂ₙf)` of a complex field. -/
def gradVec (f : EuclideanSpace ℝ (Fin n) → ℂ) (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℂ (Fin n) :=
  coordVec (fderiv ℝ f x)

theorem gradVec_apply (f : EuclideanSpace ℝ (Fin n) → ℂ) (x : EuclideanSpace ℝ (Fin n))
    (i : Fin n) : gradVec f x i = fderiv ℝ f x (ev i) := rfl

/-- The real field `φ`, viewed as a complex field. -/
def ofRealFn (φ : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℂ :=
  ((φ x : ℝ) : ℂ)

theorem hasFDerivAt_ofRealFn {φ : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hφ : DifferentiableAt ℝ φ x) :
    HasFDerivAt (ofRealFn φ) (Complex.ofRealCLM.comp (fderiv ℝ φ x)) x :=
  Complex.ofRealCLM.hasFDerivAt.comp x hφ.hasFDerivAt

theorem fderiv_ofRealFn {φ : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hφ : DifferentiableAt ℝ φ x) :
    fderiv ℝ (ofRealFn φ) x = Complex.ofRealCLM.comp (fderiv ℝ φ x) :=
  (hasFDerivAt_ofRealFn hφ).fderiv

theorem gradVec_ofRealFn_apply {φ : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hφ : DifferentiableAt ℝ φ x) (i : Fin n) :
    gradVec (ofRealFn φ) x i = ((fderiv ℝ φ x (ev i) : ℝ) : ℂ) := by
  rw [gradVec_apply, fderiv_ofRealFn hφ]
  rfl

/-- For a real-linear functional, the Euclidean norm of the coordinate vector is the operator
norm: `Σᵢ (L eᵢ)² = ‖L‖²` (Riesz representation). -/
theorem norm_coordVec_ofReal (L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :
    ‖coordVec (Complex.ofRealCLM.comp L)‖ = ‖L‖ := by
  set v := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm L
  have hv : ∀ i, L (ev i) = v i := by
    intro i
    rw [← InnerProductSpace.toDual_symm_apply (x := ev i) (y := L), ev,
      EuclideanSpace.inner_single_right]
    simp [v]
  have hL : ‖L‖ = ‖v‖ := by
    simp only [v, LinearIsometryEquiv.norm_map]
  rw [hL]
  have h1 : ‖coordVec (Complex.ofRealCLM.comp L)‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [coordVec_apply, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply,
      Complex.norm_real, hv i]
  have h2 := congrArg Real.sqrt h1
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h2

/-- For a real field differentiable at `x`, the gradient energy density is `‖fderiv φ x‖²`. -/
theorem norm_gradVec_ofRealFn {φ : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hφ : DifferentiableAt ℝ φ x) : ‖gradVec (ofRealFn φ) x‖ = ‖fderiv ℝ φ x‖ := by
  rw [gradVec, fderiv_ofRealFn hφ, norm_coordVec_ofReal]

theorem continuous_gradVec {f : EuclideanSpace ℝ (Fin n) → ℂ} (hf : ContDiff ℝ 1 f) :
    Continuous (gradVec f) :=
  coordVec.continuous.comp (hf.continuous_fderiv le_rfl)

theorem hasCompactSupport_gradVec {f : EuclideanSpace ℝ (Fin n) → ℂ} (hc : HasCompactSupport f) :
    HasCompactSupport (gradVec f) :=
  (hc.fderiv ℝ).comp_left (map_zero coordVec)

/-- **Smooth inclusion.** A `C¹` compactly supported field is in `H¹(ℝⁿ)`, and its classical
gradient is its weak gradient (integration by parts). -/
theorem isH1_of_contDiff {f : EuclideanSpace ℝ (Fin n) → ℂ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) : IsH1 f (gradVec f) where
  memLp := hf.continuous.memLp_of_hasCompactSupport hc
  memLp_grad := (continuous_gradVec hf).memLp_of_hasCompactSupport (hasCompactSupport_gradVec hc)
  weak i φ hφ hφc := by
    have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by exact_mod_cast le_top)
    have hφd : Differentiable ℝ φ := hφ1.differentiable le_rfl
    have hφC : Differentiable ℝ (ofRealFn φ) := fun x => (hasFDerivAt_ofRealFn (hφd x)).differentiableAt
    have hder : ∀ x, fderiv ℝ (ofRealFn φ) x (ev i) = ((fderiv ℝ φ x (ev i) : ℝ) : ℂ) := by
      intro x
      rw [fderiv_ofRealFn (hφd x)]
      rfl
    have hcC : Continuous (ofRealFn φ) := Complex.continuous_ofReal.comp hφ.continuous
    have hsC : HasCompactSupport (ofRealFn φ) := hφc.comp_left Complex.ofReal_zero
    have hcd : Continuous fun x => fderiv ℝ (ofRealFn φ) x (ev i) := by
      simp_rw [hder]
      exact Complex.continuous_ofReal.comp
        ((hφ1.continuous_fderiv le_rfl).clm_apply continuous_const)
    have hfd : Continuous fun x => fderiv ℝ f x (ev i) :=
      (hf.continuous_fderiv le_rfl).clm_apply continuous_const
    have h1 : Integrable (fun x => fderiv ℝ f x (ev i) * ofRealFn φ x) volume :=
      (hfd.mul hcC).integrable_of_hasCompactSupport hsC.mul_left
    have h2 : Integrable (fun x => f x * fderiv ℝ (ofRealFn φ) x (ev i)) volume :=
      (hf.continuous.mul hcd).integrable_of_hasCompactSupport hc.mul_right
    have h3 : Integrable (fun x => f x * ofRealFn φ x) volume :=
      (hf.continuous.mul hcC).integrable_of_hasCompactSupport hc.mul_right
    have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable h1 h2 h3
      (hf.differentiable le_rfl) hφC
    simp_rw [hder] at key
    simpa only [gradVec_apply, ofRealFn] using key

/-- A real `C¹` compactly supported field is in `H¹`, with gradient energy density
`‖fderiv φ‖²`. -/
theorem isH1_ofRealFn {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hc : HasCompactSupport φ) : IsH1 (ofRealFn φ) (gradVec (ofRealFn φ)) :=
  isH1_of_contDiff (Complex.ofRealCLM.contDiff.comp hφ) (hc.comp_left Complex.ofReal_zero)

theorem norm_ofRealFn (φ : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    ‖ofRealFn φ x‖ ^ 2 = φ x ^ 2 := by
  rw [ofRealFn, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- The `H¹` energy of a real `C¹` field: `∫ φ² + ∫ ‖fderiv φ‖²`. -/
theorem h1sq_ofRealFn {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hφ : ContDiff ℝ 1 φ) :
    h1sq (ofRealFn φ) (gradVec (ofRealFn φ)) =
      (∫ x, φ x ^ 2) + ∫ x, ‖fderiv ℝ φ x‖ ^ 2 := by
  have hd := hφ.differentiable le_rfl
  unfold h1sq
  simp_rw [norm_ofRealFn, norm_gradVec_ofRealFn (hd _)]

/-! ### Correspondence with the directional structure `WeakH1Field` -/

/-- A `WeakH1Field` is an `H¹` field; its gradient vector collects the directional weak
derivatives along the coordinate axes. -/
theorem WeakH1Field.isH1 (u : WeakH1Field n) :
    IsH1 u.ψ (fun x => coordVec (u.weakGradient x)) where
  memLp := u.field_memLp n
  memLp_grad := (u.gradient_memLp n).continuousLinearMap_comp coordVec
  weak i φ hφ hφc := u.distributionalDerivative (ev i) φ hφ hφc

/-- The real-linear map `v ↦ Σᵢ vᵢ wᵢ` determined by a gradient vector `w`. -/
def ofCoordVec : EuclideanSpace ℂ (Fin n) →L[ℝ] (EuclideanSpace ℝ (Fin n) →L[ℝ] ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => LinearMap.toContinuousLinearMap
        { toFun := fun v => ∑ i, ((v i : ℝ) : ℂ) * w i
          map_add' := fun v v' => by
            simp only [PiLp.add_apply, Complex.ofReal_add, add_mul, Finset.sum_add_distrib]
          map_smul' := fun c v => by
            simp only [PiLp.smul_apply, smul_eq_mul, Complex.ofReal_mul, RingHom.id_apply,
              Finset.smul_sum, Complex.real_smul, mul_assoc] }
      map_add' := fun w w' => by
        ext v
        simp only [LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
          PiLp.add_apply, mul_add, Finset.sum_add_distrib, ContinuousLinearMap.add_apply]
      map_smul' := fun c w => by
        ext v
        simp only [LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
          PiLp.smul_apply, RingHom.id_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
          Finset.smul_sum, Complex.real_smul, mul_left_comm] }

theorem ofCoordVec_apply (w : EuclideanSpace ℂ (Fin n)) (v : EuclideanSpace ℝ (Fin n)) :
    ofCoordVec w v = ∑ i, ((v i : ℝ) : ℂ) * w i := rfl

theorem coordVec_ofCoordVec (w : EuclideanSpace ℂ (Fin n)) : coordVec (ofCoordVec w) = w := by
  ext j
  rw [coordVec_apply, ofCoordVec_apply, Finset.sum_eq_single j]
  · simp [ev]
  · intro i _ hij
    simp [ev, EuclideanSpace.single_apply, hij]
  · simp

/-- A real-linear map on `ℝⁿ` is determined by its values on the coordinate vectors. -/
theorem clm_apply_eq_sum {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : EuclideanSpace ℝ (Fin n) →L[ℝ] F) (v : EuclideanSpace ℝ (Fin n)) :
    L v = ∑ i, v i • L (ev i) := by
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v]
  simp [map_sum, EuclideanSpace.basisFun_apply, ev]

/-- The partial derivatives of a compactly supported function are compactly supported. -/
theorem hasCompactSupport_fderiv_apply {φ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hφc : HasCompactSupport φ) (v : EuclideanSpace ℝ (Fin n)) :
    HasCompactSupport (fun x => fderiv ℝ φ x v) :=
  (hφc.fderiv ℝ).comp_left (g := fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => L v) (by simp)

/-- An `H¹` field satisfies the distributional identity in every direction `v`, with
directional weak derivative `Σᵢ vᵢ gᵢ`. -/
theorem IsH1.directional {ψ : EuclideanSpace ℝ (Fin n) → ℂ}
    {g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)} (h : IsH1 ψ g)
    (v : EuclideanSpace ℝ (Fin n)) (φ : EuclideanSpace ℝ (Fin n) → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) :
    ∫ x, ψ x * ((fderiv ℝ φ x v : ℝ) : ℂ) = -∫ x, ofCoordVec (g x) v * ((φ x : ℝ) : ℂ) := by
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by exact_mod_cast le_top)
  have hint : ∀ i, Integrable (fun x => ψ x * ((fderiv ℝ φ x (ev i) : ℝ) : ℂ)) volume :=
    fun i => integrable_mul_ofReal_of_compact h.locallyIntegrable
      ((hφ1.continuous_fderiv le_rfl).clm_apply continuous_const)
      (hasCompactSupport_fderiv_apply hφc (ev i))
  have hint' : ∀ i, Integrable (fun x => g x i * ((φ x : ℝ) : ℂ)) volume :=
    fun i => integrable_mul_ofReal_of_compact (h.locallyIntegrable_comp i) hφ.continuous hφc
  have e1 : (fun x => ψ x * ((fderiv ℝ φ x v : ℝ) : ℂ)) =
      fun x => ∑ i, ((v i : ℝ) : ℂ) * (ψ x * ((fderiv ℝ φ x (ev i) : ℝ) : ℂ)) := by
    funext x
    rw [clm_apply_eq_sum (fderiv ℝ φ x) v]
    simp only [smul_eq_mul, Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e2 : (fun x => ofCoordVec (g x) v * ((φ x : ℝ) : ℂ)) =
      fun x => ∑ i, ((v i : ℝ) : ℂ) * (g x i * ((φ x : ℝ) : ℂ)) := by
    funext x
    rw [ofCoordVec_apply, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e1, e2, integral_finset_sum _ fun i _ => (hint i).const_mul _,
    integral_finset_sum _ fun i _ => (hint' i).const_mul _, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul, integral_const_mul, h.weak i φ hφ hφc, mul_neg]

theorem IsH1.aestronglyMeasurable_ofCoordVec {ψ : EuclideanSpace ℝ (Fin n) → ℂ}
    {g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)} (h : IsH1 ψ g) :
    AEStronglyMeasurable (fun x => ofCoordVec (g x)) volume :=
  ofCoordVec.continuous.comp_aestronglyMeasurable h.memLp_grad.1

theorem IsH1.integrable_ofCoordVec_sq {ψ : EuclideanSpace ℝ (Fin n) → ℂ}
    {g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)} (h : IsH1 ψ g) :
    Integrable (fun x => ‖ofCoordVec (g x)‖ ^ 2) volume :=
  (memLp_two_iff_integrable_sq_norm h.aestronglyMeasurable_ofCoordVec).1
    (h.memLp_grad.continuousLinearMap_comp ofCoordVec)

/-- An `H¹` field is a `WeakH1Field`: the directional distributional identity holds in every
direction, with weak gradient `v ↦ Σᵢ vᵢ gᵢ`. -/
def IsH1.toWeakH1Field {ψ : EuclideanSpace ℝ (Fin n) → ℂ}
    {g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)} (h : IsH1 ψ g) : WeakH1Field n where
  ψ := ψ
  weakGradient x := ofCoordVec (g x)
  fieldAEStronglyMeasurable := h.memLp.1
  gradientAEStronglyMeasurable := h.aestronglyMeasurable_ofCoordVec
  squareIntegrable := h.integrable_sq
  gradientSquareIntegrable := h.integrable_ofCoordVec_sq
  distributionalDerivative := h.directional

/-- `ψ ∈ H¹(ℝⁿ)` iff `ψ` is the field of some `WeakH1Field`. -/
theorem memH1_iff_exists_weakH1Field (ψ : EuclideanSpace ℝ (Fin n) → ℂ) :
    MemH1 ψ ↔ ∃ u : WeakH1Field n, u.ψ = ψ :=
  ⟨fun ⟨_, h⟩ => ⟨h.toWeakH1Field, rfl⟩, fun ⟨u, hu⟩ => ⟨_, hu ▸ u.isH1⟩⟩

/-- The operator norm of a real-linear map `ℝⁿ → ℂ` is at most the Euclidean norm of its
coordinate vector (Cauchy–Schwarz). -/
theorem norm_le_norm_coordVec (L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℂ) :
    ‖L‖ ≤ ‖coordVec L‖ := by
  refine L.opNorm_le_bound (norm_nonneg _) fun v => ?_
  calc ‖L v‖ = ‖∑ i, v i • coordVec L i‖ := by rw [clm_apply_eq_sum L v]; rfl
    _ ≤ ∑ i, ‖v i‖ * ‖coordVec L i‖ := by
        refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
        rw [norm_smul]
    _ ≤ Real.sqrt (∑ i, ‖v i‖ ^ 2) * Real.sqrt (∑ i, ‖coordVec L i‖ ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = ‖coordVec L‖ * ‖v‖ := by
        rw [mul_comm, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]

/-- The gradient energy of a `WeakH1Field` (operator norm) is at most the Euclidean gradient
energy of the corresponding `H¹` field. -/
theorem WeakH1Field.norm_weakGradient_le (u : WeakH1Field n) (x : EuclideanSpace ℝ (Fin n)) :
    ‖u.weakGradient x‖ ≤ ‖coordVec (u.weakGradient x)‖ :=
  norm_le_norm_coordVec _

/-! ### Correspondence with `E26.IsWeakDeriv` on `Ω = ℝⁿ` -/

/-- `IsH1` is the first-order part of the `E26` weak-derivative framework on the whole
space. -/
theorem isH1_iff_isWeakDeriv {ψ : EuclideanSpace ℝ (Fin n) → ℂ}
    {g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)} :
    IsH1 ψ g ↔ MemLp ψ 2 volume ∧ MemLp g 2 volume ∧
      ∀ i : Fin n, E26.IsWeakDeriv Set.univ ![ev i] ψ (fun x => g x i) := by
  have key : ∀ (i : Fin n) (φ : EuclideanSpace ℝ (Fin n) → ℝ),
      ((∫ x in Set.univ, iteratedFDeriv ℝ 1 φ x ![ev i] • ψ x) =
        ((-1 : ℝ) ^ 1) • ∫ x in Set.univ, φ x • g x i) ↔
      ((∫ x, ψ x * ((fderiv ℝ φ x (ev i) : ℝ) : ℂ)) = -∫ x, g x i * ((φ x : ℝ) : ℂ)) := by
    intro i φ
    simp only [Measure.restrict_univ, iteratedFDeriv_one_apply, Matrix.cons_val_zero,
      Complex.real_smul, pow_one, neg_smul, one_smul]
    simp_rw [mul_comm ((φ _ : ℝ) : ℂ), mul_comm (((fderiv ℝ φ _ (ev i)) : ℝ) : ℂ)]
  constructor
  · intro h
    refine ⟨h.memLp, h.memLp_grad, fun i => ⟨(h.locallyIntegrable_comp i).locallyIntegrableOn _,
      fun φ hφ => (key i φ).2 (h.weak i φ hφ.1 hφ.2.1)⟩⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun i φ hφ hφc => (key i φ).1 ((h3 i).2 φ ⟨hφ, hφc, Set.subset_univ _⟩)⟩

/-! ### Compatibility with `Sobolev.H2` -/

/-- Every element of the Schwartz-closure space `Sobolev.H2` is in `H¹(ℝⁿ)`, with its strong
gradient as weak gradient. -/
theorem isH1_of_H2 (U : Sobolev.H2 n) :
    IsH1 (U.val : EuclideanSpace ℝ (Fin n) → ℂ)
      (fun x => WithLp.toLp 2 fun i => (U.grad i : EuclideanSpace ℝ (Fin n) → ℂ) x) where
  memLp := Lp.memLp _
  memLp_grad := MemLp.of_eval_piLp fun i => by
    simpa only [PiLp.toLp_apply] using Lp.memLp (U.grad i)
  weak i φ hφ hφc := by
    have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by exact_mod_cast le_top)
    have hφd : Differentiable ℝ φ := hφ1.differentiable le_rfl
    set χ := Sobolev.schwartzOfCompact (ofRealFn φ) (Complex.ofRealCLM.contDiff.comp hφ)
      (hφc.comp_left Complex.ofReal_zero)
    have hgrad := Sobolev.H2.inner_grad_eq U i χ
    rw [L2.inner_def, L2.inner_def] at hgrad
    have e1 : (∫ x, inner ℂ ((Sobolev.toL2 χ : EuclideanSpace ℝ (Fin n) → ℂ) x)
        ((U.grad i : EuclideanSpace ℝ (Fin n) → ℂ) x)) =
        ∫ x, (U.grad i : EuclideanSpace ℝ (Fin n) → ℂ) x * ((φ x : ℝ) : ℂ) := by
      apply integral_congr_ae
      filter_upwards [Sobolev.coeFn_toL2 χ] with x hx
      rw [hx, RCLike.inner_apply]
      simp [χ, ofRealFn]
    have e2 : (∫ x, inner ℂ ((Sobolev.toL2 (Sobolev.dS i χ) : EuclideanSpace ℝ (Fin n) → ℂ) x)
        ((U.val : EuclideanSpace ℝ (Fin n) → ℂ) x)) =
        ∫ x, (U.val : EuclideanSpace ℝ (Fin n) → ℂ) x * ((fderiv ℝ φ x (ev i) : ℝ) : ℂ) := by
      apply integral_congr_ae
      filter_upwards [Sobolev.coeFn_toL2 (Sobolev.dS i χ)] with x hx
      rw [hx, RCLike.inner_apply, Sobolev.dS_apply]
      have : fderiv ℝ (⇑χ) x (Sobolev.ev i) = ((fderiv ℝ φ x (ev i) : ℝ) : ℂ) := by
        change fderiv ℝ (ofRealFn φ) x (ev i) = _
        rw [fderiv_ofRealFn (hφd x)]
        rfl
      rw [this, Complex.conj_ofReal]
    rw [e1, e2] at hgrad
    simp only [PiLp.toLp_apply]
    rw [hgrad, neg_neg]

/-! ### Product rule with a smooth compactly supported multiplier -/

/-- **Product rule.** If `ψ ∈ H¹` with weak gradient `g` and `χ ∈ C_c^∞(ℝⁿ)` is real, then
`χψ ∈ H¹` with weak gradient `χ g + ψ ∇χ`. -/
theorem IsH1.smul_test {ψ : EuclideanSpace ℝ (Fin n) → ℂ}
    {g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)} (h : IsH1 ψ g)
    {χ : EuclideanSpace ℝ (Fin n) → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) :
    IsH1 (fun x => ((χ x : ℝ) : ℂ) * ψ x)
      (fun x => ((χ x : ℝ) : ℂ) • g x + ψ x • gradVec (ofRealFn χ) x) := by
  have hχ1 : ContDiff ℝ 1 χ := hχ.of_le (by exact_mod_cast le_top)
  have hχd : Differentiable ℝ χ := hχ1.differentiable le_rfl
  obtain ⟨M, hM⟩ := hχ.continuous.bounded_above_of_compact_support hχc
  have hgc : Continuous (gradVec (ofRealFn χ)) :=
    continuous_gradVec (Complex.ofRealCLM.contDiff.comp hχ1)
  obtain ⟨M', hM'⟩ := hgc.bounded_above_of_compact_support
    (hasCompactSupport_gradVec (hχc.comp_left Complex.ofReal_zero))
  have hχC : Continuous fun x => ((χ x : ℝ) : ℂ) := Complex.continuous_ofReal.comp hχ.continuous
  refine ⟨?_, ?_, ?_⟩
  · refine h.memLp.of_le_mul (c := M) ((hχC.aestronglyMeasurable).mul h.memLp.1)
      (Eventually.of_forall fun x => ?_)
    rw [norm_mul, Complex.norm_real]
    exact mul_le_mul_of_nonneg_right (hM x) (norm_nonneg _)
  · refine MemLp.add ?_ ?_
    · refine h.memLp_grad.of_le_mul (c := M)
        ((hχC.aestronglyMeasurable).smul h.memLp_grad.1) (Eventually.of_forall fun x => ?_)
      rw [norm_smul, Complex.norm_real]
      exact mul_le_mul_of_nonneg_right (hM x) (norm_nonneg _)
    · refine h.memLp.of_le_mul (c := M')
        (h.memLp.1.smul hgc.aestronglyMeasurable) (Eventually.of_forall fun x => ?_)
      rw [norm_smul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hM' x) (norm_nonneg _)
  · intro i φ hφ hφc
    have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by exact_mod_cast le_top)
    have hφd : Differentiable ℝ φ := hφ1.differentiable le_rfl
    -- the product test function `χ φ`
    have hprod : ∀ x, fderiv ℝ (fun y => χ y * φ y) x (ev i) =
        χ x * fderiv ℝ φ x (ev i) + φ x * fderiv ℝ χ x (ev i) := by
      intro x
      rw [fderiv_fun_mul (hχd x) (hφd x)]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    have hw := h.weak i (fun y => χ y * φ y) (hχ.mul hφ) (hχc.mul_right)
    simp_rw [hprod] at hw
    have i1 : Integrable (fun x => ψ x * ((χ x * fderiv ℝ φ x (ev i) : ℝ) : ℂ)) volume :=
      integrable_mul_ofReal_of_compact h.locallyIntegrable
        (hχ.continuous.mul ((hφ1.continuous_fderiv le_rfl).clm_apply continuous_const))
        hχc.mul_right
    have i2 : Integrable (fun x => ψ x * ((φ x * fderiv ℝ χ x (ev i) : ℝ) : ℂ)) volume :=
      integrable_mul_ofReal_of_compact h.locallyIntegrable
        (hφ.continuous.mul ((hχ1.continuous_fderiv le_rfl).clm_apply continuous_const))
        hφc.mul_right
    have i3 : Integrable (fun x => g x i * ((χ x * φ x : ℝ) : ℂ)) volume :=
      integrable_mul_ofReal_of_compact (h.locallyIntegrable_comp i)
        (hχ.continuous.mul hφ.continuous) hχc.mul_right
    have hsplit : (∫ x, ψ x * ((χ x * fderiv ℝ φ x (ev i) + φ x * fderiv ℝ χ x (ev i) : ℝ) : ℂ)) =
        (∫ x, ψ x * ((χ x * fderiv ℝ φ x (ev i) : ℝ) : ℂ)) +
          ∫ x, ψ x * ((φ x * fderiv ℝ χ x (ev i) : ℝ) : ℂ) := by
      rw [← integral_add i1 i2]
      congr 1
      funext x
      push_cast
      ring
    rw [hsplit] at hw
    have hgoal : (∫ x, ((χ x : ℝ) : ℂ) * ψ x * ((fderiv ℝ φ x (ev i) : ℝ) : ℂ)) =
        ∫ x, ψ x * ((χ x * fderiv ℝ φ x (ev i) : ℝ) : ℂ) := by
      congr 1
      funext x
      push_cast
      ring
    have hrhs : (∫ x, (((χ x : ℝ) : ℂ) • g x + ψ x • gradVec (ofRealFn χ) x) i *
        ((φ x : ℝ) : ℂ)) =
        (∫ x, g x i * ((χ x * φ x : ℝ) : ℂ)) +
          ∫ x, ψ x * ((φ x * fderiv ℝ χ x (ev i) : ℝ) : ℂ) := by
      rw [← integral_add i3 i2]
      congr 1
      funext x
      rw [PiLp.add_apply, PiLp.smul_apply, PiLp.smul_apply, gradVec_ofRealFn_apply (hχd x)]
      push_cast
      simp only [smul_eq_mul]
      ring
    rw [hgoal, hrhs]
    linear_combination hw

end ReyesMath.E68
