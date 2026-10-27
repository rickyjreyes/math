import Mathlib

/-!
# Scalar-gradient tensors on the tangent bundle

The tensor is constructed from `mfderiv` of the actual complex scalar field,
not from supplied covectors. It is a bilinear form on each genuine tangent
fiber. The chain rule proves pullback covariance, and the tangent-map theorem
proves continuity for C¹ fields (and smoothness for smooth fields).

The radical is exactly the kernel of the complex differential. Thus in four
dimensions its dimension is at least two; the tensor has rank at most two,
is positive semidefinite, and has zero determinant in every basis.
-/

noncomputable section
open scoped Manifold ContDiff
open LinearMap (BilinForm)
open Module (Basis)

namespace ReyesMath.ManifoldScalarMetric

section Algebra
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The real part of the conjugate derivative product, as a bundled bilinear form. -/
def gram (D : V →ₗ[ℝ] ℂ) : BilinForm ℝ V :=
  LinearMap.mk₂ ℝ (fun v w => (D v).re * (D w).re + (D v).im * (D w).im)
    (by intros; simp only [map_add, Complex.add_re, Complex.add_im]; ring)
    (by intros; simp only [map_smul, Complex.smul_re, Complex.smul_im, smul_eq_mul]; ring)
    (by intros; simp only [map_add, Complex.add_re, Complex.add_im]; ring)
    (by intros; simp only [map_smul, Complex.smul_re, Complex.smul_im, smul_eq_mul]; ring)

@[simp] theorem gram_apply (D : V →ₗ[ℝ] ℂ) (v w : V) :
    gram D v w = (D v).re * (D w).re + (D v).im * (D w).im := rfl

theorem gram_eq_re (D : V →ₗ[ℝ] ℂ) (v w : V) :
    gram D v w = (star (D v) * D w).re := by simp [gram_apply, Complex.mul_re]

theorem gram_symmetric (D : V →ₗ[ℝ] ℂ) : (gram D).IsSymm := by
  constructor
  intro v w
  simp only [gram_apply]
  ring

theorem gram_nonnegative (D : V →ₗ[ℝ] ℂ) (v : V) : 0 ≤ gram D v v :=
  add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)

/-- Equality with the radical of the bilinear form, not merely an included subspace. -/
theorem gram_ker (D : V →ₗ[ℝ] ℂ) :
    LinearMap.ker (gram D) = LinearMap.ker D := by
  ext v
  simp only [LinearMap.mem_ker]
  constructor
  · intro h
    have hv : (D v).re * (D v).re + (D v).im * (D v).im = 0 :=
      congrArg (fun f : V →ₗ[ℝ] ℝ => f v) h
    apply Complex.ext <;> simp only [Complex.zero_re, Complex.zero_im]
    · nlinarith [sq_nonneg (D v).im]
    · nlinarith [sq_nonneg (D v).re]
  · intro h
    ext w
    simp [gram_apply, h]

variable [FiniteDimensional ℝ V]

theorem gram_rank_le_two (D : V →ₗ[ℝ] ℂ) :
    Module.finrank ℝ (LinearMap.range (gram D)) ≤ 2 := by
  have hD := LinearMap.finrank_range_add_finrank_ker D
  have hG := LinearMap.finrank_range_add_finrank_ker (gram D)
  rw [gram_ker] at hG
  have hr : Module.finrank ℝ (LinearMap.range D) ≤ 2 := by
    simpa using (Submodule.finrank_le (LinearMap.range D))
  omega

theorem gram_nullity (D : V →ₗ[ℝ] ℂ) (h4 : Module.finrank ℝ V = 4) :
    2 ≤ Module.finrank ℝ (LinearMap.ker (gram D)) := by
  have h := LinearMap.finrank_range_add_finrank_ker (gram D)
  have hr := gram_rank_le_two D
  omega

theorem gram_degenerate (D : V →ₗ[ℝ] ℂ) (h4 : Module.finrank ℝ V = 4) :
    ¬ (gram D).Nondegenerate := by
  intro h
  have hn := gram_nullity D h4
  rw [h.ker_eq_bot] at hn
  simpa using hn

end Algebra

section MultipletAlgebra
variable {V : Type*} [AddCommGroup V] [Module ℝ V]
  {ι : Type*} [Fintype ι]

def outer (D : V →ₗ[ℝ] ℝ) : BilinForm ℝ V :=
  LinearMap.mk₂ ℝ (fun v w => D v * D w)
    (by intros; simp [add_mul]) (by intros; simp [mul_assoc])
    (by intros; simp [mul_add]) (by intros; simp [mul_left_comm, mul_assoc])

def multipletGram (weights : ι → ℝ) (D : ι → V →ₗ[ℝ] ℝ) : BilinForm ℝ V :=
  ∑ i, weights i • outer (D i)

@[simp] theorem multipletGram_apply (weights : ι → ℝ) (D : ι → V →ₗ[ℝ] ℝ) (v w : V) :
    multipletGram weights D v w = ∑ i, weights i * (D i v * D i w) := by
  simp [multipletGram, outer, LinearMap.sum_apply]

theorem multipletGram_nonnegative (weights : ι → ℝ) (hw : ∀ i, 0 ≤ weights i)
    (D : ι → V →ₗ[ℝ] ℝ) (v : V) : 0 ≤ multipletGram weights D v v := by
  rw [multipletGram_apply]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (mul_self_nonneg _)

variable [FiniteDimensional ℝ V]

theorem multipletGram_rank (weights : ι → ℝ) (D : ι → V →ₗ[ℝ] ℝ) :
    Module.finrank ℝ (LinearMap.range (multipletGram weights D)) ≤
      min (Fintype.card ι) (Module.finrank ℝ V) := by
  let J : V →ₗ[ℝ] (ι → ℝ) := LinearMap.pi D
  have hk : LinearMap.ker J ≤ LinearMap.ker (multipletGram weights D) := by
    intro v hv
    have hv' : ∀ i, D i v = 0 := fun i => congrFun hv i
    apply LinearMap.mem_ker.2
    ext w
    simp [multipletGram_apply, hv']
  have hkd := Submodule.finrank_mono hk
  have hJ := LinearMap.finrank_range_add_finrank_ker J
  have hG := LinearMap.finrank_range_add_finrank_ker (multipletGram weights D)
  have hr : Module.finrank ℝ (LinearMap.range J) ≤ Fintype.card ι := by
    simpa using (Submodule.finrank_le (LinearMap.range J))
  exact le_min (by omega) (LinearMap.finrank_range_le _)

end MultipletAlgebra

section Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

/-- The global covariant tensor derived from a complex scalar's manifold derivative. -/
def differential (ψ : M → ℂ) (p : M) : TangentSpace I p →L[ℝ] ℂ :=
  mfderiv I 𝓘(ℝ, ℂ) ψ p

def scalarDifferential (a : M → ℝ) (p : M) : TangentSpace I p →L[ℝ] ℝ :=
  mfderiv I 𝓘(ℝ, ℝ) a p

/-- The associated real covariant bilinear form. -/
def tensor (ψ : M → ℂ) (p : M) : BilinForm ℝ (TangentSpace I p) :=
  gram (differential I ψ p).toLinearMap

theorem tensor_eq_re (ψ : M → ℂ) (p : M) (v w : TangentSpace I p) :
    tensor I ψ p v w =
      (star (differential I ψ p v) * differential I ψ p w).re :=
  gram_eq_re _ _ _

theorem real_differential (ψ : M → ℂ) (p : M)
    (hψ : MDifferentiableAt I 𝓘(ℝ, ℂ) ψ p) :
    scalarDifferential I (fun x => (ψ x).re) p =
      Complex.reCLM.comp (differential I ψ p) := by
  change mfderiv I 𝓘(ℝ, ℝ) (Complex.reCLM ∘ ψ) p = _
  rw [mfderiv_comp p Complex.reCLM.differentiableAt.mdifferentiableAt hψ,
    mfderiv_eq_fderiv, ContinuousLinearMap.fderiv]
  rfl

theorem imag_differential (ψ : M → ℂ) (p : M)
    (hψ : MDifferentiableAt I 𝓘(ℝ, ℂ) ψ p) :
    scalarDifferential I (fun x => (ψ x).im) p =
      Complex.imCLM.comp (differential I ψ p) := by
  change mfderiv I 𝓘(ℝ, ℝ) (Complex.imCLM ∘ ψ) p = _
  rw [mfderiv_comp p Complex.imCLM.differentiableAt.mdifferentiableAt hψ,
    mfderiv_eq_fderiv, ContinuousLinearMap.fderiv]
  rfl

/-- The tensor is `da ⊗ da + db ⊗ db` for the actual component differentials. -/
theorem tensor_real_components (ψ : M → ℂ) (p : M)
    (hψ : MDifferentiableAt I 𝓘(ℝ, ℂ) ψ p) (v w : TangentSpace I p) :
    tensor I ψ p v w =
      scalarDifferential I (fun x => (ψ x).re) p v *
        scalarDifferential I (fun x => (ψ x).re) p w +
      scalarDifferential I (fun x => (ψ x).im) p v *
        scalarDifferential I (fun x => (ψ x).im) p w := by
  rw [real_differential I ψ p hψ, imag_differential I ψ p hψ]
  rfl

/-- Actual pullback covariance under differentiable maps, including coordinate changes. -/
theorem tensor_pullback
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : Type*} [TopologicalSpace G] (J : ModelWithCorners ℝ F G)
    {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J 1 N]
    (f : N → M) (ψ : M → ℂ) (p : N)
    (hψ : MDifferentiableAt I 𝓘(ℝ, ℂ) ψ (f p))
    (hf : MDifferentiableAt J I f p) (v w : TangentSpace J p) :
    tensor J (ψ ∘ f) p v w =
      tensor I ψ (f p) (mfderiv J I f p v) (mfderiv J I f p w) := by
  simp only [tensor, gram_apply, differential, mfderiv_comp p hψ hf]
  rfl

/-- Evaluation of the scalar's differential on the full tangent bundle. -/
def differentialEval (ψ : M → ℂ) (v : TangentBundle I M) : ℂ :=
  mfderiv I 𝓘(ℝ, ℂ) ψ v.proj v.2

theorem differentialEval_continuous (ψ : M → ℂ) (hψ : ContMDiff I 𝓘(ℝ, ℂ) 1 ψ) :
    Continuous (differentialEval I ψ) := by
  exact (contMDiff_snd_tangentBundle_modelSpace ℂ 𝓘(ℝ, ℂ) (n := 0)).continuous.comp
    (hψ.continuous_tangentMap le_rfl)

/-- C^n regularity on the actual tangent bundle when the scalar is C^(n+1). -/
theorem differentialEval_contMDiff (ψ : M → ℂ) {m n : WithTop ℕ∞}
    (hψ : ContMDiff I 𝓘(ℝ, ℂ) n ψ) (hmn : m + 1 ≤ n) :
    ContMDiff I.tangent 𝓘(ℝ, ℂ) m (differentialEval I ψ) := by
  exact (contMDiff_snd_tangentBundle_modelSpace ℂ 𝓘(ℝ, ℂ)).comp
    (hψ.contMDiff_tangentMap hmn)

/-- A continuous extension of tensor evaluation to two tangent-bundle arguments.
Restricting to pairs with equal base point gives the covariant tensor section. -/
def tensorEval (ψ : M → ℂ) (vw : TangentBundle I M × TangentBundle I M) : ℝ :=
  (differentialEval I ψ vw.1).re * (differentialEval I ψ vw.2).re +
    (differentialEval I ψ vw.1).im * (differentialEval I ψ vw.2).im

@[simp] theorem tensorEval_same_fiber (ψ : M → ℂ) (p : M) (v w : TangentSpace I p) :
    tensorEval I ψ (⟨p, v⟩, ⟨p, w⟩) = tensor I ψ p v w := rfl

theorem tensorEval_continuous (ψ : M → ℂ) (hψ : ContMDiff I 𝓘(ℝ, ℂ) 1 ψ) :
    Continuous (tensorEval I ψ) := by
  have h := differentialEval_continuous I ψ hψ
  exact ((Complex.continuous_re.comp (h.comp continuous_fst)).mul
    (Complex.continuous_re.comp (h.comp continuous_snd))).add
      ((Complex.continuous_im.comp (h.comp continuous_fst)).mul
        (Complex.continuous_im.comp (h.comp continuous_snd)))

theorem tensorEval_contMDiff (ψ : M → ℂ) {m n : WithTop ℕ∞}
    (hψ : ContMDiff I 𝓘(ℝ, ℂ) n ψ) (hmn : m + 1 ≤ n) :
    ContMDiff (I.tangent.prod I.tangent) 𝓘(ℝ, ℝ) m (tensorEval I ψ) := by
  have h := differentialEval_contMDiff I ψ hψ hmn
  have hr := Complex.reCLM.contDiff.contMDiff (n := m)
  have hi := Complex.imCLM.contDiff.contMDiff (n := m)
  exact ((hr.comp (h.comp contMDiff_fst)).mul (hr.comp (h.comp contMDiff_snd))).add
    ((hi.comp (h.comp contMDiff_fst)).mul (hi.comp (h.comp contMDiff_snd)))

/-- Nonnegative sums constructed from the actual real scalar differentials. -/
def multiplet {ι : Type*} [Fintype ι] (weights : ι → M → ℝ)
    (φ : ι → M → ℝ) (p : M) : BilinForm ℝ (TangentSpace I p) :=
  multipletGram (fun i => weights i p)
    (fun i => (mfderiv I 𝓘(ℝ, ℝ) (φ i) p : TangentSpace I p →L[ℝ] ℝ).toLinearMap)

variable [FiniteDimensional ℝ E]

/-- The full intrinsic four-dimensional obstruction for a global C¹ scalar. -/
theorem main (ψ : M → ℂ) (_hψ : ContMDiff I 𝓘(ℝ, ℂ) 1 ψ)
    (h4 : Module.finrank ℝ E = 4) (p : M) :
    (tensor I ψ p).IsSymm ∧
    (∀ v, 0 ≤ tensor I ψ p v v) ∧
    LinearMap.ker (tensor I ψ p) =
      LinearMap.ker (mfderiv I 𝓘(ℝ, ℂ) ψ p).toLinearMap ∧
    Module.finrank ℝ (LinearMap.range (tensor I ψ p)) ≤ 2 ∧
    2 ≤ Module.finrank ℝ (LinearMap.ker (tensor I ψ p)) ∧
    ¬ (tensor I ψ p).Nondegenerate := by
  letI : FiniteDimensional ℝ (TangentSpace I p) := inferInstanceAs (FiniteDimensional ℝ E)
  exact ⟨gram_symmetric _, gram_nonnegative _, gram_ker _, gram_rank_le_two _,
    gram_nullity _ h4, gram_degenerate _ h4⟩

/-- The determinant vanishes in every tangent-space basis. -/
theorem tensor_det_zero (ψ : M → ℂ) (h4 : Module.finrank ℝ E = 4)
    (p : M) (b : Basis (Fin 4) ℝ (TangentSpace I p)) :
    (BilinForm.toMatrix b (tensor I ψ p)).det = 0 := by
  letI : FiniteDimensional ℝ (TangentSpace I p) := inferInstanceAs (FiniteDimensional ℝ E)
  by_contra h
  exact gram_degenerate _ h4 (BilinForm.nondegenerate_of_det_ne_zero (tensor I ψ p) b h)

/-- The manuscript's positive-sign multiplet proposition on a smooth manifold. -/
theorem multiplet_obstruction {ι : Type*} [Fintype ι]
    (weights : ι → M → ℝ) (hw : ∀ i p, 0 ≤ weights i p)
    (φ : ι → M → ℝ) (_hφ : ∀ i, ContMDiff I 𝓘(ℝ, ℝ) 1 (φ i))
    (h4 : Module.finrank ℝ E = 4) (p : M) :
    Module.finrank ℝ (LinearMap.range (multiplet I weights φ p)) ≤ min (Fintype.card ι) 4 ∧
    ∀ v, 0 ≤ multiplet I weights φ p v v := by
  letI : FiniteDimensional ℝ (TangentSpace I p) := inferInstanceAs (FiniteDimensional ℝ E)
  refine ⟨?_, multipletGram_nonnegative _ (fun i => hw i p) _⟩
  simpa only [← h4] using multipletGram_rank (fun i => weights i p)
    (fun i => (mfderiv I 𝓘(ℝ, ℝ) (φ i) p : TangentSpace I p →L[ℝ] ℝ).toLinearMap)

/-- Full rank requires at least four real scalar gradients. Positivity still excludes
every negative direction, independently of their number. -/
theorem multiplet_rank_budget {ι : Type*} [Fintype ι]
    (weights : ι → M → ℝ) (φ : ι → M → ℝ) (p : M)
    (hr : Module.finrank ℝ (LinearMap.range (multiplet I weights φ p)) = 4) :
    4 ≤ Fintype.card ι := by
  letI : FiniteDimensional ℝ (TangentSpace I p) := inferInstanceAs (FiniteDimensional ℝ E)
  have h := multipletGram_rank (fun i => weights i p)
    (fun i => (mfderiv I 𝓘(ℝ, ℝ) (φ i) p : TangentSpace I p →L[ℝ] ℝ).toLinearMap)
  change Module.finrank ℝ (LinearMap.range (multiplet I weights φ p)) ≤ _ at h
  rw [hr] at h
  exact h.trans (min_le_left _ _)

end Manifold
end ReyesMath.ManifoldScalarMetric
