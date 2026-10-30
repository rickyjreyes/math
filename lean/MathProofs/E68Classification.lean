import Mathlib
import MathProofs.E68Sobolev
import MathProofs.E68SmoothClassification
import MathProofs.E68OneDimEnergy

/-!
# E68: the exact dimensional classification on `H¹(ℝⁿ)`

`E68Holds n` is the original estimate with its exact quantifier order: there is one finite constant
`C` such that for **every** field `ψ ∈ H¹(ℝⁿ; ℂ)` with weak gradient `g`, every center `x₀` and
every radius `R > 0`,
`∫_{B_R(x₀)} |∇ψ|² ≤ C R^{n-2} ‖ψ‖²_{H¹}`.
The exponent `n - 2` is an integer, so `R^{-1}` appears when `n = 1`.

* `e68_two`: `E68Holds 2` with `C₂ = 1`.
* `not_e68_one`: in dimension one the nonconstant compact bump violates every constant at
  large radii.
* `not_e68_of_two_lt`: for `n > 2` the smooth concentrations `R^{1-n/2} φ(x/R)` (genuine `H¹`
  fields by `isH1_ofRealFn`) violate every constant at small radii.
* **`e68_iff_two`**: for every `n ≥ 1`, `E68Holds n ↔ n = 2`.
* `e68L2_iff_two`: the same classification for `H¹` stated on `L²` equivalence classes, with the
  (a.e.-unique) weak gradient.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ContDiff

namespace ReyesMath.E68

/-- The E68 estimate in dimension `n`: one constant for every `H¹` field, center and radius. -/
def E68Holds (n : ℕ) : Prop :=
  ∃ C : ℝ, ∀ (ψ : EuclideanSpace ℝ (Fin n) → ℂ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)), IsH1 ψ g →
    ∀ (x₀ : EuclideanSpace ℝ (Fin n)) (R : ℝ), 0 < R →
      (∫ x in Metric.ball x₀ R, ‖g x‖ ^ 2) ≤ C * R ^ ((n : ℤ) - 2) * h1sq ψ g

/-- The local gradient energy is at most the global one. -/
theorem setIntegral_grad_le_integral {n : ℕ} {ψ : EuclideanSpace ℝ (Fin n) → ℂ}
    {g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)} (h : IsH1 ψ g)
    (s : Set (EuclideanSpace ℝ (Fin n))) :
    (∫ x in s, ‖g x‖ ^ 2) ≤ ∫ x, ‖g x‖ ^ 2 :=
  setIntegral_le_integral h.integrable_grad_sq (Eventually.of_forall fun _ => sq_nonneg _)

/-- **Dimension two**: the estimate holds with `C₂ = 1`, for every `H¹(ℝ²)` field, center and
radius. -/
theorem e68_two_bound {ψ : EuclideanSpace ℝ (Fin 2) → ℂ}
    {g : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℂ (Fin 2)} (h : IsH1 ψ g)
    (x₀ : EuclideanSpace ℝ (Fin 2)) (R : ℝ) :
    (∫ x in Metric.ball x₀ R, ‖g x‖ ^ 2) ≤ h1sq ψ g := by
  have h1 := setIntegral_grad_le_integral h (Metric.ball x₀ R)
  have h2 : 0 ≤ ∫ x, ‖ψ x‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  unfold h1sq
  linarith

theorem e68_two : E68Holds 2 := by
  refine ⟨1, fun ψ g h x₀ R _ => ?_⟩
  simpa using e68_two_bound h x₀ R

/-! ### Dimension one -/

/-- The derivative energy density of the compact bump vanishes outside `B_{1/2}`. -/
theorem compactProfile_fderiv_support (n : ℕ) :
    Function.support (fun x : EuclideanSpace ℝ (Fin n) =>
      ‖fderiv ℝ (fun y => compactProfile n y) x‖ ^ 2) ⊆
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (1 / 2) := by
  intro x hx
  have hd : x ∈ Function.support (fderiv ℝ (fun y => compactProfile n y)) := by
    intro hz
    exact hx (by simp [hz])
  have := (support_fderiv_subset ℝ) hd
  change x ∈ tsupport (compactProfile n : EuclideanSpace ℝ (Fin n) → ℝ) at this
  rw [(compactProfile n).tsupport_eq] at this
  simpa [compactProfile] using this

/-- For `R ≥ 1` the ball energy of the bump is its whole-space energy. -/
theorem compactProfile_ball_energy (n : ℕ) {R : ℝ} (hR : 1 ≤ R) :
    (∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R,
      ‖fderiv ℝ (fun y => compactProfile n y) x‖ ^ 2) =
      ∫ x, ‖fderiv ℝ (fun y => compactProfile n y) x‖ ^ 2 := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  by_contra he
  have hx' := compactProfile_fderiv_support n he
  apply hx
  rw [Metric.mem_closedBall] at hx'
  exact Metric.mem_ball.2 (by linarith)

/-- **Dimension one**: no constant works. The nonconstant compact bump has a fixed positive
gradient energy on every ball `B_R`, `R ≥ 1`, while `C R^{-1} ‖ψ‖²_{H¹} → 0`. -/
theorem not_e68_one : ¬ E68Holds 1 := by
  rintro ⟨C, hC⟩
  set φ : EuclideanSpace ℝ (Fin 1) → ℝ := fun y => compactProfile 1 y
  have hφ : ContDiff ℝ ∞ φ := compactProfile_smooth 1
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by exact_mod_cast le_top)
  have hφc : HasCompactSupport φ := compactProfile_hasCompactSupport 1
  set A : ℝ := ∫ x, ‖fderiv ℝ φ x‖ ^ 2
  set H : ℝ := (∫ x, φ x ^ 2) + A
  have hA : 0 < A := compactProfile_gradient_energy_positive 1 (by norm_num)
  apply large_radius_one_dimensional_obstruction A H hA
  refine ⟨C, fun R hR => ?_⟩
  have hR0 : 0 < R := by linarith
  have hb := hC (ofRealFn φ) (gradVec (ofRealFn φ)) (isH1_ofRealFn hφ1 hφc) 0 R hR0
  have hd := hφ1.differentiable le_rfl
  have hball : (∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin 1)) R,
      ‖gradVec (ofRealFn φ) x‖ ^ 2) = A := by
    simp_rw [norm_gradVec_ofRealFn (hd _)]
    exact compactProfile_ball_energy 1 hR
  rw [hball, h1sq_ofRealFn hφ1] at hb
  have hz : R ^ (((1 : ℕ) : ℤ) - 2) = R⁻¹ := by norm_num
  rw [hz] at hb
  calc A ≤ C * R⁻¹ * H := hb
    _ = C * H / R := by ring

/-! ### Dimension one through the verified whole-line bump

The failure in dimension one is also derived from the earlier whole-line theorem
`compactOneDim_forbids_uniform_inverse_radius_energy` for the bump `compactOneDim` on `ℝ`, by
lifting it to `ℝ¹ = EuclideanSpace ℝ (Fin 1)` along the measure-preserving coordinate. -/

/-- The coordinate `x ↦ x 0` of `ℝ¹` as a measurable equivalence with `ℝ`. -/
def lineEquiv : EuclideanSpace ℝ (Fin 1) ≃ᵐ ℝ :=
  (EuclideanSpace.measurableEquiv (Fin 1)).trans (MeasurableEquiv.funUnique (Fin 1) ℝ)

theorem lineEquiv_apply (x : EuclideanSpace ℝ (Fin 1)) : lineEquiv x = x 0 := rfl

theorem lineEquiv_measurePreserving :
    MeasurePreserving lineEquiv (volume : Measure (EuclideanSpace ℝ (Fin 1))) volume :=
  (volume_preserving_funUnique (Fin 1) ℝ).comp
    (EuclideanSpace.volume_preserving_measurableEquiv (Fin 1))

theorem norm_eq_abs_coord (x : EuclideanSpace ℝ (Fin 1)) : ‖x‖ = |x 0| := by
  rw [EuclideanSpace.norm_eq]
  simp [Real.sqrt_sq_eq_abs]

/-- The verified whole-line bump `compactOneDim`, as a field on `ℝ¹`. -/
def lineBump (x : EuclideanSpace ℝ (Fin 1)) : ℝ := compactOneDim (x 0)

theorem lineBump_contDiff : ContDiff ℝ ∞ lineBump :=
  compactOneDim_smooth.comp (EuclideanSpace.proj (0 : Fin 1) : _ →L[ℝ] ℝ).contDiff

theorem lineBump_hasCompactSupport : HasCompactSupport lineBump := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 1)) (1 / 2))
    fun x hx => ?_
  apply compactOneDim.zero_of_le_dist
  rw [Metric.mem_closedBall, dist_zero_right, norm_eq_abs_coord, not_le] at hx
  simp only [compactOneDim, Real.dist_eq, sub_zero]
  exact hx.le

theorem fderiv_lineBump_ev (x : EuclideanSpace ℝ (Fin 1)) :
    fderiv ℝ lineBump x (ev 0) = deriv (fun t : ℝ => compactOneDim t) (x 0) := by
  have hd : DifferentiableAt ℝ (fun t : ℝ => compactOneDim t) (x 0) :=
    (compactOneDim_smooth.differentiable (by simp)) _
  have h1 : HasFDerivAt lineBump
      ((fderiv ℝ (fun t : ℝ => compactOneDim t) (x 0)).comp
        (EuclideanSpace.proj (0 : Fin 1) : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ)) x :=
    hd.hasFDerivAt.comp x (EuclideanSpace.proj (0 : Fin 1) : _ →L[ℝ] ℝ).hasFDerivAt
  rw [h1.fderiv, ContinuousLinearMap.comp_apply]
  simp [ev]

theorem norm_gradVec_lineBump_sq (x : EuclideanSpace ℝ (Fin 1)) :
    ‖gradVec (ofRealFn lineBump) x‖ ^ 2 = (deriv (fun t : ℝ => compactOneDim t) (x 0)) ^ 2 := by
  have hd : DifferentiableAt ℝ lineBump x := (lineBump_contDiff.differentiable (by simp)) x
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_one, gradVec_ofRealFn_apply hd,
    fderiv_lineBump_ev, Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem integral_comp_line (F : ℝ → ℝ) :
    (∫ x : EuclideanSpace ℝ (Fin 1), F (x 0)) = ∫ t : ℝ, F t :=
  lineEquiv_measurePreserving.integral_comp' F

theorem setIntegral_ball_comp_line (F : ℝ → ℝ) (R : ℝ) :
    (∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin 1)) R, F (x 0)) =
      ∫ t in Metric.ball (0 : ℝ) R, F t := by
  have hpre : lineEquiv ⁻¹' Metric.ball (0 : ℝ) R = Metric.ball (0 : EuclideanSpace ℝ (Fin 1)) R := by
    ext x
    simp only [Set.mem_preimage, Metric.mem_ball, dist_zero_right, lineEquiv_apply,
      Real.norm_eq_abs, norm_eq_abs_coord]
  rw [← hpre]
  exact lineEquiv_measurePreserving.setIntegral_preimage_emb
    lineEquiv.measurableEmbedding F _

/-- **Dimension one, via the verified whole-line bump.** The lifted bump `compactOneDim (x 0)`
is an `H¹(ℝ¹)` field whose ball, mass and gradient energies are exactly the whole-line
integrals of `compactOneDim`, so `compactOneDim_forbids_uniform_inverse_radius_energy` rules out
every constant. -/
theorem not_e68_one_of_line : ¬ E68Holds 1 := by
  rintro ⟨C, hC⟩
  apply compactOneDim_forbids_uniform_inverse_radius_energy
  refine ⟨C, fun R hR => ?_⟩
  have hR0 : 0 < R := by linarith
  have hφ1 : ContDiff ℝ 1 lineBump := lineBump_contDiff.of_le (by exact_mod_cast le_top)
  have hb := hC (ofRealFn lineBump) (gradVec (ofRealFn lineBump))
    (isH1_ofRealFn hφ1 lineBump_hasCompactSupport) 0 R hR0
  have e1 : (∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin 1)) R,
      ‖gradVec (ofRealFn lineBump) x‖ ^ 2) =
      ∫ t in Metric.ball (0 : ℝ) R, (deriv (fun t : ℝ => compactOneDim t) t) ^ 2 := by
    simp_rw [norm_gradVec_lineBump_sq]
    exact setIntegral_ball_comp_line (fun t => (deriv (fun t : ℝ => compactOneDim t) t) ^ 2) R
  have e2 : h1sq (ofRealFn lineBump) (gradVec (ofRealFn lineBump)) =
      (∫ t : ℝ, (compactOneDim t) ^ 2) +
        ∫ t : ℝ, (deriv (fun t : ℝ => compactOneDim t) t) ^ 2 := by
    unfold h1sq
    simp_rw [norm_ofRealFn, norm_gradVec_lineBump_sq, lineBump]
    rw [integral_comp_line (fun t => (compactOneDim t) ^ 2),
      integral_comp_line (fun t => (deriv (fun t : ℝ => compactOneDim t) t) ^ 2)]
  rw [e1, e2] at hb
  have hz : R ^ (((1 : ℕ) : ℤ) - 2) = R⁻¹ := by norm_num
  rw [hz] at hb
  show (∫ t in Metric.ball (0 : ℝ) R, (deriv (fun t : ℝ => compactOneDim t) t) ^ 2) ≤
    C * ((∫ t : ℝ, (compactOneDim t) ^ 2) +
      ∫ t : ℝ, (deriv (fun t : ℝ => compactOneDim t) t) ^ 2) / R
  calc _ ≤ _ := hb
    _ = _ := by ring

/-! ### Dimensions above two -/

/-- **Dimensions `n > 2`**: no constant works; the smooth concentrations `R^{1-n/2} φ(x/R)` are
`H¹` fields with fixed gradient energy `A > 0`, all of it inside `B_R`, and squared mass
`R² B`. -/
theorem not_e68_of_two_lt {n : ℕ} (hn : 2 < n) : ¬ E68Holds n := by
  rintro ⟨C, hC⟩
  apply no_uniform_E68_for_smooth_concentrations n hn
  refine ⟨C, fun R hR => ?_⟩
  have hsm := smoothConcentration_smooth n R
  have hsm1 : ContDiff ℝ 1 (smoothConcentration n R) := hsm.of_le (by exact_mod_cast le_top)
  have hb := hC (ofRealFn (smoothConcentration n R)) (gradVec (ofRealFn (smoothConcentration n R)))
    (isH1_ofRealFn hsm1 (smoothConcentration_hasCompactSupport n R hR)) 0 R hR
  have hd := hsm1.differentiable le_rfl
  simp_rw [norm_gradVec_ofRealFn (hd _)] at hb
  rw [h1sq_ofRealFn hsm1] at hb
  have hz : R ^ ((n : ℤ) - 2) = R ^ (n - 2) := by
    rw [← zpow_natCast, Nat.cast_sub hn.le]
    norm_num
  rwa [hz] at hb

/-! ### The classification -/

/-- **Theorem 1.1 (exact dimensional classification).** For every dimension `n ≥ 1`, the E68
estimate holds on `H¹(ℝⁿ)` with a uniform constant if and only if `n = 2`. -/
theorem e68_iff_two (n : ℕ) (hn : 1 ≤ n) : E68Holds n ↔ n = 2 := by
  constructor
  · intro h
    rcases Nat.lt_or_ge n 2 with h1 | h2
    · have : n = 1 := by omega
      subst this
      exact absurd h not_e68_one
    · rcases h2.lt_or_eq with h3 | h3
      · exact absurd h (not_e68_of_two_lt h3)
      · exact h3.symm
  · rintro rfl
    exact e68_two

/-! ### The classification on `L²` equivalence classes -/

/-- `H¹(ℝⁿ; ℂ)` as a set of `L²` equivalence classes. -/
def H1 (n : ℕ) : Set (Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :=
  {u | MemH1 (u : EuclideanSpace ℝ (Fin n) → ℂ)}

/-- The weak gradient of a class in `H¹` (unique up to a.e. equality by `IsH1.ae_eq_grad`). -/
def h1Grad {n : ℕ} (u : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n) :=
  open Classical in
  if h : MemH1 (u : EuclideanSpace ℝ (Fin n) → ℂ) then Classical.choose h else 0

theorem isH1_h1Grad {n : ℕ} {u : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))}
    (hu : u ∈ H1 n) : IsH1 (u : EuclideanSpace ℝ (Fin n) → ℂ) (h1Grad u) := by
  have : MemH1 (u : EuclideanSpace ℝ (Fin n) → ℂ) := hu
  rw [h1Grad, dif_pos this]
  exact Classical.choose_spec this

/-- The E68 estimate for `L²` classes in `H¹`, with the weak gradient of the class. -/
def E68L2Holds (n : ℕ) : Prop :=
  ∃ C : ℝ, ∀ u ∈ H1 n, ∀ (x₀ : EuclideanSpace ℝ (Fin n)) (R : ℝ), 0 < R →
    (∫ x in Metric.ball x₀ R, ‖h1Grad u x‖ ^ 2) ≤
      C * R ^ ((n : ℤ) - 2) * h1sq (u : EuclideanSpace ℝ (Fin n) → ℂ) (h1Grad u)

/-- The function-level and class-level formulations agree. -/
theorem e68L2_iff_e68 (n : ℕ) : E68L2Holds n ↔ E68Holds n := by
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C, fun ψ g h x₀ R hR => ?_⟩
    set u := h.memLp.toLp ψ
    have hψu : (u : EuclideanSpace ℝ (Fin n) → ℂ) =ᵐ[volume] ψ := h.memLp.coeFn_toLp
    have hu' : IsH1 (u : EuclideanSpace ℝ (Fin n) → ℂ) g := h.congr_ae hψu.symm (ae_eq_refl _)
    have hu : u ∈ H1 n := ⟨g, hu'⟩
    have hg : h1Grad u =ᵐ[volume] g := (isH1_h1Grad hu).ae_eq_grad hu'
    have := hC u hu x₀ R hR
    rwa [setIntegral_grad_congr_ae hg, h1sq_congr_ae hψu hg] at this
  · rintro ⟨C, hC⟩
    exact ⟨C, fun u hu x₀ R hR => hC _ _ (isH1_h1Grad hu) x₀ R hR⟩

/-- **The classification on `L²` equivalence classes.** -/
theorem e68L2_iff_two (n : ℕ) (hn : 1 ≤ n) : E68L2Holds n ↔ n = 2 :=
  (e68L2_iff_e68 n).trans (e68_iff_two n hn)

end ReyesMath.E68
