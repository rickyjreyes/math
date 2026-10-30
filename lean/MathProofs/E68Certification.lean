import MathProofs.E68Classification
import MathProofs.E68Singular
import MathProofs.E68Corrected
import MathProofs.E68SobolevEmbedding
import MathProofs.E68H2

/-!
# E68: certification of the localized gradient-energy manuscript

Manuscript: `papers/localized-gradient-energy-e68/main.tex` (issue #41). Every statement below
is written with its exact quantifiers over the Sobolev spaces of `E68Sobolev` (`IsH1`, by weak
derivatives) and `E68H2` (`IsH2`, weak derivatives of order `≤ 2`), with actual Lebesgue integrals
on open Euclidean balls `B_R(x₀) = Metric.ball x₀ R ⊂ ℝⁿ = EuclideanSpace ℝ (Fin n)`. The
squared norm is `‖ψ‖²_{H¹} = ∫ |ψ|² + ∫ |∇ψ|²`. The constant `ω_n = |B₁(0)|` is
`volume.real (ball 0 1)`, and `σ_{n-1}` is the surface measure of the unit sphere
(`Singular.surfaceArea n`, equal to `n ω_n`).

* `bridge`: the Sobolev space `H¹`. Weak gradients are unique a.e. Membership and energies
  depend only on a.e. classes. `C¹_c` fields are in `H¹` with their classical gradients. `H¹`
  matches `WeakH1Field`, `E26.IsWeakDeriv` on `ℝⁿ`, and the strong gradient of `Sobolev.H2`.
* `classification` (Theorem 1.1): `E68(n) ↔ n = 2` for all `n ≥ 1`, uniformly over centers.
  `classification_center` is the boxed form at the center `0`, `classification_L2` the form on
  `L²` classes, and `dimension_two` gives `C₂ = 1`.
* `dimension_one`: the large-radius obstruction in dimension one.
* `singular_field` (Theorem 1.1, `n > 2`): the fixed field `χ(|x|)|x|^{-a}`.
* `smooth_concentration` (Proposition 2.1).
* `corrected` (Theorem 3.1, E68′), `admissible` (Corollary 3.2), `remark_3_3` (Remark 3.3).
* `sobolev_three`, `sobolev_four`: `H¹(ℝ³) ⊂ L⁶`, `H¹(ℝ⁴) ⊂ L⁴` for weak `H¹` fields.
* `h2_localized` (Corollary 4.1), `h2_failure` and `h2_failure_smooth` (Proposition 4.2).
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ContDiff ENNReal NNReal

namespace ReyesMath

namespace E68Cert

open E68

variable {n : ℕ}

local notation "Rn" => EuclideanSpace ℝ (Fin n)

/-! ### The Sobolev space `H¹(ℝⁿ)` -/

/-- **The `H¹` bridge.** -/
theorem bridge :
    -- uniqueness of the weak gradient
    (∀ (ψ : Rn → ℂ) (g g' : Rn → EuclideanSpace ℂ (Fin n)),
      IsH1 ψ g → IsH1 ψ g' → g =ᵐ[volume] g') ∧
    -- membership and the energies depend only on the a.e. classes
    (∀ (ψ ψ' : Rn → ℂ) (g g' : Rn → EuclideanSpace ℂ (Fin n)), IsH1 ψ g →
      ψ =ᵐ[volume] ψ' → g =ᵐ[volume] g' → IsH1 ψ' g' ∧ h1sq ψ' g' = h1sq ψ g) ∧
    -- smooth inclusion with the classical gradient
    (∀ f : Rn → ℂ, ContDiff ℝ 1 f → HasCompactSupport f → IsH1 f (gradVec f)) ∧
    -- correspondence with the directional structure `WeakH1Field`
    (∀ ψ : Rn → ℂ, MemH1 ψ ↔ ∃ u : WeakH1Field n, u.ψ = ψ) ∧
    -- correspondence with `E26.IsWeakDeriv` on the whole space
    (∀ (ψ : Rn → ℂ) (g : Rn → EuclideanSpace ℂ (Fin n)), IsH1 ψ g ↔
      MemLp ψ 2 volume ∧ MemLp g 2 volume ∧
        ∀ i : Fin n, E26.IsWeakDeriv Set.univ ![ev i] ψ (fun x => g x i)) ∧
    -- compatibility with `Sobolev.H2`
    (∀ U : Sobolev.H2 n, IsH1 (U.val : Rn → ℂ)
      (fun x => WithLp.toLp 2 fun i => (U.grad i : Rn → ℂ) x)) :=
  ⟨fun _ _ _ h h' => h.ae_eq_grad h',
    fun _ _ _ _ h hψ hg => ⟨h.congr_ae hψ hg, (h1sq_congr_ae hψ hg).symm⟩,
    fun _ hf hc => isH1_of_contDiff hf hc, memH1_iff_exists_weakH1Field,
    fun _ _ => isH1_iff_isWeakDeriv, isH1_of_H2⟩

/-! ### Theorem 1.1: the classification -/

/-- **Theorem 1.1 (exact dimensional classification).** For every `n ≥ 1`: there is a finite
constant `C`, independent of the field, the center and the radius, such that every
`ψ ∈ H¹(ℝⁿ)` satisfies `∫_{B_R(x₀)} |∇ψ|² ≤ C R^{n-2} ‖ψ‖²_{H¹}` for all `x₀` and `R > 0`, if
and only if `n = 2`. -/
theorem classification (n : ℕ) (hn : 1 ≤ n) :
    (∃ C : ℝ, ∀ (ψ : EuclideanSpace ℝ (Fin n) → ℂ)
      (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)), IsH1 ψ g →
      ∀ (x₀ : EuclideanSpace ℝ (Fin n)) (R : ℝ), 0 < R →
        (∫ x in ball x₀ R, ‖g x‖ ^ 2) ≤
          C * R ^ ((n : ℤ) - 2) * ((∫ x, ‖ψ x‖ ^ 2) + ∫ x, ‖g x‖ ^ 2)) ↔ n = 2 :=
  e68_iff_two n hn

/-- **Theorem 1.1 at the center `0`** (the boxed `(E68)`). -/
theorem classification_center (n : ℕ) (hn : 1 ≤ n) :
    (∃ C : ℝ, ∀ (ψ : EuclideanSpace ℝ (Fin n) → ℂ)
      (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)), IsH1 ψ g →
      ∀ R : ℝ, 0 < R →
        (∫ x in ball (0 : EuclideanSpace ℝ (Fin n)) R, ‖g x‖ ^ 2) ≤
          C * R ^ ((n : ℤ) - 2) * ((∫ x, ‖ψ x‖ ^ 2) + ∫ x, ‖g x‖ ^ 2)) ↔ n = 2 :=
  e68Holds0_iff_two n hn

/-- **Theorem 1.1 on `L²` equivalence classes**, with the a.e.-unique weak gradient. -/
theorem classification_L2 (n : ℕ) (hn : 1 ≤ n) : E68L2Holds n ↔ n = 2 :=
  e68L2_iff_two n hn

/-- **`n = 2`: `C₂ = 1`.** -/
theorem dimension_two (ψ : EuclideanSpace ℝ (Fin 2) → ℂ)
    (g : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℂ (Fin 2)) (h : IsH1 ψ g)
    (x₀ : EuclideanSpace ℝ (Fin 2)) (R : ℝ) :
    (∫ x in ball x₀ R, ‖g x‖ ^ 2) ≤ 1 * R ^ (((2 : ℕ) : ℤ) - 2) * h1sq ψ g := by
  simpa using e68_two_bound h x₀ R

/-- **`n = 1`: the large-radius obstruction.** The nonconstant compact bump `φ` has
`∫_{B_R} |φ'|² = ∫_ℝ |φ'|² > 0` for every `R ≥ 1`, and no constant works. -/
theorem dimension_one :
    (0 < ∫ x, ‖fderiv ℝ (fun y => compactProfile 1 y) x‖ ^ 2) ∧
    (∀ R : ℝ, 1 ≤ R →
      (∫ x in ball (0 : EuclideanSpace ℝ (Fin 1)) R,
        ‖fderiv ℝ (fun y => compactProfile 1 y) x‖ ^ 2) =
        ∫ x, ‖fderiv ℝ (fun y => compactProfile 1 y) x‖ ^ 2) ∧
    ¬ E68Holds0 1 :=
  ⟨compactProfile_gradient_energy_positive 1 (by norm_num),
    fun _ hR => compactProfile_ball_energy 1 hR, not_e68Holds0_one⟩

/-- **The fixed singular field (`n > 2`).** For `0 < a < (n-2)/2`, the field
`ψ(x) = χ(|x|)|x|^{-a}`, with `χ = 1` on `[0,1]` and `χ = 0` on `[2,∞)`, has these
properties. It is `C^∞` off the origin, with classical gradient `-a|x|^{-a-2}x` on
`0 < |x| < 1`. Its classical gradient off the origin is a weak gradient on all of `ℝⁿ`, so
`ψ ∈ H¹`. The exact integrals are `∫_{B₁}|ψ|² = σ_{n-1}/(n-2a)` and
`∫_{B_R}|∇ψ|² = σ_{n-1}a²R^{n-2-2a}/(n-2-2a)` for `0 < R ≤ 1`. Finally
`R^{2-n}∫_{B_R}|∇ψ|² → ∞`, so this one field defeats every proposed constant at arbitrarily
small radii. -/
theorem singular_field {a : ℝ} (ha : 0 < a) (ha' : a < ((n : ℝ) - 2) / 2) :
    (∀ r : ℝ, 0 ≤ r → r ≤ 1 → Singular.chi r = 1) ∧
    (∀ r : ℝ, 2 ≤ r → Singular.chi r = 0) ∧ ContDiff ℝ ∞ Singular.chi ∧
    (∀ x : Rn, Singular.psi a x = Singular.chi ‖x‖ * ‖x‖ ^ (-a)) ∧
    (∀ x : Rn, x ≠ 0 → ContDiffAt ℝ ∞ (Singular.psi a) x) ∧
    (∀ x : Rn, x ≠ 0 → ‖x‖ < 1 → gradient (Singular.psi a) x = (-a * ‖x‖ ^ (-a - 2)) • x) ∧
    (∀ x : Rn, x ≠ 0 → Singular.gradC a x = gradVec (ofRealFn (Singular.psi a)) x) ∧
    IsH1 (ofRealFn (Singular.psi a) : Rn → ℂ) (Singular.gradC a) ∧
    (∫ x in ball (0 : Rn) 1, ‖ofRealFn (Singular.psi a) x‖ ^ 2) =
      Singular.surfaceArea n / ((n : ℝ) - 2 * a) ∧
    (∫ x in ball (0 : Rn) 1, ‖Singular.gradC a x‖ ^ 2) =
      Singular.surfaceArea n * a ^ 2 / ((n : ℝ) - 2 - 2 * a) ∧
    (∀ R : ℝ, 0 < R → R < 1 →
      (∫ x in ball (0 : Rn) R, ‖Singular.gradC a x‖ ^ 2) =
        Singular.surfaceArea n * a ^ 2 * R ^ ((n : ℝ) - 2 - 2 * a) / ((n : ℝ) - 2 - 2 * a)) ∧
    Tendsto (fun R : ℝ => R ^ ((2 : ℤ) - n) *
      ∫ x in ball (0 : Rn) R, ‖Singular.gradC a x‖ ^ 2) (𝓝[>] 0) atTop ∧
    (∀ C : ℝ, ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧ R < ε ∧
      C * R ^ ((n : ℤ) - 2) * h1sq (n := n) (ofRealFn (Singular.psi a)) (Singular.gradC a) <
        ∫ x in ball (0 : Rn) R, ‖Singular.gradC a x‖ ^ 2) ∧
    Singular.surfaceArea n = n * volume.real (ball (0 : Rn) 1) :=
  ⟨fun _ h0 h1 => Singular.chi_eq_one h0 h1, fun _ h2 => Singular.chi_eq_zero h2,
    Singular.contDiff_chi, fun _ => rfl, fun _ hx => Singular.contDiffAt_psi a hx,
    fun _ hx0 hx1 => Singular.gradient_psi_of_lt_one a hx0 hx1,
    fun _ hx => Singular.gradC_eq_gradVec a hx, Singular.isH1 ha ha',
    Singular.integral_sq_ball_one ha ha', Singular.integral_grad_sq_ball_one ha ha',
    fun _ hR hR1 => Singular.integral_grad_sq_ball_sphere ha ha' hR hR1,
    Singular.blowup ha ha', fun C _ hε => Singular.defeats_every_constant ha ha' C _ hε,
    Singular.surfaceArea_eq n⟩

/-! ### Proposition 2.1: smooth concentration -/

/-- **Proposition 2.1.** For `n > 2` and every `C > 0` there are `ψ ∈ C_c^∞(ℝⁿ)` and `R > 0`
with `∫_{B_R} |∇ψ|² > C R^{n-2} ‖ψ‖²_{H¹}`. Every such `ψ` is an admissible `H¹` field, with
its classical gradient as weak gradient. -/
theorem smooth_concentration (hn : 2 < n) (C : ℝ) :
    ∃ (ψ : Rn → ℝ) (R : ℝ), ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ 0 < R ∧
      IsH1 (ofRealFn ψ) (gradVec (ofRealFn ψ)) ∧
      C * R ^ (n - 2) * ((∫ x, ψ x ^ 2) + ∫ x, ‖fderiv ℝ ψ x‖ ^ 2) <
        ∫ x in ball (0 : Rn) R, ‖fderiv ℝ ψ x‖ ^ 2 := by
  by_contra hcon
  push_neg at hcon
  apply no_uniform_E68_for_smooth_concentrations n hn
  refine ⟨C, fun R hR => ?_⟩
  have hsm := smoothConcentration_smooth n R
  exact hcon _ R hsm (smoothConcentration_hasCompactSupport n R hR) hR
    (isH1_ofRealFn (hsm.of_le (by exact_mod_cast le_top))
      (smoothConcentration_hasCompactSupport n R hR))

/-! ### Theorem 3.1, Corollary 3.2, Remark 3.3 -/

/-- **Theorem 3.1 (E68′).** For `n > 2`, `ψ ∈ H¹(ℝⁿ)` with `∇ψ ∈ Lⁿ(ℝⁿ)`, every `x₀` and every
`R > 0`: `∫_{B_R(x₀)} |∇ψ|² ≤ ω_n^{1-2/n} R^{n-2} ‖∇ψ‖²_{Lⁿ}`, with
`‖∇ψ‖²_{Lⁿ} = (∫ |∇ψ|ⁿ)^{2/n}` and `ω_n = |B₁(0)|`. -/
theorem corrected (hn : 2 < n) (ψ : Rn → ℂ) (g : Rn → EuclideanSpace ℂ (Fin n))
    (h : IsH1 ψ g) (hgn : MemLp g n volume) (x₀ : Rn) (R : ℝ) (hR : 0 < R) :
    (∫ x in ball x₀ R, ‖g x‖ ^ 2) ≤
      volume.real (ball (0 : Rn) 1) ^ (1 - 2 / (n : ℝ)) * R ^ ((n : ℤ) - 2) *
        (∫ x, ‖g x‖ ^ n) ^ (2 / (n : ℝ)) :=
  e68_corrected hn h hgn x₀ hR

/-- **Corollary 3.2 (admissible class).** -/
theorem admissible (hn : 2 < n)
    (𝒜 : Set ((Rn → ℂ) × (Rn → EuclideanSpace ℂ (Fin n)))) (K : ℝ)
    (hA : ∀ p ∈ 𝒜, IsH1 p.1 p.2 ∧ MemLp p.2 n volume ∧
      (∫ x, ‖p.2 x‖ ^ n) ^ (1 / (n : ℝ)) ≤ K * Real.sqrt (h1sq p.1 p.2)) :
    ∀ p ∈ 𝒜, ∀ (x₀ : Rn) (R : ℝ), 0 < R →
      (∫ x in ball x₀ R, ‖p.2 x‖ ^ 2) ≤
        volume.real (ball (0 : Rn) 1) ^ (1 - 2 / (n : ℝ)) * K ^ 2 * R ^ ((n : ℤ) - 2) *
          h1sq p.1 p.2 :=
  e68_admissible hn 𝒜 K hA

/-- **Remark 3.3.** The a priori bound of Corollary 3.2 does not follow from `H¹` membership. -/
theorem remark_3_3 (hn : 2 < n) :
    ¬ ∃ K : ℝ, ∀ (ψ : Rn → ℂ) (g : Rn → EuclideanSpace ℂ (Fin n)), IsH1 ψ g →
      MemLp g n volume ∧ (∫ x, ‖g x‖ ^ n) ^ (1 / (n : ℝ)) ≤ K * Real.sqrt (h1sq ψ g) :=
  no_apriori_bound_on_H1 hn

/-! ### Sobolev embeddings -/

/-- **`H¹(ℝ³) ⊂ L⁶`** for weak `H¹` fields. -/
theorem sobolev_three (ψ : EuclideanSpace ℝ (Fin 3) → ℂ)
    (g : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℂ (Fin 3)) (h : IsH1 ψ g) :
    MemLp ψ 6 volume ∧ eLpNorm ψ 6 volume ≤ sobolevConst 3 * eLpNorm g 2 volume := by
  have hp : ((6 : ℝ≥0) : ℝ)⁻¹ = 2⁻¹ - ((3 : ℕ) : ℝ)⁻¹ := by norm_num
  have e : ((6 : ℝ≥0) : ℝ≥0∞) = 6 := by norm_num
  have h1 := memLp_of_isH1 (by norm_num) hp h
  have h2 := sobolev_H1 (by norm_num) hp h
  rw [e] at h1 h2
  exact ⟨h1, h2⟩

/-- **`H¹(ℝ⁴) ⊂ L⁴`** for weak `H¹` fields. -/
theorem sobolev_four (ψ : EuclideanSpace ℝ (Fin 4) → ℂ)
    (g : EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℂ (Fin 4)) (h : IsH1 ψ g) :
    MemLp ψ 4 volume ∧ eLpNorm ψ 4 volume ≤ sobolevConst 4 * eLpNorm g 2 volume := by
  have hp : ((4 : ℝ≥0) : ℝ)⁻¹ = 2⁻¹ - ((4 : ℕ) : ℝ)⁻¹ := by norm_num
  have e : ((4 : ℝ≥0) : ℝ≥0∞) = 4 := by norm_num
  have h1 := memLp_of_isH1 (by norm_num) hp h
  have h2 := sobolev_H1 (by norm_num) hp h
  rw [e] at h1 h2
  exact ⟨h1, h2⟩

/-! ### Corollary 4.1 and Proposition 4.2 -/

/-- **Corollary 4.1.** For `n ∈ {3, 4}` there is a constant `C_n`, independent of `ψ`, `x₀` and
`R`, with `∫_{B_R(x₀)} |∇ψ|² ≤ C_n R^{n-2} ‖ψ‖²_{H²}` for every `ψ ∈ H²(ℝⁿ)`. -/
theorem h2_localized (hn : n = 3 ∨ n = 4) :
    ∃ C : ℝ, ∀ (ψ : Rn → ℂ) (g : Rn → EuclideanSpace ℂ (Fin n))
      (H : Fin n → Rn → EuclideanSpace ℂ (Fin n)), IsH2 ψ g H →
        ∀ (x₀ : Rn) (R : ℝ), 0 < R →
          (∫ x in ball x₀ R, ‖g x‖ ^ 2) ≤
            C * R ^ ((n : ℤ) - 2) *
              ((∫ x, ‖ψ x‖ ^ 2) + (∫ x, ‖g x‖ ^ 2) + ∑ i, ∫ x, ‖H i x‖ ^ 2) :=
  e68_H2 hn

/-- **Proposition 4.2.** For `n > 4` there is no constant `C_n` for which the `H²` estimate
holds for all `ψ ∈ C_c^∞(ℝⁿ)` and all `R > 0`. -/
theorem h2_failure_smooth (hn : 4 < n) :
    ¬ ∃ C : ℝ, ∀ ψ : Rn → ℂ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → ∀ R : ℝ, 0 < R →
      (∫ x in ball (0 : Rn) R, ‖gradVec ψ x‖ ^ 2) ≤
        C * R ^ ((n : ℤ) - 2) *
          h2sq ψ (gradVec ψ) (fun i => gradVec (fun x => gradVec ψ x i)) :=
  not_e68_H2_smooth hn

/-- **Proposition 4.2 on `H²`.** -/
theorem h2_failure (hn : 4 < n) :
    ¬ ∃ C : ℝ, ∀ (ψ : Rn → ℂ) (g : Rn → EuclideanSpace ℂ (Fin n))
      (H : Fin n → Rn → EuclideanSpace ℂ (Fin n)), IsH2 ψ g H →
        ∀ (x₀ : Rn) (R : ℝ), 0 < R →
          (∫ x in ball x₀ R, ‖g x‖ ^ 2) ≤ C * R ^ ((n : ℤ) - 2) * h2sq ψ g H :=
  not_e68_H2 hn

/-- The exact scaling identities of Proposition 4.2 for `u_R(x) = R^{2-n/2} φ(x/R)`. -/
theorem h2_scaling {R : ℝ} (hR : 0 < R) {φ : Rn → ℂ} (hφ : ContDiff ℝ 2 φ) :
    (∫ x, ‖dilateH2 R φ x‖ ^ 2) = R ^ 4 * ∫ x, ‖φ x‖ ^ 2 ∧
    (∫ x, ‖gradVec (dilateH2 R φ) x‖ ^ 2) = R ^ 2 * ∫ x, ‖gradVec φ x‖ ^ 2 ∧
    ∀ i : Fin n, (∫ x, ‖gradVec (fun y => gradVec (dilateH2 R φ) y i) x‖ ^ 2) =
      ∫ x, ‖gradVec (fun y => gradVec φ y i) x‖ ^ 2 :=
  ⟨integral_dilateH2_sq hR φ, integral_gradVec_dilateH2_sq hR (hφ.differentiable (by simp)),
    fun i => integral_hess_dilateH2_sq hR hφ i⟩

end E68Cert

end ReyesMath
