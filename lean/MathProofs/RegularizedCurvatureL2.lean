import Mathlib

/-!
# E26: a conditional `L²` estimate for the historical regularized curvature operator (F12)

Formalization of `papers/regularized-curvature-l2-bound/main.tex`.

Mathlib has no Sobolev spaces on open sets, so `H²(Ω; ℂ)` is defined here by weak derivatives.
Let `Ω` be open in a finite-dimensional real inner product space `E` (for `ℝ^d`,
`E = EuclideanSpace ℝ (Fin d)`) with Lebesgue measure. Then `E26.MemH2 Ω ψ` says that `ψ ∈ L²(Ω)`
and that for every `k ≤ 2` and all directions `m` there is `g ∈ L²(Ω)` with
`∫_Ω (∂^m φ) ψ = (−1)^k ∫_Ω φ g` for all `φ ∈ C_c^∞(Ω)` (`E26.IsWeakDeriv`).

`Δψ` is the weak Laplacian (`E26.IsWeakLaplacian`, tested against Mathlib's Laplacian of `φ`).
For `ψ ∈ H²` it exists in `L²(Ω)` (`E26.MemH2.exists_weakLaplacian`), and it is unique a.e.
(`E26.IsWeakLaplacian.ae_eq`, by the fundamental lemma of the calculus of variations).

* The operator: `D_ε[ψ] = ψ + ε e^{−α|ψ|²}` (`E26.Den`) and `Θ_ε[ψ] = −Δψ / D_ε[ψ]`
  (`E26.Theta`).
* Theorem E26 (`E26.e26`; `E26.e26_Rd` on `ℝ^d`). If `ess inf_Ω |D_ε[ψ]| ≥ δ > 0`, then:
  * `Δψ ∈ L²(Ω)`, `D_ε[ψ] ≠ 0` a.e. and `‖1/D_ε[ψ]‖_∞ ≤ 1/δ`;
  * `Θ_ε[ψ] ∈ L²(Ω)` with `‖Θ_ε[ψ]‖_{L²(Ω)} ≤ δ⁻¹ ‖Δψ‖_{L²(Ω)}`, also in squared-integral form.

  This holds for every open `Ω` and every dimension, with no boundary condition.
* Sufficient denominator bounds:
  * Corollary, fields bounded away from zero (`E26.cor_modulus`);
  * the remark that no `L²` function on all of `ℝ^d`, `d ≥ 1`, is bounded below by `m > 0`
    (`E26.not_ae_norm_ge_of_memLp`);
  * Corollary, nonnegative real fields, with `δ_ε = min{ε/2, ε e^{−αε²/4}} > 0`
    (`E26.cor_nonneg`).
* Counterexample (`E26.counterexample`). On `Ω = (−1, 1)` with `α = 0`, the field
  `ψ = x² − ε ∈ H²(Ω)` has `D_ε[ψ] = x²`, `Δψ = 2` and `Θ_ε[ψ] = −2/x²`. So
  `∫_Ω |Θ_ε[ψ]|² = ∞` while `‖Δψ‖² = 8`: no finite constant works, and (H) fails for every
  `δ > 0`.
* The corrected phase-covariant multiplier of M2/E17, `R_ε(z) = z̄/(|z|² + ε²e^{−2α|z|²})`, is
  bounded by `ε⁻¹ max{2, e^{αε²/2}/2}` (`E26.norm_Rε_cases`, `E26.norm_Rε_le`). This gives the
  unconditional bound `E26.corrected_bound`.
* Scope: `δ` cannot be replaced by `ε` (`E26.delta_not_replaceable`).
-/

open MeasureTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal Topology ContDiff ComplexConjugate

noncomputable section

namespace ReyesMath
namespace E26

/-! ### Weak derivatives and `H²(Ω)` -/

section General

/-- The additive denominator `D_ε[ψ] = ψ + ε e^{−α|ψ|²}`. -/
def Den {X : Type*} (ε α : ℝ) (ψ : X → ℂ) (x : X) : ℂ :=
  ψ x + ((ε * Real.exp (-α * ‖ψ x‖ ^ 2) : ℝ) : ℂ)

/-- The historical regularized curvature `Θ_ε[ψ] = −Δψ / D_ε[ψ]`, with `F = Δψ`. (Lean's
convention `z / 0 = 0` only matters on the null set where `D_ε[ψ] = 0`.) -/
def Theta {X : Type*} (ε α : ℝ) (ψ F : X → ℂ) (x : X) : ℂ := -F x / Den ε α ψ x

theorem aestronglyMeasurable_den {X : Type*} [MeasurableSpace X] {μ : Measure X} {ε α : ℝ}
    {ψ : X → ℂ} (hψ : AEStronglyMeasurable ψ μ) : AEStronglyMeasurable (Den ε α ψ) μ := by
  have hc : Continuous fun z : ℂ => z + ((ε * Real.exp (-α * ‖z‖ ^ 2) : ℝ) : ℂ) :=
    continuous_id.add (Complex.continuous_ofReal.comp (continuous_const.mul
      (Real.continuous_exp.comp (continuous_const.mul (continuous_norm.pow 2)))))
  exact hc.comp_aestronglyMeasurable hψ

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Test functions on `Ω`: smooth, compactly supported, with support in `Ω`. -/
def IsTest (Ω : Set E) (φ : E → ℝ) : Prop :=
  ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Ω

theorem IsTest.zero_of_not_mem {Ω : Set E} {φ : E → ℝ} (hφ : IsTest Ω φ) {x : E} (hx : x ∉ Ω) :
    φ x = 0 :=
  image_eq_zero_of_notMem_tsupport fun h => hx (hφ.2.2 h)

theorem iteratedFDeriv_apply_eq_zero {φ : E → ℝ} (k : ℕ) (m : Fin k → E) {x : E}
    (hx : x ∉ tsupport φ) : iteratedFDeriv ℝ k φ x m = 0 := by
  have : iteratedFDeriv ℝ k φ x = 0 := by
    by_contra h
    exact hx (support_iteratedFDeriv_subset k (Function.mem_support.2 h))
  rw [this]; rfl

theorem IsTest.continuous_iteratedFDeriv_apply {Ω : Set E} {φ : E → ℝ} (hφ : IsTest Ω φ) (k : ℕ)
    (m : Fin k → E) : Continuous fun x => iteratedFDeriv ℝ k φ x m :=
  (continuous_eval_const m).comp (hφ.1.continuous_iteratedFDeriv (by exact_mod_cast le_top))

variable [FiniteDimensional ℝ E]

theorem laplacian_eq_sum {ι : Type*} [Fintype ι] (v : OrthonormalBasis ι ℝ E) (φ : E → ℝ)
    (x : E) : Δ φ x = ∑ i, iteratedFDeriv ℝ 2 φ x ![v i, v i] := by
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis φ v]

variable [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]

/-- `g` is the weak derivative `∂_{m 0} ⋯ ∂_{m (k-1)} ψ` of `ψ` on `Ω`:
`∫_Ω (∂^m φ) ψ = (−1)^k ∫_Ω φ g` for every test function `φ`. -/
def IsWeakDeriv (Ω : Set E) {k : ℕ} (m : Fin k → E) (ψ g : E → ℂ) : Prop :=
  LocallyIntegrableOn g Ω ∧ ∀ φ : E → ℝ, IsTest Ω φ →
    ∫ x in Ω, iteratedFDeriv ℝ k φ x m • ψ x = ((-1 : ℝ) ^ k) • ∫ x in Ω, φ x • g x

/-- `ψ ∈ H²(Ω; ℂ)`: `ψ ∈ L²(Ω)` and every weak derivative of order `≤ 2` exists in `L²(Ω)`. -/
def MemH2 (Ω : Set E) (ψ : E → ℂ) : Prop :=
  MemLp ψ 2 (volume.restrict Ω) ∧
    ∀ k ≤ 2, ∀ m : Fin k → E, ∃ g : E → ℂ, MemLp g 2 (volume.restrict Ω) ∧ IsWeakDeriv Ω m ψ g

/-- `F` is the weak Laplacian `Δψ` of `ψ` on `Ω`: `∫_Ω (Δφ) ψ = ∫_Ω φ F` for every test
function `φ`. -/
def IsWeakLaplacian (Ω : Set E) (ψ F : E → ℂ) : Prop :=
  LocallyIntegrableOn F Ω ∧ ∀ φ : E → ℝ, IsTest Ω φ →
    ∫ x in Ω, Δ φ x • ψ x = ∫ x in Ω, φ x • F x

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [(volume : Measure E).IsAddHaarMeasure] in
theorem integrableOn_smul_of_compact {Ω K : Set E} (hΩ : MeasurableSet Ω) (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) {χ : E → ℝ} (hχ : Continuous χ) (hχK : ∀ x ∉ K, χ x = 0) {g : E → ℂ}
    (hg : LocallyIntegrableOn g Ω) : IntegrableOn (fun x => χ x • g x) Ω := by
  have h1 : IntegrableOn g K := hg.integrableOn_compact_subset hKΩ hK
  have h2 : IntegrableOn (fun x => χ x • g x) K := h1.continuousOn_smul hχ.continuousOn hK
  exact h2.of_forall_diff_eq_zero hΩ fun x hx => by rw [hχK x hx.2, zero_smul]

theorem locallyIntegrableOn_of_memLp {Ω : Set E} {g : E → ℂ} (hg : MemLp g 2 (volume.restrict Ω)) :
    LocallyIntegrableOn g Ω :=
  locallyIntegrableOn_of_locallyIntegrable_restrict (hg.locallyIntegrable (by norm_num))

/-- An `H²` function has a weak Laplacian `Δψ = Σ_j ∂_j²ψ`, and it lies in `L²(Ω)`. -/
theorem MemH2.exists_weakLaplacian {Ω : Set E} (hΩ : IsOpen Ω) {ψ : E → ℂ} (hψ : MemH2 Ω ψ) :
    ∃ F : E → ℂ, MemLp F 2 (volume.restrict Ω) ∧ IsWeakLaplacian Ω ψ F := by
  obtain ⟨v⟩ : Nonempty (OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E) :=
    ⟨stdOrthonormalBasis ℝ E⟩
  choose g hg using fun i => hψ.2 2 le_rfl ![v i, v i]
  have hψl := locallyIntegrableOn_of_memLp hψ.1
  have hsum : MemLp (fun x => ∑ i, g i x) 2 (volume.restrict Ω) :=
    memLp_finset_sum _ fun i _ => (hg i).1
  refine ⟨fun x => ∑ i, g i x, hsum, locallyIntegrableOn_of_memLp hsum, fun φ hφ => ?_⟩
  have hK : IsCompact (tsupport φ) := hφ.2.1
  have hint1 : ∀ i, IntegrableOn
      (fun x => iteratedFDeriv ℝ 2 φ x ![v i, v i] • ψ x) Ω := fun i =>
    integrableOn_smul_of_compact hΩ.measurableSet hK hφ.2.2
      (hφ.continuous_iteratedFDeriv_apply 2 _) (fun x hx => iteratedFDeriv_apply_eq_zero 2 _ hx)
      hψl
  have hint2 : ∀ i, IntegrableOn (fun x => φ x • g i x) Ω := fun i =>
    integrableOn_smul_of_compact hΩ.measurableSet hK hφ.2.2 hφ.1.continuous
      (fun x hx => image_eq_zero_of_notMem_tsupport hx) (hg i).2.1
  calc ∫ x in Ω, Δ φ x • ψ x
      = ∫ x in Ω, ∑ i, iteratedFDeriv ℝ 2 φ x ![v i, v i] • ψ x := by
        congr 1; funext x; rw [laplacian_eq_sum v, Finset.sum_smul]
    _ = ∑ i, ∫ x in Ω, iteratedFDeriv ℝ 2 φ x ![v i, v i] • ψ x :=
        integral_finset_sum _ fun i _ => hint1 i
    _ = ∑ i, ∫ x in Ω, φ x • g i x := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [(hg i).2.2 φ hφ]; norm_num
    _ = ∫ x in Ω, φ x • ∑ i, g i x := by
        rw [← integral_finset_sum _ fun i _ => hint2 i]
        congr 1; funext x; rw [Finset.smul_sum]

omit [(volume : Measure E).IsAddHaarMeasure] in
/-- Uniqueness of the weak Laplacian (fundamental lemma of the calculus of variations). -/
theorem IsWeakLaplacian.ae_eq {Ω : Set E} (hΩ : IsOpen Ω) {ψ F₁ F₂ : E → ℂ}
    (h₁ : IsWeakLaplacian Ω ψ F₁) (h₂ : IsWeakLaplacian Ω ψ F₂) :
    F₁ =ᵐ[volume.restrict Ω] F₂ := by
  have key := hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero (h₁.1.sub h₂.1)
    fun φ hφ hφc hφΩ => by
      have ht : IsTest Ω φ := ⟨hφ, hφc, hφΩ⟩
      have hK : IsCompact (tsupport φ) := hφc
      have i1 := integrableOn_smul_of_compact hΩ.measurableSet hK hφΩ hφ.continuous
        (fun x hx => image_eq_zero_of_notMem_tsupport hx) h₁.1
      have i2 := integrableOn_smul_of_compact hΩ.measurableSet hK hφΩ hφ.continuous
        (fun x hx => image_eq_zero_of_notMem_tsupport hx) h₂.1
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ω) fun x hx => by
        rw [ht.zero_of_not_mem hx, zero_smul]]
      simp only [Pi.sub_apply, smul_sub]
      rw [integral_sub i1 i2, ← h₁.2 φ ht, ← h₂.2 φ ht, sub_self]
  rw [Filter.EventuallyEq, ae_restrict_iff' hΩ.measurableSet]
  filter_upwards [key] with x hx hxΩ
  exact sub_eq_zero.1 (hx hxΩ)

/-! ### The operator and Theorem E26 -/

/-- **Theorem E26** (conditional `L²` estimate). Let `Ω` be open, `ψ ∈ H²(Ω; ℂ)` with weak
Laplacian `Δψ = F`, and suppose `ess inf_Ω |D_ε[ψ]| ≥ δ > 0`. Then `Δψ ∈ L²(Ω)`, `D_ε[ψ] ≠ 0` a.e.,
`‖1/D_ε[ψ]‖_∞ ≤ 1/δ`, `Θ_ε[ψ] ∈ L²(Ω)`, and `‖Θ_ε[ψ]‖_{L²(Ω)} ≤ δ⁻¹ ‖Δψ‖_{L²(Ω)}` (also in the
squared integral form). -/
theorem e26 {Ω : Set E} (hΩ : IsOpen Ω) {ε α δ : ℝ} (hδ : 0 < δ) {ψ F : E → ℂ}
    (hψ : MemH2 Ω ψ) (hF : IsWeakLaplacian Ω ψ F)
    (hH : ∀ᵐ x ∂(volume.restrict Ω), δ ≤ ‖Den ε α ψ x‖) :
    MemLp F 2 (volume.restrict Ω) ∧
    (∀ᵐ x ∂(volume.restrict Ω), Den ε α ψ x ≠ 0) ∧
    eLpNorm (fun x => (Den ε α ψ x)⁻¹) ∞ (volume.restrict Ω) ≤ ENNReal.ofReal δ⁻¹ ∧
    MemLp (Theta ε α ψ F) 2 (volume.restrict Ω) ∧
    eLpNorm (Theta ε α ψ F) 2 (volume.restrict Ω) ≤
      ENNReal.ofReal δ⁻¹ * eLpNorm F 2 (volume.restrict Ω) ∧
    ∫ x in Ω, ‖Theta ε α ψ F x‖ ^ 2 ≤ δ⁻¹ ^ 2 * ∫ x in Ω, ‖F x‖ ^ 2 := by
  obtain ⟨G, hG2, hGL⟩ := hψ.exists_weakLaplacian hΩ
  have hF2 : MemLp F 2 (volume.restrict Ω) := hG2.ae_eq (hF.ae_eq hΩ hGL).symm
  have hD := aestronglyMeasurable_den (ε := ε) (α := α) hψ.1.1
  have hne : ∀ᵐ x ∂(volume.restrict Ω), Den ε α ψ x ≠ 0 := hH.mono fun x hx h => by
    rw [h, norm_zero] at hx; linarith
  have hinv : ∀ᵐ x ∂(volume.restrict Ω), ‖(Den ε α ψ x)⁻¹‖ ≤ δ⁻¹ := hH.mono fun x hx => by
    rw [norm_inv]; exact inv_anti₀ hδ hx
  have hpt : ∀ᵐ x ∂(volume.restrict Ω), ‖Theta ε α ψ F x‖ ≤ δ⁻¹ * ‖F x‖ := hinv.mono fun x hx => by
    rw [Theta, div_eq_mul_inv, norm_mul, norm_neg, mul_comm]
    exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)
  have hΘm : AEStronglyMeasurable (Theta ε α ψ F) (volume.restrict Ω) :=
    (hF2.1.neg.aemeasurable.div hD.aemeasurable).aestronglyMeasurable
  refine ⟨hF2, hne, ?_, hF2.of_le_mul hΘm hpt, eLpNorm_le_mul_eLpNorm_of_ae_le_mul hpt 2, ?_⟩
  · rw [eLpNorm_exponent_top]; exact eLpNormEssSup_le_of_ae_bound hinv
  · have h1 : Integrable (fun x => ‖F x‖ ^ 2) (volume.restrict Ω) :=
      (memLp_two_iff_integrable_sq_norm hF2.1).1 hF2
    calc ∫ x in Ω, ‖Theta ε α ψ F x‖ ^ 2 ≤ ∫ x in Ω, δ⁻¹ ^ 2 * ‖F x‖ ^ 2 := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun x => by positivity)
            (h1.const_mul _) (hpt.mono fun x hx => ?_)
          have := pow_le_pow_left₀ (norm_nonneg _) hx 2
          simpa [mul_pow] using this
      _ = δ⁻¹ ^ 2 * ∫ x in Ω, ‖F x‖ ^ 2 := integral_const_mul _ _

/-! ### Sufficient denominator bounds -/

theorem norm_den_ge {ε α m : ℝ} (hε : 0 ≤ ε) (hα : 0 ≤ α) {z : ℂ} (hz : m ≤ ‖z‖) :
    m - ε ≤ ‖z + ((ε * Real.exp (-α * ‖z‖ ^ 2) : ℝ) : ℂ)‖ := by
  have h1 : Real.exp (-α * ‖z‖ ^ 2) ≤ 1 :=
    Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg ‖z‖])
  have h2 : ‖((ε * Real.exp (-α * ‖z‖ ^ 2) : ℝ) : ℂ)‖ ≤ ε := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc ε * Real.exp (-α * ‖z‖ ^ 2) ≤ ε * 1 := mul_le_mul_of_nonneg_left h1 hε
      _ = ε := mul_one ε
  have h3 := norm_sub_norm_le z (-(((ε * Real.exp (-α * ‖z‖ ^ 2) : ℝ) : ℂ)))
  rw [norm_neg, sub_neg_eq_add] at h3
  linarith

/-- **Corollary (fields bounded away from zero)**: if `|ψ| ≥ m > ε` a.e. on `Ω` (with `ε > 0`,
`α ≥ 0`), then `‖Θ_ε[ψ]‖_{L²(Ω)} ≤ (m − ε)⁻¹ ‖Δψ‖_{L²(Ω)}`. -/
theorem cor_modulus {Ω : Set E} (hΩ : IsOpen Ω) {ε α m : ℝ} (hε : 0 < ε) (hα : 0 ≤ α)
    (hm : ε < m) {ψ F : E → ℂ} (hψ : MemH2 Ω ψ) (hF : IsWeakLaplacian Ω ψ F)
    (hψm : ∀ᵐ x ∂(volume.restrict Ω), m ≤ ‖ψ x‖) :
    MemLp (Theta ε α ψ F) 2 (volume.restrict Ω) ∧
    eLpNorm (Theta ε α ψ F) 2 (volume.restrict Ω) ≤
      ENNReal.ofReal (m - ε)⁻¹ * eLpNorm F 2 (volume.restrict Ω) := by
  obtain ⟨-, -, -, h1, h2, -⟩ := e26 hΩ (sub_pos.2 hm) hψ hF
    (hψm.mono fun x hx => norm_den_ge hε.le hα hx)
  exact ⟨h1, h2⟩

/-- **Remark**: on the whole space (`E` nontrivial), no `L²` function satisfies `|ψ| ≥ m > 0`
almost everywhere. -/
theorem not_ae_norm_ge_of_memLp [Nontrivial E] {m : ℝ} (hm : 0 < m) {ψ : E → ℂ}
    (hψ : MemLp ψ 2 volume) : ¬ ∀ᵐ x, m ≤ ‖ψ x‖ := by
  intro h
  have hfin := hψ.meas_ge_lt_top (by norm_num) (by norm_num) (ε := ⟨m, hm.le⟩)
    (by simp [← NNReal.coe_eq_zero, hm.ne'])
  set S := {x : E | (⟨m, hm.le⟩ : ℝ≥0) ≤ ‖ψ x‖₊}
  have hset : Sᶜ = {x | ¬ m ≤ ‖ψ x‖} := by
    ext x
    simp only [S, mem_compl_iff, mem_setOf_eq]
    exact not_congr NNReal.coe_le_coe.symm
  have hSc : volume Sᶜ = 0 := by rw [hset]; exact ae_iff.1 h
  have huniv : volume (univ : Set E) = ⊤ := measure_univ_of_isAddLeftInvariant volume
  have : volume (univ : Set E) ≤ volume S + volume Sᶜ := by
    rw [← union_compl_self S]; exact measure_union_le _ _
  rw [hSc, add_zero, huniv] at this
  exact absurd (lt_of_le_of_lt this hfin) (lt_irrefl _)

/-- `δ_ε = min{ε/2, ε e^{−αε²/4}}`. -/
def deltaEps (ε α : ℝ) : ℝ := min (ε / 2) (ε * Real.exp (-α * ε ^ 2 / 4))

theorem deltaEps_pos {ε : ℝ} (hε : 0 < ε) (α : ℝ) : 0 < deltaEps ε α :=
  lt_min (by linarith) (by positivity)

theorem deltaEps_le {ε α r : ℝ} (hε : 0 < ε) (hα : 0 ≤ α) (hr : 0 ≤ r) :
    deltaEps ε α ≤ r + ε * Real.exp (-α * r ^ 2) := by
  rcases le_or_gt (ε / 2) r with h | h
  · have : 0 ≤ ε * Real.exp (-α * r ^ 2) := by positivity
    exact (min_le_left _ _).trans (by linarith)
  · have hr2 : r ^ 2 ≤ ε ^ 2 / 4 := by nlinarith
    have hexp : Real.exp (-α * ε ^ 2 / 4) ≤ Real.exp (-α * r ^ 2) :=
      Real.exp_le_exp.2 (by nlinarith)
    have := mul_le_mul_of_nonneg_left hexp hε.le
    exact (min_le_right _ _).trans (by linarith)

/-- **Corollary (nonnegative real fields)**: for real `ψ = u ≥ 0` a.e. in `H²(Ω)`, `ε > 0`,
`α ≥ 0`: `‖Θ_ε[ψ]‖_{L²(Ω)} ≤ δ_ε⁻¹ ‖Δψ‖_{L²(Ω)}`. -/
theorem cor_nonneg {Ω : Set E} (hΩ : IsOpen Ω) {ε α : ℝ} (hε : 0 < ε) (hα : 0 ≤ α)
    {u : E → ℝ} {F : E → ℂ} (hu : MemH2 Ω (fun x => (u x : ℂ)))
    (hF : IsWeakLaplacian Ω (fun x => (u x : ℂ)) F)
    (hu0 : ∀ᵐ x ∂(volume.restrict Ω), 0 ≤ u x) :
    MemLp (Theta ε α (fun x => (u x : ℂ)) F) 2 (volume.restrict Ω) ∧
    eLpNorm (Theta ε α (fun x => (u x : ℂ)) F) 2 (volume.restrict Ω) ≤
      ENNReal.ofReal (deltaEps ε α)⁻¹ * eLpNorm F 2 (volume.restrict Ω) := by
  have hD : ∀ᵐ x ∂(volume.restrict Ω), deltaEps ε α ≤ ‖Den ε α (fun x => (u x : ℂ)) x‖ :=
    hu0.mono fun x hx => by
      have e : Den ε α (fun x => (u x : ℂ)) x =
          ((u x + ε * Real.exp (-α * u x ^ 2) : ℝ) : ℂ) := by
        simp only [Den, Complex.norm_real, Real.norm_eq_abs, sq_abs]; push_cast; ring
      rw [e, Complex.norm_real, Real.norm_eq_abs]
      exact (deltaEps_le hε hα hx).trans (le_abs_self _)
  obtain ⟨-, -, -, h1, h2, -⟩ := e26 hΩ (deltaEps_pos hε α) hu hF hD
  exact ⟨h1, h2⟩

/-! ### The corrected phase-covariant regularization (M2/E17) -/

/-- The corrected multiplier `R_ε(z) = z̄ / (|z|² + ε² e^{−2α|z|²})`. -/
def Rε (ε α : ℝ) (z : ℂ) : ℂ :=
  conj z / ((‖z‖ ^ 2 + ε ^ 2 * Real.exp (-2 * α * ‖z‖ ^ 2) : ℝ) : ℂ)

theorem norm_Rε {ε : ℝ} (hε : 0 < ε) (α : ℝ) (z : ℂ) :
    ‖Rε ε α z‖ = ‖z‖ / (‖z‖ ^ 2 + ε ^ 2 * Real.exp (-2 * α * ‖z‖ ^ 2)) := by
  have hpos : 0 < ‖z‖ ^ 2 + ε ^ 2 * Real.exp (-2 * α * ‖z‖ ^ 2) := by positivity
  rw [Rε, norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]

/-- The two regimes of the corrected multiplier. -/
theorem norm_Rε_cases {ε α : ℝ} (hε : 0 < ε) (hα : 0 ≤ α) (z : ℂ) :
    (ε / 2 ≤ ‖z‖ → ‖Rε ε α z‖ ≤ ‖z‖⁻¹ ∧ ‖z‖⁻¹ ≤ 2 / ε) ∧
    (‖z‖ < ε / 2 → ‖Rε ε α z‖ ≤ ‖z‖ * Real.exp (2 * α * ‖z‖ ^ 2) / ε ^ 2 ∧
      ‖z‖ * Real.exp (2 * α * ‖z‖ ^ 2) / ε ^ 2 ≤ Real.exp (α * ε ^ 2 / 2) / (2 * ε)) := by
  rw [norm_Rε hε]
  have he : 0 < Real.exp (-2 * α * ‖z‖ ^ 2) := Real.exp_pos _
  refine ⟨fun hz => ⟨?_, ?_⟩, fun hz => ⟨?_, ?_⟩⟩
  · have hz0 : 0 < ‖z‖ := by linarith
    rw [div_le_iff₀ (by positivity)]
    have : 0 ≤ ‖z‖⁻¹ * (ε ^ 2 * Real.exp (-2 * α * ‖z‖ ^ 2)) := by positivity
    have e : ‖z‖⁻¹ * ‖z‖ ^ 2 = ‖z‖ := by field_simp
    nlinarith
  · have hz0 : 0 < ‖z‖ := by linarith
    rw [inv_le_comm₀ hz0 (by positivity), inv_div]; exact hz
  · have hd : 0 < ε ^ 2 * Real.exp (-2 * α * ‖z‖ ^ 2) := by positivity
    calc ‖z‖ / (‖z‖ ^ 2 + ε ^ 2 * Real.exp (-2 * α * ‖z‖ ^ 2))
        ≤ ‖z‖ / (ε ^ 2 * Real.exp (-2 * α * ‖z‖ ^ 2)) :=
          div_le_div_of_nonneg_left (norm_nonneg _) hd (by nlinarith [sq_nonneg ‖z‖])
      _ = ‖z‖ * Real.exp (2 * α * ‖z‖ ^ 2) / ε ^ 2 := by
          rw [show (-2 * α * ‖z‖ ^ 2) = -(2 * α * ‖z‖ ^ 2) by ring, Real.exp_neg]
          field_simp
  · have h0 := norm_nonneg z
    have hz2 : ‖z‖ ^ 2 ≤ ε ^ 2 / 4 := by nlinarith
    have hexp : Real.exp (2 * α * ‖z‖ ^ 2) ≤ Real.exp (α * ε ^ 2 / 2) :=
      Real.exp_le_exp.2 (by nlinarith [mul_le_mul_of_nonneg_left hz2 hα])
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : ‖z‖ * Real.exp (2 * α * ‖z‖ ^ 2) ≤ ε / 2 * Real.exp (α * ε ^ 2 / 2) :=
      mul_le_mul hz.le hexp (Real.exp_pos _).le (by linarith)
    nlinarith [Real.exp_pos (α * ε ^ 2 / 2)]

/-- `sup |R_ε| ≤ ε⁻¹ max{2, e^{αε²/2}/2}`. -/
theorem norm_Rε_le {ε α : ℝ} (hε : 0 < ε) (hα : 0 ≤ α) (z : ℂ) :
    ‖Rε ε α z‖ ≤ ε⁻¹ * max 2 (Real.exp (α * ε ^ 2 / 2) / 2) := by
  obtain ⟨h1, h2⟩ := norm_Rε_cases hε hα z
  rcases le_or_gt (ε / 2) ‖z‖ with hz | hz
  · obtain ⟨a, b⟩ := h1 hz
    calc ‖Rε ε α z‖ ≤ 2 / ε := a.trans b
      _ = ε⁻¹ * 2 := by ring
      _ ≤ ε⁻¹ * max 2 (Real.exp (α * ε ^ 2 / 2) / 2) :=
          mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)
  · obtain ⟨a, b⟩ := h2 hz
    calc ‖Rε ε α z‖ ≤ Real.exp (α * ε ^ 2 / 2) / (2 * ε) := a.trans b
      _ = ε⁻¹ * (Real.exp (α * ε ^ 2 / 2) / 2) := by field_simp
      _ ≤ ε⁻¹ * max 2 (Real.exp (α * ε ^ 2 / 2) / 2) :=
          mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)

theorem continuous_Rε {ε : ℝ} (hε : 0 < ε) (α : ℝ) : Continuous (Rε ε α) := by
  refine Complex.continuous_conj.div (Complex.continuous_ofReal.comp ((continuous_norm.pow 2).add
    (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul
      (continuous_norm.pow 2)))))) fun z => ?_
  have : 0 < ‖z‖ ^ 2 + ε ^ 2 * Real.exp (-2 * α * ‖z‖ ^ 2) := by positivity
  exact_mod_cast this.ne'

/-- **The corrected operator is unconditionally bounded**: for `ψ ∈ H²(Ω; ℂ)`,
`‖(Δψ) R_ε(ψ)‖_{L²(Ω)} ≤ ε⁻¹ max{2, e^{αε²/2}/2} ‖Δψ‖_{L²(Ω)}`. -/
theorem corrected_bound {Ω : Set E} (hΩ : IsOpen Ω) {ε α : ℝ} (hε : 0 < ε) (hα : 0 ≤ α)
    {ψ F : E → ℂ} (hψ : MemH2 Ω ψ) (hF : IsWeakLaplacian Ω ψ F) :
    MemLp (fun x => -F x * Rε ε α (ψ x)) 2 (volume.restrict Ω) ∧
    eLpNorm (fun x => -F x * Rε ε α (ψ x)) 2 (volume.restrict Ω) ≤
      ENNReal.ofReal (ε⁻¹ * max 2 (Real.exp (α * ε ^ 2 / 2) / 2)) *
        eLpNorm F 2 (volume.restrict Ω) := by
  obtain ⟨G, hG2, hGL⟩ := hψ.exists_weakLaplacian hΩ
  have hF2 : MemLp F 2 (volume.restrict Ω) := hG2.ae_eq (hF.ae_eq hΩ hGL).symm
  have hm : AEStronglyMeasurable (fun x => -F x * Rε ε α (ψ x)) (volume.restrict Ω) :=
    hF2.1.neg.mul ((continuous_Rε hε α).comp_aestronglyMeasurable hψ.1.1)
  have hpt : ∀ᵐ x ∂(volume.restrict Ω), ‖-F x * Rε ε α (ψ x)‖ ≤
      ε⁻¹ * max 2 (Real.exp (α * ε ^ 2 / 2) / 2) * ‖F x‖ := Eventually.of_forall fun x => by
    rw [norm_mul, norm_neg, mul_comm]
    exact mul_le_mul_of_nonneg_right (norm_Rε_le hε hα _) (norm_nonneg _)
  exact ⟨hF2.of_le_mul hm hpt, eLpNorm_le_mul_eLpNorm_of_ae_le_mul hpt 2⟩

end General

/-- **Theorem E26 on `ℝ^d`**: the estimate of `e26` for an open `Ω ⊆ ℝ^d`
(`EuclideanSpace ℝ (Fin d)` with Lebesgue measure). -/
theorem e26_Rd {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : IsOpen Ω) {ε α δ : ℝ}
    (hδ : 0 < δ) {ψ F : EuclideanSpace ℝ (Fin d) → ℂ} (hψ : MemH2 Ω ψ)
    (hF : IsWeakLaplacian Ω ψ F) (hH : ∀ᵐ x ∂(volume.restrict Ω), δ ≤ ‖Den ε α ψ x‖) :
    MemLp (Theta ε α ψ F) 2 (volume.restrict Ω) ∧
    eLpNorm (Theta ε α ψ F) 2 (volume.restrict Ω) ≤
      ENNReal.ofReal δ⁻¹ * eLpNorm F 2 (volume.restrict Ω) :=
  ⟨(e26 hΩ hδ hψ hF hH).2.2.2.1, (e26 hΩ hδ hψ hF hH).2.2.2.2.1⟩

/-! ### The counterexample on `Ω = (−1, 1)` -/

section Counterexample

/-- On `ℝ` the Laplacian is the second derivative. -/
theorem laplacian_real (φ : ℝ → ℝ) (x : ℝ) : Δ φ x = deriv (deriv φ) x := by
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis φ (OrthonormalBasis.singleton (Fin 1) ℝ)]
  simp only [Finset.univ_unique, Finset.sum_singleton, OrthonormalBasis.singleton_apply]
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, iteratedDeriv_succ, iteratedDeriv_one]
  simp

theorem iteratedFDeriv_real (φ : ℝ → ℝ) {k : ℕ} (m : Fin k → ℝ) (x : ℝ) :
    iteratedFDeriv ℝ k φ x m = (∏ i, m i) * iteratedDeriv k φ x := by
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, smul_eq_mul]

theorem tsupport_deriv_subset' (φ : ℝ → ℝ) : tsupport (deriv φ) ⊆ tsupport φ :=
  closure_minimal (support_deriv_subset (f := φ)) (isClosed_tsupport φ)

/-- Integration by parts against a `C¹` function supported inside `(a, b)`. -/
theorem integral_deriv_mul {a b : ℝ} (hab : a ≤ b) {φ u u' : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hsupp : tsupport φ ⊆ Ioo a b) (hu : ∀ x, HasDerivAt u (u' x) x) (hu' : Continuous u') :
    ∫ x in Ioo a b, deriv φ x * u x = -∫ x in Ioo a b, φ x * u' x := by
  have ha : φ a = 0 := image_eq_zero_of_notMem_tsupport fun h => lt_irrefl a (hsupp h).1
  have hb : φ b = 0 := image_eq_zero_of_notMem_tsupport fun h => lt_irrefl b (hsupp h).2
  have hφd : ∀ x, HasDerivAt φ (deriv φ x) x := fun x =>
    ((hφ.differentiable le_rfl) x).hasDerivAt
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := a) (b := b)
    (fun x _ => hφd x) (fun x _ => hu x) ((hφ.continuous_deriv le_rfl).intervalIntegrable a b)
    (hu'.intervalIntegrable a b)
  rw [ha, hb, zero_mul, zero_mul, sub_zero, zero_sub] at h
  rw [← integral_Ioc_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hab, ← intervalIntegral.integral_of_le hab, h, neg_neg]

theorem integral_smul_ofReal {s : Set ℝ} (r f : ℝ → ℝ) :
    ∫ x in s, r x • ((f x : ℝ) : ℂ) = ((∫ x in s, r x * f x : ℝ) : ℂ) := by
  simp_rw [Complex.real_smul, ← Complex.ofReal_mul]
  exact integral_complex_ofReal

theorem IsTest.contDiff_deriv {φ : ℝ → ℝ} {Ω : Set ℝ} (hφ : IsTest Ω φ) :
    ContDiff ℝ ∞ (deriv φ) := (contDiff_infty_iff_deriv.1 hφ.1).2

/-- First integration by parts for `u = x² + c` on `(−1, 1)`. -/
theorem ibp_quad1 {φ : ℝ → ℝ} (hφ : IsTest (Ioo (-1 : ℝ) 1) φ) (c : ℝ) :
    ∫ x in Ioo (-1 : ℝ) 1, deriv φ x * (x ^ 2 + c) = -∫ x in Ioo (-1 : ℝ) 1, φ x * (2 * x) :=
  integral_deriv_mul (by norm_num) (hφ.1.of_le (by exact_mod_cast le_top)) hφ.2.2
    (fun x => by simpa using (hasDerivAt_pow 2 x).add_const c) (continuous_const.mul continuous_id)

/-- Second integration by parts for `u = x² + c` on `(−1, 1)`. -/
theorem ibp_quad2 {φ : ℝ → ℝ} (hφ : IsTest (Ioo (-1 : ℝ) 1) φ) (c : ℝ) :
    ∫ x in Ioo (-1 : ℝ) 1, deriv (deriv φ) x * (x ^ 2 + c) = ∫ x in Ioo (-1 : ℝ) 1, φ x * 2 := by
  have h1 := integral_deriv_mul (a := -1) (b := 1) (by norm_num) (φ := deriv φ)
    (u := fun x => x ^ 2 + c) (u' := fun x => 2 * x)
    (hφ.contDiff_deriv.of_le (by exact_mod_cast le_top))
    ((tsupport_deriv_subset' φ).trans hφ.2.2)
    (fun x => by simpa using (hasDerivAt_pow 2 x).add_const c) (continuous_const.mul continuous_id)
  have h2 := integral_deriv_mul (a := -1) (b := 1) (by norm_num) (φ := φ)
    (u := fun x => 2 * x) (u' := fun _ => 2)
    (hφ.1.of_le (by exact_mod_cast le_top)) hφ.2.2
    (fun x => by simpa using (hasDerivAt_id x).const_mul (2 : ℝ)) continuous_const
  rw [h1, h2, neg_neg]

/-- The field `ψ_c(x) = x² + c` on `ℝ`. -/
def quad (c : ℝ) (x : ℝ) : ℂ := ((x ^ 2 + c : ℝ) : ℂ)

theorem memLp_Ioo_of_continuous {g : ℝ → ℂ} (hg : Continuous g) :
    MemLp g 2 (volume.restrict (Ioo (-1 : ℝ) 1)) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hg.continuousOn
  refine MemLp.of_bound hg.aestronglyMeasurable C ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  exact hC x (Ioo_subset_Icc_self hx)

theorem continuous_ofReal_comp {f : ℝ → ℝ} (hf : Continuous f) : Continuous fun x => (f x : ℂ) :=
  Complex.continuous_ofReal.comp hf

/-- `ψ_c ∈ H²((−1, 1))`, with weak derivatives `ψ' = 2x`, `ψ'' = 2`. -/
theorem memH2_quad (c : ℝ) : MemH2 (Ioo (-1 : ℝ) 1) (quad c) := by
  have hcq : Continuous (quad c) := continuous_ofReal_comp ((continuous_pow 2).add continuous_const)
  refine ⟨memLp_Ioo_of_continuous hcq, fun k hk m => ?_⟩
  interval_cases k
  · refine ⟨quad c, memLp_Ioo_of_continuous hcq,
      hcq.locallyIntegrable.locallyIntegrableOn _, fun φ hφ => ?_⟩
    simp
  · have hg : Continuous fun x : ℝ => ((m 0 * (2 * x) : ℝ) : ℂ) :=
      continuous_ofReal_comp (continuous_const.mul (continuous_const.mul continuous_id))
    refine ⟨fun x => ((m 0 * (2 * x) : ℝ) : ℂ), memLp_Ioo_of_continuous hg,
      hg.locallyIntegrable.locallyIntegrableOn _, fun φ hφ => ?_⟩
    simp only [iteratedFDeriv_real, Fin.prod_univ_one, iteratedDeriv_one, quad]
    rw [integral_smul_ofReal (fun x => m 0 * deriv φ x) (fun x => x ^ 2 + c),
      integral_smul_ofReal φ (fun x => m 0 * (2 * x))]
    have e1 : ∫ x in Ioo (-1 : ℝ) 1, m 0 * deriv φ x * (x ^ 2 + c) =
        m 0 * ∫ x in Ioo (-1 : ℝ) 1, deriv φ x * (x ^ 2 + c) := by
      rw [← integral_const_mul]; congr 1; funext x; ring
    have e2 : ∫ x in Ioo (-1 : ℝ) 1, φ x * (m 0 * (2 * x)) =
        m 0 * ∫ x in Ioo (-1 : ℝ) 1, φ x * (2 * x) := by
      rw [← integral_const_mul]; congr 1; funext x; ring
    rw [e1, e2, ibp_quad1 hφ c, Complex.real_smul]
    push_cast; ring
  · have hg : Continuous fun _ : ℝ => ((m 0 * m 1 * 2 : ℝ) : ℂ) := continuous_const
    refine ⟨fun _ => ((m 0 * m 1 * 2 : ℝ) : ℂ), memLp_Ioo_of_continuous hg,
      hg.locallyIntegrable.locallyIntegrableOn _, fun φ hφ => ?_⟩
    simp only [iteratedFDeriv_real, Fin.prod_univ_two, quad]
    rw [iteratedDeriv_succ, iteratedDeriv_one,
      integral_smul_ofReal (fun x => m 0 * m 1 * deriv (deriv φ) x) (fun x => x ^ 2 + c),
      integral_smul_ofReal φ (fun _ => m 0 * m 1 * 2)]
    have e1 : ∫ x in Ioo (-1 : ℝ) 1, m 0 * m 1 * deriv (deriv φ) x * (x ^ 2 + c) =
        m 0 * m 1 * ∫ x in Ioo (-1 : ℝ) 1, deriv (deriv φ) x * (x ^ 2 + c) := by
      rw [← integral_const_mul]; congr 1; funext x; ring
    have e2 : ∫ x in Ioo (-1 : ℝ) 1, φ x * (m 0 * m 1 * 2) =
        m 0 * m 1 * ∫ x in Ioo (-1 : ℝ) 1, φ x * 2 := by
      rw [← integral_const_mul]; congr 1; funext x; ring
    rw [e1, e2, ibp_quad2 hφ c, Complex.real_smul]
    push_cast; ring

/-- `Δψ_c = 2` weakly on `(−1, 1)`. -/
theorem isWeakLaplacian_quad (c : ℝ) :
    IsWeakLaplacian (Ioo (-1 : ℝ) 1) (quad c) (fun _ => 2) := by
  refine ⟨continuous_const.locallyIntegrable.locallyIntegrableOn _, fun φ hφ => ?_⟩
  simp only [laplacian_real, quad]
  rw [integral_smul_ofReal (fun x => deriv (deriv φ) x) (fun x => x ^ 2 + c), ibp_quad2 hφ c]
  have : ∫ x in Ioo (-1 : ℝ) 1, φ x • (2 : ℂ) = ((∫ x in Ioo (-1 : ℝ) 1, φ x * 2 : ℝ) : ℂ) := by
    rw [← integral_smul_ofReal φ (fun _ => 2)]; push_cast; rfl
  rw [this]

theorem theta_quad {ε : ℝ} (x : ℝ) :
    Theta ε 0 (quad (-ε)) (fun _ => 2) x = -2 / (x : ℂ) ^ 2 := by
  simp only [Theta, Den, quad, neg_zero, zero_mul, Real.exp_zero, mul_one]
  push_cast; ring_nf

theorem not_memLp_theta {ε : ℝ} :
    ¬ MemLp (Theta ε 0 (quad (-ε)) (fun _ => 2)) 2 (volume.restrict (Ioo (-1 : ℝ) 1)) := by
  intro h
  have h1 : IntegrableOn (fun x => ‖Theta ε 0 (quad (-ε)) (fun _ => 2) x‖ ^ 2) (Ioo (-1 : ℝ) 1) :=
    (memLp_two_iff_integrable_sq_norm h.1).1 h
  have h2 : IntegrableOn (fun x => ‖Theta ε 0 (quad (-ε)) (fun _ => 2) x‖ ^ 2) (Ioo (0 : ℝ) 1) :=
    h1.mono_set (Ioo_subset_Ioo_left (by norm_num))
  have h3 : IntegrableOn (fun x : ℝ => x ^ (-4 : ℝ)) (Ioo (0 : ℝ) 1) := by
    refine IntegrableOn.congr_fun (h2.const_mul (1 / 4)) (fun x hx => ?_) measurableSet_Ioo
    have hx0 : 0 < x := hx.1
    simp only [theta_quad]
    rw [norm_div, norm_neg, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0,
      Real.rpow_neg hx0.le, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
    field_simp
    ring
  have := (intervalIntegral.integrableOn_Ioo_rpow_iff one_pos).1 h3
  norm_num at this

/-- **Counterexample (positive regularization is not enough).** On `Ω = (−1, 1)`, for every
`ε` (in particular every `ε > 0`), `α = 0` and `ψ(x) = x² − ε ∈ H²(Ω)`: `D_ε[ψ] = x²`, `Δψ = 2`,
`Θ_ε[ψ] = −2/x²` (`x ≠ 0`) and `∫_Ω |Θ_ε[ψ]|² = +∞`, while `‖Δψ‖²_{L²(Ω)} = 8`. Hence no estimate
`‖Θ_ε[ψ]‖ ≤ C ‖Δψ‖` with a finite constant holds for unrestricted signed fields, and the
denominator bound (H) fails for every `δ > 0`. -/
theorem counterexample (ε : ℝ) :
    MemH2 (Ioo (-1 : ℝ) 1) (quad (-ε)) ∧
    IsWeakLaplacian (Ioo (-1 : ℝ) 1) (quad (-ε)) (fun _ => 2) ∧
    (∀ x : ℝ, Den ε 0 (quad (-ε)) x = (x : ℂ) ^ 2) ∧
    (∀ x : ℝ, x ≠ 0 → Theta ε 0 (quad (-ε)) (fun _ => 2) x = -2 / (x : ℂ) ^ 2) ∧
    ¬ MemLp (Theta ε 0 (quad (-ε)) (fun _ => 2)) 2 (volume.restrict (Ioo (-1 : ℝ) 1)) ∧
    eLpNorm (Theta ε 0 (quad (-ε)) (fun _ => 2)) 2 (volume.restrict (Ioo (-1 : ℝ) 1)) = ⊤ ∧
    ∫ x in Ioo (-1 : ℝ) 1, ‖(fun _ : ℝ => (2 : ℂ)) x‖ ^ 2 = 8 ∧
    (∀ C : ℝ≥0∞, C ≠ ⊤ →
      ¬ eLpNorm (Theta ε 0 (quad (-ε)) (fun _ => 2)) 2 (volume.restrict (Ioo (-1 : ℝ) 1)) ≤
        C * eLpNorm (fun _ : ℝ => (2 : ℂ)) 2 (volume.restrict (Ioo (-1 : ℝ) 1))) ∧
    ¬ ∃ δ > 0, ∀ᵐ x ∂(volume.restrict (Ioo (-1 : ℝ) 1)), δ ≤ ‖Den ε 0 (quad (-ε)) x‖ := by
  have hmeas : AEStronglyMeasurable (Theta ε 0 (quad (-ε)) (fun _ => 2))
      (volume.restrict (Ioo (-1 : ℝ) 1)) := by
    have : Theta ε 0 (quad (-ε)) (fun _ => 2) = fun x : ℝ => -2 / (x : ℂ) ^ 2 :=
      funext fun x => theta_quad x
    rw [this]
    exact (measurable_const.div (Complex.measurable_ofReal.pow_const 2)).aestronglyMeasurable
  have htop : eLpNorm (Theta ε 0 (quad (-ε)) (fun _ => 2)) 2
      (volume.restrict (Ioo (-1 : ℝ) 1)) = ⊤ := by
    by_contra h
    exact not_memLp_theta ⟨hmeas, lt_top_iff_ne_top.2 h⟩
  have hfin : eLpNorm (fun _ : ℝ => (2 : ℂ)) 2 (volume.restrict (Ioo (-1 : ℝ) 1)) < ⊤ :=
    (memLp_Ioo_of_continuous continuous_const).eLpNorm_lt_top
  refine ⟨memH2_quad _, isWeakLaplacian_quad _, fun x => ?_, fun x _ => theta_quad x,
    not_memLp_theta, htop, ?_, fun C hC hle => ?_, fun ⟨δ, hδ, hH⟩ => not_memLp_theta
      (e26 isOpen_Ioo hδ (memH2_quad _) (isWeakLaplacian_quad _) hH).2.2.2.1⟩
  · simp only [Den, quad, neg_zero, zero_mul, Real.exp_zero, mul_one]
    push_cast; ring
  · rw [setIntegral_const, Measure.real, Real.volume_Ioo]
    norm_num
  · rw [htop, top_le_iff] at hle
    exact (ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hC) hfin).ne hle

theorem den_quad_shift (ε η x : ℝ) : Den ε 0 (quad (η - ε)) x = ((x ^ 2 + η : ℝ) : ℂ) := by
  simp only [Den, quad, neg_zero, zero_mul, Real.exp_zero, mul_one]; push_cast; ring

/-- **`δ` cannot be replaced by `ε`** in E26 without further restrictions on `ψ`: for every
`ε > 0` the field `ψ = x² − ε + η` (`η = min{1, ε²/8}`) on `(−1, 1)` satisfies (H) with `δ = η`,
yet `‖Θ_ε[ψ]‖_{L²} > ε⁻¹ ‖Δψ‖_{L²}`. -/
theorem delta_not_replaceable {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, MemH2 (Ioo (-1 : ℝ) 1) (quad c) ∧
      IsWeakLaplacian (Ioo (-1 : ℝ) 1) (quad c) (fun _ => 2) ∧
      (∃ δ > 0, ∀ x : ℝ, δ ≤ ‖Den ε 0 (quad c) x‖) ∧
      ENNReal.ofReal ε⁻¹ * eLpNorm (fun _ : ℝ => (2 : ℂ)) 2 (volume.restrict (Ioo (-1 : ℝ) 1)) <
        eLpNorm (Theta ε 0 (quad c) (fun _ => 2)) 2 (volume.restrict (Ioo (-1 : ℝ) 1)) := by
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = min 1 (ε ^ 2 / 8) := ⟨_, rfl⟩
  have hη0 : 0 < η := by rw [hη]; exact lt_min one_pos (by positivity)
  have hη1 : η ≤ 1 := by rw [hη]; exact min_le_left _ _
  have hη2 : η ≤ ε ^ 2 / 8 := by rw [hη]; exact min_le_right _ _
  have hden : ∀ x : ℝ, 0 < x ^ 2 + η := fun x => by positivity
  have hΘ : ∀ x : ℝ, Theta ε 0 (quad (η - ε)) (fun _ => 2) x = -2 / ((x ^ 2 + η : ℝ) : ℂ) :=
    fun x => by rw [Theta, den_quad_shift]
  have hΘn : ∀ x : ℝ,
      ‖Theta ε 0 (quad (η - ε)) (fun _ => 2) x‖ ^ 2 = 4 / (x ^ 2 + η) ^ 2 := fun x => by
    rw [hΘ, norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hden x),
      div_pow]
    norm_num
  refine ⟨η - ε, memH2_quad _, isWeakLaplacian_quad _, ⟨η, hη0, fun x => ?_⟩, ?_⟩
  · rw [den_quad_shift, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hden x)]
    nlinarith [sq_nonneg x]
  have hcont : Continuous (Theta ε 0 (quad (η - ε)) (fun _ => 2)) := by
    have : Theta ε 0 (quad (η - ε)) (fun _ => 2) =
        fun x : ℝ => -2 / ((x ^ 2 + η : ℝ) : ℂ) := funext hΘ
    rw [this]
    exact continuous_const.div (continuous_ofReal_comp ((continuous_pow 2).add continuous_const))
      fun x => by exact_mod_cast (hden x).ne'
  have hm1 := memLp_Ioo_of_continuous hcont
  have hm2 := memLp_Ioo_of_continuous (continuous_const : Continuous fun _ : ℝ => (2 : ℂ))
  have hA : ∫ x in Ioo (-1 : ℝ) 1, ‖(fun _ : ℝ => (2 : ℂ)) x‖ ^ (2 : ℝ) = 8 := by
    simp only [Real.rpow_two]
    rw [setIntegral_const, Measure.real, Real.volume_Ioo]; norm_num
  have hint : IntegrableOn (fun x => ‖Theta ε 0 (quad (η - ε)) (fun _ => 2) x‖ ^ 2)
      (Ioo (-1 : ℝ) 1) := (memLp_two_iff_integrable_sq_norm hm1.1).1 hm1
  have hsub : Ioo (-η) η ⊆ Ioo (-1 : ℝ) 1 := Ioo_subset_Ioo (by linarith) hη1
  have hB : 16 / ε ^ 2 ≤
      ∫ x in Ioo (-1 : ℝ) 1, ‖Theta ε 0 (quad (η - ε)) (fun _ => 2) x‖ ^ (2 : ℝ) := by
    simp only [Real.rpow_two]
    have h1 := setIntegral_mono_set hint (Eventually.of_forall fun x => by positivity)
      hsub.eventuallyLE
    have h2 := setIntegral_ge_of_const_le (c := 1 / η ^ 2) (measurableSet_Ioo (a := -η) (b := η))
      (by simp [Real.volume_Ioo]) (fun x hx => by
        rw [hΘn, div_le_div_iff₀ (by positivity) (by positivity)]
        have hx2 : x ^ 2 < η ^ 2 := by nlinarith [hx.1, hx.2]
        have hηη : η ^ 2 ≤ η := by nlinarith
        have h3 : x ^ 2 + η ≤ 2 * η := by nlinarith
        have h4 : (x ^ 2 + η) ^ 2 ≤ (2 * η) ^ 2 := pow_le_pow_left₀ (hden x).le h3 2
        nlinarith) (hint.mono_set hsub)
    have hvol : (volume : Measure ℝ).real (Ioo (-η) η) = 2 * η := by
      rw [Measure.real, Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith)]; ring
    rw [hvol] at h2
    have h5 : 16 / ε ^ 2 ≤ 1 / η ^ 2 * (2 * η) := by
      rw [show 1 / η ^ 2 * (2 * η) = 2 / η by field_simp]
      rw [div_le_div_iff₀ (by positivity) hη0]
      nlinarith
    linarith
  rw [hm1.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top,
    hm2.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top,
    ← ENNReal.ofReal_mul (inv_nonneg.2 hε.le)]
  simp only [ENNReal.toReal_ofNat]
  rw [hA]
  have hBpos : 0 < ∫ x in Ioo (-1 : ℝ) 1, ‖Theta ε 0 (quad (η - ε)) (fun _ => 2) x‖ ^ (2 : ℝ) :=
    lt_of_lt_of_le (by positivity) hB
  rw [ENNReal.ofReal_lt_ofReal_iff (Real.rpow_pos_of_pos hBpos _),
    show (2 : ℝ)⁻¹ = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow,
    Real.lt_sqrt (by positivity), mul_pow, Real.sq_sqrt (by norm_num)]
  have : ε⁻¹ ^ 2 * 8 < 16 / ε ^ 2 := by
    rw [inv_pow, ← div_eq_inv_mul, div_lt_div_iff_of_pos_right (by positivity)]; norm_num
  linarith

end Counterexample

end E26
end ReyesMath
