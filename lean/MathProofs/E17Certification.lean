import MathProofs.E17Canonical
import MathProofs.E17GlobalBound
import MathProofs.RegularizedCurvatureL2
import MathProofs.E26HistoricalCounterexample

/-!
# M2 + E17: the corrected modulus-squared curvature regularizer

Manuscript: `papers/regularized-curvature-operator/main.tex` (issue #36). For `ε > 0`, `α ∈ ℝ`:
`D_ε(z) = |z|² + ε²e^{−2α|z|²}` (`E17Cert.Deps`), `R_ε(z) = z̄/D_ε(z)` (`E26.Rε`, equal to
`E17Canonical.reciprocal`), and `Θ_ε[ψ] = −(Δψ)R_ε(ψ)` (`M6B.fieldCurvatureD … 0 1` for the genuine
Cartesian Laplacian, `E17Cert.fieldCurvature_eq`).

* **Theorem (M2 + E17)** (`E17Cert.main_theorem`): (1) `D_ε > 0`; (2) `R_ε` is a smooth bounded map
  of `ℝ²` with `R_ε(0) = 0` and the explicit bound `max{1/ρ, ρe^{2α₊ρ²}/ε²}` for every `ρ > 0`
  (`E17Cert.global_bound`); (3) `R_ε(z) → 1/z` (`z ≠ 0`); (4) the exact difference identity and
  error formula (`E17Cert.exact_difference`, `E17Cert.error_formula`), `sup_{|z|≥δ}|R_ε − 1/z| ≤ ε²/δ³`
  for `α ≥ 0` (`E17Cert.uniform_bound`), and uniform convergence on compact subsets of `ℂ∖{0}` for
  every `α` (`E17Cert.compact_bound`, `E17Cert.tendstoUniformlyOn_compact`); (5) the curvature limit.
* **Corollaries** (`E17Cert.l2_limit`, `E17Cert.fixed_eps_control`), **Remarks** (`E17Cert.whole_space`,
  `E17Cert.node_obstruction`, `E17Cert.local_gauge`), **Proposition** (`E17Cert.phase_invariance`)
  and the **historical counterexample** (`E17Cert.historical`).
-/

open Filter Topology Complex MeasureTheory Set
open scoped ComplexConjugate ENNReal

noncomputable section

namespace ReyesMath
namespace E17Cert

open E26

/-- The corrected denominator `D_ε(z) = |z|² + ε²e^{−2α|z|²}`. -/
def Deps (ε α : ℝ) (z : ℂ) : ℝ := ‖z‖ ^ 2 + ε ^ 2 * Real.exp (-2 * α * ‖z‖ ^ 2)

theorem Deps_pos {ε : ℝ} (hε : 0 < ε) (α : ℝ) (z : ℂ) : 0 < Deps ε α z := by
  unfold Deps; positivity

theorem Rε_eq (ε α : ℝ) (z : ℂ) : Rε ε α z = conj z / (Deps ε α z : ℂ) := rfl

theorem reciprocal_eq_Rε (ε α : ℝ) (z : ℂ) : E17Canonical.reciprocal ε α z = Rε ε α z := by
  rw [E17Canonical.reciprocal_eq_explicit, Rε]
  congr 2
  simp [E17Canonical.denominator, M6B.denominator, Complex.normSq_eq_norm_sq]

theorem fieldCurvature_eq (d : ℕ) (ε α : ℝ) (ψ : EuclideanSpace ℝ (Fin d) → ℂ)
    (x : EuclideanSpace ℝ (Fin d)) :
    M6B.fieldCurvatureD d ε α 0 1 ψ x = -(M6B.laplacianD d ψ x) * Rε ε α (ψ x) := by
  rw [M6B.fieldCurvatureD, M6B.curvature, Rε]
  have : ((M6B.denominator ε α 0 1 (Complex.normSq (ψ x)) : ℝ) : ℂ) =
      ((‖ψ x‖ ^ 2 + ε ^ 2 * Real.exp (-2 * α * ‖ψ x‖ ^ 2) : ℝ) : ℂ) := by
    congr 1; simp [M6B.denominator, Complex.normSq_eq_norm_sq]
  rw [this]; ring

/-! ### The global bound and the quantitative convergence -/

/-- **The global fixed-`ε` bound**: for every `ρ > 0`,
`‖R_ε‖_∞ ≤ max{1/ρ, ρe^{2α₊ρ²}/ε²}`, `α₊ = max{α, 0}`. -/
theorem global_bound {ε : ℝ} (hε : 0 < ε) (α : ℝ) {ρ : ℝ} (hρ : 0 < ρ) (z : ℂ) :
    ‖Rε ε α z‖ ≤ max (1 / ρ) (ρ * Real.exp (2 * max α 0 * ρ ^ 2) / ε ^ 2) := by
  rw [norm_Rε hε]
  rcases le_or_gt ‖z‖ ρ with hz | hz
  · apply le_max_of_le_right
    have hz2 : ‖z‖ ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hz 2
    have he : -2 * max α 0 * ρ ^ 2 ≤ -2 * α * ‖z‖ ^ 2 := by
      have h1 : α * ‖z‖ ^ 2 ≤ max α 0 * ‖z‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
      have h2 : max α 0 * ‖z‖ ^ 2 ≤ max α 0 * ρ ^ 2 :=
        mul_le_mul_of_nonneg_left hz2 (le_max_right _ _)
      linarith
    have hlow : ε ^ 2 * Real.exp (-2 * max α 0 * ρ ^ 2) ≤
        ‖z‖ ^ 2 + ε ^ 2 * Real.exp (-2 * α * ‖z‖ ^ 2) := by
      have := mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 he) (sq_nonneg ε)
      nlinarith [sq_nonneg ‖z‖]
    have hpos : 0 < ε ^ 2 * Real.exp (-2 * max α 0 * ρ ^ 2) := by positivity
    calc ‖z‖ / (‖z‖ ^ 2 + ε ^ 2 * Real.exp (-2 * α * ‖z‖ ^ 2))
        ≤ ‖z‖ / (ε ^ 2 * Real.exp (-2 * max α 0 * ρ ^ 2)) :=
          div_le_div_of_nonneg_left (norm_nonneg _) hpos hlow
      _ ≤ ρ / (ε ^ 2 * Real.exp (-2 * max α 0 * ρ ^ 2)) := div_le_div_of_nonneg_right hz hpos.le
      _ = ρ * Real.exp (2 * max α 0 * ρ ^ 2) / ε ^ 2 := by
          rw [show -2 * max α 0 * ρ ^ 2 = -(2 * max α 0 * ρ ^ 2) by ring, Real.exp_neg]
          field_simp
  · apply le_max_of_le_left
    have hz0 : 0 < ‖z‖ := hρ.trans hz
    have := hz0.ne'
    calc ‖z‖ / (‖z‖ ^ 2 + ε ^ 2 * Real.exp (-2 * α * ‖z‖ ^ 2)) ≤ ‖z‖ / ‖z‖ ^ 2 :=
          div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
            (le_add_of_nonneg_right (by positivity))
      _ = 1 / ‖z‖ := by field_simp
      _ ≤ 1 / ρ := one_div_le_one_div_of_le hρ hz.le

theorem conj_mul_self (z : ℂ) : conj z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- **The exact difference identity**: `R_ε(z) − 1/z = −(1/z) · ε²e^{−2α|z|²}/D_ε(z)`. -/
theorem exact_difference {ε : ℝ} (hε : 0 < ε) (α : ℝ) {z : ℂ} (hz : z ≠ 0) :
    Rε ε α z - 1 / z =
      -(1 / z) * (((ε ^ 2 * Real.exp (-2 * α * ‖z‖ ^ 2)) / Deps ε α z : ℝ) : ℂ) := by
  have hD := Deps_pos hε α z
  have hDc : ((Deps ε α z : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  rw [Rε_eq, div_sub_div _ _ hDc hz, conj_mul_self]
  rw [show ((‖z‖ ^ 2 : ℝ) : ℂ) - (Deps ε α z : ℂ) * 1 =
      -((ε ^ 2 * Real.exp (-2 * α * ‖z‖ ^ 2) : ℝ) : ℂ) by simp only [Deps]; push_cast; ring]
  push_cast
  field_simp

/-- **The error formula**:
`|R_ε(z) − 1/z| = ε²e^{−2α|z|²}/(|z| D_ε(z)) ≤ ε²e^{−2α|z|²}/|z|³`. -/
theorem error_formula {ε : ℝ} (hε : 0 < ε) (α : ℝ) {z : ℂ} (hz : z ≠ 0) :
    ‖Rε ε α z - 1 / z‖ = ε ^ 2 * Real.exp (-2 * α * ‖z‖ ^ 2) / (‖z‖ * Deps ε α z) ∧
    ‖Rε ε α z - 1 / z‖ ≤ ε ^ 2 * Real.exp (-2 * α * ‖z‖ ^ 2) / ‖z‖ ^ 3 := by
  have hD := Deps_pos hε α z
  have hz0 : 0 < ‖z‖ := norm_pos_iff.2 hz
  have h1 : ‖Rε ε α z - 1 / z‖ = ε ^ 2 * Real.exp (-2 * α * ‖z‖ ^ 2) / (‖z‖ * Deps ε α z) := by
    rw [exact_difference hε α hz, norm_mul, norm_neg, norm_div, norm_one, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]
    field_simp
  refine ⟨h1, ?_⟩
  rw [h1]
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  have : ‖z‖ ^ 2 ≤ Deps ε α z := by unfold Deps; have := Real.exp_pos (-2 * α * ‖z‖ ^ 2); nlinarith
  calc ‖z‖ ^ 3 = ‖z‖ * ‖z‖ ^ 2 := by ring
    _ ≤ ‖z‖ * Deps ε α z := mul_le_mul_of_nonneg_left this hz0.le

/-- **Uniform convergence away from nodes, `α ≥ 0`**: `|R_ε(z) − 1/z| ≤ ε²/δ³` for `|z| ≥ δ`. -/
theorem uniform_bound {ε : ℝ} (hε : 0 < ε) {α : ℝ} (hα : 0 ≤ α) {δ : ℝ} (hδ : 0 < δ) {z : ℂ}
    (hz : δ ≤ ‖z‖) : ‖Rε ε α z - 1 / z‖ ≤ ε ^ 2 / δ ^ 3 := by
  have hz0 : 0 < ‖z‖ := hδ.trans_le hz
  refine (error_formula hε α (norm_pos_iff.1 hz0)).2.trans ?_
  have he : Real.exp (-2 * α * ‖z‖ ^ 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg ‖z‖])
  calc ε ^ 2 * Real.exp (-2 * α * ‖z‖ ^ 2) / ‖z‖ ^ 3 ≤ ε ^ 2 * 1 / ‖z‖ ^ 3 := by gcongr
    _ ≤ ε ^ 2 * 1 / δ ^ 3 := by gcongr
    _ = ε ^ 2 / δ ^ 3 := by ring

/-- **The compact bound for arbitrary `α`**: on `δ ≤ |z| ≤ M`,
`|R_ε(z) − 1/z| ≤ ε²e^{2α₋M²}/δ³`, `α₋ = max{−α, 0}`. -/
theorem compact_bound {ε : ℝ} (hε : 0 < ε) (α : ℝ) {δ M : ℝ} (hδ : 0 < δ) {z : ℂ}
    (h1 : δ ≤ ‖z‖) (h2 : ‖z‖ ≤ M) :
    ‖Rε ε α z - 1 / z‖ ≤ ε ^ 2 * Real.exp (2 * max (-α) 0 * M ^ 2) / δ ^ 3 := by
  have hz0 : 0 < ‖z‖ := hδ.trans_le h1
  refine (error_formula hε α (norm_pos_iff.1 hz0)).2.trans ?_
  have hz2 : ‖z‖ ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ hz0.le h2 2
  have he : Real.exp (-2 * α * ‖z‖ ^ 2) ≤ Real.exp (2 * max (-α) 0 * M ^ 2) := by
    apply Real.exp_le_exp.2
    have h3 : -α * ‖z‖ ^ 2 ≤ max (-α) 0 * ‖z‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
    have h4 : max (-α) 0 * ‖z‖ ^ 2 ≤ max (-α) 0 * M ^ 2 :=
      mul_le_mul_of_nonneg_left hz2 (le_max_right _ _)
    linarith
  calc ε ^ 2 * Real.exp (-2 * α * ‖z‖ ^ 2) / ‖z‖ ^ 3
      ≤ ε ^ 2 * Real.exp (2 * max (-α) 0 * M ^ 2) / ‖z‖ ^ 3 := by gcongr
    _ ≤ ε ^ 2 * Real.exp (2 * max (-α) 0 * M ^ 2) / δ ^ 3 := by gcongr

/-- **Uniform convergence on compact subsets of `ℂ ∖ {0}`**, for every real `α`. -/
theorem tendstoUniformlyOn_compact (α : ℝ) {K : Set ℂ} (hK : IsCompact K) (h0 : (0 : ℂ) ∉ K) :
    TendstoUniformlyOn (fun ε z => Rε ε α z) (fun z => 1 / z) (𝓝[>] 0) K := by
  rcases K.eq_empty_or_nonempty with hK0 | hKne
  · rw [hK0]; exact tendstoUniformlyOn_empty
  obtain ⟨z₀, hz₀K, hz₀⟩ := hK.exists_isMinOn hKne continuous_norm.continuousOn
  obtain ⟨z₁, -, hz₁⟩ := hK.exists_isMaxOn hKne continuous_norm.continuousOn
  have hδ : 0 < ‖z₀‖ := norm_pos_iff.2 fun h => h0 (h ▸ hz₀K)
  set C := Real.exp (2 * max (-α) 0 * ‖z₁‖ ^ 2) / ‖z₀‖ ^ 3
  have hC : 0 < C := by positivity
  rw [Metric.tendstoUniformlyOn_iff]
  intro η hη
  have hlim : Tendsto (fun ε : ℝ => ε ^ 2 * C) (𝓝[>] 0) (𝓝 0) := by
    have := ((continuous_pow 2).mul continuous_const).tendsto (0 : ℝ) (f := fun ε : ℝ => ε ^ 2 * C)
    simpa using this.mono_left nhdsWithin_le_nhds
  filter_upwards [hlim.eventually (gt_mem_nhds hη), self_mem_nhdsWithin] with ε hε (hε0 : 0 < ε)
  intro z hz
  rw [dist_comm, dist_eq_norm]
  calc ‖Rε ε α z - 1 / z‖ ≤ ε ^ 2 * Real.exp (2 * max (-α) 0 * ‖z₁‖ ^ 2) / ‖z₀‖ ^ 3 :=
        compact_bound hε0 α hδ (hz₀ hz) (hz₁ hz)
    _ = ε ^ 2 * C := by ring
    _ < η := hε

/-- **Theorem (M2 + E17).** For every `ε > 0` and `α ∈ ℝ`: (1) `D_ε > 0`, including at `z = 0`;
(2) `R_ε` is a `C^∞` map of `ℝ²`, `R_ε(0) = 0`, globally bounded; (3) `R_ε(z) → 1/z` as `ε ↓ 0`
for `z ≠ 0`; (4) for `α ≥ 0`, `sup_{|z|≥δ}|R_ε − 1/z| ≤ ε²/δ³`, and for every `α` uniform convergence
on compact subsets of `ℂ∖{0}`; (5) for every field `ψ` and `ψ(x) ≠ 0`,
`Θ_ε[ψ](x) → −Δψ(x)/ψ(x)`. -/
theorem main_theorem {ε : ℝ} (hε : 0 < ε) (α : ℝ) :
    (∀ z : ℂ, 0 < Deps ε α z) ∧
    ContDiff ℝ ⊤ (Rε ε α) ∧ Rε ε α 0 = 0 ∧
    (∀ z : ℂ, ‖Rε ε α z‖ ≤ max 1 (Real.exp (2 * max α 0) / ε ^ 2)) ∧
    (∀ z : ℂ, z ≠ 0 → Tendsto (fun η => Rε η α z) (𝓝[>] 0) (𝓝 (1 / z))) ∧
    (0 ≤ α → ∀ δ : ℝ, 0 < δ → ∀ z : ℂ, δ ≤ ‖z‖ → ‖Rε ε α z - 1 / z‖ ≤ ε ^ 2 / δ ^ 3) ∧
    (∀ K : Set ℂ, IsCompact K → (0 : ℂ) ∉ K →
      TendstoUniformlyOn (fun η z => Rε η α z) (fun z => 1 / z) (𝓝[>] 0) K) ∧
    (∀ (d : ℕ) (ψ : EuclideanSpace ℝ (Fin d) → ℂ) (x : EuclideanSpace ℝ (Fin d)), ψ x ≠ 0 →
      Tendsto (fun η => -(M6B.laplacianD d ψ x) * Rε η α (ψ x)) (𝓝[>] 0)
        (𝓝 (-(M6B.laplacianD d ψ x / ψ x)))) := by
  have hcd : ContDiff ℝ ⊤ (Rε ε α) := by
    have := E17Canonical.reciprocal_contDiff ε α hε
    rwa [show E17Canonical.reciprocal ε α = Rε ε α from funext (reciprocal_eq_Rε ε α)] at this
  refine ⟨Deps_pos hε α, hcd, by simp [Rε], fun z => ?_, fun z hz => ?_,
    fun hα δ hδ z hz => uniform_bound hε hα hδ hz, fun K hK h0 => tendstoUniformlyOn_compact α hK h0,
    fun d ψ x hx => ?_⟩
  · simpa using global_bound hε α one_pos z
  · have := E17Canonical.reciprocal_downarrow_zero α z hz
    simpa only [reciprocal_eq_Rε] using this
  · have := E17Canonical.physical_curvature_downarrow_zero d α ψ x hx
    simpa only [fieldCurvature_eq] using this

/-! ### Convergence in `L²` -/

section L2

variable {d : ℕ}

local notation "Rd" => EuclideanSpace ℝ (Fin d)

/-- **Corollary (strong `L²` limit away from nodes).** For `α ≥ 0`, `ψ ∈ H²(Ω; ℂ)` with
`|ψ| ≥ δ > 0` a.e., `‖Θ_ε[ψ] + Δψ/ψ‖_{L²(Ω)} ≤ (ε²/δ³)‖Δψ‖_{L²(Ω)} → 0`. -/
theorem l2_limit {Ω : Set Rd} (hΩ : IsOpen Ω) {α δ : ℝ} (hα : 0 ≤ α) (hδ : 0 < δ)
    {ψ F : Rd → ℂ} (hψ : MemH2 Ω ψ) (hF : IsWeakLaplacian Ω ψ F)
    (hsep : ∀ᵐ x ∂(volume.restrict Ω), δ ≤ ‖ψ x‖) :
    (∀ {ε : ℝ}, 0 < ε →
      eLpNorm (fun x => -F x * Rε ε α (ψ x) + F x / ψ x) 2 (volume.restrict Ω) ≤
        ENNReal.ofReal (ε ^ 2 / δ ^ 3) * eLpNorm F 2 (volume.restrict Ω)) ∧
    Tendsto (fun ε => eLpNorm (fun x => -F x * Rε ε α (ψ x) + F x / ψ x) 2 (volume.restrict Ω))
      (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨G, hG2, hGL⟩ := hψ.exists_weakLaplacian hΩ
  have hF2 : MemLp F 2 (volume.restrict Ω) := hG2.ae_eq (hF.ae_eq hΩ hGL).symm
  have hbound : ∀ {ε : ℝ}, 0 < ε →
      eLpNorm (fun x => -F x * Rε ε α (ψ x) + F x / ψ x) 2 (volume.restrict Ω) ≤
        ENNReal.ofReal (ε ^ 2 / δ ^ 3) * eLpNorm F 2 (volume.restrict Ω) := by
    intro ε hε
    refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul ?_ 2
    filter_upwards [hsep] with x hx
    have hx0 : ψ x ≠ 0 := norm_pos_iff.1 (hδ.trans_le hx)
    rw [show -F x * Rε ε α (ψ x) + F x / ψ x = -(F x * (Rε ε α (ψ x) - 1 / ψ x)) by
      field_simp; ring, norm_neg, norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (uniform_bound hε hα hδ hx) (norm_nonneg _)
  refine ⟨hbound, ?_⟩
  have hfin : eLpNorm F 2 (volume.restrict Ω) ≠ ⊤ := hF2.eLpNorm_ne_top
  have hlim : Tendsto (fun ε : ℝ => ENNReal.ofReal (ε ^ 2 / δ ^ 3) * eLpNorm F 2 (volume.restrict Ω))
      (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun ε : ℝ => ENNReal.ofReal (ε ^ 2 / δ ^ 3)) (𝓝[>] 0) (𝓝 0) := by
      have := (ENNReal.continuous_ofReal.comp ((continuous_pow 2).div_const (δ ^ 3))).tendsto
        (0 : ℝ)
      simpa using this.mono_left nhdsWithin_le_nhds
    simpa using ENNReal.Tendsto.mul_const h1 (Or.inr hfin)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => zero_le _)
    (eventually_nhdsWithin_of_forall fun ε hε => hbound hε)

/-- **Corollary (fixed-regularization `L²` control)**, for every real `α`:
`‖Θ_ε[ψ]‖_{L²(Ω)} ≤ ‖R_ε‖_∞ ‖Δψ‖_{L²(Ω)}` with `‖R_ε‖_∞ ≤ max{1, e^{2α₊}/ε²}`. -/
theorem fixed_eps_control {Ω : Set Rd} (hΩ : IsOpen Ω) {ε α : ℝ} (hε : 0 < ε)
    {ψ F : Rd → ℂ} (hψ : MemH2 Ω ψ) (hF : IsWeakLaplacian Ω ψ F) :
    MemLp (fun x => -F x * Rε ε α (ψ x)) 2 (volume.restrict Ω) ∧
    eLpNorm (fun x => -F x * Rε ε α (ψ x)) 2 (volume.restrict Ω) ≤
      ENNReal.ofReal (max 1 (Real.exp (2 * max α 0) / ε ^ 2)) * eLpNorm F 2 (volume.restrict Ω) := by
  obtain ⟨G, hG2, hGL⟩ := hψ.exists_weakLaplacian hΩ
  have hF2 : MemLp F 2 (volume.restrict Ω) := hG2.ae_eq (hF.ae_eq hΩ hGL).symm
  have hm : AEStronglyMeasurable (fun x => -F x * Rε ε α (ψ x)) (volume.restrict Ω) :=
    hF2.1.neg.mul ((continuous_Rε hε α).comp_aestronglyMeasurable hψ.1.1)
  have hpt : ∀ᵐ x ∂(volume.restrict Ω), ‖-F x * Rε ε α (ψ x)‖ ≤
      max 1 (Real.exp (2 * max α 0) / ε ^ 2) * ‖F x‖ := Eventually.of_forall fun x => by
    rw [norm_mul, norm_neg, mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    simpa using global_bound hε α one_pos (ψ x)
  exact ⟨hF2.of_le_mul hm hpt, eLpNorm_le_mul_eLpNorm_of_ae_le_mul hpt 2⟩

/-- **Remark (whole-space limitation)**: `|ψ| ≥ δ > 0` a.e. on `ℝ^d` is incompatible with
`ψ ∈ L²(ℝ^d)`. -/
theorem whole_space (hd : 1 ≤ d) {δ : ℝ} (hδ : 0 < δ) {ψ : Rd → ℂ} (hψ : MemLp ψ 2 volume) :
    ¬ ∀ᵐ x, δ ≤ ‖ψ x‖ := by
  haveI : Nontrivial Rd := by
    refine ⟨⟨EuclideanSpace.single (⟨0, hd⟩ : Fin d) (1 : ℝ), 0, fun h => ?_⟩⟩
    have := congrArg (fun v : Rd => v ⟨0, hd⟩) h
    simp at this
  exact not_ae_norm_ge_of_memLp hδ hψ

end L2

/-! ### No uniform convergence through a node -/

/-- **Remark (no uniform convergence through a node)**:
`|R_ε(ε) − 1/ε| = e^{−2αε²}/(ε(1 + e^{−2αε²})) ∼ 1/(2ε)`; hence the convergence is not uniform on
any punctured neighbourhood of the origin. -/
theorem node_obstruction (α : ℝ) :
    (∀ ε : ℝ, 0 < ε → ‖Rε ε α (ε : ℂ) - 1 / (ε : ℂ)‖ =
      Real.exp (-2 * α * ε ^ 2) / (ε * (1 + Real.exp (-2 * α * ε ^ 2)))) ∧
    Tendsto (fun ε : ℝ => ε * ‖Rε ε α (ε : ℂ) - 1 / (ε : ℂ)‖) (𝓝[>] 0) (𝓝 (1 / 2)) ∧
    ∀ r : ℝ, 0 < r →
      ¬ TendstoUniformlyOn (fun ε z => Rε ε α z) (fun z => 1 / z) (𝓝[>] 0)
        (Metric.ball (0 : ℂ) r \ {0}) := by
  have hval : ∀ ε : ℝ, 0 < ε → ‖Rε ε α (ε : ℂ) - 1 / (ε : ℂ)‖ =
      Real.exp (-2 * α * ε ^ 2) / (ε * (1 + Real.exp (-2 * α * ε ^ 2))) := by
    intro ε hε
    have h := (error_formula hε α (Complex.ofReal_ne_zero.2 hε.ne')).1
    rw [h, Complex.norm_real, Real.norm_of_nonneg hε.le, Deps, Complex.norm_real,
      Real.norm_of_nonneg hε.le]
    have := Real.exp_pos (-2 * α * ε ^ 2)
    field_simp
  have hlim : Tendsto (fun ε : ℝ => ε * ‖Rε ε α (ε : ℂ) - 1 / (ε : ℂ)‖) (𝓝[>] 0) (𝓝 (1 / 2)) := by
    have hc : Continuous fun ε : ℝ =>
        Real.exp (-2 * α * ε ^ 2) / (1 + Real.exp (-2 * α * ε ^ 2)) :=
      (Real.continuous_exp.comp (by fun_prop)).div (continuous_const.add
        (Real.continuous_exp.comp (by fun_prop))) fun ε => by positivity
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    rw [show Real.exp (-2 * α * (0 : ℝ) ^ 2) / (1 + Real.exp (-2 * α * (0 : ℝ) ^ 2)) = 1 / 2 by
      simp; norm_num] at this
    refine this.congr' (eventually_nhdsWithin_of_forall fun ε (hε : 0 < ε) => ?_)
    show _ = ε * ‖Rε ε α (ε : ℂ) - 1 / (ε : ℂ)‖
    rw [hval ε hε]
    have := Real.exp_pos (-2 * α * ε ^ 2)
    field_simp
  refine ⟨hval, hlim, fun r hr hunif => ?_⟩
  rw [Metric.tendstoUniformlyOn_iff] at hunif
  -- for small `ε`, `ε` lies in the punctured ball while `|R_ε(ε) − 1/ε| ≥ 1/(4ε) > 1`
  have h1 := hunif 1 one_pos
  have h2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 1 / 4 < ε * ‖Rε ε α (ε : ℂ) - 1 / (ε : ℂ)‖ :=
    hlim.eventually (lt_mem_nhds (by norm_num))
  have h3 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < min r (1 / 4) :=
    nhdsWithin_le_nhds (Iio_mem_nhds (lt_min hr (by norm_num)))
  obtain ⟨ε, ⟨⟨hA, hB⟩, hC⟩, hD⟩ := ((h1.and h2).and h3).and self_mem_nhdsWithin |>.exists
  have hε0 : 0 < ε := hD
  have hmem : (ε : ℂ) ∈ Metric.ball (0 : ℂ) r \ {0} := by
    refine ⟨?_, by simpa using hε0.ne'⟩
    rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_of_nonneg hε0.le]
    exact hC.trans_le (min_le_left _ _)
  have h4 := hA (ε : ℂ) hmem
  rw [dist_comm, dist_eq_norm] at h4
  have h5 : ε < 1 / 4 := hC.trans_le (min_le_right _ _)
  nlinarith [norm_nonneg (Rε ε α (ε : ℂ) - 1 / (ε : ℂ))]

/-! ### Global phase invariance and its limits -/

/-- **Proposition (constant `U(1)` phase invariance)** for `C²` fields:
`Θ_ε[e^{iβ}ψ] = Θ_ε[ψ]`. -/
theorem phase_invariance (d : ℕ) (ψ : EuclideanSpace ℝ (Fin d) → ℂ) (hψ : ContDiff ℝ 2 ψ)
    (β ε α : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    -(M6B.laplacianD d (fun y => Complex.exp (β * I) * ψ y) x) *
        Rε ε α (Complex.exp (β * I) * ψ x) =
      -(M6B.laplacianD d ψ x) * Rε ε α (ψ x) := by
  rw [← fieldCurvature_eq, ← fieldCurvature_eq]
  exact E17Canonical.physical_curvature_phase_invariant d ψ hψ _ (by
    rw [Complex.norm_exp_ofReal_mul_I]) ε α x

theorem laplacian_real_complex (φ : ℝ → ℂ) (x : ℝ) :
    InnerProductSpace.laplacian φ x = deriv (deriv φ) x := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis φ
    (OrthonormalBasis.singleton (Fin 1) ℝ)]
  simp only [Finset.univ_unique, Finset.sum_singleton, OrthonormalBasis.singleton_apply]
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, iteratedDeriv_succ, iteratedDeriv_one]
  simp

/-- **Remark (no local gauge invariance)**: on `ℝ`, with `ψ ≡ 1` and the position-dependent phase
`β(x) = x`, `Θ_ε[e^{iβ}ψ] = 1/D_ε(1) ≠ 0 = Θ_ε[ψ]`. -/
theorem local_gauge {ε : ℝ} (hε : 0 < ε) (α x : ℝ) :
    -(InnerProductSpace.laplacian (fun y : ℝ => Complex.exp (y * I)) x) *
        Rε ε α (Complex.exp (x * I)) =
        ((1 / Deps ε α 1 : ℝ) : ℂ) ∧
    -(InnerProductSpace.laplacian (fun _ : ℝ => (1 : ℂ)) x) * Rε ε α 1 = 0 ∧
    ((1 / Deps ε α 1 : ℝ) : ℂ) ≠ 0 := by
  have hd1 : ∀ y : ℝ, HasDerivAt (fun y : ℝ => Complex.exp (y * I)) (I * Complex.exp (y * I)) y :=
    fun y => by
      have := ((hasDerivAt_id y).ofReal_comp.mul_const I).cexp
      convert this using 1; simp; ring
  have hd2 : ∀ y : ℝ, HasDerivAt (fun y : ℝ => I * Complex.exp (y * I))
      (-Complex.exp (y * I)) y := fun y => by
    have := (hd1 y).const_mul I
    convert this using 1
    rw [← mul_assoc, Complex.I_mul_I]; ring
  have hderiv : deriv (fun y : ℝ => Complex.exp (y * I)) = fun y : ℝ => I * Complex.exp (y * I) :=
    funext fun y => (hd1 y).deriv
  have hn : ‖Complex.exp (x * I)‖ = 1 := Complex.norm_exp_ofReal_mul_I x
  have hD := Deps_pos hε α 1
  refine ⟨?_, ?_, ?_⟩
  · rw [laplacian_real_complex, hderiv, (hd2 x).deriv, Rε_eq]
    have hDe : Deps ε α (Complex.exp (x * I)) = Deps ε α 1 := by simp [Deps, hn]
    rw [hDe]
    have hc : Complex.exp (x * I) * conj (Complex.exp (x * I)) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]; simp
    have hDc : ((Deps ε α 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
    push_cast
    field_simp
    linear_combination hc
  · rw [laplacian_real_complex]; simp
  · have : 0 < 1 / Deps ε α 1 := by positivity
    exact_mod_cast this.ne'

/-! ### The historical denominator -/

/-- The historical regularized curvature at the jet `(ψ(x), Δψ(x)) = (z, w)`. -/
def thetaOld (ε α : ℝ) (z w : ℂ) : ℂ :=
  -w / E26HistoricalCounterexample.additiveDenominator ε α z

/-- **Counterexample to the historical denominator**: for `α = 0` and `ψ ≡ −ε` the denominator
`ψ + εe^{−α|ψ|²}` vanishes, while the corrected one is positive at every value; and the historical
operator is not constant-phase covariant (`z = 0`, `Δψ = 1`, phase `i`). -/
theorem historical {ε : ℝ} (hε : 0 < ε) :
    E26HistoricalCounterexample.additiveDenominator ε 0 (-(ε : ℂ)) = 0 ∧
    (∀ (α : ℝ) (z : ℂ), 0 < Deps ε α z) ∧
    thetaOld ε 0 (I * 0) (I * 1) ≠ thetaOld ε 0 0 1 := by
  refine ⟨E26HistoricalCounterexample.additiveDenominator_zero_at_negative ε, fun α z =>
    Deps_pos hε α z, ?_⟩
  simp only [thetaOld, E26HistoricalCounterexample.additiveDenominator, mul_zero, mul_one,
    norm_zero, zero_pow two_ne_zero, mul_zero, neg_zero, Real.exp_zero, mul_one, zero_add]
  intro h
  have hε' : (ε : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hε.ne'
  rw [div_eq_div_iff hε' hε'] at h
  have := congrArg Complex.im h
  simp at this
  exact hε.ne' (by simpa using this)

end E17Cert
end ReyesMath
