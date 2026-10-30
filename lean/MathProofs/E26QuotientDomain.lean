import MathProofs.E26Certification

/-!
# E26: the quotient on its measurable domain, and sharpness of the constant `1/δ`

Manuscript: `papers/regularized-curvature-l2-bound/main.tex` (issue #35). The theorem, both
corollaries, the remark, the counterexample and the historical-versus-corrected comparison are in
`RegularizedCurvatureL2` and `E26Certification`. This module adds:

* **The quotient on its measurable domain** (`E26Domain.quotient_domain`). The manuscript defines
  `Θ_ε[ψ] = −Δψ/D_ε[ψ]` only where `D_ε[ψ] ≠ 0`. That set is (null-)measurable, under (H) its
  complement is null, and `Θ_ε[ψ]·D_ε[ψ] = −Δψ` there; every function solving this a.e. on the
  domain equals `Θ_ε[ψ]` a.e. So the value chosen at denominator zeros is irrelevant.
* **Sharpness of `1/δ`** (`E26Domain.sharp_constant`). For every `K < 1` there is an admissible
  smooth field (`Ω = (−1,1)`, `α = 0`, `ψ = x² + δ − ε`, `|D_ε[ψ]| ≥ δ`) with
  `‖Θ_ε[ψ]‖ > (K/δ)‖Δψ‖`. Hence no smaller universal multiple of `1/δ` is valid.
-/

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

namespace ReyesMath
namespace E26Domain

open E26

section General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]

/-- **The quotient on its measurable domain.** Under (H), `{D_ε[ψ] ≠ 0}` is null-measurable with
null complement in `Ω`, `Θ_ε[ψ]·D_ε[ψ] = −Δψ` on it, and `Θ_ε[ψ]` is the a.e.-unique solution. -/
theorem quotient_domain {Ω : Set E} (hΩ : IsOpen Ω) {ε α δ : ℝ} (hδ : 0 < δ) {ψ F : E → ℂ}
    (hψ : MemH2 Ω ψ) (hF : IsWeakLaplacian Ω ψ F)
    (hH : ∀ᵐ x ∂(volume.restrict Ω), δ ≤ ‖Den ε α ψ x‖) :
    NullMeasurableSet {x | Den ε α ψ x ≠ 0} (volume.restrict Ω) ∧
    (volume.restrict Ω) {x | Den ε α ψ x ≠ 0}ᶜ = 0 ∧
    (∀ x, Den ε α ψ x ≠ 0 → Theta ε α ψ F x * Den ε α ψ x = -F x) ∧
    (∀ G : E → ℂ, (∀ᵐ x ∂(volume.restrict Ω), Den ε α ψ x ≠ 0 → G x * Den ε α ψ x = -F x) →
      G =ᵐ[volume.restrict Ω] Theta ε α ψ F) := by
  have hD : AEStronglyMeasurable (Den ε α ψ) (volume.restrict Ω) :=
    aestronglyMeasurable_den hψ.1.1
  have hne := (e26 hΩ hδ hψ hF hH).2.1
  have hset : {x | Den ε α ψ x ≠ 0} = Den ε α ψ ⁻¹' {0}ᶜ := by ext x; simp
  have hnm : NullMeasurableSet {x | Den ε α ψ x ≠ 0} (volume.restrict Ω) := by
    rw [hset]; exact hD.aemeasurable.nullMeasurable (measurableSet_singleton 0).compl
  refine ⟨hnm, ?_, fun x hx => ?_, fun G hG => ?_⟩
  · rw [Set.compl_setOf]; exact ae_iff.1 hne
  · rw [Theta, div_mul_cancel₀ _ hx]
  · filter_upwards [hG, hne] with x h1 h2
    rw [Theta, eq_div_iff h2]; exact h1 h2

end General

/-- **The constant `1/δ` is sharp.** For every `K < 1` there are `δ > 0` and the smooth field
`ψ = x² + δ − ε ∈ H²((−1,1))` with `|D_ε[ψ]| ≥ δ` everywhere (`α = 0`) and
`‖Θ_ε[ψ]‖_{L²} > (K/δ)‖Δψ‖_{L²}`. -/
theorem sharp_constant {ε : ℝ} {K : ℝ} (hK : K < 1) :
    ∃ δ > 0, MemH2 (Ioo (-1 : ℝ) 1) (quad (δ - ε)) ∧
      IsWeakLaplacian (Ioo (-1 : ℝ) 1) (quad (δ - ε)) (fun _ => 2) ∧
      (∀ x : ℝ, δ ≤ ‖Den ε 0 (quad (δ - ε)) x‖) ∧
      ENNReal.ofReal (K / δ) * eLpNorm (fun _ : ℝ => (2 : ℂ)) 2 (volume.restrict (Ioo (-1 : ℝ) 1)) <
        eLpNorm (Theta ε 0 (quad (δ - ε)) (fun _ => 2)) 2 (volume.restrict (Ioo (-1 : ℝ) 1)) := by
  set δ : ℝ := 2 / (1 - K) with hδdef
  have h1K : 0 < 1 - K := by linarith
  have hδ : 0 < δ := div_pos two_pos h1K
  have hKδ : K * (1 + δ) < δ := by
    have : δ * (1 - K) = 2 := by rw [hδdef]; field_simp
    nlinarith
  have hden : ∀ x : ℝ, Den ε 0 (quad (δ - ε)) x = ((x ^ 2 + δ : ℝ) : ℂ) := fun x =>
    den_quad_shift ε δ x
  have hpos : ∀ x : ℝ, 0 < x ^ 2 + δ := fun x => by positivity
  have hΘ : ∀ x : ℝ, Theta ε 0 (quad (δ - ε)) (fun _ => 2) x = -2 / ((x ^ 2 + δ : ℝ) : ℂ) :=
    fun x => by rw [Theta, hden]
  have hΘn : ∀ x : ℝ, ‖Theta ε 0 (quad (δ - ε)) (fun _ => 2) x‖ = 2 / (x ^ 2 + δ) := fun x => by
    rw [hΘ, norm_div, norm_neg, Complex.norm_real, Real.norm_of_nonneg (hpos x).le]
    norm_num
  refine ⟨δ, hδ, memH2_quad _, isWeakLaplacian_quad _, fun x => ?_, ?_⟩
  · rw [hden, Complex.norm_real, Real.norm_of_nonneg (hpos x).le]; nlinarith [sq_nonneg x]
  -- `‖Δψ‖ ≤ (1 + δ)‖Θ‖` pointwise on `(−1, 1)`
  set μ := volume.restrict (Ioo (-1 : ℝ) 1)
  have hcont : Continuous (Theta ε 0 (quad (δ - ε)) (fun _ => 2)) := by
    have : Theta ε 0 (quad (δ - ε)) (fun _ => 2) = fun x : ℝ => -2 / ((x ^ 2 + δ : ℝ) : ℂ) :=
      funext hΘ
    rw [this]
    exact continuous_const.div (Complex.continuous_ofReal.comp ((continuous_pow 2).add
      continuous_const)) fun x => by exact_mod_cast (hpos x).ne'
  have hpt : ∀ᵐ x ∂μ, ‖(fun _ : ℝ => (2 : ℂ)) x‖ ≤
      (1 + δ) * ‖Theta ε 0 (quad (δ - ε)) (fun _ => 2) x‖ := by
    refine ae_restrict_of_forall_mem measurableSet_Ioo fun x hx => ?_
    rw [hΘn, mul_div_assoc', le_div_iff₀ (hpos x)]
    have hx2 : x ^ 2 < 1 := by nlinarith [hx.1, hx.2]
    norm_num
    nlinarith
  have hN := eLpNorm_le_mul_eLpNorm_of_ae_le_mul hpt 2
  set N := eLpNorm (fun _ : ℝ => (2 : ℂ)) 2 μ
  set T := eLpNorm (Theta ε 0 (quad (δ - ε)) (fun _ => 2)) 2 μ
  have hTfin : T ≠ ⊤ := (memLp_Ioo_of_continuous hcont).eLpNorm_ne_top
  have hT0 : T ≠ 0 := by
    intro h
    rw [eLpNorm_eq_zero_iff hcont.aestronglyMeasurable two_ne_zero] at h
    have hμ : μ {x | Theta ε 0 (quad (δ - ε)) (fun _ => 2) x ≠ 0} = 0 := ae_iff.1 h
    have huniv : {x | Theta ε 0 (quad (δ - ε)) (fun _ => 2) x ≠ 0} = univ := by
      ext x; simp only [mem_setOf_eq, mem_univ, iff_true]
      rw [← norm_ne_zero_iff, hΘn]; exact (div_pos two_pos (hpos x)).ne'
    rw [huniv, Measure.restrict_apply_univ, Real.volume_Ioo] at hμ
    norm_num at hμ
  rcases le_or_gt K 0 with hK0 | hK0
  · rw [ENNReal.ofReal_of_nonpos (div_nonpos_of_nonpos_of_nonneg hK0 hδ.le), zero_mul]
    exact pos_iff_ne_zero.2 hT0
  · calc ENNReal.ofReal (K / δ) * N ≤ ENNReal.ofReal (K / δ) * (ENNReal.ofReal (1 + δ) * T) :=
          mul_le_mul_left' hN _
      _ = ENNReal.ofReal (K / δ * (1 + δ)) * T := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (div_nonneg hK0.le hδ.le)]
      _ < T := by
          rw [← ENNReal.ofReal_toReal hTfin, ← ENNReal.ofReal_mul (by positivity)]
          have hTr : 0 < T.toReal := ENNReal.toReal_pos hT0 hTfin
          rw [ENNReal.ofReal_lt_ofReal_iff hTr]
          have : K / δ * (1 + δ) < 1 := by rw [div_mul_eq_mul_div, div_lt_one hδ]; exact hKδ
          nlinarith

end E26Domain
end ReyesMath
