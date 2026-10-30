import MathProofs.E69Sobolev
import MathProofs.E17Certification

/-!
# E69: the bounded corrected regularized curvature

For `ε > 0`, `α ∈ ℝ` and `z ∈ ℂ`, `R_ε(z) = z̄ / (|z|² + ε² e^{−2α|z|²})` (`E26.Rε`); for a field
`ψ ∈ H²(ℝⁿ; ℂ)`, `Θ_ε[ψ] = −(Δψ) R_ε(ψ)` (`Theta`), with the Fourier Laplacian `E69.lap`.

**Theorem E69** (`e69`). Let `n ≥ 1` (any `n : ℕ` is allowed), `ε > 0`, `α ∈ ℝ` and `s > n/2 + 2`.
If `ψ ∈ H^s(ℝⁿ; ℂ)`, then `Θ_ε[ψ] ∈ L^∞(ℝⁿ; ℂ)` and
`‖Θ_ε[ψ]‖_∞ ≤ C_{n,s} M_{ε,α} ‖ψ‖_{H^s}`, where `M_{ε,α} = max{1, e^{2α₊}/ε²}` and
`C_{n,s} = (2π)^{-n/2} (∫ (1 + |ξ|²)^{−(s−2)} dξ)^{1/2} ∈ (0, ∞)` depends only on `n` and `s`.
-/

open Filter Topology Complex InnerProductSpace MeasureTheory Set
open scoped ContDiff FourierTransform ENNReal

namespace ReyesMath

namespace E69

open Sobolev E26

variable {n : ℕ}

local notation "Rn" => EuclideanSpace ℝ (Fin n)

/-! ### The regularized reciprocal -/

/-- `M_{ε,α} = max{1, e^{2α₊}/ε²}`, `α₊ = max{α, 0}`. -/
noncomputable def Mea (ε α : ℝ) : ℝ := max 1 (Real.exp (2 * max α 0) / ε ^ 2)

theorem one_le_Mea (ε α : ℝ) : 1 ≤ Mea ε α := le_max_left _ _

theorem Mea_pos (ε α : ℝ) : 0 < Mea ε α := one_pos.trans_le (one_le_Mea ε α)

/-- The denominator `|z|² + ε²e^{−2α|z|²}` is strictly positive, also at `z = 0`. -/
theorem denom_pos {ε : ℝ} (hε : 0 < ε) (α : ℝ) (z : ℂ) :
    0 < ‖z‖ ^ 2 + ε ^ 2 * Real.exp (-2 * α * ‖z‖ ^ 2) :=
  E17Cert.Deps_pos hε α z

/-- `R_ε` is the exact reciprocal `z̄ / D_ε(z)`. -/
theorem Rε_apply (ε α : ℝ) (z : ℂ) :
    Rε ε α z = (starRingEnd ℂ) z / ((‖z‖ ^ 2 + ε ^ 2 * Real.exp (-2 * α * ‖z‖ ^ 2) : ℝ) : ℂ) :=
  rfl

theorem Rε_zero (ε α : ℝ) : Rε ε α 0 = 0 := by simp [Rε]

/-- **The global bound** `|R_ε(z)| ≤ M_{ε,α}` for every `z ∈ ℂ`. -/
theorem norm_Rε_le_Mea {ε : ℝ} (hε : 0 < ε) (α : ℝ) (z : ℂ) : ‖Rε ε α z‖ ≤ Mea ε α :=
  (E17Cert.main_theorem hε α).2.2.2.1 z

/-- The two regimes of the proof: `|R_ε(z)| ≤ e^{2α₊}/ε²` for `|z| ≤ 1` and `|R_ε(z)| ≤ 1/|z| ≤ 1`
for `|z| ≥ 1`. -/
theorem norm_Rε_regimes {ε : ℝ} (hε : 0 < ε) (α : ℝ) (z : ℂ) :
    (‖z‖ ≤ 1 → ‖Rε ε α z‖ ≤ Real.exp (2 * max α 0) / ε ^ 2) ∧
    (1 ≤ ‖z‖ → ‖Rε ε α z‖ ≤ 1 / ‖z‖ ∧ 1 / ‖z‖ ≤ 1) := by
  rw [norm_Rε hε]
  have he : 0 < Real.exp (-2 * α * ‖z‖ ^ 2) := Real.exp_pos _
  have hz := norm_nonneg z
  refine ⟨fun h1 => ?_, fun h1 => ⟨?_, ?_⟩⟩
  · have hlow : Real.exp (-2 * max α 0) ≤ Real.exp (-2 * α * ‖z‖ ^ 2) := by
      refine Real.exp_le_exp.2 ?_
      have hz2 : ‖z‖ ^ 2 ≤ 1 := by nlinarith
      have hm : α * ‖z‖ ^ 2 ≤ max α 0 := by
        rcases le_total 0 α with ha | ha
        · rw [max_eq_left ha]
          nlinarith
        · rw [max_eq_right ha]
          nlinarith [sq_nonneg ‖z‖]
      linarith
    have hd : ε ^ 2 * Real.exp (-2 * max α 0) ≤ ‖z‖ ^ 2 + ε ^ 2 * Real.exp (-2 * α * ‖z‖ ^ 2) := by
      nlinarith [sq_nonneg ‖z‖, sq_nonneg ε]
    have hpos : 0 < ε ^ 2 * Real.exp (-2 * max α 0) := by positivity
    calc ‖z‖ / (‖z‖ ^ 2 + ε ^ 2 * Real.exp (-2 * α * ‖z‖ ^ 2))
        ≤ 1 / (ε ^ 2 * Real.exp (-2 * max α 0)) :=
          div_le_div₀ zero_le_one h1 hpos hd
      _ = Real.exp (2 * max α 0) / ε ^ 2 := by
          rw [show -2 * max α 0 = -(2 * max α 0) by ring, Real.exp_neg]
          field_simp
  · have hz0 : 0 < ‖z‖ := by linarith
    rw [div_le_div_iff₀ (by positivity) hz0]
    nlinarith [mul_pos (pow_pos hε 2) he]
  · rw [div_le_one (by linarith)]
    exact h1

theorem continuous_Rε {ε : ℝ} (hε : 0 < ε) (α : ℝ) : Continuous (Rε ε α) :=
  (E17Cert.main_theorem hε α).2.1.continuous

/-! ### The curvature `Θ_ε[ψ] = −(Δψ) R_ε(ψ)` -/

/-- **`Θ_ε[ψ] = −(Δψ) R_ε(ψ)`**, pointwise on the representatives of `ψ` and `Δψ`. -/
noncomputable def Theta (ε α : ℝ) (ψ : L2 n) (x : Rn) : ℂ :=
  -((lap ψ : Rn → ℂ) x) * Rε ε α ((ψ : Rn → ℂ) x)

/-- `Θ_ε[ψ]` is independent of the representatives, up to a null set. -/
theorem Theta_congr_ae (ε α : ℝ) (ψ : L2 n) {f F : Rn → ℂ} (hf : f =ᵐ[volume] (ψ : Rn → ℂ))
    (hF : F =ᵐ[volume] (lap ψ : Rn → ℂ)) :
    (fun x => -(F x) * Rε ε α (f x)) =ᵐ[volume] Theta ε α ψ := by
  filter_upwards [hf, hF] with x h1 h2
  rw [Theta, h1, h2]

/-- `Θ_ε[ψ]` is a measurable complex field. -/
theorem aestronglyMeasurable_Theta {ε : ℝ} (hε : 0 < ε) (α : ℝ) (ψ : L2 n) :
    AEStronglyMeasurable (Theta ε α ψ) volume :=
  (Lp.aestronglyMeasurable (lap ψ)).neg.mul
    ((continuous_Rε hε α).comp_aestronglyMeasurable (Lp.aestronglyMeasurable ψ))

/-! ### Theorem E69 -/

/-- The constant `C_{n,s} = (2π)^{-n/2} (∫ (1 + |ξ|²)^{−(s−2)} dξ)^{1/2}` of the embedding
`H^{s−2} ↪ L^∞`. It depends only on `n` and `s`. -/
noncomputable def Cns (n : ℕ) (s : ℝ) : ℝ := Cemb n (s - 2)

theorem Cns_eq (n : ℕ) (s : ℝ) :
    Cns n s = (2 * Real.pi) ^ (-((n : ℝ) / 2)) *
      Real.sqrt (∫ ξ : EuclideanSpace ℝ (Fin n), (1 + ‖ξ‖ ^ 2) ^ (-(s - 2))) := rfl

/-- `C_{n,s}` is finite and positive: the defining integral converges for `s > n/2 + 2`. -/
theorem Cns_pos {s : ℝ} (hs : (n : ℝ) / 2 + 2 < s) :
    Integrable (fun ξ : Rn => (1 + ‖ξ‖ ^ 2) ^ (-(s - 2))) ∧ 0 < Cns n s :=
  ⟨integrable_jw_neg (by linarith), Cemb_pos (by linarith)⟩

/-- **`‖Δψ‖_{L^∞} ≤ C_{n,s} ‖Δψ‖_{H^{s−2}} ≤ C_{n,s} ‖ψ‖_{H^s}`** for `s > n/2 + 2`. -/
theorem lap_linf {s : ℝ} (hs : (n : ℝ) / 2 + 2 < s) {ψ : L2 n} (hψ : MemHs s ψ) :
    MemHs (s - 2) (lap ψ) ∧ hsNorm (s - 2) (lap ψ) ≤ hsNorm s ψ ∧
    (∀ᵐ x ∂volume, ‖(lap ψ : Rn → ℂ) x‖ ≤ Cns n s * hsNorm s ψ) ∧
    MemLp (lap ψ : Rn → ℂ) ∞ volume := by
  have hs2 : 2 ≤ s := by
    have : (0 : ℝ) ≤ n / 2 := by positivity
    linarith
  have hL := memHs_lap hψ hs2
  have hle := hsNorm_lap_le hψ hs2
  obtain ⟨-, hbd, hmem, -⟩ := embedding (r := s - 2) (by linarith) hL
  refine ⟨hL, hle, ?_, hmem⟩
  filter_upwards [hbd] with x hx
  exact hx.trans (mul_le_mul_of_nonneg_left hle (Cemb_nonneg _ _))

/-- **Theorem E69 (bounded regularized curvature).** For every `n`, `ε > 0`, `α ∈ ℝ`,
`s > n/2 + 2` and `ψ ∈ H^s(ℝⁿ; ℂ)`: `Θ_ε[ψ] ∈ L^∞(ℝⁿ; ℂ)` and
`‖Θ_ε[ψ]‖_{L^∞} ≤ C_{n,s} M_{ε,α} ‖ψ‖_{H^s}`. -/
theorem e69 {ε : ℝ} (hε : 0 < ε) (α : ℝ) {s : ℝ} (hs : (n : ℝ) / 2 + 2 < s) {ψ : L2 n}
    (hψ : MemHs s ψ) :
    MemLp (Theta ε α ψ) ∞ volume ∧
    (∀ᵐ x ∂volume, ‖Theta ε α ψ x‖ ≤ Cns n s * Mea ε α * hsNorm s ψ) ∧
    eLpNorm (Theta ε α ψ) ∞ volume ≤ ENNReal.ofReal (Cns n s * Mea ε α * hsNorm s ψ) := by
  obtain ⟨-, -, hbd, -⟩ := lap_linf hs hψ
  have hb : ∀ᵐ x ∂volume, ‖Theta ε α ψ x‖ ≤ Cns n s * Mea ε α * hsNorm s ψ := by
    filter_upwards [hbd] with x hx
    rw [Theta, norm_mul, norm_neg]
    calc ‖(lap ψ : Rn → ℂ) x‖ * ‖Rε ε α ((ψ : Rn → ℂ) x)‖
        ≤ (Cns n s * hsNorm s ψ) * Mea ε α :=
          mul_le_mul hx (norm_Rε_le_Mea hε α _) (norm_nonneg _)
            (mul_nonneg (Cemb_nonneg _ _) (hsNorm_nonneg _ _))
      _ = Cns n s * Mea ε α * hsNorm s ψ := by ring
  refine ⟨memLp_top_of_bound (aestronglyMeasurable_Theta hε α ψ) _ hb, hb, ?_⟩
  rw [eLpNorm_exponent_top]
  exact eLpNormEssSup_le_of_ae_bound hb

end E69

end ReyesMath
