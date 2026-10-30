import MathProofs.BandPassFlow

/-!
# E18: corrected curvature-energy positivity on the actual torus H² model

This is a supporting kernel-checked step toward issue #37, *not* the full E18
Fréchet derivative or Lyapunov theorem. The field is represented by
\`BandPass.ell2 d\`, whose \`iota L 1\` image is Fourier H² on the flat torus.
The normalized measure in the curvature integral is converted to physical
torus volume by the outside factor \`L ^ d\`.
-/

open Filter MeasureTheory
open scoped Real

noncomputable section

namespace ReyesMath.E18FourierEnergy

open ReyesMath.BandPass ReyesMath.TorusL2

variable {L : ℝ} [hL : Fact (0 < L)] {d : ℕ}

/-- The corrected real denominator evaluated at nonnegative density. -/
def D (ε α ρ : ℝ) : ℝ := ρ + ε ^ 2 * Real.exp (-2 * α * ρ)

/-- The actual E18 curvature weight. -/
def F (ε α ρ : ℝ) : ℝ := ρ / (D ε α ρ) ^ 2

/-- Fixed positive regularization ensures the corrected denominator is positive. -/
theorem D_pos {ε ρ : ℝ} (hε : 0 < ε) (hρ : 0 ≤ ρ) (α : ℝ) :
    0 < D ε α ρ := by
  unfold D
  apply add_pos_of_nonneg_of_pos hρ
  exact mul_pos (sq_pos_of_pos hε) (Real.exp_pos _)

/-- The E18 weight is pointwise nonnegative for nonnegative squared density. -/
theorem F_nonneg (ε α : ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    0 ≤ F ε α ρ := by
  unfold F
  exact div_nonneg hρ (sq_nonneg _)

/--
The exact corrected energy on the already formalized H² torus Fourier model.
Its gradient term is the sum of the actual partial-derivative L² norms;
the curvature term weights the square of the actual Fourier Laplacian
by F(|ψ|²). The field representative Φ is continuous for d ≤ 3.
-/
def energy (hd : d ≤ 3) (c₁ c₂ ε α : ℝ) (ψ : ell2 d) : ℝ :=
  L ^ d * (c₁ * (∑ j : Fin d, ‖Dj L j ψ‖ ^ 2) +
    c₂ * ∫ x : Tor L d,
      F ε α (‖Phi L hd ψ x‖ ^ 2) * ‖(DL L ψ : L2 L d) x‖ ^ 2 ∂(μ L d))


/-- For every H² torus field, the curvature density is genuinely integrable
at fixed positive ε. This rules out using Lean's zero value for a divergent
Bochner integral as a false finite-energy certificate. -/
theorem curvature_integrable (hd : d ≤ 3) {ε : ℝ} (hε : 0 < ε)
    (α : ℝ) (ψ : ell2 d) :
    Integrable (fun x : Tor L d =>
      F ε α (‖Phi L hd ψ x‖ ^ 2) *
        ‖(DL L ψ : L2 L d) x‖ ^ 2) (μ L d) := by
  have hρ : Continuous (fun x : Tor L d => ‖Phi L hd ψ x‖ ^ 2) :=
    ((Phi L hd ψ).continuous.norm).pow 2
  have hD : Continuous (fun x : Tor L d =>
      D ε α (‖Phi L hd ψ x‖ ^ 2)) := by
    unfold D
    fun_prop
  have hw : Continuous (fun x : Tor L d =>
      F ε α (‖Phi L hd ψ x‖ ^ 2)) := by
    change Continuous (fun x : Tor L d =>
      (‖Phi L hd ψ x‖ ^ 2) / (D ε α (‖Phi L hd ψ x‖ ^ 2)) ^ 2)
    exact hρ.div (hD.pow 2) (fun x =>
      pow_ne_zero 2 (ne_of_gt (D_pos hε (sq_nonneg _) α)))
  obtain ⟨C, hC⟩ := hw.norm.bounded_above_of_compact_support
    (HasCompactSupport.of_compactSpace _)
  have hC' : ∀ x : Tor L d,
      ‖F ε α (‖Phi L hd ψ x‖ ^ 2)‖ ≤ C := by
    intro x
    simpa using hC x
  exact (BandPass.integrable_norm_sq (DL L ψ)).bdd_mul'
    hw.aestronglyMeasurable (Eventually.of_forall hC')

/-- Nonnegativity is proved for the *actual* Fourier H² energy expression. -/
theorem energy_nonneg (hd : d ≤ 3) (c₁ c₂ ε α : ℝ)
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (ψ : ell2 d) :
    0 ≤ energy (L := L) hd c₁ c₂ ε α ψ := by
  unfold energy
  apply mul_nonneg (pow_nonneg (le_of_lt hL.out) _)
  apply add_nonneg
  · exact mul_nonneg hc₁ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  · apply mul_nonneg hc₂
    apply integral_nonneg
    intro x
    exact mul_nonneg (F_nonneg ε α (sq_nonneg _)) (sq_nonneg _)

end ReyesMath.E18FourierEnergy
