import MathProofs.RegularizedCurvatureL2
import MathProofs.E26SeparatedL2
import MathProofs.E26HistoricalCounterexample

/-!
# E26 manuscript certification bridge (historical additive regularizer)

This is the original *additive* complex denominator
  D_ε[ψ] = ψ + ε exp(-α|ψ|²),
not the corrected phase-covariant M2/E17 denominator.

The existing E26 development proves the full H²/weak-Laplacian
conditional estimate, the two manuscript corollaries, a genuine
smooth one-dimensional H² counterexample when the denominator
separation condition is dropped, and the fact that δ cannot in
general be replaced by ε.

The statements below expose that theorem chain under one
manuscript-specific entrypoint. No unconditional estimate is made.
-/

open MeasureTheory

noncomputable section

namespace ReyesMath
namespace E26Certification

variable {d : ℕ}
local notation "Rd" => EuclideanSpace ℝ (Fin d)

/-- The *actual* E26 theorem on an open Euclidean domain, with a weak
Laplacian and a.e. separation of the historical additive denominator. -/
theorem main_theorem {Ω : Set Rd} (hΩ : IsOpen Ω)
    {ε α δ : ℝ} (hδ : 0 < δ) {ψ F : Rd → ℂ}
    (hψ : E26.MemH2 Ω ψ)
    (hF : E26.IsWeakLaplacian Ω ψ F)
    (hsep : ∀ᵐ x ∂(volume.restrict Ω), δ ≤ ‖E26.Den ε α ψ x‖) :
    MemLp (E26.Theta ε α ψ F) 2 (volume.restrict Ω) ∧
    eLpNorm (E26.Theta ε α ψ F) 2 (volume.restrict Ω) ≤
      ENNReal.ofReal δ⁻¹ * eLpNorm F 2 (volume.restrict Ω) :=
  E26.e26_Rd hΩ hδ hψ hF hsep

/-- For nonnegative real H² fields, the manuscript's explicit
δ_ε is a sufficient denominator separation parameter. -/
theorem nonnegative_real_corollary
    {Ω : Set Rd} (hΩ : IsOpen Ω) {ε α : ℝ}
    (hε : 0 < ε) (hα : 0 ≤ α)
    {u : Rd → ℝ} {F : Rd → ℂ}
    (hu : E26.MemH2 Ω (fun x => (u x : ℂ)))
    (hF : E26.IsWeakLaplacian Ω (fun x => (u x : ℂ)) F)
    (hu0 : ∀ᵐ x ∂(volume.restrict Ω), 0 ≤ u x) :
    MemLp (E26.Theta ε α (fun x => (u x : ℂ)) F) 2 (volume.restrict Ω) ∧
    eLpNorm (E26.Theta ε α (fun x => (u x : ℂ)) F) 2 (volume.restrict Ω) ≤
      ENNReal.ofReal (E26.deltaEps ε α)⁻¹ * eLpNorm F 2 (volume.restrict Ω) :=
  E26.cor_nonneg hΩ hε hα hu hF hu0

/-- For complex fields with |ψ| ≥ m > ε, separation follows with δ=m-ε. -/
theorem away_from_nodes_corollary
    {Ω : Set Rd} (hΩ : IsOpen Ω) {ε α m : ℝ}
    (hε : 0 < ε) (hα : 0 ≤ α) (hm : ε < m)
    {ψ F : Rd → ℂ} (hψ : E26.MemH2 Ω ψ)
    (hF : E26.IsWeakLaplacian Ω ψ F)
    (hψm : ∀ᵐ x ∂(volume.restrict Ω), m ≤ ‖ψ x‖) :
    MemLp (E26.Theta ε α ψ F) 2 (volume.restrict Ω) ∧
    eLpNorm (E26.Theta ε α ψ F) 2 (volume.restrict Ω) ≤
      ENNReal.ofReal (m - ε)⁻¹ * eLpNorm F 2 (volume.restrict Ω) :=
  E26.cor_modulus hΩ hε hα hm hψ hF hψm

/-- The manuscript's smooth counterexample on (-1,1) has
the constant L² Laplacian F=2 but a non-L² curvature quotient. -/
theorem smooth_counterexample (ε : ℝ) :
    E26.MemH2 (Set.Ioo (-1 : ℝ) 1) (E26.quad (-ε)) ∧
    E26.IsWeakLaplacian (Set.Ioo (-1 : ℝ) 1) (E26.quad (-ε)) (fun _ => 2) ∧
    ¬ MemLp (E26.Theta ε 0 (E26.quad (-ε)) (fun _ => 2)) 2
      (volume.restrict (Set.Ioo (-1 : ℝ) 1)) := by
  have h := E26.counterexample ε
  exact ⟨h.1, h.2.1, h.2.2.2.2.1⟩

/-- Even with a positive separation, replacing δ by ε fails for
a smooth H² field. The exact sharpness witness is constructed in E26. -/
theorem separation_is_not_regularization {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, E26.MemH2 (Set.Ioo (-1 : ℝ) 1) (E26.quad c) ∧
      E26.IsWeakLaplacian (Set.Ioo (-1 : ℝ) 1) (E26.quad c) (fun _ => 2) ∧
      (∃ δ > 0, ∀ x : ℝ, δ ≤ ‖E26.Den ε 0 (E26.quad c) x‖) ∧
      ENNReal.ofReal ε⁻¹ *
          eLpNorm (fun _ : ℝ => (2 : ℂ)) 2 (volume.restrict (Set.Ioo (-1 : ℝ) 1)) <
        eLpNorm (E26.Theta ε 0 (E26.quad c) (fun _ => 2)) 2
          (volume.restrict (Set.Ioo (-1 : ℝ) 1)) :=
  E26.delta_not_replaceable hε

end E26Certification
end ReyesMath
