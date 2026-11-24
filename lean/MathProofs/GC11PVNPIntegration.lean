import MathProofs.GC11PVNPBridge
import MathProofs.GC11TorusEquivariance

/-!
# GC11: identify the reused solver with the existing laboratory PDE

The bridge itself can be built independently of the carrier stability
modules. This file identifies the exact original physical nonlinearity
and the laboratory solution predicate used in those modules.
-/
noncomputable section
open Complex MeasureTheory
namespace ReyesMath
namespace GC11PVNPIntegration

open BandPass TorusL2 GC11Coercivity GC11TorusCarrier
  GC11TorusEquivariance GC11PVNPBridge

variable (L : ℝ) [Fact (0 < L)]

theorem physicalNonlin_eq (beta gamma : ℝ) (F : C(Tor L 2, ℂ)) :
    physicalNonlin L beta gamma F = originalNonlinearMap L beta gamma F := by
  ext x
  change PVNP.Torus.fnl beta gamma (F x) =
    (densitySlope beta gamma (‖F x‖ ^ 2) : ℂ) * F x
  rw [PVNP.Torus.fnl_eq]
  unfold densitySlope
  push_cast
  ring

theorem physicalNonlinL2_eq (beta gamma : ℝ) (c : ell2 2) :
    physicalNonlinL2 L beta gamma c =
      fieldL2 L (originalNonlinearMap L beta gamma (BandPass.Phi L (by decide : 2 ≤ 3) c)) := by
  unfold physicalNonlinL2 fieldL2
  rw [physicalNonlin_eq]

theorem lab_solution_fourier {k beta gamma : ℝ} {u : ℝ → ell2 2}
    (hu : IsLabSolution L k beta gamma u) :
    LaboratoryFourierSolution L k beta gamma
      (fun t => BandPass.Phi L (by decide : 2 ≤ 3) (u t)) := by
  intro t n
  have hd := hu.2 t n
  refine ⟨_, ?_, ?_⟩
  · simpa only [fieldL2, toLp_Phi] using hd
  · simp only [fieldL2, toLp_Phi]
    rw [physicalNonlinL2_eq]
    unfold fieldL2 RemainingCores.shellSymbol
    push_cast
    calc
      _ = -(Complex.I * Complex.I) *
        ((((xi2 L n - k ^ 2) ^ 2 : ℝ) : ℂ) * coef (iota L 1 (u t)) n +
          coef (ContinuousMap.toLp (E := ℂ) 2 (μ L 2) ℂ
            (originalNonlinearMap L beta gamma (BandPass.Phi L (by decide : 2 ≤ 3) (u t)))) n) := by ring
      _ = _ := by rw [Complex.I_mul_I]; ring

theorem global_original_fourier_exists {k beta gamma : ℝ}
    (hg : 0 < gamma) (c : ell2 2) :
    ∃ u : ℝ → ell2 2, u 0 = c ∧ Continuous u ∧
      LaboratoryFourierSolution L k beta gamma
        (fun t => BandPass.Phi L (by decide : 2 ≤ 3) (u t)) := by
  obtain ⟨u, h0, hu⟩ := global_lab_exists L (k := k) (beta := beta) hg c
  exact ⟨u, h0, hu.1, lab_solution_fourier L hu⟩

end GC11PVNPIntegration
end ReyesMath
