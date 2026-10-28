import Mathlib
import MathProofs.M6BSquareMass
import MathProofs.M6BSmooth

/-!
# M6B: genuine planar product-measure mass via Fubini

The manuscript's L²((0,π)²) mass means a two-dimensional Lebesgue
integral, not merely a formal iterated expression.  This file identifies
that product-measure integral exactly with the existing checked iterated
integral, using integrability of the *actual* smooth fields.
-/

noncomputable section

open MeasureTheory Set

namespace ReyesMath.M6B

/-- The actual open square (0, π) × (0, π). -/
def openSquare : Set (ℝ × ℝ) :=
  Set.Ioo 0 Real.pi ×ˢ Set.Ioo 0 Real.pi

/-- Actual two-dimensional product Lebesgue L² mass. -/
def planarSquareMass (ψ : ℝ → ℝ → ℂ) : ℝ :=
  ∫ p in openSquare, Complex.normSq (ψ p.1 p.2)
    ∂((volume : Measure ℝ).prod volume)

/-- Fubini identifies the whole square's real product-measure integral
with the previously calculated iterated Lebesgue integral whenever the
field has a continuous extension to ℝ². -/
theorem squareMass_eq_planarSquareMass (ψ : ℝ → ℝ → ℂ)
    (hψ : Continuous (fun p : ℝ × ℝ => ψ p.1 p.2)) :
    squareMass ψ = planarSquareMass ψ := by
  have hc : Continuous
      (fun p : ℝ × ℝ => Complex.normSq (ψ p.1 p.2)) := by
    simpa only [Complex.normSq_eq_norm_sq] using hψ.norm.pow 2
  have hbig : IntegrableOn
      (fun p : ℝ × ℝ => Complex.normSq (ψ p.1 p.2))
      (Set.Icc 0 Real.pi ×ˢ Set.Icc 0 Real.pi)
      ((volume : Measure ℝ).prod volume) :=
    hc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hsmall : IntegrableOn
      (fun p : ℝ × ℝ => Complex.normSq (ψ p.1 p.2))
      openSquare ((volume : Measure ℝ).prod volume) :=
    hbig.mono_set (Set.prod_mono Set.Ioo_subset_Icc_self Set.Ioo_subset_Icc_self)
  unfold squareMass planarSquareMass openSquare
  rw [intervalIntegral.integral_of_le (le_of_lt Real.pi_pos)]
  rw [integral_Ioc_eq_integral_Ioo]
  simp_rw [intervalIntegral.integral_of_le (le_of_lt Real.pi_pos),
    integral_Ioc_eq_integral_Ioo]
  exact (MeasureTheory.setIntegral_prod _ hsmall).symm

/-- Exactly the manuscript's squared L² norm, for the actual plus field. -/
theorem squarePlus_planar_mass (c : ℝ) :
    planarSquareMass (squarePlus c) = c ^ 2 * Real.pi ^ 2 / 2 := by
  rw [← squareMass_eq_planarSquareMass (squarePlus c)
    (squarePlus_smooth c).continuous]
  exact squarePlus_mass c

/-- Exactly the manuscript's squared L² norm, for the actual minus field. -/
theorem squareMinus_planar_mass (c : ℝ) :
    planarSquareMass (squareMinus c) = c ^ 2 * Real.pi ^ 2 / 2 := by
  rw [← squareMass_eq_planarSquareMass (squareMinus c)
    (squareMinus_smooth c).continuous]
  exact squareMinus_mass c

theorem squarePlus_planar_prescribed_mass (m : ℝ) (hm : 0 < m) :
    planarSquareMass (squarePlus (amplitude m)) = m := by
  rw [← squareMass_eq_planarSquareMass
    (squarePlus (amplitude m))
    (squarePlus_smooth (amplitude m)).continuous]
  exact squarePlus_prescribed_mass m hm

theorem squareMinus_planar_prescribed_mass (m : ℝ) (hm : 0 < m) :
    planarSquareMass (squareMinus (amplitude m)) = m := by
  rw [← squareMass_eq_planarSquareMass
    (squareMinus (amplitude m))
    (squareMinus_smooth (amplitude m)).continuous]
  exact squareMinus_prescribed_mass m hm

end ReyesMath.M6B
