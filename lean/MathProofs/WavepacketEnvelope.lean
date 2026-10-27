import MathProofs.SobolevH2
import MathProofs.L2Fourier

/-!
# Continuously adjustable Fourier packet envelope at fixed carrier

The carrier c and an arbitrary positive envelope radius R are independent
parameters. If a given Fourier envelope φ vanishes outside |η|<ρ,
the rescaled and shifted envelope φ(R(ξ-c)) vanishes outside
|ξ-c|<ρ/R. The reverse triangle inequality bounds its radial
bandwidth around |c| by ρ/R.

Separately the exact normalized physical-space dilation on L² preserves
the mass at all positive scales (already established in SobolevH2).
The Schwartz Fourier shift/modulation identities needed to identify
this spectral packet with a specified physical-space modulated
envelope are not proved in this file; they remain a distinct part of
the manuscript's complete wavepacket proposition.
-/

noncomputable section
namespace ReyesMath.WavepacketEnvelope
open Sobolev

private abbrev Rd (d : ℕ) := EuclideanSpace ℝ (Fin (d + 1))

/-- Fourier envelope centered at the carrier c, width proportional to 1/R. -/
def spectrum (d : ℕ) (R : ℝ) (c : Rd d)
    (φ : Rd d → ℂ) (ξ : Rd d) : ℂ :=
  φ (R • (ξ - c))

/-- Exact support containment in the ball B(c,ρ/R). -/
theorem spectrum_zero_outside_ball (d : ℕ)
    (R ρ : ℝ) (hR : 0 < R)
    (c : Rd d) (φ : Rd d → ℂ)
    (hφ : ∀ η : Rd d, ρ ≤ ‖η‖ → φ η = 0)
    (ξ : Rd d) (hfar : ρ / R ≤ ‖ξ - c‖) :
    spectrum d R c φ ξ = 0 := by
  unfold spectrum
  apply hφ
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hR]
  have hm : ρ ≤ ‖ξ - c‖ * R := (div_le_iff₀ hR).mp hfar
  nlinarith

/-- Every nonzero Fourier component lies in a carrier-centered ball
of radius ρ/R. -/
theorem nonzero_spectrum_near_carrier (d : ℕ)
    (R ρ : ℝ) (hR : 0 < R) (c : Rd d) (φ : Rd d → ℂ)
    (hφ : ∀ η : Rd d, ρ ≤ ‖η‖ → φ η = 0)
    (ξ : Rd d) (hξ : spectrum d R c φ ξ ≠ 0) :
    ‖ξ - c‖ < ρ / R := by
  by_contra h
  exact hξ (spectrum_zero_outside_ball d R ρ hR c φ hφ ξ (le_of_not_gt h))

/-- The carrier magnitude remains fixed while the radial bandwidth
shrinks like 1/R. -/
theorem radial_bandwidth (d : ℕ)
    (R ρ k : ℝ) (hR : 0 < R)
    (c : Rd d) (hc : ‖c‖ = k)
    (φ : Rd d → ℂ) (hφ : ∀ η : Rd d, ρ ≤ ‖η‖ → φ η = 0)
    (ξ : Rd d) (hξ : spectrum d R c φ ξ ≠ 0) :
    |‖ξ‖ - k| < ρ / R := by
  rw [← hc]
  exact lt_of_le_of_lt (abs_norm_sub_norm_le ξ c)
    (nonzero_spectrum_near_carrier d R ρ hR c φ hφ ξ hξ)

/-- The physical-space normalized L² envelope can be rescaled through
every positive radius without changing its exact mass. -/
theorem fixed_mass_all_scales (d : ℕ) (f : Sobolev.L2 (d + 1))
    (R : ℝ) (hR : 0 < R) :
    ‖Sobolev.dilL2 (d := d + 1) (inv_pos.mpr hR) f‖ = ‖f‖ :=
  Sobolev.norm_dilL2 (inv_pos.mpr hR) f

end ReyesMath.WavepacketEnvelope
