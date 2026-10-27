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


/-- The second spatial moment of the normalized physical envelope scales
exactly as λ⁻², with no compactness or Gaussian assumption. -/
theorem second_moment_dilation (d : ℕ) (lam : ℝ) (hlam : 0 < lam)
    (f : Rd d → ℂ) :
    (∫ x : Rd d, ‖x‖ ^ 2 * ‖Sobolev.dilF lam f x‖ ^ 2) =
      (lam ^ 2)⁻¹ * ∫ y : Rd d, ‖y‖ ^ 2 * ‖f y‖ ^ 2 := by
  have hne : lam ^ 2 ≠ 0 := pow_ne_zero _ hlam.ne'
  have hpoint : ∀ x : Rd d,
      ‖x‖ ^ 2 * ‖Sobolev.dilF lam f x‖ ^ 2 =
        (lam ^ (d + 1) / lam ^ 2) *
          (‖lam • x‖ ^ 2 * ‖f (lam • x)‖ ^ 2) := by
    intro x
    rw [Sobolev.norm_dilF_sq hlam, norm_smul,
      Real.norm_eq_abs, abs_of_pos hlam]
    field_simp
    ring
  calc
    (∫ x : Rd d, ‖x‖ ^ 2 * ‖Sobolev.dilF lam f x‖ ^ 2) =
        ∫ x : Rd d, (lam ^ (d + 1) / lam ^ 2) *
          (‖lam • x‖ ^ 2 * ‖f (lam • x)‖ ^ 2) := by
            exact integral_congr_ae (Filter.Eventually.of_forall hpoint)
    _ = (lam ^ (d + 1) / lam ^ 2) *
        ∫ x : Rd d, (‖lam • x‖ ^ 2 * ‖f (lam • x)‖ ^ 2) := by
          rw [integral_const_mul]
    _ = (lam ^ (d + 1) / lam ^ 2) *
        ((lam ^ (d + 1))⁻¹ *
          ∫ y : Rd d, ‖y‖ ^ 2 * ‖f y‖ ^ 2) := by
          rw [Sobolev.integral_comp_dil hlam
            (fun y : Rd d => ‖y‖ ^ 2 * ‖f y‖ ^ 2)]
    _ = (lam ^ 2)⁻¹ *
        ∫ y : Rd d, ‖y‖ ^ 2 * ‖f y‖ ^ 2 := by
          have hpow : lam ^ (d + 1) ≠ 0 := pow_ne_zero _ hlam.ne'
          field_simp
          ring


/-- Arbitrary real carrier phases leave every pointwise complex amplitude
unchanged. In particular this covers exp(i k ω⋅x). -/
theorem modulation_norm (z : ℂ) (phase : ℝ) :
    ‖z * Complex.exp (Complex.I * (phase : ℂ))‖ = ‖z‖ := by
  rw [norm_mul, Complex.norm_exp]
  simp

/-- The specified physically modulated normalized envelope, allowing an
arbitrary real phase function (including a fixed plane-wave carrier). -/
def physicalPacket (d : ℕ) (R : ℝ) (phase : Rd d → ℝ)
    (f : Rd d → ℂ) (x : Rd d) : ℂ :=
  Sobolev.dilF R⁻¹ f x * Complex.exp (Complex.I * (phase x : ℂ))

theorem physical_packet_norm (d : ℕ) (R : ℝ)
    (phase : Rd d → ℝ) (f : Rd d → ℂ) (x : Rd d) :
    ‖physicalPacket d R phase f x‖ = ‖Sobolev.dilF R⁻¹ f x‖ :=
  modulation_norm _ _

/-- Exact mass of the physical wavepacket is independent of its carrier
phase and its envelope radius. -/
theorem physical_packet_mass (d : ℕ) (R : ℝ) (hR : 0 < R)
    (phase : Rd d → ℝ) (f : Rd d → ℂ) :
    (∫ x : Rd d, ‖physicalPacket d R phase f x‖ ^ 2) =
      ∫ y : Rd d, ‖f y‖ ^ 2 := by
  have hlam : 0 < R⁻¹ := inv_pos.mpr hR
  calc
    (∫ x : Rd d, ‖physicalPacket d R phase f x‖ ^ 2) =
      ∫ x : Rd d, ‖Sobolev.dilF R⁻¹ f x‖ ^ 2 := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by
          rw [physical_packet_norm]
    _ = ∫ x : Rd d, (R⁻¹) ^ (d + 1) * ‖f (R⁻¹ • x)‖ ^ 2 := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x =>
          Sobolev.norm_dilF_sq hlam f x
    _ = (R⁻¹) ^ (d + 1) *
        ∫ x : Rd d, ‖f (R⁻¹ • x)‖ ^ 2 := by rw [integral_const_mul]
    _ = (R⁻¹) ^ (d + 1) * ((R⁻¹) ^ (d + 1))⁻¹ *
        ∫ y : Rd d, ‖f y‖ ^ 2 := by
          rw [Sobolev.integral_comp_dil hlam (fun y : Rd d => ‖f y‖ ^ 2)]
          ring
    _ = ∫ y : Rd d, ‖f y‖ ^ 2 := by
          have hn : (R⁻¹) ^ (d + 1) ≠ 0 := pow_ne_zero _ hlam.ne'
          field_simp

/-- Exact second-moment identity for the specified physical modulation:
every carrier phase has the same envelope radius R. -/
theorem physical_packet_second_moment (d : ℕ) (R : ℝ) (hR : 0 < R)
    (phase : Rd d → ℝ) (f : Rd d → ℂ) :
    (∫ x : Rd d, ‖x‖ ^ 2 * ‖physicalPacket d R phase f x‖ ^ 2) =
      R ^ 2 * ∫ y : Rd d, ‖y‖ ^ 2 * ‖f y‖ ^ 2 := by
  have hlam : 0 < R⁻¹ := inv_pos.mpr hR
  calc
    (∫ x : Rd d, ‖x‖ ^ 2 * ‖physicalPacket d R phase f x‖ ^ 2) =
      ∫ x : Rd d, ‖x‖ ^ 2 * ‖Sobolev.dilF R⁻¹ f x‖ ^ 2 := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by
          rw [physical_packet_norm]
    _ = ((R⁻¹) ^ 2)⁻¹ *
      ∫ y : Rd d, ‖y‖ ^ 2 * ‖f y‖ ^ 2 :=
        second_moment_dilation d R⁻¹ hlam f
    _ = R ^ 2 * ∫ y : Rd d, ‖y‖ ^ 2 * ‖f y‖ ^ 2 := by
        simp [inv_pow]

end ReyesMath.WavepacketEnvelope
