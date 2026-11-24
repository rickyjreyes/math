import MathProofs.GC11Coercivity
import Mathlib

/-!
# Exact classical stationary plane waves

The function is a function of x₁ alone on R²; hence its 2D Laplacian
reduces to the second x₁ derivative. This module verifies the actual
one-coordinate differential equation, rather than only frequency data.
No claim of orbital stability is made by these declarations.
-/
namespace ReyesMath
namespace GC11Coercivity

open RemainingCores

noncomputable def mode (K x : ℝ) : ℂ :=
  Complex.exp (Complex.I * (K : ℂ) * (x : ℂ))

noncomputable def wave (a : ℂ) (K x : ℝ) : ℂ := a * mode K x

theorem hasDerivAt_mode (K x : ℝ) :
    HasDerivAt (mode K) ((Complex.I * (K : ℂ)) * mode K x) x := by
  have h : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x :=
    Complex.ofRealCLM.hasDerivAt
  have h' := (h.const_mul (Complex.I * (K : ℂ))).cexp
  simpa [mode, mul_comm, mul_left_comm, mul_assoc] using h'

theorem deriv_wave (a : ℂ) (K : ℝ) :
    deriv (wave a K) = wave (a * (Complex.I * (K : ℂ))) K := by
  funext x
  have h := (hasDerivAt_mode K x).const_mul a
  simpa [wave, mul_assoc] using h.deriv

noncomputable def shifted (k : ℝ) (u : ℝ → ℂ) : ℝ → ℂ :=
  fun x => deriv (deriv u) x + (k : ℂ) ^ 2 * u x

theorem shifted_wave (k K : ℝ) (a : ℂ) :
    shifted k (wave a K) =
      wave (((k : ℂ) ^ 2 - (K : ℂ) ^ 2) * a) K := by
  funext x
  unfold shifted
  rw [deriv_wave, deriv_wave]
  simp only [wave]
  calc
    _ = (a * (Complex.I * Complex.I) * (K : ℂ) ^ 2 +
        (k : ℂ) ^ 2 * a) * mode K x := by ring
    _ = _ := by rw [Complex.I_mul_I]; ring

theorem norm_mode (K x : ℝ) : ‖mode K x‖ = 1 := by
  simp [mode, Complex.norm_exp, Complex.mul_re]

theorem norm_wave (a : ℂ) (K x : ℝ) : ‖wave a K x‖ = ‖a‖ := by
  rw [wave, norm_mul, norm_mode, mul_one]

noncomputable def staticResidual (k beta gamma : ℝ) (u : ℝ → ℂ) (x : ℝ) : ℂ :=
  shifted k (shifted k u) x +
    (densitySlope beta gamma (‖u x‖ ^ 2) : ℂ) * u x

theorem stationary_wave {k beta gamma K : ℝ} {a : ℂ}
    (h : frequency k beta gamma (‖a‖ ^ 2) (K ^ 2) = 0) (x : ℝ) :
    staticResidual k beta gamma (wave a K) x = 0 := by
  have hf : (k ^ 2 - K ^ 2) ^ 2 + densitySlope beta gamma (‖a‖ ^ 2) = 0 := by
    unfold frequency shellSymbol at h
    unfold densitySlope
    calc
      _ = (K ^ 2 - k ^ 2) ^ 2 - beta * ‖a‖ ^ 2 + gamma * (‖a‖ ^ 2) ^ 2 := by ring
      _ = 0 := h
  have hc : ((k : ℂ) ^ 2 - (K : ℂ) ^ 2) ^ 2 +
      (densitySlope beta gamma (‖a‖ ^ 2) : ℂ) = 0 := by
    exact_mod_cast hf
  rw [staticResidual, shifted_wave, shifted_wave, norm_wave]
  calc
    _ = (((k : ℂ) ^ 2 - (K : ℂ) ^ 2) ^ 2 +
          (densitySlope beta gamma (‖a‖ ^ 2) : ℂ)) * (a * mode K x) := by
      unfold wave
      ring
    _ = 0 := by rw [hc, zero_mul]

theorem stationary_at_density {k beta gamma rho q : ℝ}
    (hrho : 0 ≤ rho) (hq : 0 ≤ q)
    (hf : frequency k beta gamma rho q = 0) (x : ℝ) :
    staticResidual k beta gamma (wave (Real.sqrt rho : ℂ) (Real.sqrt q)) x = 0 := by
  apply stationary_wave
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt hrho, Real.sq_sqrt hq]
  exact hf

theorem explicit_stationary_fields (x : ℝ) :
    staticResidual 1 1 1 (wave (Real.sqrt (4/5) : ℂ) (Real.sqrt (7/5))) x = 0 ∧
    staticResidual 1 1 1 (wave (Real.sqrt (9/10) : ℂ) (Real.sqrt (13/10))) x = 0 := by
  obtain ⟨h₁, h₂, _⟩ := two_static_carriers
  exact ⟨stationary_at_density (by norm_num) (by norm_num) h₁ x,
    stationary_at_density (by norm_num) (by norm_num) h₂ x⟩

end GC11Coercivity
end ReyesMath
