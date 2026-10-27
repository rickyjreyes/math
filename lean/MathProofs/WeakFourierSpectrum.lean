import MathProofs.PolynomialFourier
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Distributional weak Fourier multipliers on full L²

A locally integrable complex-valued Fourier multiplier is a distribution.
If this distribution vanishes against every compactly supported smooth
real test function, the original Fourier multiplier vanishes almost
everywhere.  Thus the canonical L² Fourier transform gives no nonzero
eigenstate for a nonconstant polynomial radial multiplier.

For the Helmholtz symbol X and eigenvalue k² this gives the Fourier-side
distributional Helmholtz exclusion.

The identification of the physical-space distribution P(-Δ)u with
this Fourier-side distribution (including frequency-convention factors)
requires a separate theorem for tempered-distribution Fourier derivatives.
-/

noncomputable section
namespace ReyesMath.WeakFourierSpectrum
open MeasureTheory PolynomialFourier
open scoped Polynomial

private abbrev Rd (d : ℕ) := EuclideanSpace ℝ (Fin (d + 1))

/-- A Fourier-side polynomial multiplier interpreted as an ordinary
locally integrable function, and hence as a distribution. -/
def spectralMultiplier (d : ℕ) (p : ℝ[X])
    (u : Sobolev.L2 (d + 1)) (ξ : Rd d) : ℂ :=
  ((Polynomial.eval (‖ξ‖ ^ 2) p : ℝ) : ℂ) *
    (L2Fourier.equivalence (d + 1) u : Rd d → ℂ) ξ

/-- Weak vanishing as a distribution, expressed using compactly
supported smooth real-valued test functions. -/
def VanishesWeakly (d : ℕ) (p : ℝ[X])
    (u : Sobolev.L2 (d + 1)) : Prop :=
  LocallyIntegrable (spectralMultiplier d p u) volume ∧
    ∀ g : Rd d → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g →
      (∫ ξ, g ξ • spectralMultiplier d p u ξ ∂volume) = 0

/-- Actual weak-distribution-to-a.e. bridge followed by canonical
Plancherel: no nonzero L² eigenstate for a nonzero polynomial symbol. -/
theorem weak_spectral_kernel_zero (d : ℕ) (p : ℝ[X])
    (hp : p ≠ 0) (u : Sobolev.L2 (d + 1))
    (h : VanishesWeakly d p u) :
    u = 0 := by
  obtain ⟨hint, htests⟩ := h
  have hae : ∀ᵐ ξ : Rd d ∂volume, spectralMultiplier d p u ξ = 0 :=
    ae_eq_zero_of_integral_contDiff_smul_eq_zero hint htests
  apply PolynomialFourier.multiplier_kernel_zero d p hp u
  exact hae

/-- Distributional Fourier-side Helmholtz equation at an arbitrary
nonnegative or negative spectral value. -/
theorem weak_helmholtz_zero (d : ℕ) (k : ℝ)
    (u : Sobolev.L2 (d + 1))
    (h : VanishesWeakly d
      ((Polynomial.X : ℝ[X]) - Polynomial.C (k ^ 2)) u) :
    u = 0 := by
  apply weak_spectral_kernel_zero d
    ((Polynomial.X : ℝ[X]) - Polynomial.C (k ^ 2))
    (sub_ne_zero.mpr (Polynomial.X_ne_C (k ^ 2))) u h

/-- Nonconstant polynomial dispersion and spectral shift, in the weak
Fourier-distribution sense. -/
theorem weak_polynomial_eigenstate_zero (d : ℕ)
    (p : ℝ[X]) (eigenvalue : ℝ)
    (hp : p ≠ Polynomial.C eigenvalue)
    (u : Sobolev.L2 (d + 1))
    (h : VanishesWeakly d (p - Polynomial.C eigenvalue) u) :
    u = 0 := by
  exact weak_spectral_kernel_zero d (p - Polynomial.C eigenvalue)
    (sub_ne_zero.mpr hp) u h

end ReyesMath.WeakFourierSpectrum
