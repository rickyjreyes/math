import Mathlib

/-!
# GC11: equal nonlinear plane-wave frequencies at distinct spatial scales

For the fourth-order cubic-quintic Schrödinger equation the algebraic
frequency of a constant-amplitude plane wave of squared wavenumber q and
squared amplitude r is

    omega(q,r) = (k²-q)² - beta*r + gamma*r².

This formalization establishes that two distinct *positive* squared
wavenumbers on opposite sides of k² have the same frequency at fixed r.

These algebraic plane-wave data are not H²(R²) localized states.
No nonlinear spectral, modulational, or orbital stability is asserted.
Consequently the results do NOT resolve GC11's stable-pattern selection.
-/

namespace ReyesMath
namespace GC11

/-- Algebraic constant-amplitude plane-wave frequency. -/
def planeWaveFrequency (k beta gamma amplitudeSq waveNumberSq : ℝ) : ℝ :=
  (k ^ 2 - waveNumberSq) ^ 2 -
    beta * amplitudeSq + gamma * amplitudeSq ^ 2

/-- Reflection around q = k² preserves the nonlinear plane-wave frequency. -/
theorem symmetric_modes_same_frequency (k beta gamma amplitudeSq offset : ℝ) :
    planeWaveFrequency k beta gamma amplitudeSq (k ^ 2 - offset) =
      planeWaveFrequency k beta gamma amplitudeSq (k ^ 2 + offset) := by
  unfold planeWaveFrequency
  ring

/-- The reflected squared wavenumbers are positive and distinct whenever
    0 < offset < k². -/
theorem positive_distinct_reflected_modes (k offset : ℝ)
    (hoffset : 0 < offset) (hinside : offset < k ^ 2) :
    0 < k ^ 2 - offset ∧
      0 < k ^ 2 + offset ∧
      k ^ 2 - offset ≠ k ^ 2 + offset := by
  constructor
  · linarith
  constructor
  · nlinarith [sq_nonneg k]
  · intro heq
    linarith

/-- Explicit continuum of equal-frequency pairs of distinct positive
    squared wavenumbers, without asserting their dynamical stability. -/
theorem equal_frequency_distinct_positive_modes
    (k beta gamma amplitudeSq offset : ℝ)
    (hoffset : 0 < offset) (hinside : offset < k ^ 2) :
    0 < k ^ 2 - offset ∧
      0 < k ^ 2 + offset ∧
      k ^ 2 - offset ≠ k ^ 2 + offset ∧
      planeWaveFrequency k beta gamma amplitudeSq (k ^ 2 - offset) =
        planeWaveFrequency k beta gamma amplitudeSq (k ^ 2 + offset) := by
  obtain ⟨hleft, hright, hne⟩ :=
    positive_distinct_reflected_modes k offset hoffset hinside
  exact ⟨hleft, hright, hne,
    symmetric_modes_same_frequency k beta gamma amplitudeSq offset⟩

end GC11
end ReyesMath
