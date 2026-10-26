import Mathlib

/-!
# Null spectral support

A null spectral support forces a Fourier representative to vanish almost
everywhere.  This is the measure-theoretic core of the no-L²-shell argument;
the general higher-dimensional sphere-is-null theorem and Plancherel bridge
are separate formalization obligations.
-/

namespace ReyesMath

open MeasureTheory

/-- Any function vanishing off a measure-zero set is zero almost everywhere,
    independently of measurability assumptions on the pointwise representative. -/
theorem zero_ae_of_null_support
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (S : Set α) (hS : μ S = 0)
    (f : α → ℂ) (hf : ∀ x, x ∉ S → f x = 0) :
    f =ᵐ[μ] (fun _ => 0) := by
  have houtside : ∀ᵐ x ∂μ, x ∉ S := by
    apply ae_iff.mpr
    simpa only [Set.mem_setOf_eq, not_not] using hS
  filter_upwards [houtside] with x hx
  exact hf x hx

/-- In one Fourier dimension, the two-point shell {k,-k} cannot
    support a nonzero almost-everywhere Fourier representative. -/
theorem oneDimensional_shell_ae_zero
    (k : ℝ) (f : ℝ → ℂ)
    (hf : ∀ x, x ∉ ({k, -k} : Set ℝ) → f x = 0) :
    f =ᵐ[volume] (fun _ => 0) := by
  apply zero_ae_of_null_support volume {k, -k}
  · simp
  · exact hf

end ReyesMath
