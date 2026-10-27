import Mathlib
import MathProofs.UVGrowthBound

/-!
# Exponential ultraviolet amplification dominates every polynomial loss

This establishes a new *nonconditional* analytic consequence of the exact
unstable frequency branch: for each t>0 and fixed derivative loss N,
the multiplier exp(t σ(k²)) grows faster than C(1+k)^N, however large C is.
Thus there can be no polynomially bounded spectral multiplier at t>0.

This is the frequency-multiplier obstruction, NOT yet a representation
of the homogeneous four-jet PDE solution operator on Sobolev spaces.
-/

namespace ReyesMath

open Filter Topology

/-- For positive time and any finite polynomial frequency weight, an
arbitrarily high real wavenumber violates the proposed upper bound
on the exponentially growing UV branch. -/
theorem ultraviolet_exponential_outgrows_polynomial
    (t : ℝ) (ht : 0 < t) (N : ℕ) (C : ℝ) :
    ∃ k : ℝ, 2 ≤ k ∧
      C * (1 + k) ^ N < Real.exp (t * uvGrowth (k ^ 2)) := by
  let p : Polynomial ℝ :=
    Polynomial.C C * (Polynomial.C 1 + Polynomial.C (4 / t) * Polynomial.X) ^ N
  have hlim : Tendsto (fun y : ℝ => p.eval y / Real.exp y)
      atTop (𝓝 0) := Polynomial.tendsto_div_exp_atTop p
  have hevent : ∀ᶠ y : ℝ in atTop, p.eval y / Real.exp y < 1 :=
    hlim.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨y, hy, hsmall⟩ :=
    ((eventually_ge_atTop (t / 2)).and hevent).exists
  have hp : p.eval y = C * (1 + (4 / t) * y) ^ N := by
    simp [p]
  have hP : C * (1 + (4 / t) * y) ^ N < Real.exp y := by
    rw [hp] at hsmall
    simpa only [one_mul] using (div_lt_iff₀ (Real.exp_pos y)).mp hsmall
  let k : ℝ := 4 * y / t
  have hk : 2 ≤ k := by
    dsimp [k]
    apply (le_div_iff₀ ht).2
    linarith
  have hk2 : 4 ≤ k ^ 2 := by nlinarith
  have hkg := uv_growth_linear_in_wavenumber k hk2
  have habs : |k| = k := abs_of_nonneg (by linarith)
  rw [habs] at hkg
  have heq : t * (k / 4) = y := by
    dsimp [k]
    field_simp [ne_of_gt ht] <;> ring
  have hgrowth : y ≤ t * uvGrowth (k ^ 2) := by
    have hm := mul_le_mul_of_nonneg_left hkg ht.le
    rw [heq] at hm
    exact hm
  refine ⟨k, hk, ?_⟩
  calc
    C * (1 + k) ^ N = C * (1 + (4 / t) * y) ^ N := by
      dsimp [k]
      congr 1
      field_simp [ne_of_gt ht] <;> ring
    _ < Real.exp y := hP
    _ ≤ Real.exp (t * uvGrowth (k ^ 2)) :=
      Real.exp_le_exp.mpr hgrowth

/-- No finite-order derivative-loss polynomial can bound the unstable
frequency multiplier at any fixed positive time. -/
theorem ultraviolet_no_finite_polynomial_loss
    (t : ℝ) (ht : 0 < t) (N : ℕ) :
    ¬ ∃ C : ℝ, ∀ k : ℝ, 2 ≤ k →
      Real.exp (t * uvGrowth (k ^ 2)) ≤ C * (1 + k) ^ N := by
  rintro ⟨C, hC⟩
  obtain ⟨k, hk, hbad⟩ :=
    ultraviolet_exponential_outgrows_polynomial t ht N C
  exact (not_lt_of_ge (hC k hk)) hbad

end ReyesMath
