import MathProofs.FourierMultiplierL2
import MathProofs.E58Certification

/-!
# E61: exact whole-space Swift-Hohenberg semigroup operator norm

For d ≥ 1, k⋆ ≥ 0, a ≥ 0, t ≥ 0 and r ∈ ℝ, the unitary
Fourier multiplier with symbol
  exp(t (r - a (|ξ|² - k⋆²)²))
has exact L² operator norm exp(rt).

The upper estimate follows from nonnegative squared shell distance.
The lower estimate is *not* an isolated-shell L² eigenfunction:
the shared continuous-multiplier norm lemma proves that the operator
norm approaches the symbol's value using positive-measure test sets
near a shell point. This avoids treating the zero-measure sphere
as a nonzero physical L² eigenstate.
-/

open MeasureTheory

noncomputable section

namespace ReyesMath
namespace E61ExactNorm

variable {d : ℕ}
local notation "Rd" => EuclideanSpace ℝ (Fin d)

/-- The centered Swift-Hohenberg growth rate in the FU Fourier coordinate. -/
def growth (r a kStar : ℝ) (ξ : Rd) : ℝ :=
  r - a * (‖ξ‖ ^ 2 - kStar ^ 2) ^ 2

/-- Actual whole-space Fourier multiplier symbol of the flow. -/
def symbol (r a kStar t : ℝ) (ξ : Rd) : ℂ :=
  (Real.exp (t * growth r a kStar ξ) : ℂ)

theorem continuous_symbol (r a kStar t : ℝ) :
    Continuous (symbol (d := d) r a kStar t) := by
  unfold symbol growth
  fun_prop

theorem norm_symbol_le (r a kStar t : ℝ)
    (ha : 0 ≤ a) (ht : 0 ≤ t) (ξ : Rd) :
    ‖symbol r a kStar t ξ‖ ≤ Real.exp (t * r) := by
  have hnonneg : 0 ≤ t * (a * (‖ξ‖ ^ 2 - kStar ^ 2) ^ 2) :=
    mul_nonneg ht (mul_nonneg ha (sq_nonneg _))
  have hgrowth : t * growth r a kStar ξ ≤ t * r := by
    unfold growth
    nlinarith
  change ‖((Real.exp (t * growth r a kStar ξ) : ℝ) : ℂ)‖ ≤ _
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr hgrowth

/-- The bounded complex-linear physical L² semigroup operator. -/
def S (r a kStar t : ℝ) (ha : 0 ≤ a) (ht : 0 ≤ t) :
    Sobolev.L2 d →L[ℂ] Sobolev.L2 d :=
  FMult.fmul (symbol r a kStar t)
    (continuous_symbol r a kStar t).aestronglyMeasurable
    (norm_symbol_le r a kStar t ha ht)

/-- Exact pointwise value of the symbol on the preferred shell. -/
theorem shell_value (r a kStar t : ℝ) (ξ : Rd)
    (hξ : ‖ξ‖ = kStar) :
    ‖symbol r a kStar t ξ‖ = Real.exp (t * r) := by
  unfold symbol growth
  rw [hξ, sub_self, zero_pow two_ne_zero, mul_zero, sub_zero, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le]

/-- Exact operator norm in every positive spatial dimension.
No plane wave is asserted to lie in the whole-space L² space. -/
theorem exact_operator_norm (hd : 1 ≤ d)
    (r a kStar t : ℝ) (ha : 0 ≤ a) (ht : 0 ≤ t)
    (hk : 0 ≤ kStar) :
    ‖S (d := d) r a kStar t ha ht‖ = Real.exp (t * r) := by
  obtain ⟨ξ, hξ⟩ := E58Cert.exists_shell (d := d) hd hk
  exact FMult.opNorm_fmul_eq_of_attained
    (continuous_symbol r a kStar t)
    (norm_symbol_le r a kStar t ha ht)
    (shell_value r a kStar t ξ hξ)

/-- Below threshold the exact semigroup norm decays strictly for t>0. -/
theorem below_threshold {r a kStar t : ℝ}
    (hd : 1 ≤ d) (hr : r < 0) (ha : 0 ≤ a)
    (hk : 0 ≤ kStar) (ht : 0 < t) :
    ‖S (d := d) r a kStar t ha ht.le‖ < 1 := by
  rw [exact_operator_norm hd r a kStar t ha ht.le hk, ← Real.exp_zero]
  exact Real.exp_lt_exp.mpr (mul_neg_of_pos_of_neg ht hr)

/-- At threshold the exact whole-space semigroup norm is one. -/
theorem at_threshold (hd : 1 ≤ d) (a kStar t : ℝ)
    (ha : 0 ≤ a) (hk : 0 ≤ kStar) (ht : 0 ≤ t) :
    ‖S (d := d) 0 a kStar t ha ht‖ = 1 := by
  rw [exact_operator_norm hd 0 a kStar t ha ht hk]
  simp

/-- Above threshold the exact operator norm is greater than one at t>0. -/
theorem above_threshold {r a kStar t : ℝ}
    (hd : 1 ≤ d) (hr : 0 < r) (ha : 0 ≤ a)
    (hk : 0 ≤ kStar) (ht : 0 < t) :
    1 < ‖S (d := d) r a kStar t ha ht.le‖ := by
  rw [exact_operator_norm hd r a kStar t ha ht.le hk, ← Real.exp_zero]
  exact Real.exp_lt_exp.mpr (mul_pos ht hr)

end E61ExactNorm
end ReyesMath
