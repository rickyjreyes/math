import MathProofs.FourierShellL2
import MathProofs.RemainingCores

/-!
# E61: genuine whole-space L² linear Swift-Hohenberg evolution

For a≥0, the Fourier growth symbol λ(ξ)=r−a(q(ξ)−k★²)²
is bounded above by r. Consequently exp(t λ(ξ)) is bounded
by exp(t r) for every t≥0. We use the repository's *proved*
Plancherel equivalence to construct the exact L² multiplier
response and establish the physical L² growth upper bound.

The spectral equality and r>0 instability lower bound on a
positive-measure frequency band remain separate obligations.
-/

namespace ReyesMath
namespace E61WholeSpaceGrowth

open MeasureTheory RemainingCores

variable {d : ℕ}
local notation "Rd" => EuclideanSpace ℝ (Fin d)

/-- Real Fourier amplification, cast into the complex multiplier algebra. -/
noncomputable def symbol (r a kStar t : ℝ) (ξ : Rd) : ℂ :=
  (Real.exp (t * linearGrowth r a kStar (Sobolev.qS ξ)) : ℝ)

theorem symbol_measurable (r a kStar t : ℝ) :
    Measurable (symbol (d := d) r a kStar t) := by
  unfold symbol linearGrowth shellSymbol Sobolev.qS
  fun_prop

/-- Every mode's growth is bounded by the center rate exp(r t). -/
theorem symbol_norm_le (r a kStar t : ℝ)
    (ha : 0 ≤ a) (ht : 0 ≤ t) (ξ : Rd) :
    ‖symbol r a kStar t ξ‖ ≤ Real.exp (t * r) := by
  have hg := linearGrowth_le r a kStar (Sobolev.qS ξ) ha
  have hm : t * linearGrowth r a kStar (Sobolev.qS ξ) ≤ t * r :=
    mul_le_mul_of_nonneg_left hg ht
  have he : Real.exp (t * linearGrowth r a kStar (Sobolev.qS ξ)) ≤
      Real.exp (t * r) :=
    Real.exp_le_exp.mpr hm
  simpa [symbol, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)] using he

theorem growing_product_memLp (r a kStar t : ℝ)
    (ha : 0 ≤ a) (ht : 0 ≤ t) (f : Sobolev.L2 d) :
    MemLp (fun ξ : Rd => symbol r a kStar t ξ * f ξ) 2 volume := by
  apply MemLp.of_le_mul (Lp.memLp f)
  · exact (symbol_measurable r a kStar t).aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable f)
  · filter_upwards [] with ξ
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right
      (symbol_norm_le r a kStar t ha ht ξ) (norm_nonneg (f ξ))

/-- Actual linear Swift-Hohenberg L² solution through Plancherel. -/
noncomputable def growthResponse (r a kStar t : ℝ)
    (ha : 0 ≤ a) (ht : 0 ≤ t) (f : Sobolev.L2 d) : Sobolev.L2 d :=
  Sobolev.fourierL2.symm
    ((growing_product_memLp r a kStar t ha ht (Sobolev.fourierL2 f)).toLp
      (fun ξ : Rd =>
        symbol r a kStar t ξ * (Sobolev.fourierL2 f : Rd → ℂ) ξ))

/-- The real-world L² evolution is bounded by exp(r t),
regardless of the dimension or initial L² spectrum. -/
theorem growthResponse_norm_le (r a kStar t : ℝ)
    (ha : 0 ≤ a) (ht : 0 ≤ t) (f : Sobolev.L2 d) :
    ‖growthResponse r a kStar t ha ht f‖ ≤
      Real.exp (t * r) * ‖f‖ := by
  unfold growthResponse
  rw [(Sobolev.fourierL2).symm.norm_map]
  let g := Sobolev.fourierL2 f
  let hmem := growing_product_memLp r a kStar t ha ht g
  have h :
      ‖hmem.toLp
          (fun ξ : Rd => symbol r a kStar t ξ * g ξ)‖ ≤
        Real.exp (t * r) * ‖g‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [MemLp.coeFn_toLp hmem] with ξ hx
    rw [hx, norm_mul]
    exact mul_le_mul_of_nonneg_right
      (symbol_norm_le r a kStar t ha ht ξ) (norm_nonneg (g ξ))
  simpa only [g, hmem, (Sobolev.fourierL2).norm_map] using h

/-- In the nonpositive-growth regime r≤0, the actual L²
Swift-Hohenberg response is contractive at all positive times. -/
theorem nonpositive_growth_contraction (r a kStar t : ℝ)
    (hr : r ≤ 0) (ha : 0 ≤ a) (ht : 0 ≤ t)
    (f : Sobolev.L2 d) :
    ‖growthResponse r a kStar t ha ht f‖ ≤ ‖f‖ := by
  have hb := growthResponse_norm_le r a kStar t ha ht f
  have he : Real.exp (t * r) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (mul_nonpos_of_nonneg_of_nonpos ht hr)
  have hmul := mul_le_mul_of_nonneg_right he (norm_nonneg f)
  nlinarith

end E61WholeSpaceGrowth
end ReyesMath
