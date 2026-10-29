import MathProofs.FourierShellL2
import MathProofs.E58Sharpness

/-!
# E58: genuine whole-space L² Fourier Green resolvent

The frequency multiplier is constructed on real Euclidean frequencies.
Using Mathlib's measurable L² classes, the Fourier-domain product is
proved to belong to L², then transported to physical space via the
previously proved Plancherel isometric equivalence.

This establishes the actual existence of the bounded L² response and
its <= 1/r estimate. Exact operator norm, full H⁴ smoothing and the
distributional inverse characterization are additional obligations.
-/

namespace ReyesMath
namespace E58WholeSpaceL2

open MeasureTheory RemainingCores

variable {d : ℕ}
local notation "Rd" => EuclideanSpace ℝ (Fin d)

/-- The exact scalar Green multiplier evaluated at squared Euclidean frequency. -/
noncomputable def symbol (r a kStar : ℝ) (ξ : Rd) : ℂ :=
  (greenMultiplier r a kStar (‖ξ‖ ^ 2) : ℝ)

/-- The physical Green multiplier is a Borel-measurable complex function. -/
theorem symbol_measurable (r a kStar : ℝ) :
    Measurable (symbol (d := d) r a kStar) := by
  unfold symbol greenMultiplier shellSymbol
  fun_prop

/-- The multiplier has the correct sharp pointwise L∞ majorant. -/
theorem symbol_norm_le (r a kStar : ℝ)
    (hr : 0 < r) (ha : 0 ≤ a) (ξ : Rd) :
    ‖symbol r a kStar ξ‖ ≤ 1 / r := by
  have hb := greenMultiplier_bounds r a kStar (‖ξ‖ ^ 2) hr ha
  simpa [symbol, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb.1] using hb.2

/-- Multiplication by the exact Green symbol sends each genuine
Fourier L² class into L², with no artificial bounded-support premise. -/
theorem product_memLp (r a kStar : ℝ)
    (hr : 0 < r) (ha : 0 ≤ a) (f : Sobolev.L2 d) :
    MemLp (fun ξ : Rd => symbol r a kStar ξ * f ξ) 2 volume := by
  apply MemLp.of_le_mul (Lp.memLp f)
  · exact (symbol_measurable r a kStar).aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable f)
  · filter_upwards [] with ξ
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right
      (symbol_norm_le r a kStar hr ha ξ) (norm_nonneg (f ξ))

/-- The whole-space Green response, constructed through the *actual*
Plancherel isometry on L²(ℝᵈ), not on a surrogate finite lattice. -/
noncomputable def greenResponse (r a kStar : ℝ)
    (hr : 0 < r) (ha : 0 ≤ a) (f : Sobolev.L2 d) : Sobolev.L2 d :=
  Sobolev.fourierL2.symm
    ((product_memLp r a kStar hr ha (Sobolev.fourierL2 f)).toLp
      (fun ξ : Rd =>
        symbol r a kStar ξ * (Sobolev.fourierL2 f : Rd → ℂ) ξ))

/-- The actual L² Green response satisfies the global resolvent
upper bound ‖u‖₂ ≤ r⁻¹ ‖f‖₂, for all f ∈ L²(ℝᵈ). -/
theorem greenResponse_norm_le (r a kStar : ℝ)
    (hr : 0 < r) (ha : 0 ≤ a) (f : Sobolev.L2 d) :
    ‖greenResponse r a kStar hr ha f‖ ≤ (1 / r) * ‖f‖ := by
  unfold greenResponse
  rw [(Sobolev.fourierL2).symm.norm_map]
  let g := Sobolev.fourierL2 f
  let hmem := product_memLp r a kStar hr ha g
  have h :
      ‖hmem.toLp (fun ξ : Rd => symbol r a kStar ξ * g ξ)‖ ≤
        (1 / r) * ‖g‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [MemLp.coeFn_toLp hmem] with ξ hx
    rw [hx, norm_mul]
    exact mul_le_mul_of_nonneg_right
      (symbol_norm_le r a kStar hr ha ξ) (norm_nonneg (g ξ))
  simpa only [g, hmem, (Sobolev.fourierL2).norm_map] using h

end E58WholeSpaceL2
end ReyesMath
