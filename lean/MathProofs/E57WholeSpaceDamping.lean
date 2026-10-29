import MathProofs.FourierShellL2
import MathProofs.SpectralSharpness

/-!
# M3/E57: actual L²(ℝᵈ) Fourier-shell damping operator

The decay symbol exp(-a*t*(q(ξ)-k★²)²) is the genuine real-frequency
symbol of the fourth-order shell flow in the pinned Fourier convention
q(ξ)=(2π)²|ξ|². The multiplier is measurable, bounded by one for
a,t≥0, defines an L² equivalence class for every input, and
produces an actual physical-space L² contraction under the proved
Plancherel isometry.

Full strong semigroup continuity, generator/domain identification and
the manuscript's time-asymptotic statements remain separate.
-/

namespace ReyesMath
namespace E57WholeSpaceDamping

open MeasureTheory RemainingCores

variable {d : ℕ}
local notation "Rd" => EuclideanSpace ℝ (Fin d)

/-- Actual fourth-order spectral damping factor at a Euclidean frequency. -/
noncomputable def symbol (a t kStar : ℝ) (ξ : Rd) : ℂ :=
  (shellDamping a t kStar (Sobolev.qS ξ) : ℝ)

theorem symbol_measurable (a t kStar : ℝ) :
    Measurable (symbol (d := d) a t kStar) := by
  unfold symbol shellDamping shellSymbol Sobolev.qS
  fun_prop

/-- No physical frequency is amplified by positive-time dissipative dynamics. -/
theorem symbol_norm_le_one (a t kStar : ℝ)
    (ha : 0 ≤ a) (ht : 0 ≤ t) (ξ : Rd) :
    ‖symbol a t kStar ξ‖ ≤ 1 := by
  have hb := shellDamping_bounds a t kStar (Sobolev.qS ξ) ha ht
  simpa [symbol, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb.1] using hb.2

theorem damped_product_memLp (a t kStar : ℝ)
    (ha : 0 ≤ a) (ht : 0 ≤ t) (f : Sobolev.L2 d) :
    MemLp (fun ξ : Rd => symbol a t kStar ξ * f ξ) 2 volume := by
  apply MemLp.of_le_mul (Lp.memLp f)
  · exact (symbol_measurable a t kStar).aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable f)
  · filter_upwards [] with ξ
    rw [norm_mul]
    have h := mul_le_mul_of_nonneg_right
      (symbol_norm_le_one a t kStar ha ht ξ) (norm_nonneg (f ξ))
    simpa using h

/-- Genuine whole-space L² solution at physical time t≥0. -/
noncomputable def dampedResponse (a t kStar : ℝ)
    (ha : 0 ≤ a) (ht : 0 ≤ t) (f : Sobolev.L2 d) : Sobolev.L2 d :=
  Sobolev.fourierL2.symm
    ((damped_product_memLp a t kStar ha ht (Sobolev.fourierL2 f)).toLp
      (fun ξ : Rd =>
        symbol a t kStar ξ * (Sobolev.fourierL2 f : Rd → ℂ) ξ))

/-- The actual fourth-order Fourier-shell flow is an L² contraction
for every spatial dimension, every L² initial condition and all t≥0. -/
theorem dampedResponse_norm_le (a t kStar : ℝ)
    (ha : 0 ≤ a) (ht : 0 ≤ t) (f : Sobolev.L2 d) :
    ‖dampedResponse a t kStar ha ht f‖ ≤ ‖f‖ := by
  unfold dampedResponse
  rw [(Sobolev.fourierL2).symm.norm_map]
  let g := Sobolev.fourierL2 f
  let hmem := damped_product_memLp a t kStar ha ht g
  have h :
      ‖hmem.toLp (fun ξ : Rd => symbol a t kStar ξ * g ξ)‖ ≤
        ‖g‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [MemLp.coeFn_toLp hmem] with ξ hx
    rw [hx, norm_mul]
    have hb := mul_le_mul_of_nonneg_right
      (symbol_norm_le_one a t kStar ha ht ξ) (norm_nonneg (g ξ))
    simpa using hb
  simpa only [g, hmem, (Sobolev.fourierL2).norm_map] using h

end E57WholeSpaceDamping
end ReyesMath
