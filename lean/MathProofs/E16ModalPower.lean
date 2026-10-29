import MathProofs.E16SpectralCore

/-!
# E16: exact linear Fourier modal power amplification and strict selection

The linear finite-band Fourier semigroup multiplies each initial
complex Fourier coefficient by exp(t λ(q)); its power multiplier is
exp(2 t λ(q)). These results formalize the exact spectral gap and
strict relative amplification of the preferred nonzero squared
wavenumber, not merely the static symbol argmax.

Normalized whole-space spectral concentration, actual L² semigroup
construction and the C₀ argmax limit require further analysis.
-/

namespace ReyesMath
namespace E16ModalPower

open E16Core

/-- Exact power amplification factor at Fourier squared-wavenumber q. -/
noncomputable def powerGain (r a b q t : ℝ) : ℝ :=
  Real.exp (2 * t * growth r a b q)

/-- Growth at arbitrary q factors into the preferred-mode power
growth and a strictly dissipative Gaussian-in-detuning penalty. -/
theorem powerGain_factor (r a b q t : ℝ) (hb : b ≠ 0) :
    powerGain r a b q t =
      powerGain r a b (preferredQ a b) t *
        Real.exp (-(2 * b * t * (q - preferredQ a b) ^ 2)) := by
  have hg : growth r a b q =
      growth r a b (preferredQ a b) -
        b * (q - preferredQ a b) ^ 2 := by
    have hgap := growth_gap r a b q hb
    linarith
  unfold powerGain
  rw [hg]
  have heq : 2 * t *
      (growth r a b (preferredQ a b) -
        b * (q - preferredQ a b) ^ 2) =
      2 * t * growth r a b (preferredQ a b) +
        -(2 * b * t * (q - preferredQ a b) ^ 2) := by ring
  rw [heq, Real.exp_add]

/-- At nonnegative time, no Fourier mode gains power relative to the
unique preferred squared frequency. -/
theorem powerGain_le_preferred (r a b q t : ℝ)
    (hb : 0 < b) (ht : 0 ≤ t) :
    powerGain r a b q t ≤ powerGain r a b (preferredQ a b) t := by
  rw [powerGain_factor r a b q t (ne_of_gt hb)]
  have hp : 0 ≤ 2 * b * t * (q - preferredQ a b) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb.le) ht)
      (sq_nonneg _)
  have he : Real.exp (-(2 * b * t * (q - preferredQ a b) ^ 2)) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (neg_nonpos.mpr hp)
  nlinarith [Real.exp_pos (2 * t * growth r a b (preferredQ a b))]

/-- At every strictly positive time, any off-shell mode has
strictly less modal power amplification than the preferred shell. -/
theorem powerGain_strict_off_shell (r a b q t : ℝ)
    (hb : 0 < b) (ht : 0 < t)
    (hq : q ≠ preferredQ a b) :
    powerGain r a b q t < powerGain r a b (preferredQ a b) t := by
  rw [powerGain_factor r a b q t (ne_of_gt hb)]
  have hdiff : 0 < (q - preferredQ a b) ^ 2 :=
    sq_pos_of_ne_zero (sub_ne_zero.mpr hq)
  have hp : 0 < 2 * b * t * (q - preferredQ a b) ^ 2 :=
    mul_pos (mul_pos (mul_pos (by norm_num) hb) ht) hdiff
  have he : Real.exp (-(2 * b * t * (q - preferredQ a b) ^ 2)) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (neg_neg_of_pos hp)
  exact (mul_lt_mul_of_pos_left he (Real.exp_pos _)).trans_eq (mul_one _)

end E16ModalPower
end ReyesMath
