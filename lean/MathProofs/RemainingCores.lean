import Mathlib

/-!
# Analytic cores for outstanding manuscripts (E58, E61, E57, E62, E26, M2/E17)

These declarations prove exact pointwise/symbolic prerequisites of the cited papers.
They DO NOT prove the spectral/L² operator theorems, the infinite-dimensional
projection statements, the PDE evolution or the Sobolev regularity arguments.
The per-manuscript completion flags must remain false until those theorems
are genuinely formalized and kernel checked.
-/

namespace ReyesMath
namespace RemainingCores

/-- Squared Fourier-shell distance, the symbol of \`(Δ + k★²)²\`
after the Fourier–Laplacian correspondence has been proved separately. -/
def shellSymbol (kStar q : ℝ) : ℝ := (q - kStar ^ 2) ^ 2

theorem shellSymbol_nonneg (kStar q : ℝ) :
    0 ≤ shellSymbol kStar q := by
  unfold shellSymbol
  positivity

theorem shellSymbol_at_shell (kStar : ℝ) :
    shellSymbol kStar (kStar ^ 2) = 0 := by
  simp [shellSymbol]

/-- E61: centered linear Swift–Hohenberg growth rate at squared wavenumber q. -/
def linearGrowth (r a kStar q : ℝ) : ℝ :=
  r - a * shellSymbol kStar q

theorem linearGrowth_le (r a kStar q : ℝ) (ha : 0 ≤ a) :
    linearGrowth r a kStar q ≤ r := by
  unfold linearGrowth
  have hp : 0 ≤ a * shellSymbol kStar q :=
    mul_nonneg ha (shellSymbol_nonneg kStar q)
  linarith

theorem linearGrowth_at_shell (r a kStar : ℝ) :
    linearGrowth r a kStar (kStar ^ 2) = r := by
  simp [linearGrowth, shellSymbol]

/-- The centered *symbol* has threshold zero. This is not yet a
formalization of the unbounded operator's spectral theorem. -/
theorem centered_symbol_threshold (a kStar : ℝ) (ha : 0 ≤ a) :
    (∀ q : ℝ, -a * shellSymbol kStar q ≤ 0) ∧
      -a * shellSymbol kStar (kStar ^ 2) = 0 := by
  constructor
  · intro q
    have h := shellSymbol_nonneg kStar q
    have hm : 0 ≤ a * shellSymbol kStar q := mul_nonneg ha h
    linarith
  · simp [shellSymbol]

/-- E58: Fourier multiplier for a positive fourth-order resolvent. -/
noncomputable def greenMultiplier (r a kStar q : ℝ) : ℝ :=
  1 / (r + a * shellSymbol kStar q)

theorem greenMultiplier_bounds (r a kStar q : ℝ)
    (hr : 0 < r) (ha : 0 ≤ a) :
    0 < greenMultiplier r a kStar q ∧
      greenMultiplier r a kStar q ≤ 1 / r := by
  have hp : 0 ≤ a * shellSymbol kStar q :=
    mul_nonneg ha (shellSymbol_nonneg kStar q)
  have hd : 0 < r + a * shellSymbol kStar q := by linarith
  unfold greenMultiplier
  constructor
  · exact div_pos (by norm_num) hd
  · apply (div_le_div_iff₀ hd hr).2
    nlinarith

theorem greenMultiplier_at_shell (r a kStar : ℝ) (hr : r ≠ 0) :
    greenMultiplier r a kStar (kStar ^ 2) = 1 / r := by
  simp [greenMultiplier, shellSymbol]

/-- E57: exact Fourier-mode damping factor for the linear shell operator. -/
noncomputable def shellDamping (a t kStar q : ℝ) : ℝ :=
  Real.exp (-(a * t * shellSymbol kStar q))

theorem shellDamping_bounds (a t kStar q : ℝ)
    (ha : 0 ≤ a) (ht : 0 ≤ t) :
    0 < shellDamping a t kStar q ∧
      shellDamping a t kStar q ≤ 1 := by
  have hprod : 0 ≤ a * t * shellSymbol kStar q :=
    mul_nonneg (mul_nonneg ha ht) (shellSymbol_nonneg kStar q)
  unfold shellDamping
  constructor
  · exact Real.exp_pos _
  · have hle : -(a * t * shellSymbol kStar q) ≤ (0 : ℝ) :=
      neg_nonpos.mpr hprod
    simpa using (Real.exp_le_exp.mpr hle)

theorem shellDamping_off_shell (a t kStar q gap : ℝ)
    (ha : 0 ≤ a) (ht : 0 ≤ t)
    (hgap : gap ^ 2 ≤ shellSymbol kStar q) :
    shellDamping a t kStar q ≤ Real.exp (-(a * t * gap ^ 2)) := by
  have hat : 0 ≤ a * t := mul_nonneg ha ht
  have hmul := mul_le_mul_of_nonneg_left hgap hat
  unfold shellDamping
  apply Real.exp_le_exp.mpr
  linarith

/-- E62: denominator-safe energy fraction. The Fourier/Parseval
construction of the numerator and denominator remains to be done. -/
noncomputable def energyFraction (selected total : ℝ) : ℝ := selected / total

theorem energyFraction_bounds (selected total : ℝ)
    (hselected : 0 ≤ selected)
    (hpart : selected ≤ total) (htotal : 0 < total) :
    0 ≤ energyFraction selected total ∧
      energyFraction selected total ≤ 1 := by
  unfold energyFraction
  constructor
  · exact div_nonneg hselected (le_of_lt htotal)
  · apply (div_le_iff₀ htotal).2
    linarith

theorem energyFraction_zero_iff (selected total : ℝ)
    (htotal : 0 < total) :
    energyFraction selected total = 0 ↔ selected = 0 := by
  simp [energyFraction, ne_of_gt htotal]

theorem energyFraction_one_iff (selected total : ℝ)
    (htotal : 0 < total) :
    energyFraction selected total = 1 ↔ selected = total := by
  unfold energyFraction
  constructor
  · intro h
    have hh := (div_eq_iff (ne_of_gt htotal)).mp h
    linarith
  · intro h
    rw [h]
    exact div_self (ne_of_gt htotal)

/-- M2/E17: the corrected phase-covariant denominator is strictly
positive for EVERY complex field value, including its zeros. -/
noncomputable def correctedDenominator (ε α : ℝ) (z : ℂ) : ℝ :=
  ‖z‖ ^ 2 + ε ^ 2 * Real.exp (-2 * α * ‖z‖ ^ 2)

theorem correctedDenominator_pos (ε α : ℝ) (z : ℂ) (hε : 0 < ε) :
    0 < correctedDenominator ε α z := by
  unfold correctedDenominator
  have hp : 0 < ε ^ 2 * Real.exp (-2 * α * ‖z‖ ^ 2) :=
    mul_pos (sq_pos_of_pos hε) (Real.exp_pos _)
  nlinarith [sq_nonneg ‖z‖]

/-- E26: pointwise conditional curvature quotient norm estimate.
The a.e. separation and full L² multiplier theorem remain open. -/
theorem conditionalCurvature_pointwise
    (numerator denominator : ℂ) (δ : ℝ)
    (hδ : 0 < δ) (hsep : δ ≤ ‖denominator‖) :
    ‖numerator / denominator‖ ≤ (1 / δ) * ‖numerator‖ := by
  rw [norm_div]
  have hd : 0 < ‖denominator‖ := lt_of_lt_of_le hδ hsep
  have hh : ‖numerator‖ / ‖denominator‖ ≤ ‖numerator‖ / δ := by
    apply (div_le_div_iff₀ hd hδ).2
    have hn := norm_nonneg numerator
    nlinarith
  simpa [div_eq_mul_inv, mul_comm] using hh

end RemainingCores
end ReyesMath
