import Mathlib
import MathProofs.E68CriticalGradient
import MathProofs.E68Singular

/-!
# E68′: the corrected estimate under critical gradient integrability

Theorem 3.1 of the manuscript: for `n > 2`, `ψ ∈ H¹(ℝⁿ)` with `∇ψ ∈ Lⁿ(ℝⁿ)`, every center
`x₀` and every radius `R > 0`,
`∫_{B_R(x₀)} |∇ψ|² ≤ ω_n^{1-2/n} R^{n-2} ‖∇ψ‖²_{Lⁿ}`, with `ω_n = |B₁(0)|`.

* `eLpNorm_ball_le`: Hölder's inequality on the ball in extended-real form (this generalizes
  `local_critical_gradient_norm` to any normed codomain). The exponent is
  `1/2 - 1/n`, i.e. the conjugate pair `p = n/2`, `q = n/(n-2)` after squaring.
* `ball_energy_le`: the conversion to the manuscript's real integrals. The `L²(B_R)` and
  `Lⁿ` seminorms are rewritten as `(∫_{B_R} |g|²)^{1/2}` and `(∫ |g|ⁿ)^{1/n}`, the volume is
  `|B_R(x₀)| = ω_n Rⁿ`, and squaring turns `(ω_n Rⁿ)^{1/2-1/n}` into
  `ω_n^{1-2/n} R^{n-2}`.
* `e68_corrected`: Theorem 3.1 for `H¹` fields with `∇ψ ∈ Lⁿ`.
* `e68_apriori`, `e68_admissible`: Corollary 3.2, with constant `ω_n^{1-2/n} K²`.
* `no_apriori_bound_on_H1`: Remark 3.3. No `K` gives `∇ψ ∈ Lⁿ` with
  `‖∇ψ‖_{Lⁿ} ≤ K ‖ψ‖_{H¹}` on all of `H¹(ℝⁿ)`, because that bound would give `E68(n)`.
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric

namespace ReyesMath.E68

variable {n : ℕ}

/-- **Hölder on a ball, extended-real form.** For `n ≥ 2` and any measurable `g`,
`‖g‖_{L²(B_R(x₀))} ≤ ‖g‖_{Lⁿ(ℝⁿ)} |B_R(x₀)|^{1/2 - 1/n}`. -/
theorem eLpNorm_ball_le {F : Type*} [NormedAddCommGroup F] (hn : 2 ≤ n)
    (g : EuclideanSpace ℝ (Fin n) → F) (hg : AEStronglyMeasurable g volume)
    (x₀ : EuclideanSpace ℝ (Fin n)) (R : ℝ) :
    eLpNorm g 2 (volume.restrict (ball x₀ R)) ≤
      eLpNorm g n volume * volume (ball x₀ R) ^ (1 / 2 - 1 / (n : ℝ)) := by
  have hpq : (2 : ENNReal) ≤ (n : ENNReal) := by exact_mod_cast hn
  have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (f := g) (μ := volume.restrict (ball x₀ R)) hpq hg.restrict
  rw [Measure.restrict_apply_univ] at h
  have e : 1 / (2 : ENNReal).toReal - 1 / (n : ENNReal).toReal = 1 / 2 - 1 / (n : ℝ) := by
    simp
  rw [e] at h
  have hmono : eLpNorm g n (volume.restrict (ball x₀ R)) ≤ eLpNorm g n volume :=
    eLpNorm_mono_measure g Measure.restrict_le_self
  exact h.trans (mul_le_mul_right' hmono _)

theorem rpow_sub_two_eq_zpow (R : ℝ) (n : ℕ) : R ^ ((n : ℝ) - 2) = R ^ ((n : ℤ) - 2) := by
  rw [← Real.rpow_intCast]
  push_cast
  rfl

/-- **The real-integral form of E68′.** For `n > 2`, every `g ∈ Lⁿ(ℝⁿ)`, every center and
every `R > 0`, `∫_{B_R(x₀)} |g|² ≤ ω_n^{1-2/n} R^{n-2} (∫ |g|ⁿ)^{2/n}`. -/
theorem ball_energy_le (hn : 2 < n) {F : Type*} [NormedAddCommGroup F]
    {g : EuclideanSpace ℝ (Fin n) → F} (hgn : MemLp g n volume)
    (x₀ : EuclideanSpace ℝ (Fin n)) {R : ℝ} (hR : 0 < R) :
    (∫ x in ball x₀ R, ‖g x‖ ^ 2) ≤
      volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1) ^ (1 - 2 / (n : ℝ)) *
        R ^ ((n : ℤ) - 2) * (∫ x, ‖g x‖ ^ n) ^ (2 / (n : ℝ)) := by
  haveI : IsFiniteMeasure (volume.restrict (ball x₀ R)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hn2 : (2 : ENNReal) ≤ n := by exact_mod_cast hn.le
  have hnR : (2 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hexp : 0 ≤ 1 / 2 - 1 / (n : ℝ) := by
    rw [sub_nonneg]
    exact one_div_le_one_div_of_le two_pos hnR.le
  -- the integrability hypotheses: `g ∈ L²(B_R)` follows from `g ∈ Lⁿ` on the finite ball
  have hg2 : MemLp g 2 (volume.restrict (ball x₀ R)) := (hgn.restrict _).mono_exponent hn2
  set I2 := ∫ x in ball x₀ R, ‖g x‖ ^ 2 with hI2def
  set In := ∫ x, ‖g x‖ ^ n with hIndef
  set ω := volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1) with hωdef
  have hI2 : 0 ≤ I2 := setIntegral_nonneg measurableSet_ball fun x _ => by positivity
  have hIn : 0 ≤ In := integral_nonneg fun x => by positivity
  have hω : 0 ≤ ω := measureReal_nonneg
  have hRn : 0 ≤ R ^ n := pow_nonneg hR.le n
  -- the ball volume `|B_R(x₀)| = Rⁿ ω_n`
  have hV : volume (ball x₀ R) = ENNReal.ofReal (R ^ n * ω) := by
    rw [euclidean_ball_volume_scaling n hn x₀ R hR, ENNReal.ofReal_mul hRn, hωdef,
      measureReal_def, ENNReal.ofReal_toReal measure_ball_lt_top.ne]
  -- the seminorms as real integrals
  have e2 : eLpNorm g 2 (volume.restrict (ball x₀ R)) = ENNReal.ofReal (I2 ^ (2⁻¹ : ℝ)) := by
    rw [hg2.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top]
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    rfl
  have en : eLpNorm g n volume = ENNReal.ofReal (In ^ ((n : ℝ)⁻¹)) := by
    rw [hgn.eLpNorm_eq_integral_rpow_norm (by exact_mod_cast hn0) (ENNReal.natCast_ne_top n)]
    simp only [ENNReal.toReal_natCast, Real.rpow_natCast]
    rfl
  have ev : volume (ball x₀ R) ^ (1 / 2 - 1 / (n : ℝ)) =
      ENNReal.ofReal ((R ^ n * ω) ^ (1 / 2 - 1 / (n : ℝ))) := by
    rw [hV, ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hRn hω) hexp]
  -- the Hölder step, converted to real numbers
  have hH := eLpNorm_ball_le hn.le g hgn.1 x₀ R
  rw [e2, en, ev, ← ENNReal.ofReal_mul (Real.rpow_nonneg hIn _),
    ENNReal.ofReal_le_ofReal_iff
      (mul_nonneg (Real.rpow_nonneg hIn _) (Real.rpow_nonneg (mul_nonneg hRn hω) _))] at hH
  -- squaring: the exponent arithmetic `2(1/2 - 1/n) = 1 - 2/n` and `n(1 - 2/n) = n - 2`
  have hsq := pow_le_pow_left₀ (Real.rpow_nonneg hI2 _) hH 2
  have l1 : (I2 ^ (2⁻¹ : ℝ)) ^ 2 = I2 := by
    rw [← Real.rpow_mul_natCast hI2]
    norm_num
  have r1 : (In ^ ((n : ℝ)⁻¹) * (R ^ n * ω) ^ (1 / 2 - 1 / (n : ℝ))) ^ 2 =
      ω ^ (1 - 2 / (n : ℝ)) * R ^ ((n : ℝ) - 2) * In ^ (2 / (n : ℝ)) := by
    rw [mul_pow, ← Real.rpow_mul_natCast hIn, ← Real.rpow_mul_natCast (mul_nonneg hRn hω),
      Real.mul_rpow hRn hω, ← Real.rpow_natCast R n, ← Real.rpow_mul hR.le]
    have e1 : (n : ℝ)⁻¹ * ((2 : ℕ) : ℝ) = 2 / n := by push_cast; ring
    have e2 : (1 / 2 - 1 / (n : ℝ)) * ((2 : ℕ) : ℝ) = 1 - 2 / n := by push_cast; ring
    have e3 : (n : ℝ) * (1 - 2 / (n : ℝ)) = (n : ℝ) - 2 := by field_simp
    rw [e1, e2, e3]
    ring
  rw [l1, r1, rpow_sub_two_eq_zpow] at hsq
  exact hsq

/-- **Theorem 3.1 (corrected E68′).** Let `n > 2` and `ψ ∈ H¹(ℝⁿ)` with weak gradient
`∇ψ ∈ Lⁿ(ℝⁿ)`. For every `x₀` and `R > 0`,
`∫_{B_R(x₀)} |∇ψ|² ≤ ω_n^{1-2/n} R^{n-2} ‖∇ψ‖²_{Lⁿ}`, where `ω_n = |B₁(0)|` and
`‖∇ψ‖²_{Lⁿ} = (∫ |∇ψ|ⁿ)^{2/n}`. The hypothesis `∇ψ ∈ Lⁿ` is assumed, not derived from
`H¹` (see `no_apriori_bound_on_H1`). -/
theorem e68_corrected (hn : 2 < n) {ψ : EuclideanSpace ℝ (Fin n) → ℂ}
    {g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)} (_h : IsH1 ψ g)
    (hgn : MemLp g n volume) (x₀ : EuclideanSpace ℝ (Fin n)) {R : ℝ} (hR : 0 < R) :
    (∫ x in ball x₀ R, ‖g x‖ ^ 2) ≤
      volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1) ^ (1 - 2 / (n : ℝ)) *
        R ^ ((n : ℤ) - 2) * (∫ x, ‖g x‖ ^ n) ^ (2 / (n : ℝ)) :=
  ball_energy_le hn hgn x₀ hR

/-- **Corollary 3.2, one field.** If moreover `‖∇ψ‖_{Lⁿ} ≤ K ‖ψ‖_{H¹}`, then
`∫_{B_R(x₀)} |∇ψ|² ≤ ω_n^{1-2/n} K² R^{n-2} ‖ψ‖²_{H¹}`. -/
theorem e68_apriori (hn : 2 < n) {ψ : EuclideanSpace ℝ (Fin n) → ℂ}
    {g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)} (h : IsH1 ψ g)
    (hgn : MemLp g n volume) {K : ℝ}
    (hK : (∫ x, ‖g x‖ ^ n) ^ (1 / (n : ℝ)) ≤ K * Real.sqrt (h1sq ψ g))
    (x₀ : EuclideanSpace ℝ (Fin n)) {R : ℝ} (hR : 0 < R) :
    (∫ x in ball x₀ R, ‖g x‖ ^ 2) ≤
      volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1) ^ (1 - 2 / (n : ℝ)) * K ^ 2 *
        R ^ ((n : ℤ) - 2) * h1sq ψ g := by
  have hIn : 0 ≤ ∫ x, ‖g x‖ ^ n := integral_nonneg fun x => by positivity
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hc : 0 ≤ volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1) ^ (1 - 2 / (n : ℝ)) *
      R ^ ((n : ℤ) - 2) :=
    mul_nonneg (Real.rpow_nonneg measureReal_nonneg _) (zpow_nonneg hR.le _)
  have hsq : (∫ x, ‖g x‖ ^ n) ^ (2 / (n : ℝ)) ≤ K ^ 2 * h1sq ψ g := by
    have h2 := pow_le_pow_left₀ (Real.rpow_nonneg hIn _) hK 2
    rw [← Real.rpow_mul_natCast hIn, mul_pow, Real.sq_sqrt (h1sq_nonneg ψ g)] at h2
    convert h2 using 2
    push_cast
    ring
  calc (∫ x in ball x₀ R, ‖g x‖ ^ 2) ≤
      volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1) ^ (1 - 2 / (n : ℝ)) *
        R ^ ((n : ℤ) - 2) * (∫ x, ‖g x‖ ^ n) ^ (2 / (n : ℝ)) := e68_corrected hn h hgn x₀ hR
    _ ≤ volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1) ^ (1 - 2 / (n : ℝ)) *
        R ^ ((n : ℤ) - 2) * (K ^ 2 * h1sq ψ g) := mul_le_mul_of_nonneg_left hsq hc
    _ = _ := by ring

/-- **Corollary 3.2 (admissible class).** Let `n > 2` and let `𝒜` be a class of `H¹` fields
(with their weak gradients) satisfying the independently established a priori bound
`∇ψ ∈ Lⁿ`, `‖∇ψ‖_{Lⁿ} ≤ K ‖ψ‖_{H¹}` with `K` independent of the field. Then every member
satisfies `∫_{B_R(x₀)} |∇ψ|² ≤ ω_n^{1-2/n} K² R^{n-2} ‖ψ‖²_{H¹}` for every `x₀` and `R > 0`. -/
theorem e68_admissible (hn : 2 < n)
    (𝒜 : Set ((EuclideanSpace ℝ (Fin n) → ℂ) ×
      (EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)))) (K : ℝ)
    (hA : ∀ p ∈ 𝒜, IsH1 p.1 p.2 ∧ MemLp p.2 n volume ∧
      (∫ x, ‖p.2 x‖ ^ n) ^ (1 / (n : ℝ)) ≤ K * Real.sqrt (h1sq p.1 p.2)) :
    ∀ p ∈ 𝒜, ∀ (x₀ : EuclideanSpace ℝ (Fin n)) (R : ℝ), 0 < R →
      (∫ x in ball x₀ R, ‖p.2 x‖ ^ 2) ≤
        volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1) ^ (1 - 2 / (n : ℝ)) * K ^ 2 *
          R ^ ((n : ℤ) - 2) * h1sq p.1 p.2 :=
  fun p hp x₀ _ hR => e68_apriori hn (hA p hp).1 (hA p hp).2.1 (hA p hp).2.2 x₀ hR

/-- **Remark 3.3.** The hypothesis of Corollary 3.2 does not follow from `H¹` membership
alone. For `n > 2` there is no constant `K` for which every `H¹` field has `∇ψ ∈ Lⁿ` with
`‖∇ψ‖_{Lⁿ} ≤ K ‖ψ‖_{H¹}`. Such a `K` would make all of `H¹` admissible, and Corollary 3.2
would then give `E68(n)` with `C = ω_n^{1-2/n} K²`, contradicting the classification. -/
theorem no_apriori_bound_on_H1 (hn : 2 < n) :
    ¬ ∃ K : ℝ, ∀ (ψ : EuclideanSpace ℝ (Fin n) → ℂ)
      (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)), IsH1 ψ g →
        MemLp g n volume ∧ (∫ x, ‖g x‖ ^ n) ^ (1 / (n : ℝ)) ≤ K * Real.sqrt (h1sq ψ g) := by
  rintro ⟨K, hK⟩
  apply Singular.not_e68 hn
  refine ⟨volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1) ^ (1 - 2 / (n : ℝ)) * K ^ 2,
    fun ψ g h x₀ R hR => ?_⟩
  exact e68_apriori hn h (hK ψ g h).1 (hK ψ g h).2 x₀ hR

end ReyesMath.E68
