import Mathlib

/-!
# E58: the physical-space Green function in one dimension

Manuscript: `papers/band-selective-green-kernel-bound/main.tex`, §5 (issue #38). Here `d = 1`,
`k⋆ = 0`, `r, a > 0`, `𝓛 = r + a d⁴/dx⁴`, `b = (r/a)^{1/4}`, `c = b/√2`, `t = c|x|`, and

  `g(x) = (2√2 a^{1/4} r^{3/4})⁻¹ e^{-t}(cos t + sin t)`.

The manuscript's transform is `ĝ(k) = ∫ e^{-ikx} g(x) dx` with inverse
`(2π)⁻¹ ∫ e^{ikx} ĝ(k) dk`.

* `E58Green.fourier_g`: `ĝ(k) = 1/(r + ak⁴)` for every real `k`.
* `E58Green.inversion`: `g(x) = (2π)⁻¹ ∫ e^{ikx} (r + ak⁴)⁻¹ dk`, i.e. `g = 𝓕⁻¹G`.
* `E58Green.distrib`: `a g'''' + r g = δ₀` in the sense of distributions.
* `E58Green.ode`: the profile `h(x) = e^{-c|x|}(cos c|x| + sin c|x|)` solves `ah'''' + rh = 0` for
  `x ≠ 0`, is continuous and differentiable at `0` with `h'(0) = 0`, and
  `h'''(0⁺) − h'''(0⁻) = 8c³`; the normalization is `C = (8ac³)⁻¹ = (2√2 a^{1/4} r^{3/4})⁻¹`.
* `E58Green.sign_change`: `g < 0` at `t = π`, although `G(k) = 1/(r + ak⁴) > 0` for all `k`.
* `E58Green.not_pointwise_bound`: the multiplier bound `G ≤ 1/r` gives no pointwise bound
  `g ≤ 1/r`: for `r > 64a`, `g(0) > 1/r`.
-/

open Real Complex MeasureTheory Filter Topology Set
open scoped FourierTransform

noncomputable section

namespace ReyesMath
namespace E58Green

/-- `b = (r/a)^{1/4}`. -/
def bG (r a : ℝ) : ℝ := (r / a) ^ (1 / 4 : ℝ)

/-- `c = b/√2`. -/
def cG (r a : ℝ) : ℝ := bG r a / √2

/-- The normalization `(2√2 a^{1/4} r^{3/4})⁻¹`. -/
def CG (r a : ℝ) : ℝ := 1 / (2 * √2 * a ^ (1 / 4 : ℝ) * r ^ (3 / 4 : ℝ))

/-- The even profile `h(x) = e^{-c|x|}(cos(c|x|) + sin(c|x|))`. -/
def hG (c x : ℝ) : ℝ := Real.exp (-(c * |x|)) * (Real.cos (c * |x|) + Real.sin (c * |x|))

/-- The Green function `g(x) = C e^{-t}(cos t + sin t)`, `t = c|x|`. -/
def gG (r a x : ℝ) : ℝ := CG r a * hG (cG r a) x

variable {r a : ℝ}

theorem bG_pos (hr : 0 < r) (ha : 0 < a) : 0 < bG r a :=
  Real.rpow_pos_of_pos (div_pos hr ha) _

theorem cG_pos (hr : 0 < r) (ha : 0 < a) : 0 < cG r a :=
  div_pos (bG_pos hr ha) (Real.sqrt_pos.2 two_pos)

theorem bG_pow_four (hr : 0 < r) (ha : 0 < a) : bG r a ^ 4 = r / a := by
  rw [bG, ← Real.rpow_natCast, ← Real.rpow_mul (div_pos hr ha).le]; norm_num

theorem sqrt_two_pow_four : (√2 : ℝ) ^ 4 = 4 := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-- `4ac⁴ = r`. -/
theorem four_a_cG_pow_four (hr : 0 < r) (ha : 0 < a) : 4 * a * cG r a ^ 4 = r := by
  have := ha.ne'
  rw [cG, div_pow, bG_pow_four hr ha, sqrt_two_pow_four]
  field_simp

/-- `8ac³ = 2√2 a^{1/4} r^{3/4}`. -/
theorem eight_a_cG_cube (hr : 0 < r) (ha : 0 < a) :
    8 * a * cG r a ^ 3 = 2 * √2 * a ^ (1 / 4 : ℝ) * r ^ (3 / 4 : ℝ) := by
  have hb3 : bG r a ^ 3 = r ^ (3 / 4 : ℝ) / a ^ (3 / 4 : ℝ) := by
    rw [bG, ← Real.rpow_natCast, ← Real.rpow_mul (div_pos hr ha).le,
      Real.div_rpow hr.le ha.le]
    norm_num
  have ha' : a = a ^ (1 / 4 : ℝ) * a ^ (3 / 4 : ℝ) := by
    rw [← Real.rpow_add ha]; norm_num
  have hs : (√2 : ℝ) ^ 3 = 2 * √2 := by
    rw [pow_succ, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hs2 : (√2 : ℝ) * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h14 : 0 < a ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos ha _
  have h34 : 0 < a ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos ha _
  have hr34 : 0 < r ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos hr _
  have hsq : 0 < (√2 : ℝ) := Real.sqrt_pos.2 two_pos
  rw [cG, div_pow, hb3, hs]
  calc 8 * a * (r ^ (3 / 4 : ℝ) / a ^ (3 / 4 : ℝ) / (2 * √2))
      = 8 * (a ^ (1 / 4 : ℝ) * a ^ (3 / 4 : ℝ)) *
          (r ^ (3 / 4 : ℝ) / a ^ (3 / 4 : ℝ) / (2 * √2)) := by rw [← ha']
    _ = 8 * a ^ (1 / 4 : ℝ) * r ^ (3 / 4 : ℝ) / (2 * √2) := by
        field_simp
    _ = 2 * √2 * a ^ (1 / 4 : ℝ) * r ^ (3 / 4 : ℝ) := by
        rw [div_eq_iff (by positivity)]
        linear_combination (-4 * a ^ (1 / 4 : ℝ) * r ^ (3 / 4 : ℝ)) * hs2

/-- The normalization is `C = (8ac³)⁻¹`. -/
theorem CG_eq (hr : 0 < r) (ha : 0 < a) : CG r a = 1 / (8 * a * cG r a ^ 3) := by
  rw [CG, eight_a_cG_cube hr ha]

/-! ### The Fourier transform -/

/-- `(1 − i)/2 · (p − qi)⁻¹ + (1 + i)/2 · (p + qi)⁻¹ = (p + q)/(p² + q²)`. -/
theorem pair (p q : ℝ) (hp : p ≠ 0) :
    (1 - I) / 2 * (1 / ((p : ℂ) - q * I)) + (1 + I) / 2 * (1 / ((p : ℂ) + q * I)) =
      (((p + q) / (p ^ 2 + q ^ 2) : ℝ) : ℂ) := by
  have hD : (p ^ 2 + q ^ 2 : ℝ) ≠ 0 := by positivity
  have hDc : ((p : ℂ) ^ 2 + (q : ℂ) ^ 2) ≠ 0 := by exact_mod_cast hD
  have e1 : ((p : ℂ) - q * I) * (p + q * I) = (p : ℂ) ^ 2 + (q : ℂ) ^ 2 := by
    linear_combination (-(q : ℂ) ^ 2) * Complex.I_sq
  have h1 : (p : ℂ) - q * I ≠ 0 := fun h => hDc (by rw [← e1, h, zero_mul])
  have h2 : (p : ℂ) + q * I ≠ 0 := fun h => hDc (by rw [← e1, h, mul_zero])
  have i1 : 1 / ((p : ℂ) - q * I) = ((p : ℂ) + q * I) / ((p : ℂ) ^ 2 + (q : ℂ) ^ 2) := by
    rw [← e1]; field_simp
  have i2 : 1 / ((p : ℂ) + q * I) = ((p : ℂ) - q * I) / ((p : ℂ) ^ 2 + (q : ℂ) ^ 2) := by
    rw [← e1]; field_simp
  have hnum : (1 - I) * ((p : ℂ) + q * I) + (1 + I) * ((p : ℂ) - q * I) = 2 * ((p : ℂ) + q) := by
    linear_combination (-2 * (q : ℂ)) * Complex.I_sq
  rw [i1, i2]
  push_cast
  calc (1 - I) / 2 * (((p : ℂ) + q * I) / ((p : ℂ) ^ 2 + (q : ℂ) ^ 2)) +
        (1 + I) / 2 * (((p : ℂ) - q * I) / ((p : ℂ) ^ 2 + (q : ℂ) ^ 2))
      = ((1 - I) * ((p : ℂ) + q * I) + (1 + I) * ((p : ℂ) - q * I)) / 2 /
          ((p : ℂ) ^ 2 + (q : ℂ) ^ 2) := by ring
    _ = 2 * ((p : ℂ) + q) / 2 / ((p : ℂ) ^ 2 + (q : ℂ) ^ 2) := by rw [hnum]
    _ = ((p : ℂ) + q) / ((p : ℂ) ^ 2 + (q : ℂ) ^ 2) := by
        rw [mul_div_cancel_left₀ _ two_ne_zero]

/-- On `x ≥ 0` the integrand of `ĥ(k)` is a combination of two decaying exponentials. -/
theorem integrand_nonneg (c k x : ℝ) (hx : 0 ≤ x) :
    cexp (↑(-(k * x)) * I) * (hG c x : ℂ) =
      (1 - I) / 2 * cexp ((-c + (c - k) * I) * x) +
        (1 + I) / 2 * cexp ((-c - (c + k) * I) * x) := by
  rw [hG, abs_of_nonneg hx]
  push_cast
  rw [Complex.cos, Complex.sin]
  have e1 : cexp ((-c + (c - k) * I) * x) =
      cexp (-(k * x) * I) * cexp (-(c * x)) * cexp (c * x * I) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; ring_nf
  have e2 : cexp ((-c - (c + k) * I) * x) =
      cexp (-(k * x) * I) * cexp (-(c * x)) * cexp (-(c * x) * I) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; ring_nf
  rw [e1, e2]
  ring

/-- On `x ≤ 0` the integrand of `ĥ(k)` is a combination of two decaying exponentials. -/
theorem integrand_nonpos (c k x : ℝ) (hx : x ≤ 0) :
    cexp (↑(-(k * x)) * I) * (hG c x : ℂ) =
      (1 + I) / 2 * cexp ((c + (c - k) * I) * x) +
        (1 - I) / 2 * cexp ((c - (c + k) * I) * x) := by
  rw [hG, abs_of_nonpos hx]
  push_cast
  rw [Complex.cos, Complex.sin]
  have e1 : cexp ((c + (c - k) * I) * x) =
      cexp (-(k * x) * I) * cexp (-(c * -x)) * cexp (-(c * -x) * I) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; ring_nf
  have e2 : cexp ((c - (c + k) * I) * x) =
      cexp (-(k * x) * I) * cexp (-(c * -x)) * cexp (c * -x * I) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; ring_nf
  rw [e1, e2]
  ring

theorem integral_Ioi_cexp {w : ℂ} (hw : w.re < 0) :
    ∫ x in Ioi (0 : ℝ), cexp (w * x) = -1 / w := by
  rw [integral_exp_mul_complex_Ioi hw 0]; simp

theorem integral_Iic_cexp {w : ℂ} (hw : 0 < w.re) :
    ∫ x in Iic (0 : ℝ), cexp (w * x) = 1 / w := by
  rw [integral_exp_mul_complex_Iic hw 0]; simp

/-- The four exponents, with their real parts. -/
theorem re_aux (c k : ℝ) :
    (-(c : ℂ) + (c - k) * I).re = -c ∧ (-(c : ℂ) - (c + k) * I).re = -c ∧
      ((c : ℂ) + (c - k) * I).re = c ∧ ((c : ℂ) - (c + k) * I).re = c := by
  simp

theorem integrableOn_Ioi {c : ℝ} (hc : 0 < c) (k : ℝ) :
    IntegrableOn (fun x : ℝ => cexp (↑(-(k * x)) * I) * (hG c x : ℂ)) (Ioi 0) := by
  obtain ⟨h1, h2, -, -⟩ := re_aux c k
  refine IntegrableOn.congr_fun
    (((integrableOn_exp_mul_complex_Ioi (by rw [h1]; linarith) 0).const_mul ((1 - I) / 2)).add
      ((integrableOn_exp_mul_complex_Ioi (by rw [h2]; linarith) 0).const_mul ((1 + I) / 2)))
    (fun x hx => (integrand_nonneg c k x (le_of_lt hx)).symm) measurableSet_Ioi

theorem integrableOn_Iic {c : ℝ} (hc : 0 < c) (k : ℝ) :
    IntegrableOn (fun x : ℝ => cexp (↑(-(k * x)) * I) * (hG c x : ℂ)) (Iic 0) := by
  obtain ⟨-, -, h3, h4⟩ := re_aux c k
  refine IntegrableOn.congr_fun
    (((integrableOn_exp_mul_complex_Iic (by rw [h3]; linarith) 0).const_mul ((1 + I) / 2)).add
      ((integrableOn_exp_mul_complex_Iic (by rw [h4]; linarith) 0).const_mul ((1 - I) / 2)))
    (fun x hx => (integrand_nonpos c k x hx).symm) measurableSet_Iic

theorem integrable_integrand {c : ℝ} (hc : 0 < c) (k : ℝ) :
    Integrable (fun x : ℝ => cexp (↑(-(k * x)) * I) * (hG c x : ℂ)) := by
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
  exact (integrableOn_Iic hc k).union (integrableOn_Ioi hc k)

/-- `ĥ(k) = (2c − k)/(c² + (c − k)²) + (2c + k)/(c² + (c + k)²)`. -/
theorem fourier_hG {c : ℝ} (hc : 0 < c) (k : ℝ) :
    ∫ x : ℝ, cexp (↑(-(k * x)) * I) * (hG c x : ℂ) =
      (((2 * c - k) / (c ^ 2 + (c - k) ^ 2) + (2 * c + k) / (c ^ 2 + (c + k) ^ 2) : ℝ) : ℂ) := by
  obtain ⟨h1, h2, h3, h4⟩ := re_aux c k
  have hw₁ : (-(c : ℂ) + (c - k) * I).re < 0 := by rw [h1]; linarith
  have hw₂ : (-(c : ℂ) - (c + k) * I).re < 0 := by rw [h2]; linarith
  have hv₁ : 0 < ((c : ℂ) + (c - k) * I).re := by rw [h3]; linarith
  have hv₂ : 0 < ((c : ℂ) - (c + k) * I).re := by rw [h4]; linarith
  have Jp : ∫ x in Ioi (0 : ℝ), cexp (↑(-(k * x)) * I) * (hG c x : ℂ) =
      (1 - I) / 2 * (-1 / (-(c : ℂ) + (c - k) * I)) +
        (1 + I) / 2 * (-1 / (-(c : ℂ) - (c + k) * I)) := by
    rw [setIntegral_congr_fun measurableSet_Ioi fun x hx => integrand_nonneg c k x (le_of_lt hx),
      integral_add ((integrableOn_exp_mul_complex_Ioi hw₁ 0).const_mul _)
        ((integrableOn_exp_mul_complex_Ioi hw₂ 0).const_mul _),
      integral_const_mul, integral_const_mul, integral_Ioi_cexp hw₁, integral_Ioi_cexp hw₂]
  have Jm : ∫ x in Iic (0 : ℝ), cexp (↑(-(k * x)) * I) * (hG c x : ℂ) =
      (1 + I) / 2 * (1 / ((c : ℂ) + (c - k) * I)) +
        (1 - I) / 2 * (1 / ((c : ℂ) - (c + k) * I)) := by
    rw [setIntegral_congr_fun measurableSet_Iic fun x hx => integrand_nonpos c k x hx,
      integral_add ((integrableOn_exp_mul_complex_Iic hv₁ 0).const_mul _)
        ((integrableOn_exp_mul_complex_Iic hv₂ 0).const_mul _),
      integral_const_mul, integral_const_mul, integral_Iic_cexp hv₁, integral_Iic_cexp hv₂]
  have hsplit : ∫ x : ℝ, cexp (↑(-(k * x)) * I) * (hG c x : ℂ) =
      (∫ x in Iic (0 : ℝ), cexp (↑(-(k * x)) * I) * (hG c x : ℂ)) +
        ∫ x in Ioi (0 : ℝ), cexp (↑(-(k * x)) * I) * (hG c x : ℂ) := by
    rw [← setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi (integrableOn_Iic hc k)
      (integrableOn_Ioi hc k), Iic_union_Ioi, Measure.restrict_univ]
  have P1 := pair c (c - k) hc.ne'
  have P2 := pair c (c + k) hc.ne'
  have n1 : -1 / (-(c : ℂ) + (c - k) * I) = 1 / ((c : ℂ) - ((c - k : ℝ) : ℂ) * I) := by
    rw [show -(c : ℂ) + (c - k) * I = -((c : ℂ) - ((c - k : ℝ) : ℂ) * I) by push_cast; ring,
      neg_div_neg_eq]
  have n2 : -1 / (-(c : ℂ) - (c + k) * I) = 1 / ((c : ℂ) + ((c + k : ℝ) : ℂ) * I) := by
    rw [show -(c : ℂ) - (c + k) * I = -((c : ℂ) + ((c + k : ℝ) : ℂ) * I) by push_cast; ring,
      neg_div_neg_eq]
  have n3 : 1 / ((c : ℂ) + (c - k) * I) = 1 / ((c : ℂ) + ((c - k : ℝ) : ℂ) * I) := by push_cast; rfl
  have n4 : 1 / ((c : ℂ) - (c + k) * I) = 1 / ((c : ℂ) - ((c + k : ℝ) : ℂ) * I) := by push_cast; rfl
  rw [hsplit, Jp, Jm, n1, n2, n3, n4]
  calc (1 + I) / 2 * (1 / ((c : ℂ) + ((c - k : ℝ) : ℂ) * I)) +
        (1 - I) / 2 * (1 / ((c : ℂ) - ((c + k : ℝ) : ℂ) * I)) +
        ((1 - I) / 2 * (1 / ((c : ℂ) - ((c - k : ℝ) : ℂ) * I)) +
          (1 + I) / 2 * (1 / ((c : ℂ) + ((c + k : ℝ) : ℂ) * I)))
      = ((1 - I) / 2 * (1 / ((c : ℂ) - ((c - k : ℝ) : ℂ) * I)) +
          (1 + I) / 2 * (1 / ((c : ℂ) + ((c - k : ℝ) : ℂ) * I))) +
        ((1 - I) / 2 * (1 / ((c : ℂ) - ((c + k : ℝ) : ℂ) * I)) +
          (1 + I) / 2 * (1 / ((c : ℂ) + ((c + k : ℝ) : ℂ) * I))) := by ring
    _ = _ := by
        rw [P1, P2]; push_cast; ring

/-- `(2c − k)/(c² + (c − k)²) + (2c + k)/(c² + (c + k)²) = 8c³/(k⁴ + 4c⁴)`. -/
theorem pair_sum {c : ℝ} (hc : 0 < c) (k : ℝ) :
    (2 * c - k) / (c ^ 2 + (c - k) ^ 2) + (2 * c + k) / (c ^ 2 + (c + k) ^ 2) =
      8 * c ^ 3 / (k ^ 4 + 4 * c ^ 4) := by
  have h1 : 0 < c ^ 2 + (c - k) ^ 2 := by positivity
  have h2 : 0 < c ^ 2 + (c + k) ^ 2 := by positivity
  have h3 : 0 < k ^ 4 + 4 * c ^ 4 := by positivity
  rw [div_add_div _ _ h1.ne' h2.ne', div_eq_div_iff (mul_pos h1 h2).ne' h3.ne']
  ring

/-- **The Fourier transform of the Green function**: `ĝ(k) = 1/(r + ak⁴)`. -/
theorem fourier_g (hr : 0 < r) (ha : 0 < a) (k : ℝ) :
    ∫ x : ℝ, cexp (↑(-(k * x)) * I) * (gG r a x : ℂ) = ((1 / (r + a * k ^ 4) : ℝ) : ℂ) := by
  have hc := cG_pos hr ha
  have h4 := four_a_cG_pow_four hr ha
  simp_rw [gG, Complex.ofReal_mul, mul_left_comm _ ((CG r a : ℝ) : ℂ)]
  rw [integral_const_mul, fourier_hG hc, pair_sum hc, CG_eq hr ha, ← Complex.ofReal_mul]
  congr 1
  rw [show r + a * k ^ 4 = a * (k ^ 4 + 4 * cG r a ^ 4) by linear_combination -h4]
  have : 0 < k ^ 4 + 4 * cG r a ^ 4 := by positivity
  have := ha.ne'
  have := hc.ne'
  field_simp

/-! ### Fourier inversion: `g = 𝓕⁻¹G` -/

theorem continuous_hG (c : ℝ) : Continuous (hG c) := by unfold hG; fun_prop

theorem continuous_gC : Continuous fun x : ℝ => (gG r a x : ℂ) :=
  Complex.continuous_ofReal.comp (continuous_const.mul (continuous_hG _))

theorem integrable_gC (hr : 0 < r) (ha : 0 < a) : Integrable fun x : ℝ => (gG r a x : ℂ) := by
  refine ((integrable_integrand (cG_pos hr ha) 0).const_mul (CG r a : ℂ)).congr
    (Eventually.of_forall fun x => ?_)
  simp [gG]

/-- In Mathlib's normalization `𝓕 f(w) = ∫ e^{-2πixw} f(x) dx`: `𝓕 g(w) = ĝ(2πw)`. -/
theorem fourierIntegral_gC (hr : 0 < r) (ha : 0 < a) (w : ℝ) :
    𝓕 (fun x : ℝ => (gG r a x : ℂ)) w = ((1 / (r + a * (2 * π * w) ^ 4) : ℝ) : ℂ) := by
  rw [Real.fourierIntegral_real_eq_integral_exp_smul, ← fourier_g hr ha (2 * π * w)]
  have e : ∀ v : ℝ, (-2 * π * v * w : ℝ) = -(2 * π * w * v) := fun v => by ring
  simp_rw [e, smul_eq_mul]

theorem den_pos (hr : 0 < r) (ha : 0 < a) (w : ℝ) : 0 < r + a * (2 * π * w) ^ 4 := by positivity

theorem integrable_G (hr : 0 < r) (ha : 0 < a) :
    Integrable fun w : ℝ => ((1 / (r + a * (2 * π * w) ^ 4) : ℝ) : ℂ) := by
  have hA : 0 < a * (2 * π) ^ 4 := by positivity
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul (2 / r + 1 / (a * (2 * π) ^ 4)))
    (Complex.continuous_ofReal.comp (continuous_const.div (by fun_prop) fun w =>
      (den_pos hr ha w).ne')).aestronglyMeasurable (Eventually.of_forall fun w => ?_)
  rw [Complex.norm_real, Real.norm_of_nonneg (one_div_pos.2 (den_pos hr ha w)).le,
    ← div_eq_mul_inv, div_le_div_iff₀ (den_pos hr ha w) (by positivity), one_mul]
  have e : (2 / r + 1 / (a * (2 * π) ^ 4)) * (r + a * (2 * π * w) ^ 4) =
      2 + r / (a * (2 * π) ^ 4) + (2 * (a * (2 * π) ^ 4) / r + 1) * w ^ 4 := by
    field_simp
  rw [e]
  have h1 : 0 ≤ r / (a * (2 * π) ^ 4) := by positivity
  have h2 : 0 ≤ 2 * (a * (2 * π) ^ 4) / r * w ^ 4 := by positivity
  nlinarith [sq_nonneg (w ^ 2 - 1)]

/-- **Fourier inversion**: `g(x) = (2π)⁻¹ ∫ e^{ikx} (r + ak⁴)⁻¹ dk`, i.e. `g = 𝓕⁻¹G`. -/
theorem inversion (hr : 0 < r) (ha : 0 < a) (x : ℝ) :
    (gG r a x : ℂ) = (((2 * π)⁻¹ : ℝ) : ℂ) *
      ∫ k : ℝ, cexp (↑(k * x) * I) * ((1 / (r + a * k ^ 4) : ℝ) : ℂ) := by
  have hinv := Continuous.fourier_inversion continuous_gC (integrable_gC hr ha)
    ((integrable_G hr ha).congr (Eventually.of_forall fun w => (fourierIntegral_gC hr ha w).symm))
  have h1 : (gG r a x : ℂ) = 𝓕⁻ (𝓕 fun x : ℝ => (gG r a x : ℂ)) x := by rw [hinv]
  rw [h1, fourierIntegralInv_eq_fourierIntegral_neg, Real.fourierIntegral_real_eq_integral_exp_smul]
  simp_rw [fourierIntegral_gC hr ha, smul_eq_mul]
  have e : ∀ w : ℝ, (-2 * π * w * -x : ℝ) = 2 * π * w * x := fun w => by ring
  simp_rw [e]
  have hsub := Measure.integral_comp_mul_left
    (fun k : ℝ => cexp (↑(k * x) * I) * ((1 / (r + a * k ^ 4) : ℝ) : ℂ)) (2 * π)
  simp only at hsub
  rw [hsub, abs_of_pos (inv_pos.2 (by positivity : (0 : ℝ) < 2 * π)), Complex.real_smul]

/-! ### The distributional equation `a g'''' + r g = δ₀` -/

/-- `g = 𝓕G̃` with `G̃(w) = G(2πw)` (the symbol is even, so `𝓕⁻¹G̃ = 𝓕G̃`). -/
theorem gC_eq_fourier (hr : 0 < r) (ha : 0 < a) :
    (fun x : ℝ => (gG r a x : ℂ)) =
      𝓕 (fun w : ℝ => ((1 / (r + a * (2 * π * w) ^ 4) : ℝ) : ℂ)) := by
  have hF : 𝓕 (fun x : ℝ => (gG r a x : ℂ)) =
      fun w : ℝ => ((1 / (r + a * (2 * π * w) ^ 4) : ℝ) : ℂ) :=
    funext (fourierIntegral_gC hr ha)
  have hinv := Continuous.fourier_inversion continuous_gC (integrable_gC hr ha)
    (by rw [hF]; exact integrable_G hr ha)
  rw [hF, fourierIntegralInv_eq_fourierIntegral_comp_neg] at hinv
  rw [← hinv]
  congr 1
  funext w
  ring_nf

theorem iteratedDeriv_schwartz (φ : SchwartzMap ℝ ℂ) (n : ℕ) :
    iteratedDeriv n (φ : ℝ → ℂ) = ⇑((SchwartzMap.derivCLM ℂ)^[n] φ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih, Function.iterate_succ_apply']
    funext x
    rfl

/-- **`a g'''' + r g = δ₀` in the sense of distributions**: for every Schwartz test function
`φ`, `∫ g (aφ'''' + rφ) = φ(0)`. -/
theorem distrib (hr : 0 < r) (ha : 0 < a) (φ : SchwartzMap ℝ ℂ) :
    ∫ x : ℝ, (gG r a x : ℂ) * ((a : ℂ) * iteratedDeriv 4 φ x + (r : ℂ) * φ x) = φ 0 := by
  set φ4 : SchwartzMap ℝ ℂ := (SchwartzMap.derivCLM ℂ)^[4] φ with hφ4
  have h4 : iteratedDeriv 4 (φ : ℝ → ℂ) = ⇑φ4 := iteratedDeriv_schwartz φ 4
  set ψ : SchwartzMap ℝ ℂ := (a : ℂ) • φ4 + (r : ℂ) • φ with hψ
  have hψx : ∀ x, (a : ℂ) * iteratedDeriv 4 φ x + (r : ℂ) * φ x = ψ x := fun x => by
    rw [h4]; simp [hψ]
  simp_rw [hψx]
  -- the Fourier transform of `ψ`
  have hD : ∀ n : ℕ, n ≤ (⊤ : ℕ∞) → Integrable (iteratedDeriv n (φ : ℝ → ℂ)) := fun n _ => by
    rw [iteratedDeriv_schwartz]; exact SchwartzMap.integrable _
  have hF4 : 𝓕 (φ4 : ℝ → ℂ) = fun w : ℝ => (2 * π * I * w) ^ 4 • 𝓕 (φ : ℝ → ℂ) w := by
    rw [← h4]; exact Real.fourierIntegral_iteratedDeriv (φ.smooth ⊤) hD le_top
  have hFψ : ∀ w : ℝ, 𝓕 (ψ : ℝ → ℂ) w =
      ((a : ℂ) * (2 * π * w) ^ 4 + r) * 𝓕 (φ : ℝ → ℂ) w := fun w => by
    have : 𝓕 (ψ : ℝ → ℂ) = ⇑(SchwartzMap.fourierTransformCLM ℂ ψ) := rfl
    rw [this, hψ, map_add, map_smul, map_smul, SchwartzMap.add_apply, SchwartzMap.smul_apply,
      SchwartzMap.smul_apply, SchwartzMap.fourierTransformCLM_apply,
      SchwartzMap.fourierTransformCLM_apply]
    simp only [hF4, smul_eq_mul]
    have hI4 : (2 * π * I * w) ^ 4 = ((2 * π * w : ℝ) : ℂ) ^ 4 := by
      push_cast
      rw [mul_pow, mul_pow, mul_pow, mul_pow, Complex.I_pow_four]
      ring
    rw [hI4]; push_cast; ring
  -- the multiplication formula
  have hflip : (innerₗ ℝ : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ).flip = innerₗ ℝ := by
    ext; simp
  have hmul := VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℝ)
    Real.continuous_fourierChar continuous_inner (integrable_G hr ha) (ψ.integrable (μ := volume))
  rw [hflip] at hmul
  change ∫ ξ, 𝓕 (fun w : ℝ => ((1 / (r + a * (2 * π * w) ^ 4) : ℝ) : ℂ)) ξ • ψ ξ =
    ∫ x, ((1 / (r + a * (2 * π * x) ^ 4) : ℝ) : ℂ) • 𝓕 (ψ : ℝ → ℂ) x at hmul
  have hg : ∀ x : ℝ, (gG r a x : ℂ) =
      𝓕 (fun w : ℝ => ((1 / (r + a * (2 * π * w) ^ 4) : ℝ) : ℂ)) x :=
    fun x => congrFun (gC_eq_fourier hr ha) x
  simp only [smul_eq_mul] at hmul
  simp_rw [hg]
  rw [hmul]
  -- `G̃ · 𝓕ψ = 𝓕φ`
  have hcancel : ∀ x : ℝ, ((1 / (r + a * (2 * π * x) ^ 4) : ℝ) : ℂ) * 𝓕 (ψ : ℝ → ℂ) x =
      𝓕 (φ : ℝ → ℂ) x := fun x => by
    rw [hFψ, ← mul_assoc]
    have hne : ((r + a * (2 * π * x) ^ 4 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (den_pos hr ha x).ne'
    have : ((1 / (r + a * (2 * π * x) ^ 4) : ℝ) : ℂ) * ((a : ℂ) * (2 * π * x) ^ 4 + r) = 1 := by
      rw [show ((a : ℂ) * (2 * π * x) ^ 4 + r) = ((r + a * (2 * π * x) ^ 4 : ℝ) : ℂ) by
        push_cast; ring]
      rw [Complex.ofReal_div, Complex.ofReal_one, one_div, inv_mul_cancel₀ hne]
    rw [this, one_mul]
  simp_rw [hcancel]
  -- `∫ 𝓕φ = φ(0)` by Fourier inversion
  have hinv := Continuous.fourier_inversion φ.continuous φ.integrable
    (SchwartzMap.fourierTransformCLM ℂ φ).integrable
  have h0 := congrFun hinv 0
  rw [Real.fourierIntegralInv_eq] at h0
  simpa using h0


/-! ### The ODE away from the origin, the matching conditions and the jump -/

/-- On `x ≥ 0`, `h = p₀` with `p₀(x) = e^{-cx}(cos cx + sin cx)`; `p₁, p₂, p₃` are its
successive derivatives. -/
def p0 (c x : ℝ) : ℝ := Real.exp (-(c * x)) * (Real.cos (c * x) + Real.sin (c * x))
def p1 (c x : ℝ) : ℝ := -2 * c * Real.exp (-(c * x)) * Real.sin (c * x)
def p2 (c x : ℝ) : ℝ := -2 * c ^ 2 * Real.exp (-(c * x)) * (Real.cos (c * x) - Real.sin (c * x))
def p3 (c x : ℝ) : ℝ := 4 * c ^ 3 * Real.exp (-(c * x)) * Real.cos (c * x)

section derivs
variable (c x : ℝ)

theorem hasDerivAt_lin : HasDerivAt (fun y => c * y) c x := by
  simpa using (hasDerivAt_id x).const_mul c

theorem hasDerivAt_e :
    HasDerivAt (fun y => Real.exp (-(c * y))) (Real.exp (-(c * x)) * -c) x :=
  (hasDerivAt_lin c x).neg.exp

theorem hasDerivAt_p0 : HasDerivAt (p0 c) (p1 c x) x := by
  have := (hasDerivAt_e c x).mul ((hasDerivAt_lin c x).cos.add (hasDerivAt_lin c x).sin)
  convert this using 1
  simp only [p1, Pi.add_apply]; ring

theorem hasDerivAt_p1 : HasDerivAt (p1 c) (p2 c x) x := by
  have := ((hasDerivAt_e c x).const_mul (-2 * c)).mul (hasDerivAt_lin c x).sin
  convert this using 1
  simp only [p2]; ring

theorem hasDerivAt_p2 : HasDerivAt (p2 c) (p3 c x) x := by
  have := ((hasDerivAt_e c x).const_mul (-2 * c ^ 2)).mul
    ((hasDerivAt_lin c x).cos.sub (hasDerivAt_lin c x).sin)
  convert this using 1
  simp only [p3, Pi.sub_apply]; ring

theorem hasDerivAt_p3 : HasDerivAt (p3 c) (-4 * c ^ 4 * p0 c x) x := by
  have := ((hasDerivAt_e c x).const_mul (4 * c ^ 3)).mul (hasDerivAt_lin c x).cos
  convert this using 1
  simp only [p0]; ring

end derivs

theorem iteratedDeriv_p0 (c : ℝ) :
    iteratedDeriv 3 (p0 c) = p3 c ∧ iteratedDeriv 4 (p0 c) = fun x => -4 * c ^ 4 * p0 c x := by
  have d0 : deriv (p0 c) = p1 c := funext fun x => (hasDerivAt_p0 c x).deriv
  have d1 : deriv (p1 c) = p2 c := funext fun x => (hasDerivAt_p1 c x).deriv
  have d2 : deriv (p2 c) = p3 c := funext fun x => (hasDerivAt_p2 c x).deriv
  have d3 : deriv (p3 c) = fun x => -4 * c ^ 4 * p0 c x :=
    funext fun x => (hasDerivAt_p3 c x).deriv
  have i3 : iteratedDeriv 3 (p0 c) = p3 c := by
    rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one, d0, d1, d2]
  exact ⟨i3, by rw [iteratedDeriv_succ, i3, d3]⟩

theorem hG_eqOn_pos (c : ℝ) : EqOn (hG c) (p0 c) (Ici 0) := fun x hx => by
  simp only [hG, p0, abs_of_nonneg (show (0 : ℝ) ≤ x from hx)]

theorem hG_eqOn_neg (c : ℝ) : EqOn (hG c) (fun x => p0 c (-x)) (Iic 0) := fun x hx => by
  simp only [hG, p0, abs_of_nonpos (show x ≤ 0 from hx)]

/-- Iterated derivatives agree on an open set where the functions agree. -/
theorem iteratedDeriv_eqOn {f g : ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s) (h : EqOn f g s) (n : ℕ) :
    EqOn (iteratedDeriv n f) (iteratedDeriv n g) s := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    intro x hx
    rw [iteratedDeriv_succ, iteratedDeriv_succ]
    exact Filter.EventuallyEq.deriv_eq (Filter.eventuallyEq_of_mem (hs.mem_nhds hx) ih)

theorem iteratedDeriv_hG_pos (c : ℝ) (n : ℕ) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv n (hG c) x = iteratedDeriv n (p0 c) x :=
  iteratedDeriv_eqOn isOpen_Ioi (fun _ hy => hG_eqOn_pos c (Set.mem_Ici.2 (le_of_lt hy))) n hx

theorem iteratedDeriv_hG_neg (c : ℝ) (n : ℕ) {x : ℝ} (hx : x < 0) :
    iteratedDeriv n (hG c) x = (-1) ^ n * iteratedDeriv n (p0 c) (-x) := by
  rw [iteratedDeriv_eqOn isOpen_Iio (fun _ hy => hG_eqOn_neg c (Set.mem_Iic.2 (le_of_lt hy))) n hx,
    iteratedDeriv_comp_neg, smul_eq_mul]

/-- **The Green-function ODE and matching conditions** (`c = b/√2`): `ah'''' + rh = 0` for
`x ≠ 0`; `h` is continuous and `h'(0) = 0` (two-sided); `h'''(0⁺) = 4c³` and
`h'''(0⁻) = −4c³`, a jump of `8c³`; and `C = (8ac³)⁻¹`, so `g = Ch` has `ag'''`
jumping by exactly one. -/
theorem ode (hr : 0 < r) (ha : 0 < a) :
    (∀ x : ℝ, x ≠ 0 → a * iteratedDeriv 4 (hG (cG r a)) x + r * hG (cG r a) x = 0) ∧
    Continuous (hG (cG r a)) ∧ HasDerivAt (hG (cG r a)) 0 0 ∧
    Tendsto (iteratedDeriv 3 (hG (cG r a))) (𝓝[>] 0) (𝓝 (4 * cG r a ^ 3)) ∧
    Tendsto (iteratedDeriv 3 (hG (cG r a))) (𝓝[<] 0) (𝓝 (-(4 * cG r a ^ 3))) ∧
    4 * cG r a ^ 3 - -(4 * cG r a ^ 3) = 8 * cG r a ^ 3 ∧
    CG r a = 1 / (8 * a * cG r a ^ 3) ∧ a * CG r a * (8 * cG r a ^ 3) = 1 := by
  have h4 := four_a_cG_pow_four hr ha
  have hc0 := cG_pos hr ha
  have hCG := CG_eq hr ha
  set c := cG r a with hc
  obtain ⟨i3, i4⟩ := iteratedDeriv_p0 c
  refine ⟨fun x hx => ?_, continuous_hG c, ?_, ?_, ?_, by ring, hCG, ?_⟩
  · rcases lt_or_gt_of_ne hx with hx | hx
    · rw [iteratedDeriv_hG_neg c 4 hx, i4, hG_eqOn_neg c (le_of_lt hx)]
      linear_combination (-(p0 c (-x))) * h4
    · rw [iteratedDeriv_hG_pos c 4 hx, i4, hG_eqOn_pos c (le_of_lt hx)]
      linear_combination (-(p0 c x)) * h4
  · have h1 : HasDerivWithinAt (hG c) 0 (Ici 0) 0 := by
      have := (hasDerivAt_p0 c 0).hasDerivWithinAt (s := Ici 0)
      rw [show p1 c 0 = 0 by simp [p1]] at this
      exact this.congr (hG_eqOn_pos c) (hG_eqOn_pos c left_mem_Ici)
    have h2 : HasDerivWithinAt (hG c) 0 (Iic 0) 0 := by
      have := ((hasDerivAt_p0 c (-0)).comp 0 (hasDerivAt_neg 0)).hasDerivWithinAt (s := Iic 0)
      rw [show p1 c (-0) * -1 = 0 by simp [p1]] at this
      exact this.congr (hG_eqOn_neg c) (hG_eqOn_neg c right_mem_Iic)
    have := h2.union h1
    rwa [Iic_union_Ici, hasDerivWithinAt_univ] at this
  · have hlim : Tendsto (p3 c) (𝓝[>] 0) (𝓝 (4 * c ^ 3)) := by
      have : Continuous (p3 c) := by unfold p3; fun_prop
      simpa [p3] using (this.tendsto 0).mono_left nhdsWithin_le_nhds
    refine hlim.congr' (eventuallyEq_nhdsWithin_of_eqOn fun x hx => ?_)
    rw [iteratedDeriv_hG_pos c 3 hx, i3]
  · have hlim : Tendsto (fun x => -p3 c (-x)) (𝓝[<] 0) (𝓝 (-(4 * c ^ 3))) := by
      have : Continuous fun x => -p3 c (-x) := by unfold p3; fun_prop
      simpa [p3] using (this.tendsto 0).mono_left nhdsWithin_le_nhds
    refine hlim.congr' (eventuallyEq_nhdsWithin_of_eqOn fun x hx => ?_)
    rw [iteratedDeriv_hG_neg c 3 hx, i3]
    ring
  · rw [hCG]
    have : a * c ^ 3 ≠ 0 := by positivity
    field_simp

/-! ### Positive multiplier, sign-changing Green function -/

theorem CG_pos (hr : 0 < r) (ha : 0 < a) : 0 < CG r a := by
  rw [CG_eq hr ha]; have := cG_pos hr ha; positivity

/-- **Sign change**: at `t = π` (`x = π/c`), `g(x) = −C e^{-π} < 0`, although
`G(k) = 1/(r + ak⁴) > 0` for every real `k`. -/
theorem sign_change (hr : 0 < r) (ha : 0 < a) :
    (∀ k : ℝ, 0 < 1 / (r + a * k ^ 4)) ∧ gG r a (π / cG r a) = -(CG r a * Real.exp (-π)) ∧
      gG r a (π / cG r a) < 0 := by
  have hc := cG_pos hr ha
  have ht : cG r a * |π / cG r a| = π := by
    rw [abs_of_pos (div_pos Real.pi_pos hc)]; field_simp
  have hval : gG r a (π / cG r a) = -(CG r a * Real.exp (-π)) := by
    rw [gG, hG, ht, Real.cos_pi, Real.sin_pi]; ring
  refine ⟨fun k => by positivity, hval, ?_⟩
  rw [hval]
  have := CG_pos hr ha
  have := Real.exp_pos (-π)
  have : 0 < CG r a * Real.exp (-π) := by positivity
  linarith

/-- **No pointwise bound `g ≤ 1/r`**: for `r > 64a`, `g(0) = C > 1/r`. -/
theorem not_pointwise_bound (hr : 0 < r) (ha : 0 < a) (h64 : 64 * a < r) : 1 / r < gG r a 0 := by
  have hc := cG_pos hr ha
  have h4 := four_a_cG_pow_four hr ha
  have hg0 : gG r a 0 = 1 / (8 * a * cG r a ^ 3) := by
    simp [gG, hG, CG_eq hr ha]
  rw [hg0]
  have hc2 : 2 < cG r a := by
    by_contra h
    push_neg at h
    have : cG r a ^ 4 ≤ 2 ^ 4 := pow_le_pow_left₀ hc.le h 4
    nlinarith
  apply one_div_lt_one_div_of_lt (by positivity)
  have : 0 < a * cG r a ^ 3 := by positivity
  nlinarith [mul_pos this (sub_pos.2 hc2), h4]

end E58Green
end ReyesMath
