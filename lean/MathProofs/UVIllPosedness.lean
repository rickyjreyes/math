import Mathlib
import MathProofs.FourierLeakage

/-!
# Ultraviolet Sobolev ill-posedness of a fourth-order wave equation (F02/UV)

Formalization of `papers/uv-sobolev-ill-posedness-fourth-order-wave/main.tex`.

* Exact temporal roots: for the sector `𝒟(z,q) = (z−q) − m² − K(z−q)² + Gq(z−q) − Tq²`
  (`K > 0`, `4KT − G² > 0`), `sExp` is the growing exponent `s = σ − iα = −iω₊`,
  `sExp_char`: `K s⁴ + b(q)s² + C(q) = 0`, `dispersion_root`: `𝒟(ω₊², q) = 0`,
  `sigma_pos`: `Re s > 0` once `R(q) > 0`.
* Ultraviolet asymptotics (Proposition, eq. (general-growth)): `sigma_asymptotic`
  `Re s(k) = c_UV |k| + O(|k|⁻¹)` with `c_UV = √((√(a²+b²) − a)/2)`, `cUV_pos`;
  `sigma_lower` (`Re s(k) ≥ c_*|k|` for `|k| ≥ R`), `norm_sExp_comparable` (`|s(k)| ≍ |k|`).
  For `(□ − □² − Δ²)u = 0`: `main_sigma`, `main_cUV` (`c_UV = √((√2 − 1)/2)`),
  `main_cUV_bounds` (`0.455 < c_UV < 0.4551`).
* The equations as differential operators on `ℝ × ℝ^d` (Mathlib's Laplacian):
  `sectorOp` (`−𝒟(□, Δ)`), `waveOp` (`∂ₜ⁴ + (1 − 2Δ)∂ₜ² − Δ + 2Δ²`), `waveOp_eq_sectorOp`.
* Flat torus: exact real modes `torusSol` (`a e^{σt} cos(k·x − αt)`) are jointly smooth exact
  solutions (`torusSol_isSmoothSolution`); four-jet Sobolev norms
  `‖U‖²_{X_r} = Σⱼ ‖∂ₜʲu‖²_{H^{r+3−j}}` through Fourier coefficients (`jetSq`, `jetNorm`,
  `jetSq_torusSol`), and their isometric Hilbert realization `toJet : X_r(𝕋^d) → ℓ²`
  (`norm_toJet`).
* Theorem 1 and the Proposition on `𝕋^d`: `torus_unbounded`, `torus_no_bounded_estimate`,
  `torus_no_bounded_operator`, `torus_no_bounded_linear_extension`, and
  `wave_torus_unbounded` for the stated equation: `‖Uₙ(0)‖_{X_{r+ℓ}} → 0`,
  `‖Uₙ(t₀)‖_{X_r} = 1`, so no bounded (linear) `S(t₀) : X_{r+ℓ} → X_r` extends the evolution.

The whole-space (`M = ℝ^d`) Fourier-packet case is in `MathProofs.UVWholeSpace`.
-/

open Filter Topology Complex InnerProductSpace MeasureTheory
open scoped ContDiff

namespace ReyesMath

namespace UVIllPosed

/-! ### The growing temporal root of the dispersion polynomial -/

/-- `b(q) = 1 + (2K + G) q`. -/
noncomputable def bq (K G q : ℝ) : ℝ := 1 + (2 * K + G) * q

/-- `C(q) = m² + q + (K + G + T) q²`. -/
noncomputable def cq (K G T m2 q : ℝ) : ℝ := m2 + q + (K + G + T) * q ^ 2

/-- `R(q) = (4KT − G²) q² − 2Gq − (1 − 4Km²)`: minus the discriminant of
`K z² − b(q) z + C(q)`. -/
noncomputable def radic (K G T m2 q : ℝ) : ℝ :=
  (4 * K * T - G ^ 2) * q ^ 2 - 2 * G * q - (1 - 4 * K * m2)

/-- `Re z₊(q) = b(q)/(2K)`. -/
noncomputable def zRe (K G q : ℝ) : ℝ := bq K G q / (2 * K)

/-- `Im z₊(q) = √R(q)/(2K)`. -/
noncomputable def zIm (K G T m2 q : ℝ) : ℝ := Real.sqrt (radic K G T m2 q) / (2 * K)

/-- `|z₊(q)| = √(C(q)/K)`. -/
noncomputable def modz (K G T m2 q : ℝ) : ℝ := Real.sqrt (cq K G T m2 q / K)

/-- The growth rate `σ(q) = √((|z₊| − Re z₊)/2)`. -/
noncomputable def sigma (K G T m2 q : ℝ) : ℝ :=
  Real.sqrt ((modz K G T m2 q - zRe K G q) / 2)

/-- `α(q) = √((|z₊| + Re z₊)/2)`. -/
noncomputable def alpha (K G T m2 q : ℝ) : ℝ :=
  Real.sqrt ((modz K G T m2 q + zRe K G q) / 2)

/-- The growing temporal exponent `s(q) = σ(q) − iα(q) = −iω₊(q)`, `ω₊ = α + iσ`. -/
noncomputable def sExp (K G T m2 q : ℝ) : ℂ := ⟨sigma K G T m2 q, -alpha K G T m2 q⟩

/-- The dispersion polynomial `𝒟(z,q) = (z−q) − m² − K(z−q)² + Gq(z−q) − Tq²`. -/
noncomputable def dispersion (K G T m2 : ℝ) (z : ℂ) (q : ℝ) : ℂ :=
  (z - q) - m2 - K * (z - q) ^ 2 + G * q * (z - q) - T * q ^ 2

variable {K G T m2 q : ℝ}

theorem radic_eq : radic K G T m2 q = 4 * K * cq K G T m2 q - bq K G q ^ 2 := by
  unfold radic cq bq
  ring

theorem zRe_sq_add_zIm_sq (hK : 0 < K) (hR : 0 ≤ radic K G T m2 q) :
    zRe K G q ^ 2 + zIm K G T m2 q ^ 2 = cq K G T m2 q / K := by
  unfold zRe zIm
  rw [div_pow, div_pow, Real.sq_sqrt hR, radic_eq]
  field_simp
  ring

theorem cq_div_nonneg (hK : 0 < K) (hR : 0 ≤ radic K G T m2 q) : 0 ≤ cq K G T m2 q / K := by
  rw [← zRe_sq_add_zIm_sq hK hR]
  positivity

theorem modz_sq (hK : 0 < K) (hR : 0 ≤ radic K G T m2 q) :
    modz K G T m2 q ^ 2 = zRe K G q ^ 2 + zIm K G T m2 q ^ 2 := by
  rw [modz, Real.sq_sqrt (cq_div_nonneg hK hR), zRe_sq_add_zIm_sq hK hR]

theorem abs_zRe_le_modz (hK : 0 < K) (hR : 0 ≤ radic K G T m2 q) :
    |zRe K G q| ≤ modz K G T m2 q := by
  rw [modz]
  apply Real.abs_le_sqrt
  rw [← zRe_sq_add_zIm_sq hK hR]
  nlinarith [sq_nonneg (zIm K G T m2 q)]

theorem zIm_nonneg (hK : 0 < K) : 0 ≤ zIm K G T m2 q :=
  div_nonneg (Real.sqrt_nonneg _) (by linarith)

theorem sigma_sq (hK : 0 < K) (hR : 0 ≤ radic K G T m2 q) :
    sigma K G T m2 q ^ 2 = (modz K G T m2 q - zRe K G q) / 2 := by
  have := abs_zRe_le_modz hK hR
  rw [sigma, Real.sq_sqrt]
  linarith [le_abs_self (zRe K G q)]

theorem alpha_sq (hK : 0 < K) (hR : 0 ≤ radic K G T m2 q) :
    alpha K G T m2 q ^ 2 = (modz K G T m2 q + zRe K G q) / 2 := by
  have := abs_zRe_le_modz hK hR
  rw [alpha, Real.sq_sqrt]
  linarith [neg_abs_le (zRe K G q)]

theorem sigma_mul_alpha (hK : 0 < K) (hR : 0 ≤ radic K G T m2 q) :
    sigma K G T m2 q * alpha K G T m2 q = zIm K G T m2 q / 2 := by
  have hA := abs_zRe_le_modz hK hR
  have h1 : 0 ≤ (modz K G T m2 q - zRe K G q) / 2 := by linarith [le_abs_self (zRe K G q)]
  rw [sigma, alpha, ← Real.sqrt_mul h1]
  have hsq := modz_sq hK hR
  rw [show (modz K G T m2 q - zRe K G q) / 2 * ((modz K G T m2 q + zRe K G q) / 2) =
      (zIm K G T m2 q / 2) ^ 2 by nlinarith [hsq]]
  exact Real.sqrt_sq (by have := zIm_nonneg (G := G) (T := T) (m2 := m2) (q := q) hK; positivity)

/-- `s² = −z₊`. -/
theorem sExp_sq (hK : 0 < K) (hR : 0 ≤ radic K G T m2 q) :
    sExp K G T m2 q ^ 2 = ⟨-zRe K G q, -zIm K G T m2 q⟩ := by
  have hs := sigma_sq hK hR
  have ha := alpha_sq hK hR
  have hp := sigma_mul_alpha hK hR
  apply Complex.ext
  · simp only [sExp, sq, Complex.mul_re]
    nlinarith [hs, ha]
  · simp only [sExp, sq, Complex.mul_im]
    nlinarith [hp]

/-- The characteristic equation `K s⁴ + b(q) s² + C(q) = 0` of the growing exponent, valid
whenever `R(q) ≥ 0`. -/
theorem sExp_char (hK : 0 < K) (hR : 0 ≤ radic K G T m2 q) :
    (K : ℂ) * sExp K G T m2 q ^ 4 + (bq K G q : ℂ) * sExp K G T m2 q ^ 2 +
      (cq K G T m2 q : ℂ) = 0 := by
  have hsq := sExp_sq hK hR
  have hm := zRe_sq_add_zIm_sq hK hR
  have h2K : 2 * K * zRe K G q = bq K G q := by
    unfold zRe
    field_simp
  have hC : K * (zRe K G q ^ 2 + zIm K G T m2 q ^ 2) = cq K G T m2 q := by
    rw [hm]
    field_simp
  rw [show sExp K G T m2 q ^ 4 = (sExp K G T m2 q ^ 2) ^ 2 by ring, hsq]
  apply Complex.ext
  · simp only [sq, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.zero_re, zero_mul, sub_zero]
    linear_combination (-1 : ℝ) * hC + zRe K G q * h2K
  · simp only [sq, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.zero_im, zero_mul, add_zero]
    linear_combination zIm K G T m2 q * h2K

/-- With `ω₊ = i s` (so that `e^{−iω₊t} = e^{st}`), `z₊ = ω₊²` solves `𝒟(z, q) = 0`. -/
theorem dispersion_root (hK : 0 < K) (hR : 0 ≤ radic K G T m2 q) :
    dispersion K G T m2 ((Complex.I * sExp K G T m2 q) ^ 2) q = 0 := by
  have h := sExp_char hK hR
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  unfold dispersion
  unfold bq cq at h
  push_cast at h
  linear_combination (-1 : ℂ) * h +
    (-(K : ℂ) * (Complex.I ^ 2 - 1) * sExp K G T m2 q ^ 4 +
      (1 + (2 * K + G) * q) * sExp K G T m2 q ^ 2) * hI

theorem sExp_re : (sExp K G T m2 q).re = sigma K G T m2 q := rfl

/-- The growth rate is strictly positive when `R(q) > 0`. -/
theorem sigma_pos (hK : 0 < K) (hR : 0 < radic K G T m2 q) : 0 < sigma K G T m2 q := by
  unfold sigma
  apply Real.sqrt_pos.2
  have hIm : 0 < zIm K G T m2 q := div_pos (Real.sqrt_pos.2 hR) (by linarith)
  have hsq := modz_sq hK hR.le
  have hmod : 0 ≤ modz K G T m2 q := Real.sqrt_nonneg _
  have : zRe K G q < modz K G T m2 q := by
    by_contra h
    push_neg at h
    nlinarith
  linarith

/-! ### Ultraviolet asymptotics of the growth rate -/

/-- `a = (2K + G)/(2K)`. -/
noncomputable def aUV (K G : ℝ) : ℝ := (2 * K + G) / (2 * K)

/-- `b = √(4KT − G²)/(2K)`. -/
noncomputable def bUV (K G T : ℝ) : ℝ := Real.sqrt (4 * K * T - G ^ 2) / (2 * K)

/-- `c_UV(K, G, T) = √((√(a² + b²) − a)/2)`. -/
noncomputable def cUV (K G T : ℝ) : ℝ :=
  Real.sqrt ((Real.sqrt (aUV K G ^ 2 + bUV K G T ^ 2) - aUV K G) / 2)

theorem aUV_sq_add_bUV_sq (hK : 0 < K) (hB : 0 ≤ 4 * K * T - G ^ 2) :
    aUV K G ^ 2 + bUV K G T ^ 2 = (K + G + T) / K := by
  unfold aUV bUV
  rw [div_pow, div_pow, Real.sq_sqrt hB]
  field_simp
  ring

theorem bUV_pos (hK : 0 < K) (hB : 0 < 4 * K * T - G ^ 2) : 0 < bUV K G T :=
  div_pos (Real.sqrt_pos.2 hB) (by linarith)

theorem aUV_lt_sqrt (hK : 0 < K) (hB : 0 < 4 * K * T - G ^ 2) :
    aUV K G < Real.sqrt (aUV K G ^ 2 + bUV K G T ^ 2) := by
  have hb := bUV_pos hK hB
  calc aUV K G ≤ |aUV K G| := le_abs_self _
    _ = Real.sqrt (aUV K G ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ < Real.sqrt (aUV K G ^ 2 + bUV K G T ^ 2) :=
        Real.sqrt_lt_sqrt (sq_nonneg _) (by nlinarith)

/-- Strict positivity of the ultraviolet growth constant. -/
theorem cUV_pos (hK : 0 < K) (hB : 0 < 4 * K * T - G ^ 2) : 0 < cUV K G T := by
  unfold cUV
  apply Real.sqrt_pos.2
  linarith [aUV_lt_sqrt hK hB]

theorem cUV_sq (hK : 0 < K) (hB : 0 < 4 * K * T - G ^ 2) :
    cUV K G T ^ 2 = (Real.sqrt (aUV K G ^ 2 + bUV K G T ^ 2) - aUV K G) / 2 := by
  unfold cUV
  rw [Real.sq_sqrt]
  linarith [aUV_lt_sqrt hK hB]

/-- A threshold beyond which `R(q) > 0`. -/
noncomputable def qR (K G T m2 : ℝ) : ℝ := (2 * |G| + |1 - 4 * K * m2|) / (4 * K * T - G ^ 2) + 1

theorem one_le_qR (hB : 0 < 4 * K * T - G ^ 2) : 1 ≤ qR K G T m2 := by
  unfold qR
  have : 0 ≤ (2 * |G| + |1 - 4 * K * m2|) / (4 * K * T - G ^ 2) := by positivity
  linarith

theorem radic_pos (hB : 0 < 4 * K * T - G ^ 2) (hq : qR K G T m2 ≤ q) :
    0 < radic K G T m2 q := by
  have hq1 : 1 ≤ q := le_trans (one_le_qR hB) hq
  have hBq : 2 * |G| + |1 - 4 * K * m2| + (4 * K * T - G ^ 2) ≤ (4 * K * T - G ^ 2) * q := by
    have h := mul_le_mul_of_nonneg_left hq hB.le
    unfold qR at h
    rw [mul_add, mul_div_cancel₀ _ hB.ne', mul_one] at h
    linarith
  have h2 := mul_le_mul_of_nonneg_right hBq (by linarith : (0 : ℝ) ≤ q)
  have hG : 2 * G * q ≤ 2 * |G| * q := by nlinarith [le_abs_self G]
  have hm : 1 - 4 * K * m2 ≤ |1 - 4 * K * m2| := le_abs_self _
  have hm' : |1 - 4 * K * m2| ≤ |1 - 4 * K * m2| * q := by
    nlinarith [abs_nonneg (1 - 4 * K * m2)]
  unfold radic
  nlinarith

/-- **Ultraviolet asymptotics.** `σ(ρ²) = c_UV ρ + O(ρ⁻¹)`, i.e.
`Re s(k) = c_UV |k| + O(|k|⁻¹)` with `ρ = |k|`. -/
theorem sigma_asymptotic (hK : 0 < K) (hB : 0 < 4 * K * T - G ^ 2) :
    ∃ M ρ₀ : ℝ, 0 < M ∧ 0 < ρ₀ ∧
      ∀ ρ ≥ ρ₀, |sigma K G T m2 (ρ ^ 2) - cUV K G T * ρ| ≤ M / ρ := by
  set A := Real.sqrt (aUV K G ^ 2 + bUV K G T ^ 2) with hAdef
  have hb := bUV_pos hK hB
  have hApos : 0 < A := Real.sqrt_pos.2 (by positivity)
  have hA2 : A ^ 2 = (K + G + T) / K := by
    rw [hAdef, Real.sq_sqrt (by positivity), aUV_sq_add_bUV_sq hK hB.le]
  have hc := cUV_pos (G := G) hK hB
  have hc2 := cUV_sq (G := G) hK hB
  set M₁ := ((|m2| + 1) / (K * A) + 1 / (2 * K)) / 2 with hM₁
  have hM₁pos : 0 < M₁ := by positivity
  refine ⟨M₁ / cUV K G T, max 1 (qR K G T m2), div_pos hM₁pos hc,
    lt_max_of_lt_left one_pos, fun ρ hρ => ?_⟩
  have hρ1 : 1 ≤ ρ := le_trans (le_max_left _ _) hρ
  have hρq : qR K G T m2 ≤ ρ := le_trans (le_max_right _ _) hρ
  set q := ρ ^ 2 with hqdef
  have hq1 : 1 ≤ q := by nlinarith
  have hqρ : ρ ≤ q := by nlinarith
  have hR : 0 < radic K G T m2 q := radic_pos hB (le_trans hρq hqρ)
  have hs2 := sigma_sq hK hR.le
  have hzRe : zRe K G q - aUV K G * q = 1 / (2 * K) := by
    unfold zRe aUV bq
    field_simp
    ring
  have hmod2 : modz K G T m2 q ^ 2 = cq K G T m2 q / K := by
    rw [modz, Real.sq_sqrt (cq_div_nonneg hK hR.le)]
  have hmodnn : 0 ≤ modz K G T m2 q := Real.sqrt_nonneg _
  have hAq : 0 < A * q := by positivity
  have hdiff : (modz K G T m2 q - A * q) * (modz K G T m2 q + A * q) = (m2 + q) / K := by
    have : (modz K G T m2 q - A * q) * (modz K G T m2 q + A * q) =
        modz K G T m2 q ^ 2 - A ^ 2 * q ^ 2 := by ring
    rw [this, hmod2, hA2]
    unfold cq
    field_simp
    ring
  have hmodA : |modz K G T m2 q - A * q| ≤ (|m2| + 1) / (K * A) := by
    have h1 : |modz K G T m2 q - A * q| * (modz K G T m2 q + A * q) = |m2 + q| / K := by
      rw [← abs_of_pos (show 0 < modz K G T m2 q + A * q by linarith), ← abs_mul, hdiff,
        abs_div, abs_of_pos hK]
    have h2 : |m2 + q| ≤ (|m2| + 1) * q := by
      calc |m2 + q| ≤ |m2| + |q| := abs_add_le _ _
        _ = |m2| + q := by rw [abs_of_pos (show (0 : ℝ) < q by linarith)]
        _ ≤ (|m2| + 1) * q := by nlinarith [abs_nonneg m2]
    have h3 : |modz K G T m2 q - A * q| * (K * A) * q ≤ (|m2| + 1) * q := by
      calc |modz K G T m2 q - A * q| * (K * A) * q
          = (|modz K G T m2 q - A * q| * (A * q)) * K := by ring
        _ ≤ (|modz K G T m2 q - A * q| * (modz K G T m2 q + A * q)) * K := by
            gcongr
            linarith
        _ = |m2 + q| := by rw [h1]; field_simp
        _ ≤ (|m2| + 1) * q := h2
    rw [le_div_iff₀ (by positivity)]
    exact le_of_mul_le_mul_right h3 (by linarith)
  have hσc : |sigma K G T m2 q ^ 2 - cUV K G T ^ 2 * q| ≤ M₁ := by
    rw [hs2, hc2, ← hAdef]
    have : (modz K G T m2 q - zRe K G q) / 2 - (A - aUV K G) / 2 * q =
        ((modz K G T m2 q - A * q) - (zRe K G q - aUV K G * q)) / 2 := by ring
    rw [this, hzRe, hM₁]
    have h1 := abs_le.1 hmodA
    have hK2 : 0 < 1 / (2 * K) := by positivity
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2]
  have hσnn : 0 ≤ sigma K G T m2 q := Real.sqrt_nonneg _
  have hcρ : 0 < cUV K G T * ρ := by positivity
  have key : |sigma K G T m2 q - cUV K G T * ρ| * (sigma K G T m2 q + cUV K G T * ρ) =
      |sigma K G T m2 q ^ 2 - cUV K G T ^ 2 * q| := by
    rw [← abs_of_nonneg (show 0 ≤ sigma K G T m2 q + cUV K G T * ρ by linarith), ← abs_mul]
    congr 1
    rw [hqdef]
    ring
  have hfin : |sigma K G T m2 q - cUV K G T * ρ| * (cUV K G T * ρ) ≤ M₁ :=
    le_trans (mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)) (key ▸ hσc)
  rw [div_div, le_div_iff₀ (by positivity)]
  exact hfin

/-- For every `0 < c_* < c_UV` there is `R` with `Re s(k) ≥ c_* |k|` for `|k| ≥ R`. -/
theorem sigma_lower (hK : 0 < K) (hB : 0 < 4 * K * T - G ^ 2) {cs : ℝ}
    (hcs : cs < cUV K G T) :
    ∃ R : ℝ, 0 < R ∧ ∀ ρ ≥ R, cs * ρ ≤ sigma K G T m2 (ρ ^ 2) := by
  obtain ⟨M, ρ₀, hM, hρ₀, hasym⟩ := sigma_asymptotic (m2 := m2) hK hB
  have hgap : 0 < cUV K G T - cs := by linarith
  refine ⟨max ρ₀ (max 1 (M / (cUV K G T - cs))), lt_max_of_lt_left hρ₀, fun ρ hρ => ?_⟩
  have hρ0 : ρ₀ ≤ ρ := le_trans (le_max_left _ _) hρ
  have hρ1 : 1 ≤ ρ := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hρ
  have hρM : M / (cUV K G T - cs) ≤ ρ :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hρ
  have h1 := abs_le.1 (hasym ρ hρ0)
  have h2 : M / ρ ≤ M := div_le_self hM.le hρ1
  have h3 : M ≤ (cUV K G T - cs) * ρ := by
    rw [div_le_iff₀ hgap] at hρM
    linarith
  nlinarith [h1.1]

/-- `|s(q)|² = |z₊(q)|`, hence `|s(k)| ≍ |k|` at high frequency. -/
theorem norm_sExp_sq (hK : 0 < K) (hR : 0 ≤ radic K G T m2 q) :
    ‖sExp K G T m2 q‖ ^ 2 = modz K G T m2 q := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [sExp]
  have := sigma_sq hK hR
  have := alpha_sq hK hR
  nlinarith

/-- Two-sided high-frequency bounds `c₁|k| ≤ |s(k)| ≤ c₂|k|`. -/
theorem norm_sExp_comparable (hK : 0 < K) (hB : 0 < 4 * K * T - G ^ 2) :
    ∃ c₁ c₂ R : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ 0 < R ∧ ∀ ρ ≥ R,
      c₁ * ρ ≤ ‖sExp K G T m2 (ρ ^ 2)‖ ∧ ‖sExp K G T m2 (ρ ^ 2)‖ ≤ c₂ * ρ := by
  have hc := cUV_pos (G := G) hK hB
  obtain ⟨R₁, hR₁, hlow⟩ := sigma_lower (m2 := m2) hK hB (half_lt_self hc)
  set D := (|m2| + 1 + |K + G + T|) / K with hD
  have hDpos : 0 < D := by positivity
  refine ⟨cUV K G T / 2, Real.sqrt (Real.sqrt D), max R₁ (qR K G T m2), half_pos hc,
    Real.sqrt_pos.2 (Real.sqrt_pos.2 hDpos), lt_max_of_lt_left hR₁, fun ρ hρ => ⟨?_, ?_⟩⟩
  · calc cUV K G T / 2 * ρ ≤ sigma K G T m2 (ρ ^ 2) := hlow ρ (le_trans (le_max_left _ _) hρ)
      _ = (sExp K G T m2 (ρ ^ 2)).re := rfl
      _ ≤ |(sExp K G T m2 (ρ ^ 2)).re| := le_abs_self _
      _ ≤ ‖sExp K G T m2 (ρ ^ 2)‖ := Complex.abs_re_le_norm _
  · have hρq : qR K G T m2 ≤ ρ := le_trans (le_max_right _ _) hρ
    have hρ1 : 1 ≤ ρ := le_trans (one_le_qR hB) hρq
    have hq1 : 1 ≤ ρ ^ 2 := by nlinarith
    have hqρ : ρ ≤ ρ ^ 2 := by nlinarith
    have hR : 0 ≤ radic K G T m2 (ρ ^ 2) := (radic_pos hB (le_trans hρq hqρ)).le
    have hn := norm_sExp_sq hK hR
    have hcq : cq K G T m2 (ρ ^ 2) / K ≤ D * (ρ ^ 2) ^ 2 := by
      rw [hD, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hK]
      unfold cq
      have h1 : m2 ≤ |m2| * (ρ ^ 2) ^ 2 := by
        nlinarith [le_abs_self m2, abs_nonneg m2, one_le_pow₀ hq1 (n := 2)]
      have h2 : ρ ^ 2 ≤ (ρ ^ 2) ^ 2 := by nlinarith
      have h3 : (K + G + T) * (ρ ^ 2) ^ 2 ≤ |K + G + T| * (ρ ^ 2) ^ 2 := by
        nlinarith [le_abs_self (K + G + T), sq_nonneg (ρ ^ 2)]
      nlinarith
    have hmod : modz K G T m2 (ρ ^ 2) ≤ Real.sqrt D * ρ ^ 2 := by
      rw [modz]
      calc Real.sqrt (cq K G T m2 (ρ ^ 2) / K) ≤ Real.sqrt (D * (ρ ^ 2) ^ 2) :=
            Real.sqrt_le_sqrt hcq
        _ = Real.sqrt D * ρ ^ 2 := by
            rw [Real.sqrt_mul hDpos.le, Real.sqrt_sq (by positivity)]
    have hsq : ‖sExp K G T m2 (ρ ^ 2)‖ ^ 2 ≤ (Real.sqrt (Real.sqrt D) * ρ) ^ 2 := by
      rw [hn, mul_pow, Real.sq_sqrt (Real.sqrt_nonneg _)]
      exact hmod
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq

/-! ### The equation `(□ − □² − Δ²)u = 0`: `K = T = 1`, `G = m² = 0` -/

theorem main_radic (q : ℝ) : radic 1 0 1 0 q = 4 * q ^ 2 - 1 := by
  unfold radic
  ring

/-- `σ(q) = √((√(2q² + q) − q − 1/2)/2)` for the main equation. -/
theorem main_sigma (q : ℝ) :
    sigma 1 0 1 0 q = Real.sqrt ((Real.sqrt (2 * q ^ 2 + q) - q - 1 / 2) / 2) := by
  unfold sigma modz zRe cq bq
  rw [show ((0 : ℝ) + q + (1 + 0 + 1) * q ^ 2) / 1 = 2 * q ^ 2 + q by ring]
  congr 1
  ring

/-- `c_UV = √((√2 − 1)/2)` for the main equation. -/
theorem main_cUV : cUV 1 0 1 = Real.sqrt ((Real.sqrt 2 - 1) / 2) := by
  have ha : aUV 1 0 = 1 := by norm_num [aUV]
  have hb : bUV 1 0 1 = 1 := by
    unfold bUV
    rw [show (4 * 1 * 1 - 0 ^ 2 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    norm_num
  rw [cUV, ha, hb]
  norm_num

/-- `c_UV = 0.45508986…`: in particular `0.455 < c_UV < 0.4551`. -/
theorem main_cUV_bounds : 0.455 < cUV 1 0 1 ∧ cUV 1 0 1 < 0.4551 := by
  rw [main_cUV]
  have h1 : (1.41405 : ℝ) < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have h2 : Real.sqrt 2 < 1.41423202 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  constructor
  · rw [Real.lt_sqrt (by norm_num)]
    linarith
  · rw [Real.sqrt_lt' (by norm_num)]
    linarith

/-! ### The constant-coefficient equations -/

section Equation

variable {d : ℕ}

local notation "Rd" => EuclideanSpace ℝ (Fin d)

/-- `∂ₜʲ u(t, x)`. -/
noncomputable def dt (j : ℕ) (u : ℝ → Rd → ℝ) (t : ℝ) (x : Rd) : ℝ :=
  iteratedDeriv j (fun τ => u τ x) t

/-- The sector operator `−𝒟(□, Δ) = K∂ₜ⁴ + ∂ₜ² − (2K+G)Δ∂ₜ² − Δ + m² + (K+G+T)Δ²`, where
`𝒟 = □ − m² − K□² − GΔ□ − TΔ²` and `□ = −∂ₜ² + Δ`.  On `e^{st} e^{ik·x}` it acts by
`K s⁴ + b(|k|²) s² + C(|k|²)`. -/
noncomputable def sectorOp (K G T m2 : ℝ) (u : ℝ → Rd → ℝ) (t : ℝ) (x : Rd) : ℝ :=
  K * dt 4 u t x + dt 2 u t x - (2 * K + G) * Δ (dt 2 u t) x - Δ (u t) x + m2 * u t x +
    (K + G + T) * Δ (Δ (u t)) x

/-- The fourth-order wave equation `∂ₜ⁴u + (1 − 2Δ)∂ₜ²u − Δu + 2Δ²u = 0`, the expansion of
`(□ − □² − Δ²)u = 0`. -/
noncomputable def waveOp (u : ℝ → Rd → ℝ) (t : ℝ) (x : Rd) : ℝ :=
  dt 4 u t x + (dt 2 u t x - 2 * Δ (dt 2 u t) x) - Δ (u t) x + 2 * Δ (Δ (u t)) x

theorem waveOp_eq_sectorOp (u : ℝ → Rd → ℝ) : waveOp u = sectorOp 1 0 1 0 u := by
  funext t x
  unfold waveOp sectorOp
  ring

/-- A smooth exact solution: jointly `C^∞` in `(t, x)` and solving the equation everywhere. -/
structure IsSmoothSolution (K G T m2 : ℝ) (u : ℝ → Rd → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ (fun p : ℝ × Rd => u p.1 p.2)
  eq : ∀ t x, sectorOp K G T m2 u t x = 0

/-- `d/dt Re(c e^{st}) = Re(c s e^{st})`. -/
theorem hasDerivAt_re_cexp (c s : ℂ) (t : ℝ) :
    HasDerivAt (fun τ : ℝ => (c * Complex.exp (s * τ)).re) (c * s * Complex.exp (s * t)).re t := by
  have h1 : HasDerivAt (fun τ : ℝ => s * (τ : ℂ)) s t := by
    simpa using ((hasDerivAt_id t).ofReal_comp).const_mul s
  have h2 := (h1.cexp.const_mul c)
  have h3 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t h2
  convert h3 using 1
  simp only [Complex.reCLM_apply]
  ring_nf

theorem iteratedDeriv_re_cexp (s : ℂ) : ∀ (j : ℕ) (c : ℂ),
    iteratedDeriv j (fun τ : ℝ => (c * Complex.exp (s * τ)).re) =
      fun τ : ℝ => (c * s ^ j * Complex.exp (s * τ)).re
  | 0, c => by simp
  | j + 1, c => by
    rw [iteratedDeriv_succ', show deriv (fun τ : ℝ => (c * Complex.exp (s * τ)).re) =
        fun τ : ℝ => ((c * s) * Complex.exp (s * τ)).re from
          funext fun τ => (hasDerivAt_re_cexp c s τ).deriv, iteratedDeriv_re_cexp s j (c * s)]
    funext τ
    ring_nf

end Equation

/-! ### The flat torus `𝕋^d = (ℝ/2πℤ)^d` -/

section Torus

open FourierLeakage

variable {d : ℕ}

local notation "Rd" => EuclideanSpace ℝ (Fin d)

/-- `2π`-periodicity in every coordinate direction: functions on `𝕋^d`. -/
def IsTorusPeriodic (u : ℝ → Rd → ℝ) : Prop :=
  ∀ t x (j : Fin d), u t (x + (2 * Real.pi) • EuclideanSpace.single j 1) = u t x

/-- `Re(w e^{ik·x})`. -/
noncomputable def reMode (w : ℂ) (k : Fin d → ℤ) (x : Rd) : ℝ := (w * E k x).re

theorem laplacian_reMode (w : ℂ) (k : Fin d → ℤ) :
    Δ (reMode w k) = reMode (((-nsq k : ℝ) : ℂ) * w) k := by
  funext x
  have hf : ContDiff ℝ 2 (fun y : Rd => w * E k y) := contDiff_const.mul (contDiff_E k)
  have h := (hf.contDiffAt (x := x)).laplacian_CLM_comp_left (l := Complex.reCLM)
  have he : reMode w k = ⇑Complex.reCLM ∘ fun y : Rd => w * E k y := by
    funext y
    simp [reMode]
  rw [he, h]
  simp only [Function.comp_apply, Complex.reCLM_apply, reMode]
  rw [laplacian_const_mul_E, laplacian_E]
  congr 1
  push_cast
  ring

/-- The exact torus mode `u(t,x) = a Re(e^{st} e^{ik·x})`. -/
noncomputable def torusSol (a : ℝ) (s : ℂ) (k : Fin d → ℤ) (t : ℝ) (x : Rd) : ℝ :=
  reMode ((a : ℂ) * Complex.exp (s * t)) k x

theorem dt_torusSol (a : ℝ) (s : ℂ) (k : Fin d → ℤ) (j : ℕ) (t : ℝ) :
    dt j (torusSol a s k) t = reMode ((a : ℂ) * s ^ j * Complex.exp (s * t)) k := by
  funext x
  have : (fun τ => torusSol a s k τ x) =
      fun τ : ℝ => (((a : ℂ) * E k x) * Complex.exp (s * τ)).re := by
    funext τ
    simp only [torusSol, reMode]
    ring_nf
  rw [dt, this, iteratedDeriv_re_cexp]
  simp only [reMode]
  ring_nf

theorem torusSol_periodic (a : ℝ) (s : ℂ) (k : Fin d → ℤ) : IsTorusPeriodic (torusSol a s k) := by
  intro t x j
  simp only [torusSol, reMode, E_periodic]

theorem contDiff_torusSol (a : ℝ) (s : ℂ) (k : Fin d → ℤ) :
    ContDiff ℝ ∞ (fun p : ℝ × Rd => torusSol a s k p.1 p.2) := by
  have h1 : ContDiff ℝ ∞ (fun p : ℝ × Rd => (a : ℂ) * Complex.exp (s * (p.1 : ℂ))) :=
    contDiff_const.mul (Complex.contDiff_exp.comp
      (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp contDiff_fst)))
  have h2 : ContDiff ℝ ∞ (fun p : ℝ × Rd => E k p.2) := (contDiff_E k).comp contDiff_snd
  exact Complex.reCLM.contDiff.comp (h1.mul h2)

/-- The torus modes built on the growing root are smooth exact solutions. -/
theorem torusSol_isSmoothSolution {K G T m2 : ℝ} (hK : 0 < K) (k : Fin d → ℤ)
    (hR : 0 ≤ radic K G T m2 (nsq k)) (a : ℝ) :
    IsSmoothSolution K G T m2 (torusSol a (sExp K G T m2 (nsq k)) k) := by
  refine ⟨contDiff_torusSol _ _ _, fun t x => ?_⟩
  set s := sExp K G T m2 (nsq k)
  have hchar := sExp_char hK hR
  have hu : torusSol a s k t = reMode ((a : ℂ) * Complex.exp (s * t)) k := rfl
  unfold sectorOp
  rw [dt_torusSol, dt_torusSol, hu, laplacian_reMode, laplacian_reMode, laplacian_reMode]
  simp only [reMode]
  have hlin : ∀ z₁ z₂ z₃ z₄ z₅ z₆ : ℂ,
      K * z₁.re + z₂.re - (2 * K + G) * z₃.re - z₄.re + m2 * z₅.re + (K + G + T) * z₆.re =
        ((K : ℂ) * z₁ + z₂ - ((2 * K + G : ℝ) : ℂ) * z₃ - z₄ + (m2 : ℂ) * z₅ +
          ((K + G + T : ℝ) : ℂ) * z₆).re := by
    intro z₁ z₂ z₃ z₄ z₅ z₆
    simp only [Complex.add_re, Complex.sub_re, Complex.re_ofReal_mul]
  rw [hlin]
  have key : ((a : ℂ) * Complex.exp (s * t) * E k x) *
      ((K : ℂ) * s ^ 4 + (bq K G (nsq k) : ℂ) * s ^ 2 + (cq K G T m2 (nsq k) : ℂ)) = 0 := by
    rw [hchar, mul_zero]
  rw [← Complex.zero_re, ← key]
  congr 1
  unfold bq cq
  push_cast
  ring

end Torus

/-! ### Sobolev four-jet norms on `𝕋^d` -/

section TorusNorms

open FourierLeakage

variable {d : ℕ}

local notation "Rd" => EuclideanSpace ℝ (Fin d)

/-- `‖f‖²_{H^p(𝕋^d)} = (2π)^d Σ_k (1 + |k|²)^p |f̂(k)|²` (Parseval normalization). -/
noncomputable def sobSq (p : ℝ) (f : Rd → ℂ) : ℝ :=
  (2 * Real.pi) ^ d * ∑' k, (1 + nsq k) ^ p * ‖coeff f k‖ ^ 2

/-- `f ∈ H^p(𝕋^d)`: the weighted coefficient series converges. -/
def MemSob (p : ℝ) (f : Rd → ℂ) : Prop :=
  Summable fun k => (1 + nsq k) ^ p * ‖coeff f k‖ ^ 2

/-- The four-jet `U(t) = (u, ∂ₜu, ∂ₜ²u, ∂ₜ³u)(t)` lies in
`X_r = H^{r+3} × H^{r+2} × H^{r+1} × H^r`. -/
def MemJet (r : ℝ) (u : ℝ → Rd → ℝ) (t : ℝ) : Prop :=
  ∀ j : Fin 4, MemSob (r + 3 - (j : ℕ)) (fun x => (dt j u t x : ℂ))

/-- `‖U(t)‖²_{X_r} = Σ_{j=0}^{3} ‖∂ₜʲu(t)‖²_{H^{r+3−j}}`. -/
noncomputable def jetSq (r : ℝ) (u : ℝ → Rd → ℝ) (t : ℝ) : ℝ :=
  ∑ j : Fin 4, sobSq (r + 3 - (j : ℕ)) (fun x => (dt j u t x : ℂ))

/-- `‖U(t)‖_{X_r}`. -/
noncomputable def jetNorm (r : ℝ) (u : ℝ → Rd → ℝ) (t : ℝ) : ℝ := Real.sqrt (jetSq r u t)

theorem nsq_neg (k : Fin d → ℤ) : nsq (-k) = nsq k := by
  simp [nsq]

theorem nsq_nonneg (k : Fin d → ℤ) : 0 ≤ nsq k := by
  unfold nsq
  positivity

theorem ne_neg_of_ne_zero {k : Fin d → ℤ} (hk : k ≠ 0) : k ≠ -k := by
  intro h
  apply hk
  funext j
  have := congrFun h j
  simp only [Pi.neg_apply] at this
  simp only [Pi.zero_apply]
  omega

theorem coeff_reMode (w : ℂ) (k n : Fin d → ℤ) :
    coeff (fun x => ((reMode w k x : ℝ) : ℂ)) n =
      (if k = n then w / 2 else 0) + (if -k = n then (starRingEnd ℂ) w / 2 else 0) := by
  have hf : (fun x => ((reMode w k x : ℝ) : ℂ)) =
      fun x => (w / 2) * E k x + ((starRingEnd ℂ) w / 2) * E (-k) x := by
    funext x
    rw [reMode, Complex.re_eq_add_conj, map_mul, E_neg]
    ring
  rw [hf, coeff_add (continuous_const.mul (continuous_E _)) (continuous_const.mul (continuous_E _)),
    coeff_const_mul, coeff_const_mul, coeff_E, coeff_E]
  split_ifs <;> simp

/-- For `k ≠ 0`: `‖Re(w e^{ik·x})‖²_{H^p} = C_𝕋 |w|² (1+|k|²)^p`, `C_𝕋 = (2π)^d/2`. -/
theorem sobSq_reMode (w : ℂ) {k : Fin d → ℤ} (hk : k ≠ 0) (p : ℝ) :
    MemSob p (fun x => ((reMode w k x : ℝ) : ℂ)) ∧
      sobSq p (fun x => ((reMode w k x : ℝ) : ℂ)) =
        (2 * Real.pi) ^ d / 2 * ((1 + nsq k) ^ p * ‖w‖ ^ 2) := by
  have hkk := ne_neg_of_ne_zero hk
  have hzero : ∀ n ∉ ({k, -k} : Finset (Fin d → ℤ)),
      (1 + nsq n) ^ p * ‖coeff (fun x => ((reMode w k x : ℝ) : ℂ)) n‖ ^ 2 = 0 := by
    intro n hn
    have h1 : k ≠ n := fun h => hn (by simp [h])
    have h2 : -k ≠ n := fun h => hn (by simp [← h])
    rw [coeff_reMode, if_neg h1, if_neg h2]
    simp
  refine ⟨summable_of_ne_finset_zero hzero, ?_⟩
  rw [sobSq, tsum_eq_sum hzero, Finset.sum_pair hkk, coeff_reMode, coeff_reMode, if_pos rfl,
    if_neg (Ne.symm hkk), if_neg hkk, if_pos rfl, nsq_neg]
  simp only [add_zero, zero_add, norm_div, Complex.norm_conj, Complex.norm_ofNat]
  ring

/-- `N_{r}(s,k)² = C_𝕋 Σ_{j=0}^{3} |s|^{2j} (1+|k|²)^{r+3−j}`. -/
noncomputable def Nsq (r : ℝ) (s : ℂ) (k : Fin d → ℤ) : ℝ :=
  (2 * Real.pi) ^ d / 2 * ∑ j : Fin 4, (1 + nsq k) ^ (r + 3 - (j : ℕ)) * ‖s‖ ^ (2 * (j : ℕ))

theorem Nsq_pos (r : ℝ) (s : ℂ) (k : Fin d → ℤ) : 0 < Nsq r s k := by
  unfold Nsq
  have hk := nsq_nonneg k
  apply mul_pos (by positivity)
  rw [Fin.sum_univ_succ]
  apply add_pos_of_pos_of_nonneg
  · simp only [Fin.val_zero, Nat.cast_zero, sub_zero, mul_zero, pow_zero, mul_one]
    exact Real.rpow_pos_of_pos (by linarith) _
  · exact Finset.sum_nonneg fun j _ => mul_nonneg (Real.rpow_nonneg (by linarith) _)
      (pow_nonneg (norm_nonneg _) _)

/-- Gaining `ℓ` derivatives multiplies `N²` by `(1 + |k|²)^ℓ`. -/
theorem Nsq_add (r ℓ : ℝ) (s : ℂ) (k : Fin d → ℤ) :
    Nsq (r + ℓ) s k = (1 + nsq k) ^ ℓ * Nsq r s k := by
  unfold Nsq
  have hk : 0 < 1 + nsq k := by linarith [nsq_nonneg k]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show r + ℓ + 3 - (j : ℕ) = ℓ + (r + 3 - (j : ℕ)) by ring, Real.rpow_add hk]
  ring

/-- Exact four-jet norm of a torus mode: `‖U(t)‖²_{X_r} = a² e^{2 Re(s) t} N_r²`. -/
theorem jetSq_torusSol (a : ℝ) (s : ℂ) {k : Fin d → ℤ} (hk : k ≠ 0) (r t : ℝ) :
    MemJet r (torusSol a s k) t ∧
      jetSq r (torusSol a s k) t = a ^ 2 * Real.exp (2 * s.re * t) * Nsq r s k := by
  have hnorm : ∀ j : ℕ, ‖(a : ℂ) * s ^ j * Complex.exp (s * t)‖ ^ 2 =
      a ^ 2 * Real.exp (2 * s.re * t) * ‖s‖ ^ (2 * j) := by
    intro j
    rw [norm_mul, norm_mul, Complex.norm_exp, Complex.norm_real, norm_pow]
    have : (s * (t : ℂ)).re = s.re * t := by simp
    rw [this, mul_pow, mul_pow, Real.norm_eq_abs, sq_abs, ← Real.exp_nat_mul, ← pow_mul]
    push_cast
    ring_nf
  refine ⟨fun j => ?_, ?_⟩
  · rw [dt_torusSol]
    exact (sobSq_reMode _ hk _).1
  · unfold jetSq Nsq
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [dt_torusSol, (sobSq_reMode _ hk _).2, hnorm]
    ring

end TorusNorms

/-! ### The torus theorem -/

section TorusTheorem

open FourierLeakage

variable {d : ℕ}

local notation "Rd" => EuclideanSpace ℝ (Fin d)

/-- The lattice frequency `ρ e₁ ∈ ℤ^d`. -/
noncomputable def lineFreq (hd : 0 < d) (ρ : ℕ) : Fin d → ℤ := Pi.single ⟨0, hd⟩ (ρ : ℤ)

theorem nsq_lineFreq (hd : 0 < d) (ρ : ℕ) : nsq (lineFreq hd ρ) = (ρ : ℝ) ^ 2 := by
  unfold nsq lineFreq
  rw [Finset.sum_eq_single ⟨0, hd⟩]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

theorem lineFreq_ne_zero (hd : 0 < d) {ρ : ℕ} (hρ : 0 < ρ) : lineFreq hd ρ ≠ 0 := by
  intro h
  have := congrFun h ⟨0, hd⟩
  simp [lineFreq] at this
  omega

/-- **Theorem (unbounded positive-time Sobolev evolution on `𝕋^d`).**  For the sector
`𝒟(z,q) = (z−q) − m² − K(z−q)² + Gq(z−q) − Tq²` with `K > 0`, `4KT − G² > 0` (hence `T > 0`),
every `r`, every `ℓ ≥ 0` and every `t₀ > 0`, there are smooth exact `2π`-periodic solutions
`uₙ` with `U_n(t) ∈ X_r ∩ X_{r+ℓ}`, `‖Uₙ(0)‖_{X_{r+ℓ}} → 0` and `‖Uₙ(t₀)‖_{X_r} = 1`. -/
theorem torus_unbounded {K G T m2 : ℝ} (hK : 0 < K) (hB : 0 < 4 * K * T - G ^ 2) (hd : 0 < d)
    (r ℓ t₀ : ℝ) (hℓ : 0 ≤ ℓ) (ht₀ : 0 < t₀) :
    ∃ u : ℕ → ℝ → Rd → ℝ,
      (∀ n, IsSmoothSolution K G T m2 (u n)) ∧ (∀ n, IsTorusPeriodic (u n)) ∧
      (∀ n t, MemJet r (u n) t ∧ MemJet (r + ℓ) (u n) t) ∧
      Tendsto (fun n => jetNorm (r + ℓ) (u n) 0) atTop (𝓝 0) ∧
      ∀ n, jetNorm r (u n) t₀ = 1 := by
  have hc := cUV_pos (G := G) hK hB
  obtain ⟨R, hR, hlow⟩ := sigma_lower (m2 := m2) hK hB (half_lt_self hc)
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge (max (max R (qR K G T m2)) 1)
  set ρ : ℕ → ℕ := fun n => n + N₀ with hρdef
  have hρbig : ∀ n, max (max R (qR K G T m2)) 1 ≤ (ρ n : ℝ) := fun n => by
    simp only [hρdef]
    push_cast
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hρR : ∀ n, R ≤ (ρ n : ℝ) := fun n =>
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (hρbig n)
  have hρq : ∀ n, qR K G T m2 ≤ (ρ n : ℝ) := fun n =>
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (hρbig n)
  have hρ1 : ∀ n, 1 ≤ (ρ n : ℝ) := fun n => le_trans (le_max_right _ _) (hρbig n)
  have hρpos : ∀ n, 0 < ρ n := fun n => by
    have := hρ1 n
    exact_mod_cast (show (0 : ℝ) < ρ n by linarith)
  set k : ℕ → (Fin d → ℤ) := fun n => lineFreq hd (ρ n) with hkdef
  have hk0 : ∀ n, k n ≠ 0 := fun n => lineFreq_ne_zero hd (hρpos n)
  have hnsq : ∀ n, nsq (k n) = (ρ n : ℝ) ^ 2 := fun n => nsq_lineFreq hd _
  have hRad : ∀ n, 0 ≤ radic K G T m2 (nsq (k n)) := fun n => by
    rw [hnsq]
    have h1 := hρ1 n
    exact (radic_pos hB (le_trans (hρq n) (by nlinarith))).le
  set s : ℕ → ℂ := fun n => sExp K G T m2 (nsq (k n)) with hsdef
  have hσ : ∀ n, cUV K G T / 2 * (ρ n : ℝ) ≤ (s n).re := fun n => by
    simp only [hsdef, sExp_re, hnsq]
    exact hlow _ (hρR n)
  set a : ℕ → ℝ := fun n => Real.exp (-(s n).re * t₀) / Real.sqrt (Nsq r (s n) (k n)) with hadef
  have ha2 : ∀ n, a n ^ 2 * Nsq r (s n) (k n) = Real.exp (-(2 * (s n).re * t₀)) := fun n => by
    simp only [hadef]
    rw [div_pow, Real.sq_sqrt (Nsq_pos _ _ _).le, ← Real.exp_nat_mul]
    field_simp [(Nsq_pos r (s n) (k n)).ne']
    ring_nf
  refine ⟨fun n => torusSol (a n) (s n) (k n),
    fun n => torusSol_isSmoothSolution hK (k n) (hRad n) (a n),
    fun n => torusSol_periodic _ _ _,
    fun n t => ⟨(jetSq_torusSol _ _ (hk0 n) r t).1, (jetSq_torusSol _ _ (hk0 n) (r + ℓ) t).1⟩,
    ?_, fun n => ?_⟩
  · have heq : ∀ n, jetNorm (r + ℓ) (torusSol (a n) (s n) (k n)) 0 =
        Real.exp (-(s n).re * t₀) * (1 + (ρ n : ℝ) ^ 2) ^ (ℓ / 2) := by
      intro n
      rw [jetNorm, (jetSq_torusSol _ _ (hk0 n) _ _).2, Nsq_add, hnsq]
      have hx : 0 < 1 + (ρ n : ℝ) ^ 2 := by positivity
      rw [show a n ^ 2 * Real.exp (2 * (s n).re * 0) * ((1 + (ρ n : ℝ) ^ 2) ^ ℓ *
          Nsq r (s n) (k n)) = (Real.exp (-(s n).re * t₀) * (1 + (ρ n : ℝ) ^ 2) ^ (ℓ / 2)) ^ 2 by
        rw [mul_zero, Real.exp_zero, mul_one, mul_pow, ← Real.rpow_natCast
          ((1 + (ρ n : ℝ) ^ 2) ^ (ℓ / 2)), ← Real.rpow_mul hx.le, ← Real.exp_nat_mul]
        rw [show ℓ / 2 * ((2 : ℕ) : ℝ) = ℓ by push_cast; ring]
        have := ha2 n
        rw [show a n ^ 2 * ((1 + (ρ n : ℝ) ^ 2) ^ ℓ * Nsq r (s n) (k n)) =
          (a n ^ 2 * Nsq r (s n) (k n)) * (1 + (ρ n : ℝ) ^ 2) ^ ℓ by ring, this]
        congr 1
        congr 1
        push_cast
        ring]
      exact Real.sqrt_sq (by positivity)
    simp_rw [heq]
    set b := cUV K G T / 2 * t₀ with hb
    have hbpos : 0 < b := by positivity
    have hbound : ∀ n, Real.exp (-(s n).re * t₀) * (1 + (ρ n : ℝ) ^ 2) ^ (ℓ / 2) ≤
        2 ^ (ℓ / 2) * ((ρ n : ℝ) ^ ℓ * Real.exp (-b * (ρ n : ℝ))) := by
      intro n
      have h1 : Real.exp (-(s n).re * t₀) ≤ Real.exp (-b * (ρ n : ℝ)) := by
        apply Real.exp_le_exp.2
        have := hσ n
        rw [hb]
        nlinarith
      have hρ := hρ1 n
      have h2 : (1 + (ρ n : ℝ) ^ 2) ^ (ℓ / 2) ≤ 2 ^ (ℓ / 2) * (ρ n : ℝ) ^ ℓ := by
        calc (1 + (ρ n : ℝ) ^ 2) ^ (ℓ / 2) ≤ (2 * (ρ n : ℝ) ^ 2) ^ (ℓ / 2) :=
              Real.rpow_le_rpow (by positivity) (by nlinarith) (by positivity)
          _ = 2 ^ (ℓ / 2) * (ρ n : ℝ) ^ ℓ := by
              rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast,
                ← Real.rpow_mul (by positivity)]
              congr 2
              push_cast
              ring
      calc Real.exp (-(s n).re * t₀) * (1 + (ρ n : ℝ) ^ 2) ^ (ℓ / 2)
          ≤ Real.exp (-b * (ρ n : ℝ)) * (2 ^ (ℓ / 2) * (ρ n : ℝ) ^ ℓ) :=
            mul_le_mul h1 h2 (by positivity) (by positivity)
        _ = 2 ^ (ℓ / 2) * ((ρ n : ℝ) ^ ℓ * Real.exp (-b * (ρ n : ℝ))) := by ring
    have hρlim : Tendsto (fun n => (ρ n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat N₀)
    have hlim : Tendsto (fun n => 2 ^ (ℓ / 2) * ((ρ n : ℝ) ^ ℓ * Real.exp (-b * (ρ n : ℝ))))
        atTop (𝓝 0) := by
      have := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ℓ b hbpos).comp hρlim
      simpa using this.const_mul (2 ^ (ℓ / 2))
    exact squeeze_zero (fun n => by positivity) hbound hlim
  · rw [jetNorm, (jetSq_torusSol _ _ (hk0 n) _ _).2]
    rw [show a n ^ 2 * Real.exp (2 * (s n).re * t₀) * Nsq r (s n) (k n) =
        (a n ^ 2 * Nsq r (s n) (k n)) * Real.exp (2 * (s n).re * t₀) by ring, ha2,
      ← Real.exp_add]
    simp

/-- **No bounded extension (`𝕋^d`).**  The same solutions violate every estimate
`‖U(t₀)‖_{X_r} ≤ C ‖U(0)‖_{X_{r+ℓ}}`. -/
theorem torus_no_bounded_estimate {K G T m2 : ℝ} (hK : 0 < K) (hB : 0 < 4 * K * T - G ^ 2)
    (hd : 0 < d) (r ℓ t₀ : ℝ) (hℓ : 0 ≤ ℓ) (ht₀ : 0 < t₀) :
    ∃ u : ℕ → ℝ → Rd → ℝ,
      (∀ n, IsSmoothSolution K G T m2 (u n)) ∧ (∀ n, IsTorusPeriodic (u n)) ∧
      (∀ n t, MemJet r (u n) t ∧ MemJet (r + ℓ) (u n) t) ∧
      ¬∃ C : ℝ, ∀ n, jetNorm r (u n) t₀ ≤ C * jetNorm (r + ℓ) (u n) 0 := by
  obtain ⟨u, hsol, hper, hmem, hlim, hone⟩ := torus_unbounded (m2 := m2) hK hB hd r ℓ t₀ hℓ ht₀
  refine ⟨u, hsol, hper, hmem, fun ⟨C, hC⟩ => ?_⟩
  have h := (hlim.const_mul C).eventually (gt_mem_nhds (show C * 0 < 1 by simp))
  obtain ⟨n, hn⟩ := h.exists
  have := hC n
  rw [hone n] at this
  linarith

end TorusTheorem

/-! ### The Hilbert-space realization of `X_r(𝕋^d)` and bounded operators -/

section TorusOperator

open FourierLeakage

variable {d : ℕ}

local notation "Rd" => EuclideanSpace ℝ (Fin d)

/-- `ℓ²(Fin 4 × ℤ^d)`, which realizes `X_r(𝕋^d)` isometrically for every `r` through
`U ↦ ((2π)^{d/2} (1+|k|²)^{(r+3−j)/2} \widehat{∂ₜʲu}(k))_{j,k}`. -/
abbrev JetSpace (d : ℕ) := lp (fun _ : Fin 4 × (Fin d → ℤ) => ℂ) 2

/-- The weighted Fourier family of a four-jet. -/
noncomputable def jetFamily (r : ℝ) (u : ℝ → Rd → ℝ) (t : ℝ) (jk : Fin 4 × (Fin d → ℤ)) : ℂ :=
  (Real.sqrt ((2 * Real.pi) ^ d * (1 + nsq jk.2) ^ (r + 3 - (jk.1 : ℕ))) : ℂ) *
    coeff (fun x => (dt jk.1 u t x : ℂ)) jk.2

open Classical in
/-- The four-jet `U(t)` as an element of `X_r(𝕋^d) ≅ ℓ²` (zero if `U(t) ∉ X_r`). -/
noncomputable def toJet (r : ℝ) (u : ℝ → Rd → ℝ) (t : ℝ) : JetSpace d :=
  if h : Memℓp (jetFamily r u t) 2 then ⟨jetFamily r u t, h⟩ else 0

theorem norm_jetFamily_sq (r : ℝ) (u : ℝ → Rd → ℝ) (t : ℝ) (jk : Fin 4 × (Fin d → ℤ)) :
    ‖jetFamily r u t jk‖ ^ 2 = (2 * Real.pi) ^ d *
      ((1 + nsq jk.2) ^ (r + 3 - (jk.1 : ℕ)) * ‖coeff (fun x => (dt jk.1 u t x : ℂ)) jk.2‖ ^ 2) := by
  have hk : 0 ≤ 1 + nsq jk.2 := by linarith [nsq_nonneg jk.2]
  rw [jetFamily, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt (by positivity)]
  ring

theorem summable_jetFamily {r : ℝ} {u : ℝ → Rd → ℝ} {t : ℝ} (h : MemJet r u t) :
    Summable fun jk => ‖jetFamily r u t jk‖ ^ 2 := by
  have hnn : 0 ≤ fun jk : Fin 4 × (Fin d → ℤ) => ‖jetFamily r u t jk‖ ^ 2 :=
    fun jk => sq_nonneg _
  refine (summable_prod_of_nonneg hnn).2 ⟨fun j => ?_, Summable.of_finite⟩
  simp_rw [norm_jetFamily_sq]
  exact (h j).mul_left _

theorem memℓp_jetFamily {r : ℝ} {u : ℝ → Rd → ℝ} {t : ℝ} (h : MemJet r u t) :
    Memℓp (jetFamily r u t) 2 := by
  apply memℓp_gen
  simpa [ENNReal.toReal_ofNat, Real.rpow_two] using summable_jetFamily h

/-- `‖U(t)‖_{ℓ²} = ‖U(t)‖_{X_r}` for `U(t) ∈ X_r`. -/
theorem norm_toJet {r : ℝ} {u : ℝ → Rd → ℝ} {t : ℝ} (h : MemJet r u t) :
    ‖toJet r u t‖ = jetNorm r u t := by
  rw [toJet, dif_pos (memℓp_jetFamily h), lp.norm_eq_tsum_rpow (by norm_num)]
  have hsum := summable_jetFamily h
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  change (∑' jk, ‖jetFamily r u t jk‖ ^ 2) ^ (1 / 2 : ℝ) = _
  rw [hsum.tsum_prod' fun j => (summable_prod_of_nonneg (fun jk => sq_nonneg
    ‖jetFamily r u t jk‖)).1 hsum |>.1 j, tsum_fintype, jetNorm, jetSq, Real.sqrt_eq_rpow]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  simp_rw [norm_jetFamily_sq]
  rw [sobSq, tsum_mul_left]

/-- **No bounded extension (`𝕋^d`), operator form.**  No map `S : X_{r+ℓ} → X_r` with
`‖S V‖ ≤ C‖V‖` (in particular no bounded linear operator) agrees with the classical evolution
`Uₙ(0) ↦ Uₙ(t₀)` on the exact solutions of `torus_unbounded`. -/
theorem torus_no_bounded_operator {K G T m2 : ℝ} (hK : 0 < K) (hB : 0 < 4 * K * T - G ^ 2)
    (hd : 0 < d) (r ℓ t₀ : ℝ) (hℓ : 0 ≤ ℓ) (ht₀ : 0 < t₀) :
    ∃ u : ℕ → ℝ → Rd → ℝ,
      (∀ n, IsSmoothSolution K G T m2 (u n)) ∧ (∀ n, IsTorusPeriodic (u n)) ∧
      (∀ n t, MemJet r (u n) t ∧ MemJet (r + ℓ) (u n) t) ∧
      Tendsto (fun n => ‖toJet (r + ℓ) (u n) 0‖) atTop (𝓝 0) ∧ (∀ n, ‖toJet r (u n) t₀‖ = 1) ∧
      ∀ (S : JetSpace d → JetSpace d) (C : ℝ), (∀ V, ‖S V‖ ≤ C * ‖V‖) →
        ¬∀ n, S (toJet (r + ℓ) (u n) 0) = toJet r (u n) t₀ := by
  obtain ⟨u, hsol, hper, hmem, hlim, hone⟩ := torus_unbounded (m2 := m2) hK hB hd r ℓ t₀ hℓ ht₀
  have hlim' : Tendsto (fun n => ‖toJet (r + ℓ) (u n) 0‖) atTop (𝓝 0) := by
    simpa only [norm_toJet (hmem _ _).2] using hlim
  have hone' : ∀ n, ‖toJet r (u n) t₀‖ = 1 := fun n => by rw [norm_toJet (hmem n t₀).1, hone n]
  refine ⟨u, hsol, hper, hmem, hlim', hone', fun S C hS hev => ?_⟩
  have h := (hlim'.const_mul C).eventually (gt_mem_nhds (show C * 0 < 1 by simp))
  obtain ⟨n, hn⟩ := h.exists
  have := hS (toJet (r + ℓ) (u n) 0)
  rw [hev n, hone' n] at this
  linarith

/-- In particular no bounded linear operator `S(t₀) : X_{r+ℓ}(𝕋^d) → X_r(𝕋^d)` extends the
classical evolution. -/
theorem torus_no_bounded_linear_extension {K G T m2 : ℝ} (hK : 0 < K)
    (hB : 0 < 4 * K * T - G ^ 2) (hd : 0 < d) (r ℓ t₀ : ℝ) (hℓ : 0 ≤ ℓ) (ht₀ : 0 < t₀) :
    ∃ u : ℕ → ℝ → Rd → ℝ,
      (∀ n, IsSmoothSolution K G T m2 (u n)) ∧ (∀ n, IsTorusPeriodic (u n)) ∧
      ∀ S : JetSpace d →L[ℂ] JetSpace d, ¬∀ n, S (toJet (r + ℓ) (u n) 0) = toJet r (u n) t₀ := by
  obtain ⟨u, hsol, hper, -, -, -, hS⟩ :=
    torus_no_bounded_operator (m2 := m2) hK hB hd r ℓ t₀ hℓ ht₀
  exact ⟨u, hsol, hper, fun S => hS S ‖S‖ S.le_opNorm⟩

end TorusOperator

/-! ### Theorem 1 on `𝕋^d` for `(□ − □² − Δ²)u = 0` -/

section MainTorus

variable {d : ℕ}

local notation "Rd" => EuclideanSpace ℝ (Fin d)

theorem isSmoothSolution_wave_iff (u : ℝ → Rd → ℝ) :
    IsSmoothSolution 1 0 1 0 u ↔
      ContDiff ℝ ∞ (fun p : ℝ × Rd => u p.1 p.2) ∧ ∀ t x, waveOp u t x = 0 := by
  rw [waveOp_eq_sectorOp]
  exact ⟨fun h => ⟨h.smooth, h.eq⟩, fun h => ⟨h.1, h.2⟩⟩

/-- **Theorem 1 (`M = 𝕋^d`).**  For every `r`, every fixed `ℓ ≥ 0` and every `t₀ > 0` there
are smooth exact real solutions of `∂ₜ⁴u + (1 − 2Δ)∂ₜ²u − Δu + 2Δ²u = 0` on `𝕋^d` with
`‖Uₙ(0)‖_{X_{r+ℓ}} → 0` and `‖Uₙ(t₀)‖_{X_r} = 1`; consequently no map
`S(t₀) : X_{r+ℓ}(𝕋^d) → X_r(𝕋^d)` with `‖S V‖ ≤ C‖V‖` (in particular no bounded linear
extension of the classical evolution) sends `Uₙ(0)` to `Uₙ(t₀)` for all `n`. -/
theorem wave_torus_unbounded (hd : 0 < d) (r ℓ t₀ : ℝ) (hℓ : 0 ≤ ℓ) (ht₀ : 0 < t₀) :
    ∃ u : ℕ → ℝ → Rd → ℝ,
      (∀ n, ContDiff ℝ ∞ (fun p : ℝ × Rd => u n p.1 p.2) ∧ ∀ t x, waveOp (u n) t x = 0) ∧
      (∀ n, IsTorusPeriodic (u n)) ∧ (∀ n t, MemJet r (u n) t ∧ MemJet (r + ℓ) (u n) t) ∧
      Tendsto (fun n => jetNorm (r + ℓ) (u n) 0) atTop (𝓝 0) ∧ (∀ n, jetNorm r (u n) t₀ = 1) ∧
      ∀ (S : JetSpace d → JetSpace d) (C : ℝ), (∀ V, ‖S V‖ ≤ C * ‖V‖) →
        ¬∀ n, S (toJet (r + ℓ) (u n) 0) = toJet r (u n) t₀ := by
  have hK : (0 : ℝ) < 1 := one_pos
  have hB : (0 : ℝ) < 4 * 1 * 1 - 0 ^ 2 := by norm_num
  obtain ⟨u', hsol', hper', hmem', hlim', hone'⟩ := torus_unbounded (m2 := 0) hK hB hd r ℓ t₀ hℓ ht₀
  refine ⟨u', fun n => (isSmoothSolution_wave_iff _).1 (hsol' n), hper', hmem', hlim', hone',
    fun S C hSC hev => ?_⟩
  have hlim'' : Tendsto (fun n => ‖toJet (r + ℓ) (u' n) 0‖) atTop (𝓝 0) := by
    simpa only [norm_toJet (hmem' _ _).2] using hlim'
  have h := (hlim''.const_mul C).eventually (gt_mem_nhds (show C * 0 < 1 by simp))
  obtain ⟨n, hn⟩ := h.exists
  have := hSC (toJet (r + ℓ) (u' n) 0)
  rw [hev n, norm_toJet (hmem' n t₀).1, hone' n] at this
  linarith

end MainTorus

end UVIllPosed

end ReyesMath
