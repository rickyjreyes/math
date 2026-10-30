import MathProofs.TorusFourier
import MathProofs.SpectralConcentration
import MathProofs.E62LebesgueFraction

/-!
# E62: certification of the spectral energy concentration manuscript

Manuscript: `papers/spectral-energy-concentration-e62/main.tex` (issue #34). Every theorem,
proposition and remark of the manuscript, stated for the manuscript's actual objects.

* **Theorem E62** (`E62Cert.theorem_e62`). Let `𝕋^d = (ℝ/2πℤ)^d`, `A ∈ L²(𝕋^d)` nonzero and
  `𝒜⋆ ⊆ ℤ^d` arbitrary. The coefficients are exactly
  `Â_k = (2π)^{-d} ∫_{𝕋^d} A(x) e^{-ik·x} dx`, Parseval
  `‖A‖²_{L²(dx)} = (2π)^d Σ_k |Â_k|²` holds, `E_tot = E⋆ + E_out` with `0 < E_tot < ∞` and
  `E_out ≥ 0`, `0 ≤ η ≤ 1`, and `η = 0 ⇔ Â_k = 0` on `𝒜⋆`, `η = 1 ⇔ Â_k = 0` off `𝒜⋆`.
* **Remark (sharpness)**: the nonzero fields `e^{ip·x}` (`p ∈ 𝒜⋆`) and `e^{iq·x}` (`q ∉ 𝒜⋆`)
  give `η = 1` and `η = 0` (`E62Cert.sharpness`).
* **Orthogonal Fourier projector** (`E62Cert.projector`): `\widehat{P⋆A} = 1_{𝒜⋆} Â`,
  `P⋆² = P⋆`, `P⋆* = P⋆`, `P⋆` is the orthogonal projection onto the selected subspace (its
  range), `η = ‖P⋆A‖²/‖A‖²`, `‖A‖² = ‖P⋆A‖² + ‖(I − P⋆)A‖²`, `η = 0 ⇔ P⋆A = 0` and
  `η = 1 ⇔ (I − P⋆)A = 0`; the same ratio with the physical `L²(dx)` norms
  (`E62Cert.projector_physical`).
* **Proposition (continuous spectrum)** for *Lebesgue*-measurable `ℬ ⊆ ℝ^d`
  (`E62Cert.continuous_spectrum`): the denominator is positive, `0 ≤ η_ℬ ≤ 1`, and the two a.e.
  equality conditions.
* **Remarks**: zero-width shell (`E62Cert.zero_width_shell`), the zero field `0/0`
  (`E62Cert.zero_field`), and the non-monotone two-mode example `η(t) = cos² t` with constant
  total energy (`E62Cert.no_monotonicity`).
-/

open Filter Topology Complex InnerProductSpace MeasureTheory Set
open scoped ComplexConjugate Real

noncomputable section

namespace ReyesMath
namespace E62Cert

open TorusL2

/-- The selected-mode energy split `E_tot = E⋆ + E_out`. -/
theorem Etot_split {L : ℝ} [Fact (0 < L)] {d : ℕ} (S : Set (Fin d → ℤ)) (A : L2 L d) :
    Etot A = Estar S A + Estar Sᶜ A ∧ 0 ≤ Estar S A ∧ 0 ≤ Estar Sᶜ A := by
  have h1 := (hasSum_Estar S A).add (hasSum_Estar Sᶜ A)
  have h2 : (fun k => S.indicator (fun k => ‖coef A k‖ ^ 2) k +
      Sᶜ.indicator (fun k => ‖coef A k‖ ^ 2) k) = fun k => ‖coef A k‖ ^ 2 := by
    funext k; by_cases hk : k ∈ S <;> simp [hk]
  rw [h2] at h1
  refine ⟨?_, ?_, ?_⟩
  · rw [Etot, h1.tsum_eq, Estar_eq, Estar_eq]
  · rw [Estar_eq]; positivity
  · rw [Estar_eq]; positivity

/-- **Theorem E62** on `𝕋^d = (ℝ/2πℤ)^d` with the manuscript's coefficient normalization. -/
theorem theorem_e62 {d : ℕ} (S : Set (Fin d → ℤ)) {A : L2 (2 * π) d} (hA : A ≠ 0) :
    (∀ k, coef A k = (((2 * π) ^ d)⁻¹ : ℝ) * ∫ x, A x * conj (emode k x)) ∧
    (∀ (k : Fin d → ℤ) (t : Fin d → ℝ),
      emode (L := 2 * π) k (fun i => (t i : AddCircle (2 * π))) =
        Complex.exp (Complex.I * ∑ i, (k i : ℂ) * t i)) ∧
    ∫ x, ‖A x‖ ^ 2 = (2 * π) ^ d * Etot A ∧
    Summable (fun k => ‖coef A k‖ ^ 2) ∧ 0 < Etot A ∧
    Etot A = Estar S A + Estar Sᶜ A ∧ 0 ≤ Estar Sᶜ A ∧
    0 ≤ eta S A ∧ eta S A ≤ 1 ∧
    (eta S A = 0 ↔ ∀ k ∈ S, coef A k = 0) ∧
    (eta S A = 1 ↔ ∀ k ∉ S, coef A k = 0) := by
  obtain ⟨hs, -, hpos, h0, h1, hz, ho⟩ := e62 S hA
  obtain ⟨hsplit, -, hout⟩ := Etot_split S A
  exact ⟨(e62_parseval A).2, emode_two_pi, (e62_parseval A).1, hs, hpos, hsplit, hout, h0, h1,
    hz, ho⟩

/-- `e_p` is the function `x ↦ e^{ip·x}` (as an element of `L²`). -/
theorem basis_eq_mode {d : ℕ} (p : Fin d → ℤ) :
    basis (2 * π) d p = (emode (L := 2 * π) p).toLp 2 (μ (2 * π) d) ℂ := basis_eq_toLp p

/-- **Remark (sharpness)**: both endpoints are attained by nonzero single modes. -/
theorem sharpness {d : ℕ} (S : Set (Fin d → ℤ)) {p q : Fin d → ℤ} (hp : p ∈ S) (hq : q ∉ S) :
    basis (2 * π) d p ≠ 0 ∧ eta S (basis (2 * π) d p) = 1 ∧
    basis (2 * π) d q ≠ 0 ∧ eta S (basis (2 * π) d q) = 0 := by
  have hne : ∀ n : Fin d → ℤ, basis (2 * π) d n ≠ 0 := fun n h => by
    have := norm_basis (L := 2 * π) n; rw [h, norm_zero] at this; exact zero_ne_one this
  exact ⟨hne p, eta_basis_mem S hp, hne q, eta_basis_not_mem S hq⟩

/-- **The orthogonal Fourier projector `P⋆`.** -/
theorem projector {d : ℕ} (S : Set (Fin d → ℤ)) {A : L2 (2 * π) d} (hA : A ≠ 0) :
    (∀ k, coef (P (2 * π) d S A) k = S.indicator 1 k * coef A k) ∧
    (P (2 * π) d S).comp (P (2 * π) d S) = P (2 * π) d S ∧
    ContinuousLinearMap.adjoint (P (2 * π) d S) = P (2 * π) d S ∧
    (∀ B, P (2 * π) d S B = (H (2 * π) d S).starProjection B) ∧
    LinearMap.range (P (2 * π) d S) = H (2 * π) d S ∧
    eta S A = ‖P (2 * π) d S A‖ ^ 2 / ‖A‖ ^ 2 ∧
    ‖A‖ ^ 2 = ‖P (2 * π) d S A‖ ^ 2 + ‖A - P (2 * π) d S A‖ ^ 2 ∧
    0 ≤ eta S A ∧ eta S A ≤ 1 ∧
    (eta S A = 0 ↔ P (2 * π) d S A = 0) ∧ (eta S A = 1 ↔ A - P (2 * π) d S A = 0) := by
  obtain ⟨h0, h1, h2, h3⟩ := eta_proj S hA
  exact ⟨coef_P S A, P_idem S, P_adjoint S, P_eq_starProjection S, range_P S, eta_eq S A,
    pythagoras S A, h0, h1, h2, h3⟩

/-- The projector ratio with the physical `L²(dx)` norms (`dx` the Lebesgue measure on `𝕋^d`):
`η = ‖P⋆A‖²_{L²(dx)} / ‖A‖²_{L²(dx)}`. -/
theorem projector_physical {d : ℕ} (S : Set (Fin d → ℤ)) (A : L2 (2 * π) d) :
    eta S A = (∫ x, ‖(P (2 * π) d S A : Tor (2 * π) d → ℂ) x‖ ^ 2) / ∫ x, ‖A x‖ ^ 2 := by
  have hpos : (0 : ℝ) < (2 * π) ^ d := pow_pos Real.two_pi_pos d
  rw [integral_norm_sq_volume, integral_norm_sq_volume, ← Etot, ← Etot, Etot_eq, Etot_eq, eta_eq,
    mul_div_mul_left _ _ hpos.ne']

/-! ### The continuous-spectrum proposition and the remarks -/

section Continuous

open Sobolev SpectralConc

variable {d : ℕ}

local notation "Rd" => EuclideanSpace ℝ (Fin d)

/-- **Proposition (continuous spectrum)**: for nonzero `A ∈ L²(ℝ^d)` and a *Lebesgue*-measurable
`ℬ ⊆ ℝ^d` (null-measurable for Lebesgue measure), the denominator `∫|Â|²` is positive,
`0 ≤ η_ℬ ≤ 1`, `η_ℬ = 0 ⇔ Â = 0` a.e. on `ℬ`, and `η_ℬ = 1 ⇔ Â = 0` a.e. off `ℬ`. -/
theorem continuous_spectrum {A : L2 d} (hA : A ≠ 0) {B : Set Rd}
    (hB : NullMeasurableSet B volume) :
    0 < ∫ ξ, ‖FU A ξ‖ ^ 2 ∧ 0 ≤ etaC A B ∧ etaC A B ≤ 1 ∧
      (etaC A B = 0 ↔ ∀ᵐ ξ ∂volume, ξ ∈ B → FU A ξ = 0) ∧
      (etaC A B = 1 ↔ ∀ᵐ ξ ∂volume, ξ ∉ B → FU A ξ = 0) := by
  have hT : MeasurableSet (toMeasurable volume B) := measurableSet_toMeasurable _ _
  have hBT : B =ᵐ[volume] toMeasurable volume B := hB.toMeasurable_ae_eq.symm
  have he : etaC A B = etaC A (toMeasurable volume B) := by
    unfold etaC; rw [setIntegral_congr_set hBT]
  obtain ⟨h1, h2, h3, h4, h5⟩ := e62_continuous hA hT
  refine ⟨h1, he ▸ h2, he ▸ h3, ?_, ?_⟩
  · rw [he, h4]
    constructor <;> intro h <;> filter_upwards [h, hBT] with ξ hξ hm
    · exact fun hx => hξ (Eq.mp hm hx)
    · exact fun hx => hξ (Eq.mpr hm hx)
  · rw [he, h5]
    constructor <;> intro h <;> filter_upwards [h, hBT] with ξ hξ hm
    · exact fun hx => hξ fun h' => hx (Eq.mpr hm h')
    · exact fun hx => hξ fun h' => hx (Eq.mp hm h')

/-- **Remark (zero-width shell)**: the exact sphere `|ξ| = k⋆` carries no `L²` energy fraction,
for every field (including nonzero ones), `d ≥ 1`. -/
theorem zero_width_shell (hd : 1 ≤ d) (A : L2 d) (k : ℝ) : etaC A (Metric.sphere 0 k) = 0 :=
  etaC_sphere hd A k

end Continuous

/-- **Remark (zero field)**: for `A = 0` both `E⋆` and `E_tot` vanish, so the ratio is the
indeterminate `0/0`; the value `η = 0` is only Lean's division convention. -/
theorem zero_field {L : ℝ} [Fact (0 < L)] {d : ℕ} (S : Set (Fin d → ℤ)) :
    Estar S (0 : L2 L d) = 0 ∧ Etot (0 : L2 L d) = 0 := by
  rw [Estar_eq, Etot_eq, map_zero, norm_zero]; norm_num

/-- **Remark (no monotonicity follows from E62)**: for `p ∈ 𝒜⋆`, `q ∉ 𝒜⋆`, the field
`A(t) = cos t e^{ip·x} + sin t e^{iq·x}` is nonzero with total spectral energy `1` for every `t`,
and `η(t) = cos² t`, which is neither monotone nor antitone. -/
theorem no_monotonicity {d : ℕ} (S : Set (Fin d → ℤ)) {p q : Fin d → ℤ} (hp : p ∈ S)
    (hq : q ∉ S) :
    (∀ t : ℝ, Etot ((Real.cos t : ℂ) • basis (2 * π) d p + (Real.sin t : ℂ) • basis (2 * π) d q)
      = 1) ∧
    (∀ t : ℝ, (Real.cos t : ℂ) • basis (2 * π) d p + (Real.sin t : ℂ) • basis (2 * π) d q ≠ 0) ∧
    (∀ t : ℝ, eta S ((Real.cos t : ℂ) • basis (2 * π) d p +
      (Real.sin t : ℂ) • basis (2 * π) d q) = Real.cos t ^ 2) ∧
    ¬ Monotone (fun t : ℝ => eta S ((Real.cos t : ℂ) • basis (2 * π) d p +
      (Real.sin t : ℂ) • basis (2 * π) d q)) ∧
    ¬ Antitone (fun t : ℝ => eta S ((Real.cos t : ℂ) • basis (2 * π) d p +
      (Real.sin t : ℂ) • basis (2 * π) d q)) := by
  obtain ⟨h1, h2, h3, h4⟩ := eta_not_monotone (L := 2 * π) S hp hq
  refine ⟨fun t => ?_, h1, h2, h3, h4⟩
  have hpq : p ≠ q := fun h => hq (h ▸ hp)
  rw [Etot_eq]
  have horth : ⟪(Real.cos t : ℂ) • basis (2 * π) d p, (Real.sin t : ℂ) • basis (2 * π) d q⟫_ℂ
      = 0 := by
    rw [inner_smul_left, inner_smul_right, (basis (2 * π) d).orthonormal.2 hpq, mul_zero,
      mul_zero]
  have := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth
  rw [sq, this, norm_smul, norm_smul, norm_basis, norm_basis, Complex.norm_real,
    Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, mul_one, mul_one]
  nlinarith [Real.cos_sq_add_sin_sq t, sq_abs (Real.cos t), sq_abs (Real.sin t)]

end E62Cert
end ReyesMath
