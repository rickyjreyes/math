import MathProofs.FourierMultiplierL2
import MathProofs.E16TorusRemark

/-!
# E58: the band-selective Green multiplier and its sharp `L²` resolvent norm

Manuscript: `papers/band-selective-green-kernel-bound/main.tex` (issue #38). Throughout `d ≥ 1`,
`r > 0`, `a ≥ 0`, `k⋆ ≥ 0`, and `𝓛 = r + a(Δ + k⋆²)²`. Fourier transforms are the unitary
`Sobolev.FU`; multiplier statements are independent of the normalization constant.

* `E58Cert.Lop58`: `𝓛` on Schwartz space, `𝓛φ = rφ + a(Δ + k⋆²)²φ` (`E58Cert.Lop58_apply`),
  with symbol `ℓ(k) = r + a(|k|² − k⋆²)²` (`E58Cert.FU_Lop58`).
* **Theorem E58** (`E58Cert.theorem_e58`): `0 < G ≤ 1/r`; for `a > 0` equality iff
  `|k| = k⋆`; `sup G = 1/r`; `G ≡ 1/r` for `a = 0`.
* **Proposition (sharp continuum resolvent bound)** (`E58Cert.resolvent`): for every `f ∈ L²`
  there is a unique `u ∈ L²` with `𝓛u = f` in the sense of tempered distributions, namely
  `û = Gf̂`; `‖𝓛⁻¹‖_{L²→L²} = 1/r`; for `a > 0`, `u ∈ H⁴`. The manuscript's near-shell family
  `E_ε` (`E58Cert.near_shell`) witnesses the lower bound `≥ 1/(r + aε²)`.
* **Remark (norm attainment)** (`E58Cert.not_attained`, `E58Cert.attained_of_a_zero`).
* **Energy (coercivity) proof** (`E58Cert.coercivity`):
  `⟨u, 𝓛u⟩ = r‖u‖² + a‖(Δ + k⋆²)u‖² ≥ r‖u‖²` on `H⁴`, hence `‖u‖ ≤ r⁻¹‖𝓛u‖`.
* **Band selectivity** (`E58Cert.band_selectivity`): `G = 1/(r + aδ²)`, `G' < 0` for `δ > 0`,
  strictly decreasing, `G(δ) ~ 1/(aδ²)`.
* **Scope** (`E58Cert.scope`): `r = 0` lets the symbol vanish on the shell; `a < 0` breaks the
  lower bound `ℓ ≥ r` and lets the symbol vanish at a real frequency.
* **Periodic box** (`E58Cert.periodic_box`): on `𝕋_L^d` the resolvent norm is the maximum of `G`
  over the lattice, `≤ 1/r`, with equality for `a > 0` iff a lattice frequency lies on the shell.

The physical-space Green function in `d = 1` (sign change, failure of the pointwise bound, the
distributional identity) is in `MathProofs.E58GreenFunction`.
-/

open Filter Topology Complex InnerProductSpace MeasureTheory Set
open scoped ContDiff FourierTransform ComplexConjugate ENNReal

noncomputable section

namespace ReyesMath
namespace E58Cert

open Sobolev SpectralConc FMult

variable {d : ℕ}

local notation "Rd" => EuclideanSpace ℝ (Fin d)

/-- The symbol `ℓ(k) = r + a(|k|² − k⋆²)²`. -/
def ell (r a ks : ℝ) (k : Rd) : ℝ := r + a * (‖k‖ ^ 2 - ks ^ 2) ^ 2

/-- The Green multiplier `G(k) = 1/ℓ(k)`. -/
def G (r a ks : ℝ) (k : Rd) : ℝ := 1 / ell r a ks k

theorem continuous_ell (r a ks : ℝ) : Continuous (ell (d := d) r a ks) := by
  unfold ell; fun_prop

theorem ell_ge {r a : ℝ} (ha : 0 ≤ a) (ks : ℝ) (k : Rd) : r ≤ ell r a ks k := by
  have := mul_nonneg ha (sq_nonneg (‖k‖ ^ 2 - ks ^ 2)); unfold ell; linarith

theorem ell_pos {r a : ℝ} (hr : 0 < r) (ha : 0 ≤ a) (ks : ℝ) (k : Rd) : 0 < ell r a ks k :=
  lt_of_lt_of_le hr (ell_ge ha ks k)

theorem continuous_G {r a : ℝ} (hr : 0 < r) (ha : 0 ≤ a) (ks : ℝ) : Continuous (G (d := d) r a ks) :=
  continuous_const.div (continuous_ell r a ks) fun k => (ell_pos hr ha ks k).ne'

theorem G_pos {r a : ℝ} (hr : 0 < r) (ha : 0 ≤ a) (ks : ℝ) (k : Rd) : 0 < G r a ks k :=
  one_div_pos.2 (ell_pos hr ha ks k)

theorem G_le {r a : ℝ} (hr : 0 < r) (ha : 0 ≤ a) (ks : ℝ) (k : Rd) : G r a ks k ≤ 1 / r :=
  one_div_le_one_div_of_le hr (ell_ge ha ks k)

theorem G_eq_iff {r a ks : ℝ} (ha : 0 < a) (hks : 0 ≤ ks) (k : Rd) :
    G r a ks k = 1 / r ↔ ‖k‖ = ks := by
  rw [G, one_div, one_div, inv_inj, ell]
  constructor
  · intro h
    have h1 : a * (‖k‖ ^ 2 - ks ^ 2) ^ 2 = 0 := by linarith
    have h2 := (mul_eq_zero.1 h1).resolve_left ha.ne'
    have h3 : ‖k‖ ^ 2 = ks ^ 2 := by linarith [(pow_eq_zero_iff (n := 2) two_ne_zero).1 h2]
    exact (pow_left_inj₀ (norm_nonneg _) hks two_ne_zero).1 h3
  · intro h; rw [h]; ring

/-- A point of the shell `|k| = k⋆` (nonempty for `d ≥ 1`, also when `k⋆ = 0`). -/
theorem exists_shell (hd : 1 ≤ d) {ks : ℝ} (hks : 0 ≤ ks) : ∃ k : Rd, ‖k‖ = ks :=
  ⟨ks • EuclideanSpace.single (⟨0, hd⟩ : Fin d) 1, by
    rw [norm_smul, EuclideanSpace.norm_single, norm_one, mul_one, Real.norm_eq_abs,
      abs_of_nonneg hks]⟩

/-- **Theorem E58** (positive, sharply bounded Green multiplier). -/
theorem theorem_e58 (hd : 1 ≤ d) {r a ks : ℝ} (hr : 0 < r) (ha : 0 ≤ a) (hks : 0 ≤ ks) :
    (∀ k : Rd, 0 < G r a ks k ∧ G r a ks k ≤ 1 / r) ∧
    (0 < a → ∀ k : Rd, (G r a ks k = 1 / r ↔ ‖k‖ = ks)) ∧
    (⨆ k : Rd, G r a ks k) = 1 / r ∧
    (a = 0 → ∀ k : Rd, G r a ks k = 1 / r) := by
  have hzero : a = 0 → ∀ k : Rd, G r a ks k = 1 / r := by
    rintro rfl k; simp [G, ell]
  obtain ⟨k₀, hk₀⟩ := exists_shell hd hks
  have hG₀ : G r a ks k₀ = 1 / r := by simp [G, ell, hk₀]
  refine ⟨fun k => ⟨G_pos hr ha ks k, G_le hr ha ks k⟩, fun ha' k => G_eq_iff ha' hks k, ?_,
    hzero⟩
  exact le_antisymm (ciSup_le fun k => G_le hr ha ks k)
    (hG₀ ▸ le_ciSup ⟨1 / r, by rintro _ ⟨k, rfl⟩; exact G_le hr ha ks k⟩ k₀)

/-! ### The operator on Schwartz space and its symbol -/

/-- `𝓛 = r + a(Δ + k⋆²)²` on Schwartz space (the polynomial operator of `SpectralConc` with
matched coefficients `r + ak⋆⁴`, `−2ak⋆²`, `−a`). -/
def Lop58 (r a ks : ℝ) : SchwartzMap Rd ℂ →L[ℂ] SchwartzMap Rd ℂ :=
  Lop (-2 * a * ks ^ 2) (-a) (r + a * ks ^ 4)

/-- `(Δ + k⋆²)` on Schwartz space. -/
def shiftS (ks : ℝ) : SchwartzMap Rd ℂ →L[ℂ] SchwartzMap Rd ℂ :=
  lapS + ((ks ^ 2 : ℝ) : ℂ) • ContinuousLinearMap.id ℂ _

theorem Lop58_apply (r a ks : ℝ) (φ : SchwartzMap Rd ℂ) :
    Lop58 r a ks φ = (r : ℂ) • φ + (a : ℂ) • shiftS ks (shiftS ks φ) := by
  rw [Lop58, Lop_apply]
  simp only [shiftS, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, map_add, map_smul]
  push_cast
  module

theorem lam_eq_ell (r a ks : ℝ) (ξ : Rd) :
    lam (-2 * a * ks ^ 2) (-a) (r + a * ks ^ 4) ξ = ell r a ks ξ := by
  unfold lam ell; ring

/-- `\widehat{𝓛φ} = ℓ φ̂`. -/
theorem FU_Lop58 (r a ks : ℝ) (φ : SchwartzMap Rd ℂ) :
    (FU (toL2 (Lop58 r a ks φ)) : Rd → ℂ) =ᵐ[volume]
      fun ξ => (ell r a ks ξ : ℂ) * FU (toL2 φ) ξ := by
  have := FU_Lop (-2 * a * ks ^ 2) (-a) (r + a * ks ^ 4) φ
  simpa only [lam_eq_ell] using this

/-- `𝓛u = f` in the sense of tempered distributions: `⟨𝓛φ, u⟩ = ⟨φ, f⟩` for every Schwartz
`φ` (`𝓛` is formally self-adjoint with real coefficients). -/
def Solves (r a ks : ℝ) (u f : L2 d) : Prop :=
  ∀ φ : SchwartzMap Rd ℂ, ⟪toL2 (Lop58 r a ks φ), u⟫_ℂ = ⟪toL2 φ, f⟫_ℂ

theorem solves_iff (r a ks : ℝ) (u f : L2 d) :
    Solves r a ks u f ↔ (fun ξ => (ell r a ks ξ : ℂ) * FU u ξ) =ᵐ[volume] (FU f : Rd → ℂ) := by
  have := isGen_iff (-2 * a * ks ^ 2) (-a) (r + a * ks ^ 4) u f
  simp only [lam_eq_ell] at this
  exact this

/-! ### The resolvent -/

theorem norm_G_le {r a : ℝ} (hr : 0 < r) (ha : 0 ≤ a) (ks : ℝ) (k : Rd) :
    ‖(G r a ks k : ℂ)‖ ≤ 1 / r := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (G_pos hr ha ks k)]; exact G_le hr ha ks k

theorem continuous_Gc {r a : ℝ} (hr : 0 < r) (ha : 0 ≤ a) (ks : ℝ) :
    Continuous fun k : Rd => (G r a ks k : ℂ) :=
  Complex.continuous_ofReal.comp (continuous_G hr ha ks)

/-- The inverse `𝓛⁻¹ = 𝓕⁻¹ M_G 𝓕` on `L²`. -/
def Linv {r a : ℝ} (hr : 0 < r) (ha : 0 ≤ a) (ks : ℝ) : L2 d →L[ℂ] L2 d :=
  fmul (fun k => (G r a ks k : ℂ)) (continuous_Gc hr ha ks).aestronglyMeasurable (norm_G_le hr ha ks)

theorem FU_Linv {r a : ℝ} (hr : 0 < r) (ha : 0 ≤ a) (ks : ℝ) (f : L2 d) :
    (FU (Linv hr ha ks f) : Rd → ℂ) =ᵐ[volume] fun ξ => (G r a ks ξ : ℂ) * FU f ξ :=
  coeFn_FU_fmul _ _ _ f

theorem norm_Linv_apply_sq {r a : ℝ} (hr : 0 < r) (ha : 0 ≤ a) (ks : ℝ) (f : L2 d) :
    ‖Linv hr ha ks f‖ ^ 2 = ∫ ξ, G r a ks ξ ^ 2 * ‖FU f ξ‖ ^ 2 := by
  rw [← norm_FU, SpectralConc.norm_sq_L2]
  refine integral_congr_ae ?_
  filter_upwards [FU_Linv hr ha ks f] with ξ h
  rw [h, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (G_pos hr ha ks ξ), mul_pow]

theorem integrable_G_sq {r a : ℝ} (hr : 0 < r) (ha : 0 ≤ a) (ks : ℝ) (g : L2 d) :
    Integrable fun ξ : Rd => G r a ks ξ ^ 2 * ‖(g : Rd → ℂ) ξ‖ ^ 2 := by
  refine Integrable.mono' ((integrable_norm_sq_L2 g).const_mul ((1 / r) ^ 2))
    (((continuous_G hr ha ks).pow 2).aestronglyMeasurable.mul
      ((Lp.aestronglyMeasurable g).norm.pow 2)) (Eventually.of_forall fun ξ => ?_)
  have h1 := G_pos hr ha ks ξ
  have h2 := G_le hr ha ks ξ
  rw [Real.norm_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h1.le h2 2) (by positivity)

/-- The `H⁴` gain: `(1 + |k|²)² ≤ C ℓ(k)` for `a > 0`. -/
theorem bw_sq_le_ell {r a : ℝ} (hr : 0 < r) (ha : 0 < a) (ks : ℝ) (k : Rd) :
    bw k ^ 2 ≤ (2 / r + 4 / a + 4 * ks ^ 4 / r) * ell r a ks k := by
  have hge : r ≤ ell r a ks k := ell_ge ha.le ks k
  -- `(1 + q)² ≤ 2 + 4(q − k⋆²)² + 4k⋆⁴` with `q = |k|²`
  have h1 : bw k ^ 2 ≤ 2 + 4 * (‖k‖ ^ 2 - ks ^ 2) ^ 2 + 4 * ks ^ 4 := by
    unfold bw; nlinarith [sq_nonneg (‖k‖ ^ 2 - 1), sq_nonneg (‖k‖ ^ 2 - 2 * ks ^ 2)]
  have h2 : 4 * (‖k‖ ^ 2 - ks ^ 2) ^ 2 ≤ 4 / a * ell r a ks k := by
    rw [div_mul_eq_mul_div, le_div_iff₀ ha, ell]; nlinarith
  have h3 : (2 : ℝ) ≤ 2 / r * ell r a ks k := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hr]; linarith
  have h4 : 4 * ks ^ 4 ≤ 4 * ks ^ 4 / r * ell r a ks k := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hr]
    exact mul_le_mul_of_nonneg_left hge (by positivity)
  calc bw k ^ 2 ≤ 2 + 4 * (‖k‖ ^ 2 - ks ^ 2) ^ 2 + 4 * ks ^ 4 := h1
    _ ≤ 2 / r * ell r a ks k + 4 / a * ell r a ks k + 4 * ks ^ 4 / r * ell r a ks k := by
        linarith
    _ = (2 / r + 4 / a + 4 * ks ^ 4 / r) * ell r a ks k := by ring

/-- **Proposition (sharp continuum resolvent bound).** -/
theorem resolvent (hd : 1 ≤ d) {r a ks : ℝ} (hr : 0 < r) (ha : 0 ≤ a) (hks : 0 ≤ ks) :
    (∀ f : L2 d, Solves r a ks (Linv hr ha ks f) f) ∧
    (∀ f u : L2 d, Solves r a ks u f → u = Linv hr ha ks f) ∧
    (∀ f : L2 d, (FU (Linv hr ha ks f) : Rd → ℂ) =ᵐ[volume]
      fun ξ => (G r a ks ξ : ℂ) * FU f ξ) ∧
    ‖Linv (d := d) hr ha ks‖ = 1 / r ∧
    (0 < a → ∀ f : L2 d, InH 2 (Linv hr ha ks f)) := by
  have hex : ∀ f : L2 d, Solves r a ks (Linv hr ha ks f) f := fun f => by
    rw [solves_iff]
    filter_upwards [FU_Linv hr ha ks f] with ξ h
    rw [h, ← mul_assoc, G, ← Complex.ofReal_mul, mul_one_div_cancel (ell_pos hr ha ks ξ).ne',
      Complex.ofReal_one, one_mul]
  refine ⟨hex, fun f u hu => ?_, FU_Linv hr ha ks, ?_, fun ha' f => ?_⟩
  · apply FU.injective
    apply Lp.ext
    have h1 := (solves_iff r a ks u f).1 hu
    filter_upwards [h1, FU_Linv hr ha ks f] with ξ h1 h2
    rw [h2, ← h1, ← mul_assoc, G, ← Complex.ofReal_mul, one_div_mul_cancel
      (ell_pos hr ha ks ξ).ne', Complex.ofReal_one, one_mul]
  · obtain ⟨k₀, hk₀⟩ := exists_shell hd hks
    refine opNorm_fmul_eq_of_attained (continuous_Gc hr ha ks) (norm_G_le hr ha ks)
      (ξ₀ := k₀) ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (G_pos hr ha ks k₀)]
    simp [G, ell, hk₀]
  · -- `(1 + |k|²)² G(k)` is bounded
    set C := 2 / r + 4 / a + 4 * ks ^ 4 / r
    have hb : ∀ k : Rd, ‖((bw k ^ 2 * G r a ks k : ℝ) : ℂ)‖ ≤ C := fun k => by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity)
        (G_pos hr ha ks k).le), G, mul_one_div, div_le_iff₀ (ell_pos hr ha ks k)]
      exact bw_sq_le_ell hr ha' ks k
    have hm : AEStronglyMeasurable (fun k : Rd => ((bw k ^ 2 * G r a ks k : ℝ) : ℂ)) volume :=
      (Complex.continuous_ofReal.comp ((continuous_bw.pow 2).mul
        (continuous_G hr ha ks))).aestronglyMeasurable
    refine (memLp_mul hm hb (FU f)).ae_eq ?_
    filter_upwards [FU_Linv hr ha ks f] with ξ h
    rw [h]; push_cast; ring

/-- The manuscript's explicit near-shell construction: for every `ε > 0` there is a nonzero
`f_ε` with Fourier transform supported in `E_ε = {||k|² − k⋆²| < ε}` and
`‖𝓛⁻¹f_ε‖ ≥ (r + aε²)⁻¹ ‖f_ε‖`. -/
theorem near_shell (hd : 1 ≤ d) {r a ks : ℝ} (hr : 0 < r) (ha : 0 ≤ a) (hks : 0 ≤ ks) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ f : L2 d, f ≠ 0 ∧ (∀ᵐ ξ ∂volume, ε ≤ |‖ξ‖ ^ 2 - ks ^ 2| → FU f ξ = 0) ∧
      1 / (r + a * ε ^ 2) * ‖f‖ ≤ ‖Linv hr ha ks f‖ := by
  set E := {ξ : Rd | |‖ξ‖ ^ 2 - ks ^ 2| < ε}
  have hEo : IsOpen E := isOpen_lt ((continuous_norm.pow 2).sub continuous_const).abs
    continuous_const
  have hEb : E ⊆ Metric.closedBall 0 (Real.sqrt (ks ^ 2 + ε)) := fun ξ hξ => by
    rw [Metric.mem_closedBall, dist_zero_right]
    apply Real.le_sqrt_of_sq_le
    have := (abs_lt.1 (show |‖ξ‖ ^ 2 - ks ^ 2| < ε from hξ)).2; linarith
  have hfin : volume E ≠ ⊤ :=
    ((measure_mono hEb).trans_lt measure_closedBall_lt_top).ne
  obtain ⟨k₀, hk₀⟩ := exists_shell hd hks
  have hk₀E : k₀ ∈ E := by simp [E, hk₀, hε]
  have hpos : 0 < volume E := hEo.measure_pos volume ⟨k₀, hk₀E⟩
  set g := ind E hEo.measurableSet hfin
  refine ⟨FU.symm g, ?_, ?_, ?_⟩
  · intro h
    have : ‖g‖ ^ 2 = 0 := by
      rw [← LinearIsometryEquiv.norm_map FU.symm, h, norm_zero]; ring
    rw [norm_ind_sq] at this
    exact (ENNReal.toReal_pos hpos.ne' hfin).ne' this
  · rw [LinearIsometryEquiv.apply_symm_apply]
    filter_upwards [coeFn_ind E hEo.measurableSet hfin] with ξ h hξ
    rw [h, Set.indicator_of_notMem (show ξ ∉ E from not_lt.2 hξ)]
  · have hgnorm : ‖FU.symm g‖ = ‖g‖ := LinearIsometryEquiv.norm_map _ _
    have hsq : (1 / (r + a * ε ^ 2)) ^ 2 * ‖g‖ ^ 2 ≤ ‖Linv hr ha ks (FU.symm g)‖ ^ 2 := by
      rw [norm_Linv_apply_sq, LinearIsometryEquiv.apply_symm_apply,
        show ‖g‖ ^ 2 = (volume E).toReal from norm_ind_sq E hEo.measurableSet hfin]
      have hint := integrable_G_sq hr ha ks g
      calc (1 / (r + a * ε ^ 2)) ^ 2 * (volume E).toReal
          = ∫ ξ in E, (1 / (r + a * ε ^ 2)) ^ 2 := by
            rw [setIntegral_const, smul_eq_mul, mul_comm]; rfl
        _ ≤ ∫ ξ in E, G r a ks ξ ^ 2 * ‖(g : Rd → ℂ) ξ‖ ^ 2 := by
            refine setIntegral_mono_on_ae (integrableOn_const hfin) hint.integrableOn
              hEo.measurableSet ?_
            filter_upwards [coeFn_ind E hEo.measurableSet hfin] with ξ h hξ
            rw [h, Set.indicator_of_mem hξ, norm_one, one_pow, mul_one]
            refine pow_le_pow_left₀ (by positivity) ?_ 2
            rw [G, ell]
            refine one_div_le_one_div_of_le (ell_pos hr ha ks ξ) ?_
            have h1 : (‖ξ‖ ^ 2 - ks ^ 2) ^ 2 ≤ ε ^ 2 := by
              rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (le_of_lt hξ) 2
            nlinarith
        _ ≤ ∫ ξ, G r a ks ξ ^ 2 * ‖(g : Rd → ℂ) ξ‖ ^ 2 :=
            setIntegral_le_integral hint (Eventually.of_forall fun ξ => by
              show (0 : ℝ) ≤ _; positivity)
    rw [hgnorm]
    have h0 : 0 ≤ 1 / (r + a * ε ^ 2) * ‖g‖ := by
      have : 0 < r + a * ε ^ 2 := by positivity
      positivity
    exact (pow_le_pow_iff_left₀ h0 (norm_nonneg _) two_ne_zero).1 (by rw [mul_pow]; exact hsq)

/-- **Remark (norm attainment), `a > 0`**: no nonzero input attains the norm. -/
theorem not_attained (hd : 1 ≤ d) {r a ks : ℝ} (hr : 0 < r) (ha : 0 < a) (hks : 0 ≤ ks)
    {f : L2 d} (hf : f ≠ 0) : ‖Linv hr ha.le ks f‖ < 1 / r * ‖f‖ := by
  haveI := nontrivial_Rd hd
  have hshell : volume (Metric.sphere (0 : Rd) ks) = 0 := Measure.addHaar_sphere volume 0 ks
  have hlt : ∀ ξ : Rd, ξ ∉ Metric.sphere (0 : Rd) ks → G r a ks ξ < 1 / r := fun ξ hξ =>
    lt_of_le_of_ne (G_le hr ha.le ks ξ) fun h => hξ (by
      rw [mem_sphere_zero_iff_norm]; exact (G_eq_iff ha hks ξ).1 h)
  -- the defect `∫ (r⁻² − G²)|f̂|²` is positive
  set D : Rd → ℝ := fun ξ => ((1 / r) ^ 2 - G r a ks ξ ^ 2) * ‖FU f ξ‖ ^ 2 with hDdef
  have hD0 : ∀ ξ, 0 ≤ D ξ := fun ξ => mul_nonneg (by
    nlinarith [G_le hr ha.le ks ξ, G_pos hr ha.le ks ξ]) (by positivity)
  have hA : Integrable fun ξ : Rd => (1 / r) ^ 2 * ‖(FU f : Rd → ℂ) ξ‖ ^ 2 :=
    (integrable_norm_sq_L2 (FU f)).const_mul _
  have hB := integrable_G_sq hr ha.le ks (FU f)
  have hDi : Integrable D :=
    (hA.sub hB).congr (Eventually.of_forall fun ξ => by
      simp only [hDdef, Pi.sub_apply]; ring)
  have hsupp : 0 < volume (Function.support D) := by
    have hFU : ¬ (FU f : Rd → ℂ) =ᵐ[volume] 0 := fun h => hf (by
      apply FU.injective; rw [map_zero]; exact Lp.ext (h.trans (Lp.coeFn_zero _ _ _).symm))
    have h1 : 0 < volume {ξ : Rd | FU f ξ ≠ 0} := by
      rw [pos_iff_ne_zero]; intro h
      exact hFU (by rw [Filter.EventuallyEq, ae_iff]; simpa using h)
    have h2 : {ξ : Rd | FU f ξ ≠ 0} ⊆ Function.support D ∪ Metric.sphere 0 ks := by
      intro ξ hξ
      by_cases hs : ξ ∈ Metric.sphere (0 : Rd) ks
      · exact Or.inr hs
      · left
        have hG := hlt ξ hs
        have hGp := G_pos hr ha.le ks ξ
        have hpos : (0 : ℝ) < (1 / r) ^ 2 - G r a ks ξ ^ 2 := by nlinarith
        exact mul_ne_zero hpos.ne' (pow_ne_zero 2 (norm_ne_zero_iff.2 hξ))
    have := (measure_mono (μ := volume) h2).trans (measure_union_le _ _)
    rw [hshell, add_zero] at this
    exact lt_of_lt_of_le h1 this
  have hpos : 0 < ∫ ξ, D ξ := (integral_pos_iff_support_of_nonneg hD0 hDi).2 hsupp
  have hnf : ‖f‖ ^ 2 = ∫ ξ, ‖(FU f : Rd → ℂ) ξ‖ ^ 2 := by
    rw [← norm_FU f, SpectralConc.norm_sq_L2]
  have key : ∫ ξ, D ξ = (1 / r * ‖f‖) ^ 2 - ‖Linv hr ha.le ks f‖ ^ 2 := by
    have e1 : ∫ ξ, D ξ = ∫ ξ, ((1 / r) ^ 2 * ‖(FU f : Rd → ℂ) ξ‖ ^ 2 -
        G r a ks ξ ^ 2 * ‖(FU f : Rd → ℂ) ξ‖ ^ 2) := by
      congr 1; funext ξ; simp only [hDdef]; ring
    rw [e1, integral_sub hA hB, integral_const_mul, ← hnf, ← norm_Linv_apply_sq, mul_pow]
  have hsq : ‖Linv hr ha.le ks f‖ ^ 2 < (1 / r * ‖f‖) ^ 2 := by linarith
  exact (pow_lt_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq

/-- **Remark (norm attainment), `a = 0`**: `𝓛⁻¹ = r⁻¹ I`, so every input attains the norm. -/
theorem attained_of_a_zero {r ks : ℝ} (hr : 0 < r) (f : L2 d) :
    Linv hr le_rfl ks f = ((1 / r : ℝ) : ℂ) • f ∧ ‖Linv (d := d) hr le_rfl ks f‖ = 1 / r * ‖f‖ := by
  have h : Linv hr le_rfl ks f = ((1 / r : ℝ) : ℂ) • f := by
    apply FU.injective; apply Lp.ext
    filter_upwards [FU_Linv hr le_rfl ks f, Lp.coeFn_smul ((1 / r : ℝ) : ℂ) (FU f)] with ξ h1 h2
    rw [h1, map_smul, h2, Pi.smul_apply, smul_eq_mul]
    simp [G, ell]
  refine ⟨h, ?_⟩
  rw [h, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]

/-! ### The energy (coercivity) proof on `H⁴` -/

theorem norm_ell_le {r a : ℝ} (hr : 0 < r) (ha : 0 ≤ a) (ks : ℝ) (k : Rd) :
    ‖(ell r a ks k : ℂ)‖ ≤ (r + 2 * a + 2 * a * ks ^ 4) * bw k ^ 2 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (ell_pos hr ha ks k), ell]
  have h1 : (1 : ℝ) ≤ bw k ^ 2 := one_le_pow₀ (one_le_bw k)
  have h2 : (‖k‖ ^ 2 - ks ^ 2) ^ 2 ≤ (2 + 2 * ks ^ 4) * bw k ^ 2 := by
    have : ‖k‖ ^ 2 ≤ bw k := by unfold bw; linarith
    have hb1 : 1 ≤ bw k := one_le_bw k
    nlinarith [sq_nonneg (‖k‖ ^ 2 + ks ^ 2), sq_nonneg ks, pow_nonneg (sq_nonneg ks) 2,
      sq_nonneg (‖k‖ ^ 2)]
  nlinarith [mul_le_mul_of_nonneg_left h2 ha]

theorem norm_shift_le (ks : ℝ) (k : Rd) :
    ‖(((ks ^ 2 - ‖k‖ ^ 2 : ℝ)) : ℂ)‖ ≤ (ks ^ 2 + 1) * bw k ^ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, pow_one]
  unfold bw
  have h0 : 0 ≤ ‖k‖ ^ 2 := by positivity
  rw [abs_le]; constructor <;> nlinarith [sq_nonneg ks]

/-- `𝓛` with domain `H⁴`. -/
def Lh4 {r a : ℝ} (hr : 0 < r) (ha : 0 ≤ a) (ks : ℝ) : L2 d →ₗ.[ℂ] L2 d :=
  pmulOp 2 (fun k => (ell r a ks k : ℂ))
    (Complex.continuous_ofReal.comp (continuous_ell r a ks)).aestronglyMeasurable
    (norm_ell_le hr ha ks)

/-- `(Δ + k⋆²)` with domain `H²`. -/
def shiftH (ks : ℝ) : L2 d →ₗ.[ℂ] L2 d :=
  pmulOp 1 (fun k => ((ks ^ 2 - ‖k‖ ^ 2 : ℝ) : ℂ))
    (Complex.continuous_ofReal.comp (continuous_const.sub (continuous_norm.pow 2))).aestronglyMeasurable
    (norm_shift_le ks)

theorem Lh4_domain {r a : ℝ} (hr : 0 < r) (ha : 0 ≤ a) (ks : ℝ) :
    (Lh4 (d := d) hr ha ks).domain = Hdom 2 := rfl

theorem shiftH_domain (ks : ℝ) : (shiftH (d := d) ks).domain = Hdom 1 := rfl

/-- `H⁴ ⊆ H²`: an element of `D(𝓛)` as an element of `D(Δ + k⋆²)`. -/
def toH2 {r a : ℝ} {hr : 0 < r} {ha : 0 ≤ a} {ks : ℝ} (u : (Lh4 (d := d) hr ha ks).domain) :
    (shiftH (d := d) ks).domain :=
  ⟨u, by
    rw [shiftH_domain, mem_Hdom]
    have h : (u : L2 d) ∈ Hdom 2 := by rw [← Lh4_domain hr ha ks]; exact u.2
    exact inH_mono (j := 1) (k := 2) (by norm_num) (mem_Hdom.1 h)⟩

@[simp] theorem coe_toH2 {r a : ℝ} {hr : 0 < r} {ha : 0 ≤ a} {ks : ℝ}
    (u : (Lh4 (d := d) hr ha ks).domain) : ((toH2 u : (shiftH (d := d) ks).domain) : L2 d) = u :=
  rfl

/-- **Energy proof of the upper estimate**: for `a > 0` and `u ∈ H⁴`,
`⟨u, 𝓛u⟩ = r‖u‖² + a‖(Δ + k⋆²)u‖² ≥ r‖u‖²`, and therefore `‖u‖ ≤ r⁻¹‖𝓛u‖`. -/
theorem coercivity {r a ks : ℝ} (hr : 0 < r) (ha : 0 < a) (u : (Lh4 (d := d) hr ha.le ks).domain) :
    ⟪(u : L2 d), Lh4 hr ha.le ks u⟫_ℂ =
      ((r * ‖(u : L2 d)‖ ^ 2 + a * ‖shiftH ks (toH2 u)‖ ^ 2 : ℝ) : ℂ) ∧
    r * ‖(u : L2 d)‖ ^ 2 ≤ (⟪(u : L2 d), Lh4 hr ha.le ks u⟫_ℂ).re ∧
    ‖(u : L2 d)‖ ≤ ‖Lh4 hr ha.le ks u‖ / r := by
  set u1 : (shiftH (d := d) ks).domain := toH2 u
  have hL : (FU (Lh4 hr ha.le ks u) : Rd → ℂ) =ᵐ[volume]
      fun ξ => (ell r a ks ξ : ℂ) * FU (u : L2 d) ξ :=
    FU_pmulOp 2 _ _ (norm_ell_le hr ha.le ks) u
  have hS : (FU (shiftH ks u1) : Rd → ℂ) =ᵐ[volume]
      fun ξ => ((ks ^ 2 - ‖ξ‖ ^ 2 : ℝ) : ℂ) * FU (u : L2 d) ξ :=
    FU_pmulOp 1 _ _ (norm_shift_le ks) u1
  have hint1 := integrable_norm_sq_L2 (FU (u : L2 d))
  have hS2 : ‖shiftH ks u1‖ ^ 2 = ∫ ξ, (ks ^ 2 - ‖ξ‖ ^ 2) ^ 2 * ‖FU (u : L2 d) ξ‖ ^ 2 := by
    rw [← norm_FU, SpectralConc.norm_sq_L2]
    refine integral_congr_ae ?_
    filter_upwards [hS] with ξ h
    rw [h, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  have hint2 : Integrable fun ξ : Rd => (ks ^ 2 - ‖ξ‖ ^ 2) ^ 2 * ‖FU (u : L2 d) ξ‖ ^ 2 := by
    refine (integrable_norm_sq_L2 (FU (shiftH ks u1))).congr ?_
    filter_upwards [hS] with ξ h
    rw [h, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  have hinner : ⟪(u : L2 d), Lh4 hr ha.le ks u⟫_ℂ =
      ((∫ ξ, ell r a ks ξ * ‖FU (u : L2 d) ξ‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_FU_eq, ← integral_complex_ofReal]
    refine integral_congr_ae ?_
    filter_upwards [hL] with ξ h
    rw [h, mul_left_comm, Complex.conj_mul', ← Complex.ofReal_pow]; push_cast; ring
  have hsplit : ∫ ξ, ell r a ks ξ * ‖FU (u : L2 d) ξ‖ ^ 2 =
      r * ‖(u : L2 d)‖ ^ 2 + a * ‖shiftH ks u1‖ ^ 2 := by
    rw [hS2, ← norm_FU, SpectralConc.norm_sq_L2, ← integral_const_mul, ← integral_const_mul,
      ← integral_add (hint1.const_mul _) (hint2.const_mul _)]
    congr 1; funext ξ; simp only [ell]; ring
  have h1 : ⟪(u : L2 d), Lh4 hr ha.le ks u⟫_ℂ =
      ((r * ‖(u : L2 d)‖ ^ 2 + a * ‖shiftH ks u1‖ ^ 2 : ℝ) : ℂ) := by rw [hinner, hsplit]
  have h2 : r * ‖(u : L2 d)‖ ^ 2 ≤ (⟪(u : L2 d), Lh4 hr ha.le ks u⟫_ℂ).re := by
    rw [h1, Complex.ofReal_re]
    have : 0 ≤ a * ‖shiftH ks u1‖ ^ 2 := by positivity
    linarith
  refine ⟨h1, h2, ?_⟩
  rw [le_div_iff₀ hr]
  by_cases hu : (u : L2 d) = 0
  · rw [hu, norm_zero, zero_mul]; positivity
  · have hpos : 0 < ‖(u : L2 d)‖ := norm_pos_iff.2 hu
    have h3 : (⟪(u : L2 d), Lh4 hr ha.le ks u⟫_ℂ).re ≤ ‖(u : L2 d)‖ * ‖Lh4 hr ha.le ks u‖ :=
      (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
    nlinarith

/-! ### Band selectivity -/

/-- `G` as a function of the detuning `δ = ||k|² − k⋆²|`. -/
def Gdet (r a δ : ℝ) : ℝ := 1 / (r + a * δ ^ 2)

/-- **Band selectivity**: `G(k) = 1/(r + aδ²)`, `dG/dδ = −2aδ/(r + aδ²)² < 0` for `δ > 0`,
strict decrease in the detuning, and `G(δ) ~ 1/(aδ²)` as `δ → ∞`. -/
theorem band_selectivity {r a ks : ℝ} (hr : 0 < r) (ha : 0 < a) :
    (∀ k : Rd, G r a ks k = Gdet r a |‖k‖ ^ 2 - ks ^ 2|) ∧
    (∀ δ : ℝ, HasDerivAt (Gdet r a) (-(2 * a * δ) / (r + a * δ ^ 2) ^ 2) δ) ∧
    (∀ δ : ℝ, 0 < δ → -(2 * a * δ) / (r + a * δ ^ 2) ^ 2 < 0) ∧
    StrictAntiOn (Gdet r a) (Ici 0) ∧
    Tendsto (fun δ => Gdet r a δ * (a * δ ^ 2)) atTop (𝓝 1) := by
  have hden : ∀ δ : ℝ, 0 < r + a * δ ^ 2 := fun δ => by positivity
  refine ⟨fun k => by rw [G, ell, Gdet, sq_abs], fun δ => ?_, fun δ hδ => ?_, ?_, ?_⟩
  · have h := ((hasDerivAt_pow 2 δ).const_mul a).const_add r
    have := (hasDerivAt_const δ (1 : ℝ)).div h (hden δ).ne'
    convert this using 1
    norm_num
    ring
  · have : 0 < 2 * a * δ := by positivity
    exact div_neg_of_neg_of_pos (neg_neg_of_pos this) (pow_pos (hden δ) 2)
  · intro x hx y hy hxy
    simp only [Gdet]
    have hx0 : (0 : ℝ) ≤ x := hx
    exact one_div_lt_one_div_of_lt (hden x)
      (by nlinarith [mul_pos ha (mul_pos (sub_pos.2 hxy) (show (0 : ℝ) < x + y by linarith))])
  · have h1 : Tendsto (fun δ : ℝ => r / (a * δ ^ 2)) atTop (𝓝 0) := by
      have := (tendsto_pow_atTop (two_ne_zero)).const_mul_atTop ha
      exact (tendsto_const_nhds (x := r)).div_atTop this
    have h2 := ((tendsto_const_nhds (x := (1 : ℝ))).add h1).inv₀ (by norm_num : (1 : ℝ) + 0 ≠ 0)
    simp only [add_zero, inv_one] at h2
    refine h2.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with δ hδ
    simp only [Gdet]
    have : a * δ ^ 2 ≠ 0 := by positivity
    field_simp
    ring

/-! ### Scope -/

/-- **Scope**: with `r = 0` (and `a > 0`) the symbol vanishes on the shell; with `a < 0` it is not
bounded below by `r` and vanishes at a real frequency. -/
theorem scope (hd : 1 ≤ d) :
    (∀ a ks : ℝ, 0 ≤ ks → ∃ k : Rd, ell 0 a ks k = 0) ∧
    (∀ r a ks : ℝ, 0 < r → a < 0 → 0 ≤ ks →
      (∃ k : Rd, ell r a ks k < r) ∧ ∃ k : Rd, ell r a ks k = 0) := by
  refine ⟨fun a ks hks => ?_, fun r a ks hr ha hks => ⟨?_, ?_⟩⟩
  · obtain ⟨k, hk⟩ := exists_shell hd hks
    exact ⟨k, by simp [ell, hk]⟩
  · obtain ⟨k, hk⟩ := exists_shell hd (by positivity : (0 : ℝ) ≤ ks + 1)
    refine ⟨k, ?_⟩
    rw [ell, hk]
    have : 0 < ((ks + 1) ^ 2 - ks ^ 2) ^ 2 := by nlinarith
    nlinarith
  · set q := ks ^ 2 + Real.sqrt (r / -a)
    have hq : 0 ≤ q := by positivity
    obtain ⟨k, hk⟩ := exists_shell hd (Real.sqrt_nonneg q)
    refine ⟨k, ?_⟩
    have ha0 : a ≠ 0 := ha.ne
    rw [ell, hk, Real.sq_sqrt hq, show q - ks ^ 2 = Real.sqrt (r / -a) by ring,
      Real.sq_sqrt (div_nonneg hr.le (by linarith))]
    field_simp
    ring

/-! ### The periodic box -/

section Box

variable {L : ℝ}

/-- The symbol at the lattice frequency `ξ_n = (2π/L)n`: `ℓ(ξ_n) = r + a(|ξ_n|² − k⋆²)²`
(`E16Torus.xi2 L n = |ξ_n|²`). -/
def ellT (L r a ks : ℝ) (n : Fin d → ℤ) : ℝ := r + a * (E16Torus.xi2 L n - ks ^ 2) ^ 2

/-- The lattice Green symbol `G(ξ_n) = 1/ℓ(ξ_n)`. -/
def GT (L r a ks : ℝ) (n : Fin d → ℤ) : ℝ := 1 / ellT L r a ks n

theorem ellT_ge {r a : ℝ} (ha : 0 ≤ a) (ks : ℝ) (n : Fin d → ℤ) : r ≤ ellT L r a ks n := by
  have := mul_nonneg ha (sq_nonneg (E16Torus.xi2 L n - ks ^ 2)); unfold ellT; linarith

theorem GT_pos {r a : ℝ} (hr : 0 < r) (ha : 0 ≤ a) (ks : ℝ) (n : Fin d → ℤ) :
    0 < GT L r a ks n :=
  one_div_pos.2 (lt_of_lt_of_le hr (ellT_ge ha ks n))

theorem GT_le {r a : ℝ} (hr : 0 < r) (ha : 0 ≤ a) (ks : ℝ) (n : Fin d → ℤ) :
    GT L r a ks n ≤ 1 / r :=
  one_div_le_one_div_of_le hr (ellT_ge ha ks n)

theorem norm_GT_le {r a : ℝ} (hr : 0 < r) (ha : 0 ≤ a) (ks : ℝ) (n : Fin d → ℤ) :
    ‖(GT L r a ks n : ℂ)‖ ≤ 1 / r := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (GT_pos hr ha ks n)]
  exact GT_le hr ha ks n

variable [hL : Fact (0 < L)]

variable (L) in
/-- The periodic resolvent `𝓛⁻¹` on `L²(𝕋_L^d)`: the Fourier multiplier with symbol
`G(ξ_n)`. -/
def LinvT {r a : ℝ} (hr : 0 < r) (ha : 0 ≤ a) (ks : ℝ) :
    TorusL2.L2 L d →L[ℂ] TorusL2.L2 L d :=
  TorusL2.mult L d (fun n => (GT L r a ks n : ℂ)) (norm_GT_le hr ha ks)

/-- The operator norm of a torus Fourier multiplier is the maximum of its symbol when that
maximum is attained. -/
theorem opNorm_multT {w : (Fin d → ℤ) → ℂ} {C : ℝ} (hw : ∀ k, ‖w k‖ ≤ C) {n₀ : Fin d → ℤ}
    (hmax : ∀ k, ‖w k‖ ≤ ‖w n₀‖) : ‖TorusL2.mult L d w hw‖ = ‖w n₀‖ := by
  apply le_antisymm
  · rw [TorusL2.mult_congr hw hmax fun _ => rfl]
    exact LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _
  · have hb : TorusL2.mult L d w hw (TorusL2.basis L d n₀) = w n₀ • TorusL2.basis L d n₀ := by
      apply TorusL2.ext_coef; intro k
      rw [TorusL2.coef_mult, TorusL2.coef_smul, TorusL2.coef_basis]
      split_ifs with h
      · subst h; ring
      · ring
    have := (TorusL2.mult L d w hw).le_opNorm (TorusL2.basis L d n₀)
    rwa [hb, norm_smul, TorusL2.norm_basis, mul_one, mul_one] at this

/-- **Periodic box.** On `𝕋_L^d` the same pointwise bound holds at every lattice frequency;
the resolvent is the coefficientwise multiplier `û_n = G(ξ_n) f̂_n` (the unique solution of
`ℓ(ξ_n)û_n = f̂_n`); its norm is the maximum of `G` over the lattice, `≤ 1/r`; for `a > 0` it
equals `1/r` iff some lattice frequency lies on the shell `|ξ_n| = k⋆`, and is strictly
smaller otherwise. -/
theorem periodic_box {r a ks : ℝ} (hr : 0 < r) (ha : 0 ≤ a) :
    (∀ n : Fin d → ℤ, 0 < GT L r a ks n ∧ GT L r a ks n ≤ 1 / r) ∧
    (∀ (f : TorusL2.L2 L d) (n : Fin d → ℤ),
      (ellT L r a ks n : ℂ) * TorusL2.coef (LinvT L hr ha ks f) n = TorusL2.coef f n) ∧
    (∀ f u : TorusL2.L2 L d,
      (∀ n, (ellT L r a ks n : ℂ) * TorusL2.coef u n = TorusL2.coef f n) →
        u = LinvT L hr ha ks f) ∧
    (∃ n₀ : Fin d → ℤ, (∀ n : Fin d → ℤ, GT L r a ks n ≤ GT L r a ks n₀) ∧
      ‖LinvT (d := d) L hr ha ks‖ = GT L r a ks n₀) ∧
    ‖LinvT (d := d) L hr ha ks‖ = ⨆ n : Fin d → ℤ, GT L r a ks n ∧
    ‖LinvT (d := d) L hr ha ks‖ ≤ 1 / r ∧
    (0 < a → (‖LinvT (d := d) L hr ha ks‖ = 1 / r ↔
      ∃ n : Fin d → ℤ, E16Torus.xi2 L n = ks ^ 2)) ∧
    (0 < a → (¬ ∃ n : Fin d → ℤ, E16Torus.xi2 L n = ks ^ 2) →
      ‖LinvT (d := d) L hr ha ks‖ < 1 / r) := by
  have hcoef : ∀ (f : TorusL2.L2 L d) n,
      TorusL2.coef (LinvT L hr ha ks f) n = (GT L r a ks n : ℂ) * TorusL2.coef f n :=
    fun f n => TorusL2.coef_mult _ f n
  have hell : ∀ n : Fin d → ℤ, (ellT L r a ks n : ℂ) * (GT L r a ks n : ℂ) = 1 := fun n => by
    rw [GT, ← Complex.ofReal_mul, mul_one_div_cancel
      (lt_of_lt_of_le hr (ellT_ge ha ks n)).ne', Complex.ofReal_one]
  -- the lattice minimum of the symbol
  obtain ⟨n₀, hn₀⟩ : ∃ n₀ : Fin d → ℤ, ∀ n, ellT L r a ks n₀ ≤ ellT L r a ks n := by
    rcases ha.eq_or_lt with h | h
    · exact ⟨0, fun n => by simp [ellT, ← h]⟩
    · have h0 : Tendsto (fun q : ℝ => q - ks ^ 2) atTop atTop :=
        Tendsto.congr (fun q => (sub_eq_add_neg q (ks ^ 2)).symm)
          (tendsto_atTop_add_const_right atTop (-ks ^ 2) tendsto_id)
      have h1 : Tendsto (fun q : ℝ => r + a * (q - ks ^ 2) ^ 2) atTop atTop :=
        tendsto_atTop_add_const_left _ r (((tendsto_pow_atTop two_ne_zero).comp h0).const_mul_atTop h)
      exact (h1.comp (E16Torus.tendsto_xi2 (d := d) (L := L))).exists_forall_le
  have hmax : ∀ n, GT L r a ks n ≤ GT L r a ks n₀ := fun n =>
    one_div_le_one_div_of_le (lt_of_lt_of_le hr (ellT_ge ha ks n₀)) (hn₀ n)
  have hnG : ∀ n : Fin d → ℤ, ‖(GT L r a ks n : ℂ)‖ = GT L r a ks n := fun n => by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (GT_pos hr ha ks n)]
  have hnorm : ‖LinvT (d := d) L hr ha ks‖ = GT L r a ks n₀ := by
    rw [LinvT, opNorm_multT (norm_GT_le hr ha ks) (n₀ := n₀) fun k => by
      rw [hnG, hnG]; exact hmax k, hnG]
  have hsup : (⨆ n : Fin d → ℤ, GT L r a ks n) = GT L r a ks n₀ :=
    le_antisymm (ciSup_le hmax)
      (le_ciSup ⟨1 / r, by rintro _ ⟨n, rfl⟩; exact GT_le hr ha ks n⟩ n₀)
  have hle : ‖LinvT (d := d) L hr ha ks‖ ≤ 1 / r := hnorm ▸ GT_le hr ha ks n₀
  have hiff : 0 < a → (‖LinvT (d := d) L hr ha ks‖ = 1 / r ↔
      ∃ n : Fin d → ℤ, E16Torus.xi2 L n = ks ^ 2) := by
    intro ha'
    rw [hnorm]
    constructor
    · intro h
      refine ⟨n₀, ?_⟩
      have h1 : ellT L r a ks n₀ = r := by
        rw [GT, one_div, one_div, inv_inj] at h; exact h
      have h2 : a * (E16Torus.xi2 L n₀ - ks ^ 2) ^ 2 = 0 := by unfold ellT at h1; linarith
      have h3 := pow_eq_zero_iff (n := 2) two_ne_zero |>.1 ((mul_eq_zero.1 h2).resolve_left ha'.ne')
      linarith
    · rintro ⟨n, hn⟩
      have h1 : GT L r a ks n = 1 / r := by simp [GT, ellT, hn]
      exact le_antisymm (GT_le hr ha ks n₀) (h1 ▸ hmax n)
  refine ⟨fun n => ⟨GT_pos hr ha ks n, GT_le hr ha ks n⟩, fun f n => ?_, fun f u hu => ?_,
    ⟨n₀, hmax, hnorm⟩, hnorm.trans hsup.symm, hle, hiff, fun ha' hno =>
      lt_of_le_of_ne hle fun h => hno ((hiff ha').1 h)⟩
  · rw [hcoef, ← mul_assoc, hell, one_mul]
  · apply TorusL2.ext_coef; intro n
    rw [hcoef, ← hu n, ← mul_assoc, mul_comm (GT L r a ks n : ℂ), hell, one_mul]

end Box

end E58Cert
end ReyesMath
