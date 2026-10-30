import MathProofs.SwiftHohenbergL2
import MathProofs.E57L2Semigroup
import MathProofs.E61Certification

/-!
# M3 + E57: exact spectral shell damping on `L²(ℝ^d)`

Manuscript: `papers/swift-hohenberg-fourier-shell-damping/main.tex` (issue #43). Throughout
`d ≥ 1`, `k⋆ > 0`, `a > 0`, `𝒜 = (Δ + k⋆²)²`, `p(ξ) = (|ξ|² − k⋆²)²` (`SH.psym`), with the
unitary Fourier transform `Sobolev.FU`. The evolution `∂ₜu = −a𝒜u` is the `r = 0` case of
`SH.Lr` (`L₀ = −a𝒜`, `E57Cert.L0_eq`), with semigroup `S(t) = SH.Sr 0`.

* **Theorem (i)** (`E57Cert.part_i`): the natural realisation of `𝒜` is the maximal multiplication
  operator, domain `H⁴` (`1 + p² ≍ (1 + |ξ|²)⁴`, `E57Cert.equivalence`), self-adjoint and
  nonnegative, `⟨u, 𝒜u⟩ = ‖(Δ + k⋆²)u‖²`, form domain `H²`; the symbol on Schwartz functions
  (`E57Cert.symbol_schwartz`, `E57Cert.shellOp_apply`).
* **Main theorem** (`E57Cert.main_theorem`): unique `L²` mild solution `u ∈ C([0,∞); L²)`,
  (ii) `û(t) = e^{−atp}û₀`, (iii) `‖P_δu(t)‖ ≤ e^{−aδ²t}‖P_δu₀‖` (`E57Cert.Pdelta`, an orthogonal
  projection), (iv) strong decay, `‖S(t)‖ = 1`, no uniform exponential rate.
* **The semigroup** (`E57Cert.semigroup`): contraction, semigroup law, strong continuity, and
  generator exactly `−a𝒜` on `H⁴`; the earlier `E57L2Semigroup.S` is the same operator.
* **Positive times** (`E57Cert.smoothing`, `E57Cert.strong_ode`): `p^j û(t) ∈ L²` for every `j`
  (so `u(t) ∈ D(𝒜^j)`, in particular `H⁴`), and `u'(t) = −a𝒜u(t)` strongly for `t > 0`.
* **Corollaries**: `E57Cert.shell_corollary` (exact shell, near-shell expansion),
  `E57Cert.no_shell_state`; **Remark (Fourier mode)**: `E57Cert.plane_wave_not_memLp`.
* **Proposition (monotone quadratic energy)** (`E57Cert.energy_identities`): `dE/dt = −a‖𝒜u‖²`,
  `½ d/dt‖u‖² = −a‖(Δ + k⋆²)u‖²` for `t > 0`, the integrated identity for `t ≥ 0`, and both
  identities at `t = 0` when `u₀ ∈ H⁴`.
* **Remark (gradient-flow convention)** (`E57Cert.gradient`): `∇_ℝE[u] = 𝒜u`.
* **Proposition (discrete shells on a flat torus)** (`E57Cert.periodic`).
* **Proposition (linear threshold)** (`E57Cert.linear_threshold`, from E61) and the **scope remark**
  on sign reversal (`E57Cert.sign_reversal`).
-/

open Filter Topology Complex InnerProductSpace MeasureTheory Set
open scoped ContDiff ComplexConjugate ENNReal

noncomputable section

namespace ReyesMath
namespace E57Cert

open Sobolev SpectralConc FMult SH

variable {d : ℕ}

local notation "Rd" => EuclideanSpace ℝ (Fin d)

/-! ### Theorem (i): the operator `𝒜 = (Δ + k⋆²)²` -/

/-- On Schwartz space `(Δ + k⋆²)² = Δ² + 2k⋆²Δ + k⋆⁴`. -/
theorem shellOp_apply (ks : ℝ) (φ : SchwartzMap Rd ℂ) :
    Lop (-2 * ks ^ 2) (-1) (ks ^ 4) φ =
      lapS (lapS φ) + ((2 * ks ^ 2 : ℝ) : ℂ) • lapS φ + ((ks ^ 4 : ℝ) : ℂ) • φ := by
  rw [Lop_apply]; push_cast; module

/-- **M3, the shell Fourier symbol**, on Schwartz functions:
`\widehat{(Δ + k⋆²)²φ} = (|ξ|² − k⋆²)² φ̂`. -/
theorem symbol_schwartz (ks : ℝ) (φ : SchwartzMap Rd ℂ) :
    (FU (toL2 (Lop (-2 * ks ^ 2) (-1) (ks ^ 4) φ)) : Rd → ℂ) =ᵐ[volume]
      fun ξ => (psym ks ξ : ℂ) * FU (toL2 φ) ξ := by
  filter_upwards [FU_Lop (-2 * ks ^ 2) (-1) (ks ^ 4) φ] with ξ h
  rw [h, lam_eq_psym]

/-- `1 + p² ≍ (1 + |ξ|²)⁴`. -/
theorem equivalence (ks : ℝ) : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ ξ : Rd,
    c * bw ξ ^ 4 ≤ 1 + psym ks ξ ^ 2 ∧ 1 + psym ks ξ ^ 2 ≤ C * bw ξ ^ 4 := by
  set K := 2 + 2 * ks ^ 4
  set K' := 2 * (1 + ks ^ 2) ^ 2
  refine ⟨1 / (8 + 2 * K' ^ 2), 1 + K ^ 2, by positivity, by positivity, fun ξ => ⟨?_, ?_⟩⟩
  · have h1 := bw_sq_le_psym ks ξ
    have hp := psym_nonneg ks ξ
    have hb := (bw_pos ξ).le
    have h2 : bw ξ ^ 4 ≤ (2 * psym ks ξ + K') ^ 2 := by
      rw [show bw ξ ^ 4 = (bw ξ ^ 2) ^ 2 by ring]
      exact pow_le_pow_left₀ (by positivity) h1 2
    have h3 : (2 * psym ks ξ + K') ^ 2 ≤ (8 + 2 * K' ^ 2) * (1 + psym ks ξ ^ 2) := by
      nlinarith [sq_nonneg (2 * psym ks ξ - K'), sq_nonneg (psym ks ξ), sq_nonneg K']
    rw [one_div_mul_eq_div, div_le_iff₀ (by positivity)]
    nlinarith
  · have h1 := psym_le ks ξ
    have hp := psym_nonneg ks ξ
    have h4 : (1 : ℝ) ≤ bw ξ ^ 4 := one_le_pow₀ (one_le_bw ξ)
    have h2 : psym ks ξ ^ 2 ≤ K ^ 2 * bw ξ ^ 4 := by
      calc psym ks ξ ^ 2 ≤ (K * bw ξ ^ 2) ^ 2 := pow_le_pow_left₀ hp h1 2
        _ = K ^ 2 * bw ξ ^ 4 := by ring
    nlinarith

/-- **Theorem (i).** The natural `L²` realisation of `𝒜` is the maximal multiplication operator
with domain `{u : pû ∈ L²} = H⁴`; it is self-adjoint and nonnegative,
`⟨u, 𝒜u⟩ = ∫ p|û|² = ‖(Δ + k⋆²)u‖² ≥ 0`, and its form domain is `H²`. -/
theorem part_i (ks : ℝ) :
    (Aop (d := d) ks).domain = Hdom 2 ∧
    (∀ u : L2 d, InH 2 u ↔ MemLp (fun ξ => (psym ks ξ : ℂ) * FU u ξ) 2 volume) ∧
    (∀ u : (Aop (d := d) ks).domain, (FU (Aop ks u) : Rd → ℂ) =ᵐ[volume]
      fun ξ => (psym ks ξ : ℂ) * FU (u : L2 d) ξ) ∧
    IsSelfAdjoint (Aop (d := d) ks) ∧
    (∀ {u : L2 d} (hu : InH 2 u),
      ⟪u, Aop ks ⟨u, hu⟩⟫_ℂ = ((∫ ξ, psym ks ξ * ‖FU u ξ‖ ^ 2 : ℝ) : ℂ) ∧
      (∫ ξ, psym ks ξ * ‖FU u ξ‖ ^ 2) =
        ‖Bop ks ⟨u, inH_mono (j := 1) (k := 2) (by norm_num) hu⟩‖ ^ 2 ∧
      0 ≤ (⟪u, Aop ks ⟨u, hu⟩⟫_ℂ).re) ∧
    (∀ u : L2 d, InH 1 u ↔ MemLp (fun ξ => ((‖ξ‖ ^ 2 - ks ^ 2 : ℝ) : ℂ) * FU u ξ) 2 volume) :=
  ⟨Aop_domain ks, inH_two_iff ks, FU_Aop ks, Aop_isSelfAdjoint ks, fun hu => inner_Aop ks hu,
    inH_one_iff ks⟩

/-- `L₀ = −a𝒜` on `H⁴`. -/
theorem L0_eq {a : ℝ} (ha : 0 ≤ a) (ks : ℝ) {u : L2 d} (hu : InH 2 u) :
    Lr 0 ha ks ⟨u, hu⟩ = -((a : ℂ) • Aop ks ⟨u, hu⟩) := by
  rw [Lr_eq 0 ha ks hu]; simp

/-! ### The off-shell projection `P_δ` -/

/-- `Ω_δ = {ξ : ||ξ|² − k⋆²| ≥ δ}`. -/
def Omega (ks δ : ℝ) : Set Rd := {ξ | δ ≤ |‖ξ‖ ^ 2 - ks ^ 2|}

theorem measurableSet_Omega (ks δ : ℝ) : MeasurableSet (Omega (d := d) ks δ) :=
  measurableSet_le measurable_const (by fun_prop)

/-- The multiplier `1_{Ω_δ}`. -/
def chiO (ks δ : ℝ) : Rd → ℂ := (Omega ks δ).indicator 1

theorem norm_chiO_le (ks δ : ℝ) (ξ : Rd) : ‖chiO ks δ ξ‖ ≤ 1 := by
  unfold chiO; by_cases h : ξ ∈ Omega ks δ <;> simp [h]

theorem aesm_chiO (ks δ : ℝ) : AEStronglyMeasurable (chiO (d := d) ks δ) volume :=
  (measurable_one.indicator (measurableSet_Omega ks δ)).aestronglyMeasurable

/-- The orthogonal Fourier projection `P_δ = 𝓕⁻¹ 1_{Ω_δ} 𝓕`. -/
def Pdelta (ks δ : ℝ) : L2 d →L[ℂ] L2 d := fmul (chiO ks δ) (aesm_chiO ks δ) (norm_chiO_le ks δ)

theorem FU_Pdelta (ks δ : ℝ) (u : L2 d) :
    (FU (Pdelta ks δ u) : Rd → ℂ) =ᵐ[volume] fun ξ => chiO ks δ ξ * FU u ξ :=
  coeFn_FU_fmul _ _ _ u

/-- `P_δ` is an orthogonal projection: idempotent and self-adjoint. -/
theorem Pdelta_projection (ks δ : ℝ) :
    (Pdelta (d := d) ks δ).comp (Pdelta ks δ) = Pdelta ks δ ∧
    ∀ u v : L2 d, ⟪Pdelta ks δ u, v⟫_ℂ = ⟪u, Pdelta ks δ v⟫_ℂ := by
  refine ⟨?_, fun u v => ?_⟩
  · ext1 u; apply FU.injective; apply Lp.ext
    filter_upwards [FU_Pdelta ks δ (Pdelta ks δ u), FU_Pdelta ks δ u] with ξ h1 h2
    rw [ContinuousLinearMap.comp_apply, h1, h2]
    unfold chiO; by_cases h : ξ ∈ Omega ks δ <;> simp [h]
  · rw [inner_FU_eq, inner_FU_eq]
    apply integral_congr_ae
    filter_upwards [FU_Pdelta ks δ u, FU_Pdelta ks δ v] with ξ h1 h2
    rw [h1, h2]
    unfold chiO; by_cases h : ξ ∈ Omega ks δ <;> simp [h]

/-! ### The semigroup and the main theorem -/

theorem FU_S0 {a : ℝ} (ha : 0 ≤ a) (ks : ℝ) {t : ℝ} (ht : 0 ≤ t) (u₀ : L2 d) :
    (FU (Sr 0 ha ks t u₀) : Rd → ℂ) =ᵐ[volume]
      fun ξ => (Real.exp (-(a * t * psym ks ξ)) : ℂ) * FU u₀ ξ := by
  filter_upwards [FU_Sr 0 ha ks t u₀] with ξ h
  rw [h, esr, max_eq_left ht, lamr]
  congr 3; ring

/-- The earlier operator `E57L2Semigroup.S` (built with the `2π`-normalized transform) is the
semigroup `e^{tL₀}`. -/
theorem e57_eq_Sr {a ks t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) :
    E57L2Semigroup.S (d := d) a ks t ha ht = Sr 0 ha ks t := by
  ext1 f; apply FU.injective; apply Lp.ext
  have hc : (0 : ℝ) < (2 * Real.pi)⁻¹ := inv_pos.2 two_pi_pos'
  have hFf : (FU f : Rd → ℂ) =ᵐ[volume] dilF (2 * Real.pi)⁻¹ (fourierL2 f) := by
    rw [FU_apply]; exact coeFn_dilL2 hc _
  rw [FU_apply (E57L2Semigroup.S a ks t ha ht f)]
  filter_upwards [coeFn_dilL2 hc (fourierL2 (E57L2Semigroup.S a ks t ha ht f)),
    dilF_congr_ae hc (E57L2Semigroup.fourier_S a ks t ha ht f), FU_S0 ha ks ht f, hFf]
    with ξ h1 h2 h3 h4
  rw [h1, h2, h3, h4]
  simp only [dilF, E57WholeSpaceDamping.symbol, RemainingCores.shellDamping,
    RemainingCores.shellSymbol, qS_dil, psym]
  push_cast
  ring

/-- **The contraction semigroup and its generator**: `‖S(t)‖ ≤ 1`, `S(0) = I`,
`S(s+t) = S(s)S(t)`, strong continuity, and the generator is exactly `−a𝒜` with domain `H⁴`. -/
theorem semigroup (hd : 1 ≤ d) {a ks : ℝ} (ha : 0 < a) (hks : 0 < ks) :
    (∀ t, 0 ≤ t → ‖Sr (d := d) 0 ha.le ks t‖ ≤ 1) ∧
    Sr (d := d) 0 ha.le ks 0 = ContinuousLinearMap.id ℂ _ ∧
    (∀ s t, 0 ≤ s → 0 ≤ t →
      Sr (d := d) 0 ha.le ks (s + t) = (Sr 0 ha.le ks s).comp (Sr 0 ha.le ks t)) ∧
    (∀ u : L2 d, Continuous fun t => Sr 0 ha.le ks t u) ∧
    (∀ {u : L2 d} (hu : InH 2 u),
      Tendsto (fun h : ℝ => ((h⁻¹ : ℝ) : ℂ) • (Sr 0 ha.le ks h u - u)) (𝓝[>] 0)
        (𝓝 (-((a : ℂ) • Aop ks ⟨u, hu⟩)))) ∧
    (∀ {u w : L2 d}, Tendsto (fun h : ℝ => ((h⁻¹ : ℝ) : ℂ) • (Sr 0 ha.le ks h u - u)) (𝓝[>] 0)
        (𝓝 w) → ∃ hu : InH 2 u, w = -((a : ℂ) • Aop ks ⟨u, hu⟩)) ∧
    (∀ t (ht : 0 ≤ t), E57L2Semigroup.S (d := d) a ks t ha.le ht = Sr 0 ha.le ks t) := by
  refine ⟨fun t ht => by rw [opNorm_Sr hd ha.le hks.le ht, zero_mul, Real.exp_zero],
    Sr_zero 0 ha.le ks, fun s t hs ht => Sr_add 0 ha.le ks hs ht, continuous_Sr ha hks,
    fun hu => ?_, fun h => ?_, fun t ht => e57_eq_Sr ha.le ht⟩
  · rw [← L0_eq ha.le ks hu]; exact generator ha.le hu
  · obtain ⟨hu, hw⟩ := generator_domain ha h
    exact ⟨hu, by rw [← hw, L0_eq ha.le ks hu]⟩

/-- **Theorem (M3 + E57).** For every `u₀ ∈ L²`, `∂ₜu = −a(Δ + k⋆²)²u` has a unique `L²` mild
solution `u ∈ C([0,∞); L²)`, namely `u(t) = S(t)u₀`, and:
(ii) `û(t) = e^{−atp}û₀` a.e.; (iii) `‖P_δu(t)‖ ≤ e^{−aδ²t}‖P_δu₀‖` for `δ > 0`;
(iv) `‖u(t)‖ → 0`, while `‖S(t)‖ = 1` for every `t ≥ 0` (no uniform exponential rate). -/
theorem main_theorem (hd : 1 ≤ d) {a ks : ℝ} (ha : 0 < a) (hks : 0 < ks) (u₀ : L2 d) :
    IsMildSH 0 ha.le ks u₀ (fun t => Sr 0 ha.le ks t u₀) ∧
    (∀ u : ℝ → L2 d, IsMildSH 0 ha.le ks u₀ u → ∀ t, 0 ≤ t → u t = Sr 0 ha.le ks t u₀) ∧
    ContinuousOn (fun t => Sr 0 ha.le ks t u₀) (Ici 0) ∧
    (∀ t, 0 ≤ t → (FU (Sr 0 ha.le ks t u₀) : Rd → ℂ) =ᵐ[volume]
      fun ξ => (Real.exp (-(a * t * psym ks ξ)) : ℂ) * FU u₀ ξ) ∧
    (∀ δ : ℝ, 0 < δ → ∀ t, 0 ≤ t →
      ‖Pdelta ks δ (Sr 0 ha.le ks t u₀)‖ ≤ Real.exp (-(a * δ ^ 2 * t)) * ‖Pdelta ks δ u₀‖) ∧
    Tendsto (fun t => ‖Sr 0 ha.le ks t u₀‖) atTop (𝓝 0) ∧
    (∀ t, 0 ≤ t → ‖Sr (d := d) 0 ha.le ks t‖ = 1) ∧
    ¬ ∃ C c : ℝ, 0 < c ∧ ∀ t, 0 ≤ t → ‖Sr (d := d) 0 ha.le ks t‖ ≤ C * Real.exp (-(c * t)) := by
  obtain ⟨hmild, huniq⟩ := mild_iff (r := 0) ha hks u₀
  obtain ⟨hdecay, hnorm, hnounif, -⟩ := E61Cert.critical hd ha hks
  refine ⟨hmild, huniq, (continuous_Sr ha hks u₀).continuousOn, fun t ht => FU_S0 ha.le ks ht u₀,
    fun δ hδ t ht => ?_, hdecay u₀ _ hmild, hnorm, hnounif⟩
  -- the off-shell estimate
  have key : ‖Pdelta ks δ (Sr 0 ha.le ks t u₀)‖ ^ 2 ≤
      (Real.exp (-(a * δ ^ 2 * t)) * ‖Pdelta ks δ u₀‖) ^ 2 := by
    rw [← norm_FU, SpectralConc.norm_sq_L2, mul_pow, ← norm_FU (Pdelta ks δ u₀),
      SpectralConc.norm_sq_L2, ← integral_const_mul]
    refine integral_mono_ae (integrable_norm_sq_L2 _) ((integrable_norm_sq_L2 _).const_mul _) ?_
    filter_upwards [FU_Pdelta ks δ (Sr 0 ha.le ks t u₀), FU_S0 ha.le ks ht u₀,
      FU_Pdelta ks δ u₀] with ξ h1 h2 h3
    rw [h1, h2, h3]
    unfold chiO
    by_cases hm : ξ ∈ Omega ks δ
    · simp only [Set.indicator_of_mem hm, Pi.one_apply, one_mul, norm_mul, mul_pow,
        Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
      apply Real.exp_le_exp.2
      have hp : δ ^ 2 ≤ psym ks ξ := by
        have h4 : δ ≤ |‖ξ‖ ^ 2 - ks ^ 2| := hm
        unfold psym
        calc δ ^ 2 ≤ |‖ξ‖ ^ 2 - ks ^ 2| ^ 2 := pow_le_pow_left₀ hδ.le h4 2
          _ = (‖ξ‖ ^ 2 - ks ^ 2) ^ 2 := sq_abs _
      push_cast
      nlinarith [mul_le_mul_of_nonneg_left hp (mul_nonneg ha.le ht)]
    · simp [Set.indicator_of_notMem hm]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 key

/-! ### Corollaries -/

/-- **Corollary (exact preferred shell and near-shell expansion).** The damping exponent
`λ = −ap` is nonpositive, vanishes exactly on `|ξ| = k⋆`, and with `|ξ| = k⋆ + h`,
`p = (2k⋆h + h²)² = 4k⋆²h² + 4k⋆h³ + h⁴`. -/
theorem shell_corollary {a ks : ℝ} (ha : 0 < a) (hks : 0 ≤ ks) :
    (∀ ξ : Rd, -(a * psym ks ξ) ≤ 0) ∧
    (∀ ξ : Rd, -(a * psym ks ξ) = 0 ↔ ‖ξ‖ = ks) ∧
    (∀ ξ : Rd, psym ks ξ = (2 * ks * (‖ξ‖ - ks) + (‖ξ‖ - ks) ^ 2) ^ 2) ∧
    (∀ h : ℝ, (2 * ks * h + h ^ 2) ^ 2 = 4 * ks ^ 2 * h ^ 2 + 4 * ks * h ^ 3 + h ^ 4) := by
  refine ⟨fun ξ => by nlinarith [mul_nonneg ha.le (psym_nonneg ks ξ)], fun ξ => ?_,
    fun ξ => by unfold psym; ring, fun h => by ring⟩
  rw [← psym_eq_zero_iff hks, neg_eq_zero]
  constructor
  · intro h; exact (mul_eq_zero.1 h).resolve_left ha.ne'
  · intro h; rw [h, mul_zero]

/-- **Corollary (no nonzero exact-shell `L²` state).** -/
theorem no_shell_state (hd : 1 ≤ d) (ks : ℝ) (u : L2 d)
    (h : ∀ᵐ ξ ∂volume, ξ ∉ Metric.sphere (0 : Rd) ks → (FU u : Rd → ℂ) ξ = 0) : u = 0 :=
  Sobolev.shell_theorem hd ks u h

/-- **Remark (meaning of a Fourier mode)**: a plane wave of fixed frequency is not in `L²(ℝ^d)`. -/
theorem plane_wave_not_memLp (hd : 1 ≤ d) (k : Rd) :
    ¬ MemLp (fun x : Rd => Complex.exp (((inner ℝ k x : ℝ) : ℂ) * Complex.I)) 2 volume := by
  haveI := nontrivial_Rd hd
  intro h
  have hn : MemLp (fun x : Rd => ‖Complex.exp (((inner ℝ k x : ℝ) : ℂ) * Complex.I)‖) 2 volume :=
    h.norm
  have h1 : (fun x : Rd => ‖Complex.exp (((inner ℝ k x : ℝ) : ℂ) * Complex.I)‖) = fun _ => (1 : ℝ) :=
    funext fun x => Complex.norm_exp_ofReal_mul_I _
  rw [h1, memLp_const_iff two_ne_zero ENNReal.ofNat_ne_top] at hn
  rcases hn with h0 | hfin
  · exact one_ne_zero h0
  · rw [measure_univ_of_isAddLeftInvariant] at hfin
    exact lt_irrefl _ hfin


/-! ### Smoothing and the strong equation at positive times -/

/-- `x^j e^{−cx} ≤ j!/c^j` for `x ≥ 0`, `c > 0`. -/
theorem pow_mul_exp_neg_le {x c : ℝ} (hx : 0 ≤ x) (hc : 0 < c) (j : ℕ) :
    x ^ j * Real.exp (-(c * x)) ≤ j.factorial / c ^ j := by
  have h := Real.pow_div_factorial_le_exp (c * x) (mul_nonneg hc.le hx) j
  have hf : (0 : ℝ) < j.factorial := by exact_mod_cast Nat.factorial_pos j
  rw [div_le_iff₀ hf, mul_pow] at h
  rw [le_div_iff₀ (by positivity), Real.exp_neg]
  have he := Real.exp_pos (c * x)
  calc x ^ j * (Real.exp (c * x))⁻¹ * c ^ j = (c ^ j * x ^ j) * (Real.exp (c * x))⁻¹ := by ring
    _ ≤ (Real.exp (c * x) * j.factorial) * (Real.exp (c * x))⁻¹ :=
        mul_le_mul_of_nonneg_right h (inv_nonneg.2 he.le)
    _ = j.factorial := by field_simp

/-- **Smoothing**: for `t > 0` and every `j`, `p^j û(t) ∈ L²`, i.e. `u(t) ∈ D(𝒜^j)`; in
particular `u(t) ∈ H⁴`. -/
theorem smoothing {a ks : ℝ} (ha : 0 < a) {t : ℝ} (ht : 0 < t) (u₀ : L2 d) (j : ℕ) :
    MemLp (fun ξ => (psym ks ξ : ℂ) ^ j * FU (Sr 0 ha.le ks t u₀) ξ) 2 volume := by
  have hm : AEStronglyMeasurable
      (fun ξ : Rd => ((psym ks ξ ^ j * Real.exp (-(a * t * psym ks ξ)) : ℝ) : ℂ)) volume :=
    (Complex.continuous_ofReal.comp (((continuous_psym ks).pow j).mul
      (Real.continuous_exp.comp (continuous_const.mul (continuous_psym ks)).neg))).aestronglyMeasurable
  have hb : ∀ ξ : Rd, ‖((psym ks ξ ^ j * Real.exp (-(a * t * psym ks ξ)) : ℝ) : ℂ)‖ ≤
      j.factorial / (a * t) ^ j := fun ξ => by
    rw [Complex.norm_real, Real.norm_of_nonneg (by have := psym_nonneg ks ξ; positivity)]
    exact pow_mul_exp_neg_le (psym_nonneg ks ξ) (mul_pos ha ht) j
  refine (memLp_mul hm hb (FU u₀)).ae_eq ?_
  filter_upwards [FU_S0 ha.le ks ht.le u₀] with ξ h
  rw [h]; push_cast; ring

theorem inH_of_pos {a ks : ℝ} (ha : 0 < a) {t : ℝ} (ht : 0 < t) (u₀ : L2 d) :
    InH 2 (Sr 0 ha.le ks t u₀) :=
  (inH_two_iff ks _).2 (by simpa using smoothing (ks := ks) ha ht u₀ 1)

/-- `|eˣ − eʸ| ≤ |x − y| e^{max x y}`. -/
theorem abs_exp_sub_exp_le (x y : ℝ) :
    |Real.exp x - Real.exp y| ≤ |x - y| * Real.exp (max x y) := by
  have h := abs_exp_sub_one_le' (x - y)
  have e : Real.exp x - Real.exp y = Real.exp y * (Real.exp (x - y) - 1) := by
    rw [mul_sub, ← Real.exp_add]; ring_nf
  have hm : y + max (x - y) 0 = max x y := by
    rcases le_total y x with hxy | hxy
    · rw [max_eq_left (by linarith), max_eq_left hxy]; ring
    · rw [max_eq_right (by linarith), max_eq_right hxy]; ring
  rw [e, abs_mul, abs_of_pos (Real.exp_pos y), ← hm, Real.exp_add]
  calc Real.exp y * |Real.exp (x - y) - 1|
      ≤ Real.exp y * (|x - y| * Real.exp (max (x - y) 0)) :=
        mul_le_mul_of_nonneg_left h (Real.exp_pos y).le
    _ = |x - y| * (Real.exp y * Real.exp (max (x - y) 0)) := by ring

/-- `x e^{−x} ≤ 1` for `x ≥ 0`. -/
theorem mul_exp_neg_le_one {x : ℝ} (hx : 0 ≤ x) : x * Real.exp (-x) ≤ 1 := by
  have := pow_mul_exp_neg_le (c := 1) hx one_pos 1
  simpa using this

/-- The difference quotient of `s ↦ e^{−asp}` at `t`, minus its derivative `−ap e^{−atp}`. -/
def dq (a ks t s : ℝ) (ξ : Rd) : ℝ :=
  (Real.exp (-(a * s * psym ks ξ)) - Real.exp (-(a * t * psym ks ξ))) / (s - t) +
    a * psym ks ξ * Real.exp (-(a * t * psym ks ξ))

theorem continuous_dq (a ks t s : ℝ) : Continuous (dq (d := d) a ks t s) := by
  have := continuous_psym (d := d) ks
  unfold dq; fun_prop

theorem dq_bound {a ks t s : ℝ} (ha : 0 < a) (ht : 0 < t) (hs : t / 2 < s) (hst : s ≠ t)
    (ξ : Rd) : |dq a ks t s ξ| ≤ 3 / t := by
  have hp := psym_nonneg ks ξ
  have hap : 0 ≤ a * psym ks ξ := mul_nonneg ha.le hp
  have hst' : s - t ≠ 0 := sub_ne_zero.2 hst
  have e1 : |(Real.exp (-(a * s * psym ks ξ)) - Real.exp (-(a * t * psym ks ξ))) / (s - t)| ≤
      2 / t := by
    rw [abs_div, div_le_iff₀ (abs_pos.2 hst')]
    have h := abs_exp_sub_exp_le (-(a * s * psym ks ξ)) (-(a * t * psym ks ξ))
    have hmax : max (-(a * s * psym ks ξ)) (-(a * t * psym ks ξ)) ≤
        -(t / 2 * (a * psym ks ξ)) := by
      apply max_le <;> nlinarith
    have h2 : (a * psym ks ξ) * Real.exp (-(t / 2 * (a * psym ks ξ))) ≤ 2 / t := by
      have := mul_exp_neg_le_one (mul_nonneg (by linarith : (0 : ℝ) ≤ t / 2) hap)
      rw [le_div_iff₀ ht]
      nlinarith [Real.exp_pos (-(t / 2 * (a * psym ks ξ)))]
    have h3 : |-(a * s * psym ks ξ) - -(a * t * psym ks ξ)| = a * psym ks ξ * |s - t| := by
      rw [show -(a * s * psym ks ξ) - -(a * t * psym ks ξ) = (a * psym ks ξ) * -(s - t) by ring,
        abs_mul, abs_neg, abs_of_nonneg hap]
    calc |Real.exp (-(a * s * psym ks ξ)) - Real.exp (-(a * t * psym ks ξ))|
        ≤ (a * psym ks ξ * |s - t|) * Real.exp (-(t / 2 * (a * psym ks ξ))) := by
          rw [← h3]
          exact h.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hmax) (abs_nonneg _))
      _ = (a * psym ks ξ) * Real.exp (-(t / 2 * (a * psym ks ξ))) * |s - t| := by ring
      _ ≤ 2 / t * |s - t| := mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
  have e2 : |a * psym ks ξ * Real.exp (-(a * t * psym ks ξ))| ≤ 1 / t := by
    rw [abs_of_nonneg (by positivity), le_div_iff₀ ht]
    have := mul_exp_neg_le_one (mul_nonneg ht.le hap)
    calc a * psym ks ξ * Real.exp (-(a * t * psym ks ξ)) * t
        = t * (a * psym ks ξ) * Real.exp (-(t * (a * psym ks ξ))) := by ring_nf
      _ ≤ 1 := this
  unfold dq
  calc _ ≤ |(Real.exp (-(a * s * psym ks ξ)) - Real.exp (-(a * t * psym ks ξ))) / (s - t)| +
        |a * psym ks ξ * Real.exp (-(a * t * psym ks ξ))| := abs_add _ _
    _ ≤ 2 / t + 1 / t := add_le_add e1 e2
    _ = 3 / t := by ring

theorem tendsto_dq (a ks t : ℝ) (ξ : Rd) :
    Tendsto (fun s => dq a ks t s ξ) (𝓝[≠] t) (𝓝 0) := by
  have hd : HasDerivAt (fun s : ℝ => Real.exp (-(a * s * psym ks ξ)))
      (Real.exp (-(a * t * psym ks ξ)) * -(a * psym ks ξ)) t := by
    have := ((hasDerivAt_id t).const_mul (-(a * psym ks ξ))).exp
    convert this using 1
    · funext s; simp only [id]; ring_nf
    · simp only [id]; ring_nf
  have hs := (hasDerivAt_iff_tendsto_slope.1 hd).add_const
    (a * psym ks ξ * Real.exp (-(a * t * psym ks ξ)))
  have h0 : Real.exp (-(a * t * psym ks ξ)) * -(a * psym ks ξ) +
      a * psym ks ξ * Real.exp (-(a * t * psym ks ξ)) = 0 := by ring
  rw [h0] at hs
  refine hs.congr' (eventually_nhdsWithin_of_forall fun s _ => ?_)
  simp only [dq, slope_def_field]

/-- **The strong equation at positive times**: for `t > 0`, `u(t) ∈ H⁴` and
`u'(t) = −a𝒜u(t)` in `L²`. -/
theorem strong_ode {a ks : ℝ} (ha : 0 < a) {t : ℝ} (ht : 0 < t) (u₀ : L2 d) :
    HasDerivAt (fun s => Sr 0 ha.le ks s u₀)
      (-((a : ℂ) • Aop ks ⟨Sr 0 ha.le ks t u₀, inH_of_pos ha ht u₀⟩)) t := by
  set w := -((a : ℂ) • Aop ks ⟨Sr 0 ha.le ks t u₀, inH_of_pos ha ht u₀⟩) with hw_def
  have hw : (FU w : Rd → ℂ) =ᵐ[volume] fun ξ =>
      ((-(a * psym ks ξ * Real.exp (-(a * t * psym ks ξ))) : ℝ) : ℂ) * FU u₀ ξ := by
    rw [hw_def, map_neg, map_smul]
    filter_upwards [FU_Aop ks ⟨Sr 0 ha.le ks t u₀, inH_of_pos ha ht u₀⟩,
      Lp.coeFn_neg ((a : ℂ) • FU (Aop ks ⟨Sr 0 ha.le ks t u₀, inH_of_pos ha ht u₀⟩)),
      Lp.coeFn_smul (a : ℂ) (FU (Aop ks ⟨Sr 0 ha.le ks t u₀, inH_of_pos ha ht u₀⟩)),
      FU_S0 ha.le ks ht.le u₀] with ξ h1 h2 h3 h4
    rw [h2, Pi.neg_apply, h3, Pi.smul_apply, h1, smul_eq_mul]
    change -((a : ℂ) * ((psym ks ξ : ℂ) * (FU (Sr 0 ha.le ks t u₀) : Rd → ℂ) ξ)) = _
    rw [h4]; push_cast; ring
  have hsq : ∀ s : ℝ, 0 ≤ s → ‖slope (fun s => Sr 0 ha.le ks s u₀) t s - w‖ ^ 2 =
      ∫ ξ, dq a ks t s ξ ^ 2 * ‖FU u₀ ξ‖ ^ 2 := by
    intro s hs
    rw [slope_def_module, ← Complex.coe_smul, ← norm_FU, SpectralConc.norm_sq_L2]
    refine integral_congr_ae ?_
    rw [map_sub, map_smul, map_sub]
    filter_upwards [FU_S0 ha.le ks hs u₀, FU_S0 ha.le ks ht.le u₀, hw,
      Lp.coeFn_sub ((((s - t)⁻¹ : ℝ) : ℂ) • (FU (Sr 0 ha.le ks s u₀) - FU (Sr 0 ha.le ks t u₀)))
        (FU w),
      Lp.coeFn_smul (((s - t)⁻¹ : ℝ) : ℂ) (FU (Sr 0 ha.le ks s u₀) - FU (Sr 0 ha.le ks t u₀)),
      Lp.coeFn_sub (FU (Sr 0 ha.le ks s u₀)) (FU (Sr 0 ha.le ks t u₀))] with ξ h1 h2 h3 h4 h5 h6
    rw [h4, Pi.sub_apply, h5, Pi.smul_apply, h6, Pi.sub_apply, h1, h2, h3, smul_eq_mul]
    rw [show (((s - t)⁻¹ : ℝ) : ℂ) * ((Real.exp (-(a * s * psym ks ξ)) : ℂ) * FU u₀ ξ -
        (Real.exp (-(a * t * psym ks ξ)) : ℂ) * FU u₀ ξ) -
        ((-(a * psym ks ξ * Real.exp (-(a * t * psym ks ξ))) : ℝ) : ℂ) * FU u₀ ξ =
        (dq a ks t s ξ : ℂ) * FU u₀ ξ by
      simp only [dq]; push_cast; ring]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  have hlim : Tendsto (fun s => ∫ ξ, dq a ks t s ξ ^ 2 * ‖FU u₀ ξ‖ ^ 2) (𝓝[≠] t) (𝓝 0) := by
    have := tendsto_integral_filter_of_dominated_convergence (l := 𝓝[≠] t)
      (F := fun s ξ => dq a ks t s ξ ^ 2 * ‖FU u₀ ξ‖ ^ 2) (f := fun _ => (0 : ℝ))
      (fun ξ => (3 / t) ^ 2 * ‖FU u₀ ξ‖ ^ 2)
      (Eventually.of_forall fun s => ((continuous_dq a ks t s).pow 2).aestronglyMeasurable.mul
        ((Lp.aestronglyMeasurable (FU u₀)).norm.pow 2)) ?_
      ((integrable_norm_sq_L2 _).const_mul _) ?_
    · simpa using this
    · have hball : Ioi (t / 2) ∈ 𝓝 t := Ioi_mem_nhds (by linarith)
      filter_upwards [nhdsWithin_le_nhds hball, self_mem_nhdsWithin] with s hs (hst : s ≠ t)
      refine Eventually.of_forall fun ξ => ?_
      rw [Real.norm_of_nonneg (by positivity)]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (dq_bound ha ht hs hst ξ) 2
    · refine Eventually.of_forall fun ξ => ?_
      have := ((tendsto_dq a ks t ξ).pow 2).mul_const (‖FU u₀ ξ‖ ^ 2)
      simpa using this
  have h2 : Tendsto (fun s => ‖slope (fun s => Sr 0 ha.le ks s u₀) t s - w‖ ^ 2) (𝓝[≠] t)
      (𝓝 0) := by
    refine hlim.congr' ?_
    filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds ht)] with s hs
    exact (hsq s (le_of_lt hs)).symm
  rw [hasDerivAt_iff_tendsto_slope, tendsto_iff_norm_sub_tendsto_zero]
  have h3 := h2.sqrt
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using h3


/-! ### Energy-dissipation identities -/

/-- `G_j(s) = ∫ p^j e^{−2asp}|û₀|²`; `G₀(s) = ‖u(s)‖²`, `G₁(s) = ‖(Δ + k⋆²)u(s)‖²`,
`G₂(s) = ‖𝒜u(s)‖²` (`E57Cert.G_zero`, `E57Cert.G_one`, `E57Cert.G_two`). -/
def G (a ks : ℝ) (u₀ : L2 d) (j : ℕ) (s : ℝ) : ℝ :=
  ∫ ξ, psym ks ξ ^ j * Real.exp (-(2 * a * s * psym ks ξ)) * ‖FU u₀ ξ‖ ^ 2

theorem aesm_Gint (a ks : ℝ) (u₀ : L2 d) (j : ℕ) (s : ℝ) :
    AEStronglyMeasurable (fun ξ : Rd =>
      psym ks ξ ^ j * Real.exp (-(2 * a * s * psym ks ξ)) * ‖FU u₀ ξ‖ ^ 2) volume :=
  (((continuous_psym ks).pow j).mul (Real.continuous_exp.comp
    (continuous_const.mul (continuous_psym ks)).neg)).aestronglyMeasurable.mul
    ((Lp.aestronglyMeasurable (FU u₀)).norm.pow 2)

/-- For `s > 0` the integrand of `G_j(s)` is dominated by `j!/(2as)^j |û₀|²`. -/
theorem Gint_le {a ks : ℝ} (ha : 0 < a) (u₀ : L2 d) (j : ℕ) {s : ℝ} (hs : 0 < s) (ξ : Rd) :
    psym ks ξ ^ j * Real.exp (-(2 * a * s * psym ks ξ)) * ‖FU u₀ ξ‖ ^ 2 ≤
      j.factorial / (2 * a * s) ^ j * ‖FU u₀ ξ‖ ^ 2 :=
  mul_le_mul_of_nonneg_right (by
    have := pow_mul_exp_neg_le (psym_nonneg ks ξ) (by positivity : 0 < 2 * a * s) j
    simpa [mul_assoc] using this) (by positivity)

theorem integrable_Gint {a ks : ℝ} (ha : 0 < a) (u₀ : L2 d) (j : ℕ) {s : ℝ} (hs : 0 < s) :
    Integrable fun ξ : Rd =>
      psym ks ξ ^ j * Real.exp (-(2 * a * s * psym ks ξ)) * ‖FU u₀ ξ‖ ^ 2 := by
  refine Integrable.mono' ((integrable_norm_sq_L2 (FU u₀)).const_mul
    (j.factorial / (2 * a * s) ^ j)) (aesm_Gint a ks u₀ j s) (Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_of_nonneg (by have := psym_nonneg ks ξ; positivity)]
  exact Gint_le ha u₀ j hs ξ

/-- `d/ds G_j(s) = −2a G_{j+1}(s)` for `s > 0`. -/
theorem hasDerivAt_G {a ks : ℝ} (ha : 0 < a) (u₀ : L2 d) (j : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (G a ks u₀ j) (-(2 * a) * G a ks u₀ (j + 1) t) t := by
  have hbound : ∀ ξ : Rd, ∀ s ∈ Metric.ball t (t / 2),
      ‖-(2 * a) * psym ks ξ ^ (j + 1) * Real.exp (-(2 * a * s * psym ks ξ)) * ‖FU u₀ ξ‖ ^ 2‖ ≤
        2 * a * ((j + 1).factorial / (a * t) ^ (j + 1)) * ‖FU u₀ ξ‖ ^ 2 := by
    intro ξ s hs
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hs
    have hp := psym_nonneg ks ξ
    have h1 : Real.exp (-(2 * a * s * psym ks ξ)) ≤ Real.exp (-(a * t * psym ks ξ)) :=
      Real.exp_le_exp.2 (by nlinarith [mul_nonneg ha.le hp])
    have h2 := pow_mul_exp_neg_le hp (mul_pos ha ht) (j + 1)
    rw [show -(a * t * psym ks ξ) = -((a * t) * psym ks ξ) by ring] at h1
    rw [norm_mul, norm_mul, norm_mul, Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ ‖FU u₀ ξ‖ ^ 2),
      norm_neg, Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ 2 * a),
      Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (Real.exp_pos _).le]
    have h3 : psym ks ξ ^ (j + 1) * Real.exp (-(2 * a * s * psym ks ξ)) ≤
        (j + 1).factorial / (a * t) ^ (j + 1) :=
      (mul_le_mul_of_nonneg_left h1 (by positivity)).trans h2
    calc 2 * a * psym ks ξ ^ (j + 1) * Real.exp (-(2 * a * s * psym ks ξ)) * ‖FU u₀ ξ‖ ^ 2
        = 2 * a * (psym ks ξ ^ (j + 1) * Real.exp (-(2 * a * s * psym ks ξ))) *
            ‖FU u₀ ξ‖ ^ 2 := by ring
      _ ≤ 2 * a * ((j + 1).factorial / (a * t) ^ (j + 1)) * ‖FU u₀ ξ‖ ^ 2 := by gcongr
  have hdiff : ∀ ξ : Rd, ∀ s ∈ Metric.ball t (t / 2),
      HasDerivAt (fun s => psym ks ξ ^ j * Real.exp (-(2 * a * s * psym ks ξ)) * ‖FU u₀ ξ‖ ^ 2)
        (-(2 * a) * psym ks ξ ^ (j + 1) * Real.exp (-(2 * a * s * psym ks ξ)) *
          ‖FU u₀ ξ‖ ^ 2) s := by
    intro ξ s _
    have := ((((hasDerivAt_id s).const_mul (-(2 * a * psym ks ξ))).exp).const_mul
      (psym ks ξ ^ j)).mul_const (‖FU u₀ ξ‖ ^ 2)
    convert this using 1
    · funext s'; simp only [id]; ring_nf
    · simp only [id]; ring_nf
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (x₀ := t)
    (F := fun s ξ => psym ks ξ ^ j * Real.exp (-(2 * a * s * psym ks ξ)) * ‖FU u₀ ξ‖ ^ 2)
    (F' := fun s ξ => -(2 * a) * psym ks ξ ^ (j + 1) * Real.exp (-(2 * a * s * psym ks ξ)) *
      ‖FU u₀ ξ‖ ^ 2) (half_pos ht)
    (Eventually.of_forall fun s => aesm_Gint a ks u₀ j s) (integrable_Gint ha u₀ j ht)
    ((aesm_Gint a ks u₀ (j + 1) t).const_mul (-(2 * a)) |>.congr
      (Eventually.of_forall fun ξ => by ring))
    (Eventually.of_forall hbound) ((integrable_norm_sq_L2 (FU u₀)).const_mul _)
    (Eventually.of_forall hdiff)
  have e : (∫ ξ, -(2 * a) * psym ks ξ ^ (j + 1) * Real.exp (-(2 * a * t * psym ks ξ)) *
      ‖FU u₀ ξ‖ ^ 2) = -(2 * a) * G a ks u₀ (j + 1) t := by
    rw [G, ← integral_const_mul]; congr 1; funext ξ; ring
  rw [← e]
  exact key.2

/-- `|e^{−x} − 1| ≤ x` for `x ≥ 0`. -/
theorem abs_exp_neg_sub_one_le {x : ℝ} (hx : 0 ≤ x) : |Real.exp (-x) - 1| ≤ x := by
  rw [abs_of_nonpos (by linarith [Real.exp_le_one_iff.2 (neg_nonpos.2 hx)])]
  linarith [Real.add_one_le_exp (-x)]

/-- At `s = 0`, `G_j` has right derivative `−2a G_{j+1}(0)` when `p^{j+1}|û₀|² ∈ L¹`. -/
theorem hasDerivWithinAt_G_zero {a ks : ℝ} (ha : 0 < a) (u₀ : L2 d) (j : ℕ)
    (hint : Integrable fun ξ : Rd => psym ks ξ ^ (j + 1) * ‖FU u₀ ξ‖ ^ 2) :
    HasDerivWithinAt (G a ks u₀ j) (-(2 * a) * G a ks u₀ (j + 1) 0) (Ici 0) 0 := by
  have hint0 : Integrable fun ξ : Rd => psym ks ξ ^ j * ‖FU u₀ ξ‖ ^ 2 := by
    refine Integrable.mono' ((integrable_norm_sq_L2 (FU u₀)).add hint)
      (((continuous_psym ks).pow j).aestronglyMeasurable.mul
        ((Lp.aestronglyMeasurable (FU u₀)).norm.pow 2)) (Eventually.of_forall fun ξ => ?_)
    have hp := psym_nonneg ks ξ
    rw [Real.norm_of_nonneg (by positivity)]
    have : psym ks ξ ^ j ≤ 1 + psym ks ξ ^ (j + 1) := by
      rcases le_total (psym ks ξ) 1 with h | h
      · have := pow_le_one₀ hp h (n := j); have := pow_nonneg hp (j + 1); linarith
      · have := pow_le_pow_right₀ h (Nat.le_add_right j 1); linarith
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg ‖FU u₀ ξ‖]
  have hG : ∀ s, 0 ≤ s → Integrable fun ξ : Rd =>
      psym ks ξ ^ j * Real.exp (-(2 * a * s * psym ks ξ)) * ‖FU u₀ ξ‖ ^ 2 := fun s hs =>
    hint0.mono' (aesm_Gint a ks u₀ j s) (Eventually.of_forall fun ξ => by
      have hp := psym_nonneg ks ξ
      rw [Real.norm_of_nonneg (by positivity)]
      have : Real.exp (-(2 * a * s * psym ks ξ)) ≤ 1 :=
        Real.exp_le_one_iff.2 (by nlinarith [mul_nonneg (mul_nonneg ha.le hs) hp])
      calc psym ks ξ ^ j * Real.exp (-(2 * a * s * psym ks ξ)) * ‖FU u₀ ξ‖ ^ 2
          ≤ psym ks ξ ^ j * 1 * ‖FU u₀ ξ‖ ^ 2 := by gcongr
        _ = psym ks ξ ^ j * ‖FU u₀ ξ‖ ^ 2 := by ring)
  rw [hasDerivWithinAt_iff_tendsto_slope, show Ici (0 : ℝ) \ {0} = Ioi 0 from Ici_diff_left]
  -- the slope is the integral of the difference quotients
  have hslope : ∀ h : ℝ, 0 < h → slope (G a ks u₀ j) 0 h =
      ∫ ξ, psym ks ξ ^ j * ((Real.exp (-(2 * a * h * psym ks ξ)) - 1) / h) * ‖FU u₀ ξ‖ ^ 2 := by
    intro h hh
    rw [slope_def_field, sub_zero, G, G, ← integral_sub (hG h hh.le) (hG 0 le_rfl),
      ← integral_div]
    congr 1; funext ξ; simp; ring
  have hlim := tendsto_integral_filter_of_dominated_convergence (l := 𝓝[>] (0 : ℝ))
    (F := fun h ξ => psym ks ξ ^ j * ((Real.exp (-(2 * a * h * psym ks ξ)) - 1) / h) *
      ‖FU u₀ ξ‖ ^ 2)
    (f := fun ξ => -(2 * a) * psym ks ξ ^ (j + 1) * ‖FU u₀ ξ‖ ^ 2)
    (fun ξ => 2 * a * (psym ks ξ ^ (j + 1) * ‖FU u₀ ξ‖ ^ 2))
    (Eventually.of_forall fun h => (((continuous_psym ks).pow j).mul
      (((Real.continuous_exp.comp (continuous_const.mul (continuous_psym ks)).neg).sub
        continuous_const).div_const h)).aestronglyMeasurable.mul
      ((Lp.aestronglyMeasurable (FU u₀)).norm.pow 2))
    (by
      filter_upwards [self_mem_nhdsWithin] with h (hh : 0 < h)
      refine Eventually.of_forall fun ξ => ?_
      have hp := psym_nonneg ks ξ
      have h1 := abs_exp_neg_sub_one_le (by positivity : 0 ≤ 2 * a * h * psym ks ξ)
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_div, abs_of_pos hh,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ psym ks ξ ^ j),
        abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖FU u₀ ξ‖ ^ 2)]
      have h2 : |Real.exp (-(2 * a * h * psym ks ξ)) - 1| / h ≤ 2 * a * psym ks ξ := by
        rw [div_le_iff₀ hh]; linarith
      calc psym ks ξ ^ j * (|Real.exp (-(2 * a * h * psym ks ξ)) - 1| / h) * ‖FU u₀ ξ‖ ^ 2
          ≤ psym ks ξ ^ j * (2 * a * psym ks ξ) * ‖FU u₀ ξ‖ ^ 2 := by gcongr
        _ = 2 * a * (psym ks ξ ^ (j + 1) * ‖FU u₀ ξ‖ ^ 2) := by ring)
    (hint.const_mul _)
    (Eventually.of_forall fun ξ => by
      have hd : HasDerivAt (fun h : ℝ => Real.exp (-(2 * a * h * psym ks ξ)))
          (Real.exp (-(2 * a * 0 * psym ks ξ)) * -(2 * a * psym ks ξ)) 0 := by
        have := ((hasDerivAt_id (0 : ℝ)).const_mul (-(2 * a * psym ks ξ))).exp
        convert this using 1
        · funext h; simp only [id]; ring_nf
        · simp only [id]; ring_nf
      have hs := (hasDerivAt_iff_tendsto_slope.1 hd).mono_left
        (nhdsWithin_mono (0 : ℝ) fun x (hx : 0 < x) => ne_of_gt hx)
      have := (hs.const_mul (psym ks ξ ^ j)).mul_const (‖FU u₀ ξ‖ ^ 2)
      have hval : psym ks ξ ^ j * (Real.exp (-(2 * a * 0 * psym ks ξ)) * -(2 * a * psym ks ξ)) *
          ‖FU u₀ ξ‖ ^ 2 = -(2 * a) * psym ks ξ ^ (j + 1) * ‖FU u₀ ξ‖ ^ 2 := by
        simp only [mul_zero, zero_mul, neg_zero, Real.exp_zero, one_mul]; ring
      rw [hval] at this
      refine this.congr' (eventually_nhdsWithin_of_forall fun h _ => ?_)
      simp only [slope_def_field, sub_zero, mul_zero, zero_mul, neg_zero, Real.exp_zero])
  refine (hlim.congr' (eventually_nhdsWithin_of_forall fun h hh => (hslope h hh).symm)).trans ?_
  rw [G]
  apply le_of_eq
  congr 1
  rw [← integral_const_mul]
  congr 1; funext ξ; simp; ring

theorem G_zero {a ks : ℝ} (ha : 0 ≤ a) (u₀ : L2 d) {s : ℝ} (hs : 0 ≤ s) :
    ‖Sr 0 ha ks s u₀‖ ^ 2 = G a ks u₀ 0 s := by
  rw [← norm_FU, SpectralConc.norm_sq_L2, G]
  refine integral_congr_ae ?_
  filter_upwards [FU_S0 ha ks hs u₀] with ξ h
  rw [h, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, mul_pow,
    ← Real.exp_nat_mul]
  push_cast; ring_nf

theorem G_one {a ks : ℝ} (ha : 0 < a) (u₀ : L2 d) {s : ℝ} (hs : 0 < s) :
    ‖Bop ks ⟨Sr 0 ha.le ks s u₀, inH_mono (j := 1) (k := 2) (by norm_num) (inH_of_pos ha hs u₀)⟩‖
      ^ 2 = G a ks u₀ 1 s := by
  rw [← norm_FU, SpectralConc.norm_sq_L2, G]
  refine integral_congr_ae ?_
  filter_upwards [FU_Bop ks ⟨Sr 0 ha.le ks s u₀,
    inH_mono (j := 1) (k := 2) (by norm_num) (inH_of_pos ha hs u₀)⟩, FU_S0 ha.le ks hs.le u₀]
    with ξ h1 h2
  rw [h1]
  rw [h2, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs,
    ← Real.exp_nat_mul, psym]
  push_cast; ring_nf

theorem G_two {a ks : ℝ} (ha : 0 < a) (u₀ : L2 d) {s : ℝ} (hs : 0 < s) :
    ‖Aop ks ⟨Sr 0 ha.le ks s u₀, inH_of_pos ha hs u₀⟩‖ ^ 2 = G a ks u₀ 2 s := by
  rw [← norm_FU, SpectralConc.norm_sq_L2, G]
  refine integral_congr_ae ?_
  filter_upwards [FU_Aop ks ⟨Sr 0 ha.le ks s u₀, inH_of_pos ha hs u₀⟩, FU_S0 ha.le ks hs.le u₀]
    with ξ h1 h2
  rw [h1]
  rw [h2, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_of_nonneg (psym_nonneg ks ξ), mul_pow,
    mul_pow, ← Real.exp_nat_mul]
  push_cast; ring_nf

/-- The energy `E(s) = ½‖(Δ + k⋆²)u(s)‖²` (Fourier form, defined for all `s`; it equals
`½‖(Δ + k⋆²)u(s)‖²` for `s > 0`, and for `s ≥ 0` when `u₀ ∈ H²`). -/
def energy (a ks : ℝ) (u₀ : L2 d) (s : ℝ) : ℝ := G a ks u₀ 1 s / 2

/-- **Proposition (monotone quadratic energy).** For `t > 0`,
`dE/dt = −a‖(Δ + k⋆²)²u(t)‖² ≤ 0` and `½ d/dt‖u(t)‖² = −a‖(Δ + k⋆²)u(t)‖² ≤ 0`; integrated,
`‖u(t)‖² + 2a∫₀ᵗ‖(Δ + k⋆²)u‖² = ‖u₀‖²` for every `t ≥ 0`; and if `u₀ ∈ H⁴` both identities also
hold at `t = 0` (as right derivatives). -/
theorem energy_identities {a ks : ℝ} (ha : 0 < a) (hks : 0 < ks) (u₀ : L2 d) :
    (∀ s (hs : 0 < s), energy a ks u₀ s =
      ‖Bop ks ⟨Sr 0 ha.le ks s u₀,
        inH_mono (j := 1) (k := 2) (by norm_num) (inH_of_pos ha hs u₀)⟩‖ ^ 2 / 2) ∧
    (∀ t (ht : 0 < t), HasDerivAt (energy a ks u₀)
      (-a * ‖Aop ks ⟨Sr 0 ha.le ks t u₀, inH_of_pos ha ht u₀⟩‖ ^ 2) t ∧
      -a * ‖Aop ks ⟨Sr 0 ha.le ks t u₀, inH_of_pos ha ht u₀⟩‖ ^ 2 ≤ 0) ∧
    (∀ t (ht : 0 < t), HasDerivAt (fun s => ‖Sr 0 ha.le ks s u₀‖ ^ 2)
      (-(2 * a) * ‖Bop ks ⟨Sr 0 ha.le ks t u₀,
        inH_mono (j := 1) (k := 2) (by norm_num) (inH_of_pos ha ht u₀)⟩‖ ^ 2) t ∧
      -(2 * a) * ‖Bop ks ⟨Sr 0 ha.le ks t u₀,
        inH_mono (j := 1) (k := 2) (by norm_num) (inH_of_pos ha ht u₀)⟩‖ ^ 2 ≤ 0) ∧
    (∀ t, 0 ≤ t → ‖Sr 0 ha.le ks t u₀‖ ^ 2 + 2 * a * ∫ s in (0 : ℝ)..t, G a ks u₀ 1 s =
      ‖u₀‖ ^ 2) ∧
    (∀ hu : InH 2 u₀,
      HasDerivWithinAt (fun s => ‖Sr 0 ha.le ks s u₀‖ ^ 2)
        (-(2 * a) * ‖Bop ks ⟨u₀, inH_mono (j := 1) (k := 2) (by norm_num) hu⟩‖ ^ 2) (Ici 0) 0 ∧
      HasDerivWithinAt (energy a ks u₀) (-a * ‖Aop ks ⟨u₀, hu⟩‖ ^ 2) (Ici 0) 0) := by
  -- integrability of `p²|û₀|²` and `p|û₀|²` for `u₀ ∈ H⁴`
  have hH4 : ∀ hu : InH 2 u₀, Integrable fun ξ : Rd => psym ks ξ ^ 2 * ‖FU u₀ ξ‖ ^ 2 := by
    intro hu
    have hm := (inH_two_iff ks u₀).1 hu
    refine (integrable_norm_sq_L2 (hm.toLp _ : L2 d)).congr ?_
    filter_upwards [hm.coeFn_toLp] with ξ h
    rw [h, norm_mul, Complex.norm_real, Real.norm_of_nonneg (psym_nonneg ks ξ), mul_pow]
  have hH2 : ∀ hu : InH 2 u₀, Integrable fun ξ : Rd => psym ks ξ ^ (0 + 1) * ‖FU u₀ ξ‖ ^ 2 := by
    intro hu
    refine Integrable.mono' ((integrable_norm_sq_L2 (FU u₀)).add (hH4 hu))
      (((continuous_psym ks).pow (0 + 1)).aestronglyMeasurable.mul
        ((Lp.aestronglyMeasurable (FU u₀)).norm.pow 2)) (Eventually.of_forall fun ξ => ?_)
    have hp := psym_nonneg ks ξ
    rw [Real.norm_of_nonneg (by positivity)]
    simp only [Pi.add_apply, zero_add, pow_one]
    nlinarith [sq_nonneg (psym ks ξ - 1), sq_nonneg ‖FU u₀ ξ‖, mul_nonneg hp (sq_nonneg ‖FU u₀ ξ‖)]
  have hG1 : ∀ s (hs : 0 < s), G a ks u₀ 1 s =
      ‖Bop ks ⟨Sr 0 ha.le ks s u₀,
        inH_mono (j := 1) (k := 2) (by norm_num) (inH_of_pos ha hs u₀)⟩‖ ^ 2 :=
    fun s hs => (G_one ha u₀ hs).symm
  have hG1nn : ∀ s, 0 ≤ G a ks u₀ 1 s := fun s =>
    integral_nonneg fun ξ => by have := psym_nonneg ks ξ; positivity
  refine ⟨fun s hs => by rw [energy, hG1 s hs], fun t ht => ⟨?_, ?_⟩, fun t ht => ⟨?_, ?_⟩,
    fun t ht => ?_, fun hu => ⟨?_, ?_⟩⟩
  · have := (hasDerivAt_G (ks := ks) ha u₀ 1 ht).div_const 2
    rw [show -(2 * a) * G a ks u₀ (1 + 1) t / 2 = -a * G a ks u₀ 2 t by ring,
      ← G_two ha u₀ ht] at this
    exact this
  · have := sq_nonneg ‖Aop ks ⟨Sr 0 ha.le ks t u₀, inH_of_pos ha ht u₀⟩‖
    nlinarith
  · have h := hasDerivAt_G (ks := ks) ha u₀ 0 ht
    rw [show (0 + 1 : ℕ) = 1 from rfl, hG1 t ht] at h
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact G_zero ha.le u₀ (le_of_lt hs)
  · have := sq_nonneg ‖Bop ks ⟨Sr 0 ha.le ks t u₀,
      inH_mono (j := 1) (k := 2) (by norm_num) (inH_of_pos ha ht u₀)⟩‖
    nlinarith
  · -- FTC on `[0, t]` for `G₀`, whose derivative `−2aG₁` is nonpositive
    rcases ht.eq_or_lt with h0 | ht'
    · subst h0; simp [Sr_zero]
    have hcont : ContinuousOn (G a ks u₀ 0) (Icc 0 t) :=
      (((continuous_Sr ha hks u₀).norm.pow 2).continuousOn).congr fun s hs =>
        (G_zero ha.le u₀ hs.1).symm
    have hderiv : ∀ s ∈ Ioo 0 t, HasDerivAt (G a ks u₀ 0) (-(2 * a) * G a ks u₀ 1 s) s :=
      fun s hs => hasDerivAt_G ha u₀ 0 hs.1
    have hint : IntervalIntegrable (fun s => -(2 * a) * G a ks u₀ 1 s) volume 0 t := by
      have h := intervalIntegral.intervalIntegrable_deriv_of_nonneg (g := fun s => -G a ks u₀ 0 s)
        (g' := fun s => 2 * a * G a ks u₀ 1 s)
        (by rw [uIcc_of_le ht]; exact hcont.neg)
        (fun s hs => by
          rw [min_eq_left ht, max_eq_right ht] at hs
          have := (hderiv s hs).neg
          convert this using 1; ring)
        (fun s _ => by have := hG1nn s; positivity)
      refine h.neg.congr (Filter.Eventually.of_forall fun s => ?_)
      simp only [Pi.neg_apply]; ring
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht hcont hderiv hint
    rw [intervalIntegral.integral_const_mul] at hftc
    have h0 : ‖u₀‖ ^ 2 = G a ks u₀ 0 0 := by
      rw [← G_zero ha.le u₀ le_rfl, Sr_zero]; rfl
    rw [G_zero ha.le u₀ ht, h0]
    linarith
  · have h := hasDerivWithinAt_G_zero ha u₀ 0 (hH2 hu)
    have hG10 : G a ks u₀ (0 + 1) 0 =
        ‖Bop ks ⟨u₀, inH_mono (j := 1) (k := 2) (by norm_num) hu⟩‖ ^ 2 := by
      rw [← (inner_Aop ks hu).2.1, G]
      congr 1; funext ξ; simp
    rw [hG10] at h
    refine h.congr (fun s hs => G_zero ha.le u₀ hs) ?_
    exact G_zero ha.le u₀ le_rfl
  · have h := (hasDerivWithinAt_G_zero ha u₀ 1 (hH4 hu)).div_const 2
    have hG20 : G a ks u₀ (1 + 1) 0 = ‖Aop ks ⟨u₀, hu⟩‖ ^ 2 := by
      rw [← norm_FU, SpectralConc.norm_sq_L2, G]
      refine integral_congr_ae ?_
      filter_upwards [FU_Aop ks ⟨u₀, hu⟩] with ξ h1
      rw [h1]
      change psym ks ξ ^ (1 + 1) * Real.exp (-(2 * a * 0 * psym ks ξ)) * ‖FU u₀ ξ‖ ^ 2 =
        ‖(psym ks ξ : ℂ) * (FU u₀ : Rd → ℂ) ξ‖ ^ 2
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (psym_nonneg ks ξ), mul_pow]
      simp
    rw [hG20, show -(2 * a) * ‖Aop ks ⟨u₀, hu⟩‖ ^ 2 / 2 = -a * ‖Aop ks ⟨u₀, hu⟩‖ ^ 2 by ring] at h
    exact h


/-! ### Remark: the gradient-flow convention -/

theorem inner_Bop (ks : ℝ) {u v : L2 d} (hu : InH 2 u) (hv : InH 1 v) :
    ⟪Bop ks ⟨u, inH_mono (j := 1) (k := 2) (by norm_num) hu⟩, Bop ks ⟨v, hv⟩⟫_ℂ =
      ⟪Aop ks ⟨u, hu⟩, v⟫_ℂ := by
  rw [inner_FU_eq, inner_FU_eq]
  apply integral_congr_ae
  filter_upwards [FU_Bop ks ⟨u, inH_mono (j := 1) (k := 2) (by norm_num) hu⟩, FU_Bop ks ⟨v, hv⟩,
    FU_Aop ks ⟨u, hu⟩] with ξ h1 h2 h3
  rw [h1, h2, h3, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, psym]
  push_cast; ring

/-- **Remark (gradient-flow convention).** With the real inner product `Re⟨·,·⟩`, the gradient of
`E[u] = ½‖(Δ + k⋆²)u‖²` at `u ∈ H⁴` is `𝒜u`: for every direction `v ∈ H²`,
`d/dε E[u + εv]|_{ε=0} = Re⟨𝒜u, v⟩`, and `𝒜u` is the only `w ∈ L²` with
`Re⟨w, v⟩ = Re⟨𝒜u, v⟩` for all `v ∈ H²`. Hence `uₜ = −a∇_ℝE[u]`. -/
theorem gradient (ks : ℝ) {u : L2 d} (hu : InH 2 u) :
    (∀ {v : L2 d} (hv : InH 1 v),
      HasDerivAt (fun ε : ℝ => ‖Bop ks ⟨u + (ε : ℂ) • v,
        inH_add (inH_mono (j := 1) (k := 2) (by norm_num) hu) (inH_smul hv _)⟩‖ ^ 2 / 2)
        (⟪Aop ks ⟨u, hu⟩, v⟫_ℂ).re 0) ∧
    ∀ w : L2 d, (∀ v (_ : InH 1 v), (⟪w, v⟫_ℂ).re = (⟪Aop ks ⟨u, hu⟩, v⟫_ℂ).re) →
      w = Aop ks ⟨u, hu⟩ := by
  have hu1 : InH 1 u := inH_mono (j := 1) (k := 2) (by norm_num) hu
  refine ⟨fun {v} hv => ?_, fun w hw => ?_⟩
  · set U := Bop ks ⟨u, hu1⟩
    set V := Bop ks ⟨v, hv⟩
    have hlin : ∀ ε : ℝ, Bop ks ⟨u + (ε : ℂ) • v, inH_add hu1 (inH_smul hv _)⟩ =
        U + (ε : ℂ) • V := fun ε => by
      rw [show (⟨u + (ε : ℂ) • v, inH_add hu1 (inH_smul hv _)⟩ : (Bop (d := d) ks).domain) =
        ⟨u, hu1⟩ + (ε : ℂ) • ⟨v, hv⟩ from rfl, LinearPMap.map_add, LinearPMap.map_smul]
    have hpoly : ∀ ε : ℝ, ‖Bop ks ⟨u + (ε : ℂ) • v, inH_add hu1 (inH_smul hv _)⟩‖ ^ 2 / 2 =
        ‖U‖ ^ 2 / 2 + ε * (⟪U, V⟫_ℂ).re + ε ^ 2 * (‖V‖ ^ 2 / 2) := fun ε => by
      rw [hlin, @norm_add_sq ℂ, inner_smul_right, norm_smul, Complex.norm_real, Real.norm_eq_abs,
        mul_pow, sq_abs, RCLike.re_to_complex, Complex.re_ofReal_mul]
      ring
    have h := (((hasDerivAt_id (0 : ℝ)).mul_const (⟪U, V⟫_ℂ).re).const_add (‖U‖ ^ 2 / 2)).add
      ((hasDerivAt_pow 2 (0 : ℝ)).mul_const (‖V‖ ^ 2 / 2))
    refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun ε => ?_)
    · rw [show U = Bop ks ⟨u, inH_mono (j := 1) (k := 2) (by norm_num) hu⟩ from rfl,
        inner_Bop ks hu hv]
      simp
    · simp only [Pi.add_apply, id]
      exact hpoly ε
  · have hdense : Dense ((Hdom (d := d) 2 : Submodule ℂ (L2 d)) : Set (L2 d)) := dense_Hdom
    refine hdense.eq_of_inner_left fun v => ?_
    have hv1 : InH 1 (v : L2 d) := inH_mono (j := 1) (k := 2) (by norm_num) v.2
    have h1 := hw v hv1
    have h2 := hw (Complex.I • (v : L2 d)) (inH_smul hv1 _)
    rw [inner_smul_right, inner_smul_right, Complex.I_mul_re, Complex.I_mul_re] at h2
    exact Complex.ext h1 (by linarith)

/-! ### The periodic-domain counterpart -/

section Torus

variable (L : ℝ) [Fact (0 < L)]

/-- The resonant lattice frequencies `|ξ_n| = k⋆`. -/
def Res (ks : ℝ) : Set (Fin d → ℤ) := {n | E16Torus.xi2 L n = ks ^ 2}

/-- The torus flow `û_n(t) = e^{−at(|ξ_n|² − k⋆²)²}û_n(0)` (the `E16Torus` flow with
`(a, b, r) ↦ (2ak⋆², a, −ak⋆⁴)`). -/
def flowT {a : ℝ} (ha : 0 < a) (ks t : ℝ) (A₀ : TorusL2.L2 L d) : TorusL2.L2 L d :=
  E16Torus.flow L (2 * a * ks ^ 2) (0 - a * ks ^ 4) ha t A₀

theorem coef_flowT {a : ℝ} (ha : 0 < a) (ks : ℝ) {t : ℝ} (ht : 0 ≤ t) (A₀ : TorusL2.L2 L d)
    (n : Fin d → ℤ) :
    TorusL2.coef (flowT L ha ks t A₀) n =
      (Real.exp (-(a * t * (E16Torus.xi2 L n - ks ^ 2) ^ 2)) : ℂ) * TorusL2.coef A₀ n := by
  rw [flowT, E16Torus.coef_flow ha ht, E61Cert.lamT_eq_lamL]
  congr 3; unfold E61Cert.lamL; ring

/-- **Proposition (discrete Fourier shells on a flat torus).** With `Π₀` the orthogonal projection
onto the resonant span (`Π₀ = 0` if it is trivial) and
`g_L = min{(|ξ_n|² − k⋆²)² : |ξ_n| ≠ k⋆} > 0`,
`‖u(t) − Π₀u₀‖ ≤ e^{−ag_Lt}‖u₀ − Π₀u₀‖`; in particular `u(t) → Π₀u₀`. -/
theorem periodic (hd : 1 ≤ d) {a : ℝ} (ha : 0 < a) (ks : ℝ) :
    (Res (d := d) L ks = ∅ → TorusL2.P L d (Res L ks) = 0) ∧
    ∃ gL : ℝ, 0 < gL ∧
      (∃ n₀ : Fin d → ℤ, n₀ ∉ Res L ks ∧ gL = (E16Torus.xi2 L n₀ - ks ^ 2) ^ 2) ∧
      (∀ n : Fin d → ℤ, n ∉ Res L ks → gL ≤ (E16Torus.xi2 L n - ks ^ 2) ^ 2) ∧
      ∀ (A₀ : TorusL2.L2 L d) (t : ℝ), 0 ≤ t →
        ‖flowT L ha ks t A₀ - TorusL2.P L d (Res L ks) A₀‖ ≤
          Real.exp (-(a * gL * t)) * ‖A₀ - TorusL2.P L d (Res L ks) A₀‖ := by
  refine ⟨fun h => by rw [h]; exact TorusL2.P_empty, ?_⟩
  -- a non-resonant lattice point
  have hne : (Res (d := d) L ks)ᶜ.Nonempty := by
    obtain ⟨m, hm⟩ : ∃ m : ℕ, ks ^ 2 < (2 * Real.pi / L * m) ^ 2 := by
      obtain ⟨m, hm⟩ := exists_nat_gt (|ks| / (2 * Real.pi / L))
      refine ⟨m, ?_⟩
      have hc : 0 < 2 * Real.pi / L := div_pos Real.two_pi_pos (Fact.out)
      rw [div_lt_iff₀ hc] at hm
      have h0 : 0 ≤ |ks| := abs_nonneg ks
      calc ks ^ 2 = |ks| ^ 2 := (sq_abs ks).symm
        _ < (↑m * (2 * Real.pi / L)) ^ 2 := pow_lt_pow_left₀ hm h0 two_ne_zero
        _ = (2 * Real.pi / L * m) ^ 2 := by ring
    refine ⟨Pi.single (⟨0, hd⟩ : Fin d) (m : ℤ), fun h => ?_⟩
    change E16Torus.xi2 L _ = ks ^ 2 at h
    rw [E61Cert.xi2_single L hd] at h
    push_cast at h
    linarith
  have ht : Tendsto (fun n : Fin d → ℤ => (E16Torus.xi2 L n - ks ^ 2) ^ 2) cofinite atTop := by
    have h0 : Tendsto (fun q : ℝ => q - ks ^ 2) atTop atTop :=
      Tendsto.congr (fun q => (sub_eq_add_neg q (ks ^ 2)).symm)
        (tendsto_atTop_add_const_right atTop (-ks ^ 2) tendsto_id)
    exact ((tendsto_pow_atTop two_ne_zero).comp h0).comp (E16Torus.tendsto_xi2 (d := d) (L := L))
  obtain ⟨n₀, hn₀, hmin⟩ := ht.exists_within_forall_le hne
  have hgpos : 0 < (E16Torus.xi2 L n₀ - ks ^ 2) ^ 2 := by
    have : E16Torus.xi2 L n₀ - ks ^ 2 ≠ 0 := fun h => hn₀ (by
      change E16Torus.xi2 L n₀ = ks ^ 2; linarith)
    positivity
  refine ⟨_, hgpos, ⟨n₀, hn₀, rfl⟩, fun n hn => hmin n hn, fun A₀ t ht0 => ?_⟩
  set g := (E16Torus.xi2 L n₀ - ks ^ 2) ^ 2
  -- coefficients of `u(t) − Π₀u₀` and of `u₀ − Π₀u₀`
  have hc1 : ∀ n, TorusL2.coef (flowT L ha ks t A₀ - TorusL2.P L d (Res L ks) A₀) n =
      (1 - TorusL2.chi (Res L ks) n) *
        ((Real.exp (-(a * t * (E16Torus.xi2 L n - ks ^ 2) ^ 2)) : ℂ) * TorusL2.coef A₀ n) := by
    intro n
    rw [TorusL2.coef_sub, coef_flowT L ha ks ht0, TorusL2.coef_P]
    by_cases hn : n ∈ Res L ks
    · have : E16Torus.xi2 L n - ks ^ 2 = 0 := by
        have h' : E16Torus.xi2 L n = ks ^ 2 := hn
        linarith
      rw [TorusL2.chi_mem hn, this]; simp
    · rw [TorusL2.chi_not_mem hn]; ring
  have hc2 : ∀ n, TorusL2.coef (A₀ - TorusL2.P L d (Res L ks) A₀) n =
      (1 - TorusL2.chi (Res L ks) n) * TorusL2.coef A₀ n := by
    intro n; rw [TorusL2.coef_sub, TorusL2.coef_P]; ring
  have key : ‖flowT L ha ks t A₀ - TorusL2.P L d (Res L ks) A₀‖ ^ 2 ≤
      (Real.exp (-(a * g * t)) * ‖A₀ - TorusL2.P L d (Res L ks) A₀‖) ^ 2 := by
    rw [mul_pow]
    refine hasSum_le (fun n => ?_) (TorusL2.hasSum_sq _)
      ((TorusL2.hasSum_sq (A₀ - TorusL2.P L d (Res L ks) A₀)).mul_left _)
    rw [hc1, hc2, norm_mul, norm_mul, norm_mul, mul_pow, mul_pow, mul_pow, Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_pos _).le]
    by_cases hn : n ∈ Res L ks
    · rw [TorusL2.chi_mem hn]; simp
    · rw [TorusL2.chi_not_mem hn]
      have hq := hmin n hn
      have h1 : Real.exp (-(a * t * (E16Torus.xi2 L n - ks ^ 2) ^ 2)) ^ 2 ≤
          Real.exp (-(a * g * t)) ^ 2 := by
        apply pow_le_pow_left₀ (Real.exp_pos _).le
        exact Real.exp_le_exp.2 (by nlinarith [mul_nonneg ha.le ht0])
      have h2 := norm_nonneg (TorusL2.coef A₀ n)
      calc ‖(1 : ℂ) - 0‖ ^ 2 * (Real.exp (-(a * t * (E16Torus.xi2 L n - ks ^ 2) ^ 2)) ^ 2 *
            ‖TorusL2.coef A₀ n‖ ^ 2)
          ≤ ‖(1 : ℂ) - 0‖ ^ 2 * (Real.exp (-(a * g * t)) ^ 2 * ‖TorusL2.coef A₀ n‖ ^ 2) := by
            gcongr
        _ = Real.exp (-(a * g * t)) ^ 2 * (‖(1 : ℂ) - 0‖ ^ 2 * ‖TorusL2.coef A₀ n‖ ^ 2) := by ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 key

end Torus

/-! ### The linear control parameter and the scope of the claim -/

/-- **Proposition (linear Swift–Hohenberg threshold)**, from E61: for
`∂ₜu = ru − a(Δ + k⋆²)²u` the spectral bound is `r`, the threshold is `r_c = 0`, the growing band
for `r > 0` is `||ξ|² − k⋆²| < √(r/a)`, and on `𝕋_L^d` the first growing mode appears at
`r_c(L) = a min_n(|ξ_n|² − k⋆²)²`. -/
theorem linear_threshold (hd : 1 ≤ d) {a ks : ℝ} (ha : 0 < a) (hks : 0 < ks) (r : ℝ) :
    uspectrum (Lr (d := d) r ha.le ks) = {z : ℂ | z.im = 0 ∧ z.re ≤ r} ∧
    IsLeast (Set.range fun k : Rd => a * psym ks k) 0 ∧
    (0 < r → ∀ k : Rd, 0 < lamr r a ks k ↔ |‖k‖ ^ 2 - ks ^ 2| < √(r / a)) ∧
    ∀ (L : ℝ) [Fact (0 < L)], ((∃ n : Fin d → ℤ, 0 ≤ E61Cert.lamL L r a ks n) ↔
      E61Cert.rcL d L a ks ≤ r) := by
  obtain ⟨-, hspec, -, hleast, -, -⟩ := E61Cert.theorem_e61 hd ha hks r
  refine ⟨hspec, hleast, fun hr => (E61Cert.unstable_band ha hks).1 hr, fun L _ => ?_⟩
  exact (E61Cert.periodic_box L ha r).2.2.2.2.2

/-- **Remark (scope: sign reversal)**: for `∂ₜu = +a(Δ + k⋆²)²u` the Fourier factor `e^{+atp}` is
unbounded, so every `t > 0` amplifies some band-limited nonzero datum by more than any prescribed
factor `M`: high-frequency growth, and no bounded `L²` evolution. -/
theorem sign_reversal (hd : 1 ≤ d) {a ks : ℝ} (ha : 0 < a) {t : ℝ} (ht : 0 < t) (M : ℝ) :
    ∃ u₀ : L2 d, u₀ ≠ 0 ∧ (∃ R : ℝ, ∀ᵐ ξ ∂volume, R < ‖ξ‖ → (FU u₀ : Rd → ℂ) ξ = 0) ∧
      M ^ 2 * ‖u₀‖ ^ 2 ≤ ∫ ξ, Real.exp (2 * a * t * psym ks ξ) * ‖FU u₀ ξ‖ ^ 2 := by
  -- a frequency with `e^{atp} > |M|`
  set e : Rd := EuclideanSpace.single (⟨0, hd⟩ : Fin d) 1
  have he : ‖e‖ = 1 := by simp [e]
  obtain ⟨s, hs⟩ := exists_nat_gt (ks ^ 2 + |M| / (a * t) + 1)
  set ξ₀ : Rd := Real.sqrt s • e
  have hξ₀ : ‖ξ₀‖ ^ 2 = s := by
    rw [norm_smul, he, mul_one, Real.norm_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt (Nat.cast_nonneg s)]
  have hp₀ : |M| < a * t * psym ks ξ₀ := by
    have h1 : |M| / (a * t) + 1 ≤ ‖ξ₀‖ ^ 2 - ks ^ 2 := by rw [hξ₀]; linarith
    have h2 : 1 ≤ ‖ξ₀‖ ^ 2 - ks ^ 2 := by
      have := div_nonneg (abs_nonneg M) (mul_pos ha ht).le; linarith
    have h3 : ‖ξ₀‖ ^ 2 - ks ^ 2 ≤ psym ks ξ₀ := by unfold psym; nlinarith
    have h4 : |M| < a * t * (‖ξ₀‖ ^ 2 - ks ^ 2) := by
      have := (div_lt_iff₀' (mul_pos ha ht)).1 (show |M| / (a * t) < ‖ξ₀‖ ^ 2 - ks ^ 2 by linarith)
      linarith
    nlinarith [mul_pos ha ht]
  -- a small ball around `ξ₀` where `atp > |M|`
  have hc : Continuous fun ξ : Rd => a * t * psym ks ξ := continuous_const.mul (continuous_psym ks)
  obtain ⟨ρ, hρ, hball⟩ := Metric.continuous_iff.1 hc ξ₀ (a * t * psym ks ξ₀ - |M|) (by linarith)
  have hU : MeasurableSet (Metric.ball ξ₀ ρ) := measurableSet_ball
  have hfin : volume (Metric.ball ξ₀ ρ) ≠ ⊤ := measure_ball_lt_top.ne
  have hpos : 0 < (volume (Metric.ball ξ₀ ρ)).toReal :=
    ENNReal.toReal_pos (Metric.measure_ball_pos volume ξ₀ hρ).ne' hfin
  set g := ind (Metric.ball ξ₀ ρ) hU hfin
  have hFu : FU (FU.symm g) = g := LinearIsometryEquiv.apply_symm_apply _ _
  refine ⟨FU.symm g, fun h => ?_, ⟨‖ξ₀‖ + ρ, ?_⟩, ?_⟩
  · have : ‖g‖ ^ 2 = 0 := by rw [← hFu, h, map_zero, norm_zero]; ring
    rw [norm_ind_sq] at this; linarith
  · rw [hFu]
    filter_upwards [coeFn_ind (Metric.ball ξ₀ ρ) hU hfin] with ξ h hξ
    rw [h, Set.indicator_of_notMem]
    intro hmem
    rw [Metric.mem_ball, dist_eq_norm] at hmem
    linarith [norm_sub_norm_le ξ ξ₀]
  · rw [← norm_FU (FU.symm g), hFu, SpectralConc.norm_sq_L2, ← integral_const_mul]
    refine integral_mono_ae ((integrable_norm_sq_L2 g).const_mul _) ?_ ?_
    · -- the amplified integrand is integrable: `g` is supported in the ball
      have hcont : Continuous fun ξ : Rd => Real.exp (2 * a * t * psym ks ξ) := by
        have := continuous_psym (d := d) ks; fun_prop
      refine Integrable.mono' ((integrable_norm_sq_L2 g).const_mul
        (Real.exp (2 * (a * t * psym ks ξ₀ + (a * t * psym ks ξ₀ - |M|)))))
        (hcont.aestronglyMeasurable.mul ((Lp.aestronglyMeasurable g).norm.pow 2)) ?_
      filter_upwards [coeFn_ind (Metric.ball ξ₀ ρ) hU hfin] with ξ h
      rw [Real.norm_of_nonneg (by positivity)]
      by_cases hmem : ξ ∈ Metric.ball ξ₀ ρ
      · refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (by positivity)
        have := hball ξ hmem
        rw [Real.dist_eq, abs_lt] at this
        nlinarith
      · rw [h, Set.indicator_of_notMem hmem]; simp
    · filter_upwards [coeFn_ind (Metric.ball ξ₀ ρ) hU hfin] with ξ h
      by_cases hmem : ξ ∈ Metric.ball ξ₀ ρ
      · refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        have h1 := hball ξ hmem
        rw [Real.dist_eq, abs_lt] at h1
        have h2 : |M| < a * t * psym ks ξ := by linarith
        have h3 : M ^ 2 ≤ Real.exp (a * t * psym ks ξ) ^ 2 := by
          rw [← sq_abs M]
          exact pow_le_pow_left₀ (abs_nonneg M) (h2.le.trans
            ((Real.add_one_le_exp _).trans' (by linarith))) 2
        rw [← Real.exp_nat_mul] at h3
        convert h3 using 2; push_cast; ring
      · rw [h, Set.indicator_of_notMem hmem]; simp

end E57Cert
end ReyesMath
