import Mathlib

/-!
# Exact continuous weighted closed-loop phase locking (F07)

Complete formalization of the main theorem, both corollaries, the sector
proposition and the uniform-weight example of
`papers/weighted-closed-loop-phase-locking/main.tex`.

* A phase `χ ∈ H¹(0,S;ℝ)` is represented by its absolutely continuous
  representative: `χ s = χ 0 + ∫₀ˢ g` on `[0,S]` for some `g ∈ L²(0,S)`
  (`IsH1Phase`).  The energy is written with the *actual* derivative
  `deriv χ`, which is proved to agree with `g` almost everywhere by the
  Lebesgue differentiation theorem (`IsH1Phase.ae_hasDerivAt`).
* The weight is only assumed measurable with `0 < w₋ ≤ w ≤ w₊` a.e., and
  `Ω, σ ∈ L²(0,S)`, exactly as in the manuscript (`PhaseLockingData`).

Main results: `phase_locking_exact_minimum` (minimum `Δₙ²/I`, explicit
minimizer, exact remainder identity, a.e. uniqueness of `q*`, uniqueness of
minimizers up to constants), `exact_lock_criterion`,
`optimalPhase_perturbation`, `optimalPhase_second_variation`,
`perturbation_weight_eq_zero_iff`, `sector_selection`,
`nearest_integers_unique`, `nearest_integers_tie`, `uniform_weight_example`.
-/

open MeasureTheory Set Filter Topology

namespace ReyesMath

/-- Lebesgue differentiation: the indefinite integral of an integrable function on `ℝ`
is differentiable almost everywhere, with derivative the integrand. -/
theorem ae_hasDerivAt_integral {g : ℝ → ℝ} (hg : Integrable g) (a : ℝ) :
    ∀ᵐ x, HasDerivAt (fun s => ∫ t in a..s, g t) (g x) x := by
  have hloc : LocallyIntegrable g volume := hg.locallyIntegrable
  filter_upwards [(IsUnifLocDoublingMeasure.vitaliFamily (volume : Measure ℝ) 1).ae_tendsto_average
    hloc] with x hx
  have key : ∀ y, x ≠ y → ∀ u v, u < v → (u = x ∧ v = y ∨ u = y ∧ v = x) →
      (∫ t in a..y, g t) - (∫ t in a..x, g t) = (y - x) * ⨍ t in Icc u v, g t := by
    intro y hxy u v huv h
    rw [setAverage_eq, Real.volume_real_Icc, max_eq_left (sub_nonneg.2 huv.le),
      smul_eq_mul, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le huv.le]
    rw [intervalIntegral.integral_interval_sub_left (hg.intervalIntegrable)
      (hg.intervalIntegrable)]
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · field_simp [sub_ne_zero.2 (Ne.symm hxy)]
    · rw [intervalIntegral.integral_symm]
      field_simp [sub_ne_zero.2 hxy]
      ring
  have L1 : Tendsto (fun y => ((∫ t in a..y, g t) - (∫ t in a..x, g t)) / (y - x))
      (𝓝[>] x) (𝓝 (g x)) := by
    apply Tendsto.congr' _ (hx.comp (Real.tendsto_Icc_vitaliFamily_right x))
    filter_upwards [self_mem_nhdsWithin] with y (hxy : x < y)
    rw [key y hxy.ne x y hxy (Or.inl ⟨rfl, rfl⟩), Function.comp_apply]
    field_simp [sub_ne_zero.2 hxy.ne']
  have L2 : Tendsto (fun y => ((∫ t in a..y, g t) - (∫ t in a..x, g t)) / (y - x))
      (𝓝[<] x) (𝓝 (g x)) := by
    apply Tendsto.congr' _ (hx.comp (Real.tendsto_Icc_vitaliFamily_left x))
    filter_upwards [self_mem_nhdsWithin] with y (hxy : y < x)
    rw [key y hxy.ne' y x hxy (Or.inr ⟨rfl, rfl⟩), Function.comp_apply]
    field_simp [sub_ne_zero.2 hxy.ne]
  rw [hasDerivAt_iff_tendsto_slope, slope_fun_def_field, ← nhdsLT_sup_nhdsGT, tendsto_sup]
  exact ⟨L2, L1⟩

/-- A real phase in `H¹(0,S)`, in its absolutely continuous representative:
`χ s = χ 0 + ∫₀ˢ g` on `[0,S]` for some `g ∈ L²(0,S)`. -/
def IsH1Phase (S : ℝ) (χ : ℝ → ℝ) : Prop :=
  ∃ g : ℝ → ℝ, MemLp g 2 (volume.restrict (Ioc 0 S)) ∧
    ∀ s ∈ Icc 0 S, χ s = χ 0 + ∫ t in (0:ℝ)..s, g t

/-- The derivative of an `H¹` phase exists almost everywhere and equals its density. -/
theorem IsH1Phase.ae_hasDerivAt {S : ℝ} {χ g : ℝ → ℝ}
    (hg : MemLp g 2 (volume.restrict (Ioc 0 S)))
    (hχ : ∀ s ∈ Icc 0 S, χ s = χ 0 + ∫ t in (0:ℝ)..s, g t) :
    ∀ᵐ s ∂(volume.restrict (Ioc 0 S)), HasDerivAt χ (g s) s := by
  have hgi : IntegrableOn g (Ioc 0 S) := hg.integrable one_le_two
  set g' := (Ioc 0 S).indicator g with hg'
  have hg'i : Integrable g' := (integrable_indicator_iff measurableSet_Ioc).2 hgi
  have hderiv := ae_hasDerivAt_integral hg'i 0
  have hIoo : ∀ᵐ s ∂(volume.restrict (Ioc 0 S)), s ∈ Ioo 0 S := by
    rw [ae_restrict_iff' measurableSet_Ioc]
    have : ∀ᵐ s ∂volume, s ≠ S := by
      rw [ae_iff]
      simp
    filter_upwards [this] with s hs h
    exact ⟨h.1, lt_of_le_of_ne h.2 hs⟩
  filter_upwards [ae_restrict_of_ae hderiv, hIoo, ae_restrict_mem measurableSet_Ioc]
    with s hs (hs' : s ∈ Ioo 0 S) (hs'' : s ∈ Ioc 0 S)
  have hloc : χ =ᶠ[𝓝 s] fun x => χ 0 + ∫ t in (0:ℝ)..x, g' t := by
    filter_upwards [Ioo_mem_nhds hs'.1 hs'.2] with x hx
    rw [hχ x ⟨hx.1.le, hx.2.le⟩]
    congr 1
    rw [intervalIntegral.integral_of_le hx.1.le, intervalIntegral.integral_of_le hx.1.le]
    refine setIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
    rw [hg', indicator_of_mem (show t ∈ Ioc 0 S from ⟨ht.1, ht.2.trans hx.2.le⟩)]
  have := (hs.const_add (χ 0)).congr_of_eventuallyEq hloc
  rwa [hg', indicator_of_mem hs''] at this


/-- Standing hypotheses of the closed-loop phase-locking manuscript: a loop of
length `S > 0`, a measurable weight with `0 < w₋ ≤ w ≤ w₊` a.e., and targets
`Ω, σ ∈ L²(0,S)`. -/
structure PhaseLockingData (S : ℝ) (w Ω σ : ℝ → ℝ) : Prop where
  pos : 0 < S
  w_meas : AEStronglyMeasurable w (volume.restrict (Ioc 0 S))
  w_bounds : ∃ wlo whi : ℝ, 0 < wlo ∧
    ∀ᵐ s ∂(volume.restrict (Ioc 0 S)), wlo ≤ w s ∧ w s ≤ whi
  Ω_mem : MemLp Ω 2 (volume.restrict (Ioc 0 S))
  σ_mem : MemLp σ 2 (volume.restrict (Ioc 0 S))

namespace PhaseLockingData

variable {S : ℝ} {w Ω σ : ℝ → ℝ}

local notation "μ" => volume.restrict (Ioc (0:ℝ) S)

theorem w_ae_pos (hD : PhaseLockingData S w Ω σ) : ∀ᵐ s ∂μ, 0 < w s := by
  obtain ⟨wlo, whi, hlo, hb⟩ := hD.w_bounds
  filter_upwards [hb] with s hs using hlo.trans_le hs.1

theorem inv_memLp (hD : PhaseLockingData S w Ω σ) (p : ENNReal) :
    MemLp (fun s => (w s)⁻¹) p μ := by
  obtain ⟨wlo, whi, hlo, hb⟩ := hD.w_bounds
  refine MemLp.of_bound ?_ wlo⁻¹ ?_
  · exact (aestronglyMeasurable_iff_aemeasurable.2
      (aestronglyMeasurable_iff_aemeasurable.1 hD.w_meas).inv)
  · filter_upwards [hb] with s hs
    have hpos : 0 < w s := hlo.trans_le hs.1
    rw [Real.norm_eq_abs, abs_inv, abs_of_pos hpos]
    exact inv_anti₀ hlo hs.1

theorem w_memLp_top (hD : PhaseLockingData S w Ω σ) : ∃ C, ∀ᵐ s ∂μ, ‖w s‖ ≤ C := by
  obtain ⟨wlo, whi, hlo, hb⟩ := hD.w_bounds
  refine ⟨whi, ?_⟩
  filter_upwards [hb] with s hs
  rw [Real.norm_eq_abs, abs_of_pos (hlo.trans_le hs.1)]
  exact hs.2

theorem weighted_sq_integrable (hD : PhaseLockingData S w Ω σ) {f : ℝ → ℝ}
    (hf : MemLp f 2 μ) : Integrable (fun s => w s * f s ^ 2) μ := by
  obtain ⟨C, hC⟩ := hD.w_memLp_top
  exact hf.integrable_sq.bdd_mul' hD.w_meas hC

/-- The inverse-weight integral `I = ∫₀ˢ w⁻¹` is strictly positive. -/
theorem inv_integral_pos (hD : PhaseLockingData S w Ω σ) :
    0 < ∫ s in (0:ℝ)..S, (w s)⁻¹ := by
  rw [intervalIntegral.integral_of_le hD.pos.le]
  have hint : Integrable (fun s => (w s)⁻¹) μ := (hD.inv_memLp 1).integrable le_rfl
  refine (integral_pos_iff_support_of_nonneg_ae ?_ hint).2 ?_
  · filter_upwards [hD.w_ae_pos] with s hs
    exact (inv_pos.2 hs).le
  · have hsupp : (Ioc (0:ℝ) S) ∩ {s | 0 < w s} ⊆ Function.support (fun s => (w s)⁻¹) := by
      intro s hs
      exact (inv_pos.2 hs.2).ne'
    have hpos := hD.w_ae_pos
    rw [ae_restrict_iff' measurableSet_Ioc] at hpos
    have hmeas : volume (Ioc (0:ℝ) S \ {s | 0 < w s}) = 0 := by
      rw [ae_iff] at hpos
      refine measure_mono_null ?_ hpos
      intro s hs
      exact fun h => hs.2 (h hs.1)
    rw [Measure.restrict_apply' measurableSet_Ioc]
    have hIoc : volume (Ioc (0:ℝ) S) ≤ volume (Function.support (fun s => (w s)⁻¹) ∩ Ioc 0 S) := by
      calc volume (Ioc (0:ℝ) S)
          ≤ volume ((Ioc (0:ℝ) S ∩ {s | 0 < w s}) ∪ (Ioc (0:ℝ) S \ {s | 0 < w s})) := by
            apply measure_mono
            intro s hs
            by_cases h : 0 < w s
            · exact Or.inl ⟨hs, h⟩
            · exact Or.inr ⟨hs, h⟩
        _ ≤ volume (Ioc (0:ℝ) S ∩ {s | 0 < w s}) + volume (Ioc (0:ℝ) S \ {s | 0 < w s}) :=
            measure_union_le _ _
        _ = volume (Ioc (0:ℝ) S ∩ {s | 0 < w s}) := by rw [hmeas, add_zero]
        _ ≤ volume (Function.support (fun s => (w s)⁻¹) ∩ Ioc 0 S) := by
            apply measure_mono
            intro s hs
            exact ⟨hsupp hs, hs.1⟩
    refine lt_of_lt_of_le ?_ hIoc
    rw [Real.volume_Ioc]
    simpa using hD.pos

end PhaseLockingData

open PhaseLockingData

variable {S : ℝ} {w Ω σ : ℝ → ℝ}

local notation "μ" => volume.restrict (Ioc (0:ℝ) S)

theorem IsH1Phase.deriv_ae_eq {χ g : ℝ → ℝ}
    (hg : MemLp g 2 (volume.restrict (Ioc 0 S)))
    (hχ : ∀ s ∈ Icc 0 S, χ s = χ 0 + ∫ t in (0:ℝ)..s, g t) :
    deriv χ =ᵐ[volume.restrict (Ioc 0 S)] g := by
  filter_upwards [IsH1Phase.ae_hasDerivAt hg hχ] with s hs using hs.deriv

theorem IsH1Phase.deriv_memLp {χ : ℝ → ℝ} (hχ : IsH1Phase S χ) :
    MemLp (deriv χ) 2 (volume.restrict (Ioc 0 S)) := by
  obtain ⟨g, hg, hχ⟩ := hχ
  exact hg.ae_eq (IsH1Phase.deriv_ae_eq hg hχ).symm

theorem IsH1Phase.integral_deriv {χ : ℝ → ℝ} (hS : 0 ≤ S) (hχ : IsH1Phase S χ) :
    ∫ s in (0:ℝ)..S, deriv χ s = χ S - χ 0 := by
  obtain ⟨g, hg, hrep⟩ := hχ
  rw [hrep S ⟨hS, le_rfl⟩, add_sub_cancel_left, intervalIntegral.integral_of_le hS,
    intervalIntegral.integral_of_le hS]
  exact integral_congr_ae (IsH1Phase.deriv_ae_eq hg hrep)

/-- `Δₙ = 2πn − mΦ − J`. -/
noncomputable def closureMismatch (S : ℝ) (Ω σ : ℝ → ℝ) (m n : ℤ) : ℝ :=
  2 * Real.pi * n - m * (∫ s in (0:ℝ)..S, Ω s) - ∫ s in (0:ℝ)..S, σ s

/-- `I = ∫₀ˢ w⁻¹`. -/
noncomputable def inverseWeightIntegral (S : ℝ) (w : ℝ → ℝ) : ℝ :=
  ∫ s in (0:ℝ)..S, (w s)⁻¹

theorem inverseWeightIntegral_pos (hD : PhaseLockingData S w Ω σ) :
    0 < inverseWeightIntegral S w :=
  hD.inv_integral_pos

/-- The admissible `H¹` phases of winding number `n`. -/
def admissiblePhases (S : ℝ) (n : ℤ) : Set (ℝ → ℝ) :=
  {χ | IsH1Phase S χ ∧ χ S - χ 0 = 2 * Real.pi * n}

/-- The covariant phase gradient `q = χ' − mΩ`, with `χ'` the actual a.e. derivative. -/
noncomputable def covariantGradient (Ω : ℝ → ℝ) (m : ℤ) (χ : ℝ → ℝ) (s : ℝ) : ℝ :=
  deriv χ s - m * Ω s

/-- The weighted phase-locking energy `E[χ] = ∫₀ˢ w (q − σ)²`. -/
noncomputable def lockingEnergy (S : ℝ) (w Ω σ : ℝ → ℝ) (m : ℤ) (χ : ℝ → ℝ) : ℝ :=
  ∫ s in (0:ℝ)..S, w s * (covariantGradient Ω m χ s - σ s) ^ 2

/-- The optimal covariant gradient `q* = σ + Δₙ / (I w)`. -/
noncomputable def optimalGradient (S : ℝ) (w Ω σ : ℝ → ℝ) (m n : ℤ) (s : ℝ) : ℝ :=
  σ s + closureMismatch S Ω σ m n / (inverseWeightIntegral S w * w s)

/-- The explicit minimizing phase `χ* = χ₀ + ∫₀ˢ (mΩ + q*)`. -/
noncomputable def optimalPhase (S : ℝ) (w Ω σ : ℝ → ℝ) (m n : ℤ) (χ₀ : ℝ) (s : ℝ) : ℝ :=
  χ₀ + ∫ t in (0:ℝ)..s, (m * Ω t + optimalGradient S w Ω σ m n t)

/-- Completing the square against a constant multiplier. -/
theorem weighted_square_expansion (hD : PhaseLockingData S w Ω σ) {f : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioc 0 S))) (c : ℝ) :
    ∫ s in (0:ℝ)..S, w s * (f s - c / w s) ^ 2 =
      (∫ s in (0:ℝ)..S, w s * f s ^ 2) - 2 * c * (∫ s in (0:ℝ)..S, f s) +
        c ^ 2 * inverseWeightIntegral S w := by
  unfold inverseWeightIntegral
  simp only [intervalIntegral.integral_of_le hD.pos.le]
  have h1 : Integrable (fun s => w s * f s ^ 2) μ := hD.weighted_sq_integrable hf
  have h2 : Integrable f μ := hf.integrable one_le_two
  have h3 : Integrable (fun s => (w s)⁻¹) μ := (hD.inv_memLp 1).integrable le_rfl
  have hpt : (fun s => w s * (f s - c / w s) ^ 2) =ᵐ[μ]
      fun s => w s * f s ^ 2 - 2 * c * f s + c ^ 2 * (w s)⁻¹ := by
    filter_upwards [hD.w_ae_pos] with s hs
    field_simp
    ring
  have h12 : Integrable (fun s => w s * f s ^ 2 - 2 * c * f s) μ := h1.sub (h2.const_mul _)
  rw [integral_congr_ae hpt, integral_add h12 (h3.const_mul _),
    integral_sub h1 (h2.const_mul _), integral_const_mul, integral_const_mul]

theorem mismatch_memLp (hD : PhaseLockingData S w Ω σ) {χ : ℝ → ℝ} (hχ : IsH1Phase S χ)
    (m : ℤ) : MemLp (fun s => covariantGradient Ω m χ s - σ s) 2 μ :=
  (hχ.deriv_memLp.sub (hD.Ω_mem.const_mul (m : ℝ))).sub hD.σ_mem

theorem optimalGradient_memLp (hD : PhaseLockingData S w Ω σ) (m n : ℤ) :
    MemLp (optimalGradient S w Ω σ m n) 2 μ := by
  have h := hD.σ_mem.add ((hD.inv_memLp 2).const_mul
    (closureMismatch S Ω σ m n / inverseWeightIntegral S w))
  refine h.ae_eq (Eventually.of_forall fun s => ?_)
  simp only [Pi.add_apply, optimalGradient, div_eq_mul_inv, mul_inv]
  ring

theorem gradient_gap_memLp (hD : PhaseLockingData S w Ω σ) {χ : ℝ → ℝ} (hχ : IsH1Phase S χ)
    (m n : ℤ) :
    MemLp (fun s => covariantGradient Ω m χ s - optimalGradient S w Ω σ m n s) 2 μ :=
  (hχ.deriv_memLp.sub (hD.Ω_mem.const_mul (m : ℝ))).sub (optimalGradient_memLp hD m n)

theorem memLp_intervalIntegrable (hS : 0 ≤ S) {f : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioc 0 S))) : IntervalIntegrable f volume 0 S :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le hS).2 (hf.integrable one_le_two)

/-- Integrating the covariant mismatch against the winding constraint gives `Δₙ`. -/
theorem mismatch_integral (hD : PhaseLockingData S w Ω σ) (m : ℤ) {n : ℤ} {χ : ℝ → ℝ}
    (hχ : χ ∈ admissiblePhases S n) :
    ∫ s in (0:ℝ)..S, (covariantGradient Ω m χ s - σ s) = closureMismatch S Ω σ m n := by
  have hS := hD.pos.le
  have h1 := memLp_intervalIntegrable hS hχ.1.deriv_memLp
  have h2 := memLp_intervalIntegrable hS (hD.Ω_mem.const_mul (m : ℝ))
  have h3 := memLp_intervalIntegrable hS hD.σ_mem
  unfold covariantGradient closureMismatch
  rw [intervalIntegral.integral_sub (h1.sub h2) h3, intervalIntegral.integral_sub h1 h2,
    intervalIntegral.integral_const_mul, hχ.1.integral_deriv hS, hχ.2]

/-- **Exact remainder identity.** -/
theorem lockingEnergy_remainder (hD : PhaseLockingData S w Ω σ) (m n : ℤ) {χ : ℝ → ℝ}
    (hχ : χ ∈ admissiblePhases S n) :
    lockingEnergy S w Ω σ m χ =
      closureMismatch S Ω σ m n ^ 2 / inverseWeightIntegral S w +
        ∫ s in (0:ℝ)..S, w s *
          (covariantGradient Ω m χ s - optimalGradient S w Ω σ m n s) ^ 2 := by
  set Δ := closureMismatch S Ω σ m n with hΔ
  set I := inverseWeightIntegral S w with hIdef
  have hI : 0 < I := hD.inv_integral_pos
  have hexp := weighted_square_expansion hD (mismatch_memLp hD hχ.1 m) (Δ / I)
  have hcongr : (∫ s in (0:ℝ)..S, w s *
      (covariantGradient Ω m χ s - optimalGradient S w Ω σ m n s) ^ 2) =
      ∫ s in (0:ℝ)..S, w s * ((covariantGradient Ω m χ s - σ s) - (Δ / I) / w s) ^ 2 := by
    congr 1
    funext s
    simp only [optimalGradient, div_div]
    ring
  rw [hcongr, hexp, mismatch_integral hD m hχ]
  unfold lockingEnergy
  field_simp
  ring

theorem weighted_gap_nonneg (hD : PhaseLockingData S w Ω σ) (f : ℝ → ℝ) :
    0 ≤ ∫ s in (0:ℝ)..S, w s * f s ^ 2 := by
  rw [intervalIntegral.integral_of_le hD.pos.le]
  refine integral_nonneg_of_ae ?_
  filter_upwards [hD.w_ae_pos] with s hs
  exact mul_nonneg hs.le (sq_nonneg _)

/-- A weighted square integral vanishes exactly when the function vanishes a.e. -/
theorem weighted_gap_eq_zero_iff (hD : PhaseLockingData S w Ω σ) {f : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioc 0 S))) :
    (∫ s in (0:ℝ)..S, w s * f s ^ 2) = 0 ↔ f =ᵐ[volume.restrict (Ioc 0 S)] 0 := by
  rw [intervalIntegral.integral_of_le hD.pos.le,
    integral_eq_zero_iff_of_nonneg_ae _ (hD.weighted_sq_integrable hf)]
  · constructor
    · intro h
      filter_upwards [h, hD.w_ae_pos] with s hs hw
      have : w s * f s ^ 2 = 0 := hs
      rcases mul_eq_zero.1 this with h0 | h0
      · exact absurd h0 hw.ne'
      · exact pow_eq_zero_iff (two_ne_zero) |>.1 h0
    · intro h
      filter_upwards [h] with s hs
      simp [hs]
  · filter_upwards [hD.w_ae_pos] with s hs
    exact mul_nonneg hs.le (sq_nonneg _)

/-- The explicit phase is admissible in winding sector `n`. -/
theorem optimalPhase_mem (hD : PhaseLockingData S w Ω σ) (m n : ℤ) (χ₀ : ℝ) :
    optimalPhase S w Ω σ m n χ₀ ∈ admissiblePhases S n := by
  have hS := hD.pos.le
  have hg : MemLp (fun t => (m : ℝ) * Ω t + optimalGradient S w Ω σ m n t) 2 μ :=
    (hD.Ω_mem.const_mul (m : ℝ)).add (optimalGradient_memLp hD m n)
  refine ⟨⟨_, hg, fun s _ => ?_⟩, ?_⟩
  · simp [optimalPhase]
  · have hI : inverseWeightIntegral S w ≠ 0 := hD.inv_integral_pos.ne'
    have h1 := memLp_intervalIntegrable hS (hD.Ω_mem.const_mul (m : ℝ))
    have h2 := memLp_intervalIntegrable hS hD.σ_mem
    have h3 := memLp_intervalIntegrable hS ((hD.inv_memLp 2).const_mul
      (closureMismatch S Ω σ m n / inverseWeightIntegral S w))
    have hsplit : (fun t => (m : ℝ) * Ω t + optimalGradient S w Ω σ m n t) =
        fun t => ((m : ℝ) * Ω t + σ t) +
          (closureMismatch S Ω σ m n / inverseWeightIntegral S w) * (w t)⁻¹ := by
      funext t
      simp only [optimalGradient, div_eq_mul_inv, mul_inv]
      ring
    simp only [optimalPhase, intervalIntegral.integral_same, add_zero]
    rw [add_sub_cancel_left, hsplit, intervalIntegral.integral_add (h1.add h2) h3,
      intervalIntegral.integral_add h1 h2, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
    change _ + _ + closureMismatch S Ω σ m n / inverseWeightIntegral S w *
      inverseWeightIntegral S w = _
    rw [div_mul_cancel₀ _ hI]
    unfold closureMismatch
    ring

/-- The explicit phase realizes the optimal covariant gradient a.e. -/
theorem optimalPhase_gradient (hD : PhaseLockingData S w Ω σ) (m n : ℤ) (χ₀ : ℝ) :
    covariantGradient Ω m (optimalPhase S w Ω σ m n χ₀) =ᵐ[volume.restrict (Ioc 0 S)]
      optimalGradient S w Ω σ m n := by
  have hg : MemLp (fun t => (m : ℝ) * Ω t + optimalGradient S w Ω σ m n t) 2 μ :=
    (hD.Ω_mem.const_mul (m : ℝ)).add (optimalGradient_memLp hD m n)
  have hrep : ∀ s ∈ Icc 0 S, optimalPhase S w Ω σ m n χ₀ s =
      optimalPhase S w Ω σ m n χ₀ 0 +
        ∫ t in (0:ℝ)..s, ((m : ℝ) * Ω t + optimalGradient S w Ω σ m n t) := by
    intro s _
    simp [optimalPhase]
  filter_upwards [IsH1Phase.deriv_ae_eq hg hrep] with s hs
  simp only [covariantGradient, hs]
  ring

theorem optimalPhase_energy (hD : PhaseLockingData S w Ω σ) (m n : ℤ) (χ₀ : ℝ) :
    lockingEnergy S w Ω σ m (optimalPhase S w Ω σ m n χ₀) =
      closureMismatch S Ω σ m n ^ 2 / inverseWeightIntegral S w := by
  rw [lockingEnergy_remainder hD m n (optimalPhase_mem hD m n χ₀)]
  have hzero : (∫ s in (0:ℝ)..S, w s *
      (covariantGradient Ω m (optimalPhase S w Ω σ m n χ₀) s -
        optimalGradient S w Ω σ m n s) ^ 2) = 0 := by
    refine (weighted_gap_eq_zero_iff hD
      (gradient_gap_memLp hD (optimalPhase_mem hD m n χ₀).1 m n)).2 ?_
    filter_upwards [optimalPhase_gradient hD m n χ₀] with s hs
    simp [hs]
  rw [hzero, add_zero]

theorem lockingEnergy_lower_bound (hD : PhaseLockingData S w Ω σ) (m n : ℤ) {χ : ℝ → ℝ}
    (hχ : χ ∈ admissiblePhases S n) :
    closureMismatch S Ω σ m n ^ 2 / inverseWeightIntegral S w ≤
      lockingEnergy S w Ω σ m χ := by
  rw [lockingEnergy_remainder hD m n hχ]
  exact le_add_of_nonneg_right (weighted_gap_nonneg hD _)

/-- Equality in the lower bound holds exactly for the optimal covariant gradient. -/
theorem lockingEnergy_eq_min_iff (hD : PhaseLockingData S w Ω σ) (m n : ℤ) {χ : ℝ → ℝ}
    (hχ : χ ∈ admissiblePhases S n) :
    lockingEnergy S w Ω σ m χ = closureMismatch S Ω σ m n ^ 2 / inverseWeightIntegral S w ↔
      covariantGradient Ω m χ =ᵐ[volume.restrict (Ioc 0 S)] optimalGradient S w Ω σ m n := by
  rw [lockingEnergy_remainder hD m n hχ, add_eq_left,
    weighted_gap_eq_zero_iff hD (gradient_gap_memLp hD hχ.1 m n)]
  constructor
  · intro h
    filter_upwards [h] with s hs
    exact sub_eq_zero.1 hs
  · intro h
    filter_upwards [h] with s hs
    simp [hs]

/-- Every minimizer differs from the explicit phase by an additive constant. -/
theorem lockingEnergy_minimizer_unique (hD : PhaseLockingData S w Ω σ) (m n : ℤ) {χ : ℝ → ℝ}
    (hχ : χ ∈ admissiblePhases S n)
    (hmin : lockingEnergy S w Ω σ m χ =
      closureMismatch S Ω σ m n ^ 2 / inverseWeightIntegral S w) :
    ∃ c : ℝ, ∀ s ∈ Icc 0 S, χ s = optimalPhase S w Ω σ m n 0 s + c := by
  obtain ⟨g, hg, hrep⟩ := hχ.1
  have hq := (lockingEnergy_eq_min_iff hD m n hχ).1 hmin
  have hgq : g =ᵐ[volume.restrict (Ioc 0 S)]
      fun t => (m : ℝ) * Ω t + optimalGradient S w Ω σ m n t := by
    filter_upwards [IsH1Phase.deriv_ae_eq hg hrep, hq] with t ht hqt
    rw [← ht, ← hqt]
    simp [covariantGradient]
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioc] at hgq
  refine ⟨χ 0, fun s hs => ?_⟩
  rw [hrep s hs, optimalPhase, zero_add, add_comm]
  congr 1
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [hgq] with t ht htmem
  rw [uIoc_of_le hs.1] at htmem
  exact ht ⟨htmem.1, htmem.2.trans hs.2⟩

/-- **Theorem (exact weighted phase-locking minimum).**  For the actual `H¹`
phase class with winding `n`, the minimum of `E` is `Δₙ²/I`; it is attained by
the explicit phase `χ*`; every admissible phase satisfies the exact remainder
identity; minimizers are characterized by `q = q*` a.e. and are unique up to an
additive constant. -/
theorem phase_locking_exact_minimum (hD : PhaseLockingData S w Ω σ) (m n : ℤ) :
    IsLeast (lockingEnergy S w Ω σ m '' admissiblePhases S n)
        (closureMismatch S Ω σ m n ^ 2 / inverseWeightIntegral S w) ∧
    (∀ χ₀ : ℝ, optimalPhase S w Ω σ m n χ₀ ∈ admissiblePhases S n ∧
        lockingEnergy S w Ω σ m (optimalPhase S w Ω σ m n χ₀) =
          closureMismatch S Ω σ m n ^ 2 / inverseWeightIntegral S w) ∧
    (∀ χ ∈ admissiblePhases S n, lockingEnergy S w Ω σ m χ =
        closureMismatch S Ω σ m n ^ 2 / inverseWeightIntegral S w +
          ∫ s in (0:ℝ)..S, w s *
            (covariantGradient Ω m χ s - optimalGradient S w Ω σ m n s) ^ 2) ∧
    (∀ χ ∈ admissiblePhases S n,
        lockingEnergy S w Ω σ m χ =
            closureMismatch S Ω σ m n ^ 2 / inverseWeightIntegral S w ↔
          covariantGradient Ω m χ =ᵐ[volume.restrict (Ioc 0 S)]
            optimalGradient S w Ω σ m n) ∧
    (∀ χ ∈ admissiblePhases S n,
        lockingEnergy S w Ω σ m χ =
            closureMismatch S Ω σ m n ^ 2 / inverseWeightIntegral S w →
          ∃ c : ℝ, ∀ s ∈ Icc 0 S, χ s = optimalPhase S w Ω σ m n 0 s + c) := by
  refine ⟨⟨⟨_, optimalPhase_mem hD m n 0, optimalPhase_energy hD m n 0⟩, ?_⟩,
    fun χ₀ => ⟨optimalPhase_mem hD m n χ₀, optimalPhase_energy hD m n χ₀⟩,
    fun χ hχ => lockingEnergy_remainder hD m n hχ,
    fun χ hχ => lockingEnergy_eq_min_iff hD m n hχ,
    fun χ hχ hmin => lockingEnergy_minimizer_unique hD m n hχ hmin⟩
  rintro e ⟨χ, hχ, rfl⟩
  exact lockingEnergy_lower_bound hD m n hχ

/-- **Corollary (criterion for an exact lock).** -/
theorem exact_lock_criterion (hD : PhaseLockingData S w Ω σ) (m n : ℤ) :
    (∃ χ ∈ admissiblePhases S n,
        covariantGradient Ω m χ =ᵐ[volume.restrict (Ioc 0 S)] σ) ↔
      2 * Real.pi * n = m * (∫ s in (0:ℝ)..S, Ω s) + ∫ s in (0:ℝ)..S, σ s := by
  constructor
  · rintro ⟨χ, hχ, hlock⟩
    have h := mismatch_integral hD m hχ
    have hz : (∫ s in (0:ℝ)..S, (covariantGradient Ω m χ s - σ s)) = 0 := by
      rw [intervalIntegral.integral_of_le hD.pos.le]
      refine integral_eq_zero_of_ae ?_
      filter_upwards [hlock] with s hs
      simp [hs]
    rw [hz] at h
    unfold closureMismatch at h
    linarith
  · intro h
    have hΔ : closureMismatch S Ω σ m n = 0 := by
      unfold closureMismatch
      linarith
    refine ⟨_, optimalPhase_mem hD m n 0, ?_⟩
    filter_upwards [optimalPhase_gradient hD m n 0] with s hs
    rw [hs, optimalGradient, hΔ, zero_div, add_zero]

theorem exact_lock_min_zero_iff (hD : PhaseLockingData S w Ω σ) (m n : ℤ) :
    closureMismatch S Ω σ m n ^ 2 / inverseWeightIntegral S w = 0 ↔
      closureMismatch S Ω σ m n = 0 := by
  rw [div_eq_zero_iff, or_iff_left (inverseWeightIntegral_pos hD).ne',
    pow_eq_zero_iff two_ne_zero]

theorem optimalPhase_density_memLp (hD : PhaseLockingData S w Ω σ) (m n : ℤ) :
    MemLp (fun t => (m : ℝ) * Ω t + optimalGradient S w Ω σ m n t) 2 μ :=
  (hD.Ω_mem.const_mul (m : ℝ)).add (optimalGradient_memLp hD m n)

theorem optimalPhase_rep (m n : ℤ) (χ₀ : ℝ) :
    ∀ s ∈ Icc 0 S, optimalPhase S w Ω σ m n χ₀ s =
      optimalPhase S w Ω σ m n χ₀ 0 +
        ∫ t in (0:ℝ)..s, ((m : ℝ) * Ω t + optimalGradient S w Ω σ m n t) := by
  intro s _
  simp [optimalPhase]

theorem memLp_intervalIntegrable_of_mem (hS : 0 ≤ S) {f : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioc 0 S))) {s : ℝ} (hs : s ∈ Icc 0 S) :
    IntervalIntegrable f volume 0 s := by
  refine (memLp_intervalIntegrable hS hf).mono_set ?_
  rw [uIcc_of_le hS, uIcc_of_le hs.1]
  exact Icc_subset_Icc le_rfl hs.2

/-- **Corollary (strict phase-sector variational stability)**: a periodic `H¹`
perturbation of the minimizer stays admissible and raises the energy by exactly
`ε² ∫ w |η'|²`. -/
theorem optimalPhase_perturbation (hD : PhaseLockingData S w Ω σ) (m n : ℤ) {η : ℝ → ℝ}
    (hη : IsH1Phase S η) (hper : η S = η 0) (ε : ℝ) :
    (fun s => optimalPhase S w Ω σ m n 0 s + ε * η s) ∈ admissiblePhases S n ∧
    lockingEnergy S w Ω σ m (fun s => optimalPhase S w Ω σ m n 0 s + ε * η s) =
      lockingEnergy S w Ω σ m (optimalPhase S w Ω σ m n 0) +
        ε ^ 2 * ∫ s in (0:ℝ)..S, w s * deriv η s ^ 2 := by
  have hS := hD.pos.le
  obtain ⟨gη, hgη, hrepη⟩ := hη
  have hgs := optimalPhase_density_memLp hD m n
  have hreps := optimalPhase_rep (S := S) (w := w) (Ω := Ω) (σ := σ) m n 0
  have hmem : (fun s => optimalPhase S w Ω σ m n 0 s + ε * η s) ∈ admissiblePhases S n := by
    refine ⟨⟨fun t => ((m : ℝ) * Ω t + optimalGradient S w Ω σ m n t) + ε * gη t,
      hgs.add (hgη.const_mul ε), fun s hs => ?_⟩, ?_⟩
    · have hi1 := memLp_intervalIntegrable_of_mem hS hgs hs
      have hi2 := memLp_intervalIntegrable_of_mem hS hgη hs
      simp only
      rw [intervalIntegral.integral_add hi1 (hi2.const_mul ε),
        intervalIntegral.integral_const_mul, hreps s hs, hrepη s hs]
      ring
    · have h := (optimalPhase_mem hD m n 0).2
      simp only
      rw [hper]
      linarith
  refine ⟨hmem, ?_⟩
  rw [lockingEnergy_remainder hD m n hmem, optimalPhase_energy hD m n 0,
    ← intervalIntegral.integral_const_mul]
  congr 1
  rw [intervalIntegral.integral_of_le hS, intervalIntegral.integral_of_le hS]
  refine integral_congr_ae ?_
  filter_upwards [IsH1Phase.ae_hasDerivAt hgs hreps, IsH1Phase.ae_hasDerivAt hgη hrepη]
    with s h1 h2
  have hsum : deriv (fun s => optimalPhase S w Ω σ m n 0 s + ε * η s) s =
      ((m : ℝ) * Ω s + optimalGradient S w Ω σ m n s) + ε * gη s :=
    (h1.add (h2.const_mul ε)).deriv
  simp only [covariantGradient, hsum, h2.deriv]
  ring

/-- The second variation along a periodic perturbation is `2 ∫ w |η'|²`. -/
theorem optimalPhase_second_variation (hD : PhaseLockingData S w Ω σ) (m n : ℤ)
    {η : ℝ → ℝ} (hη : IsH1Phase S η) (hper : η S = η 0) :
    deriv (deriv fun ε : ℝ =>
        lockingEnergy S w Ω σ m (fun s => optimalPhase S w Ω σ m n 0 s + ε * η s)) 0 =
      2 * ∫ s in (0:ℝ)..S, w s * deriv η s ^ 2 := by
  set A := lockingEnergy S w Ω σ m (optimalPhase S w Ω σ m n 0)
  set W := ∫ s in (0:ℝ)..S, w s * deriv η s ^ 2
  have hfun : (fun ε : ℝ =>
      lockingEnergy S w Ω σ m (fun s => optimalPhase S w Ω σ m n 0 s + ε * η s)) =
      fun ε => A + W * ε ^ 2 := by
    funext ε
    rw [(optimalPhase_perturbation hD m n hη hper ε).2]
    ring
  have hd : deriv (fun ε : ℝ => A + W * ε ^ 2) = fun ε => W * (2 * ε) := by
    funext ε
    have h : HasDerivAt (fun ε : ℝ => A + W * ε ^ 2) (W * (2 * ε)) ε := by
      have := ((hasDerivAt_pow 2 ε).const_mul W).const_add A
      simpa using this
    exact h.deriv
  rw [hfun, hd]
  have h : HasDerivAt (fun ε : ℝ => W * (2 * ε)) (W * 2) 0 := by
    have := ((hasDerivAt_id (0:ℝ)).const_mul 2).const_mul W
    simpa using this
  rw [h.deriv]
  ring

/-- The second variation vanishes exactly for perturbations that are constant on `[0,S]`. -/
theorem perturbation_weight_eq_zero_iff (hD : PhaseLockingData S w Ω σ) {η : ℝ → ℝ}
    (hη : IsH1Phase S η) :
    (∫ s in (0:ℝ)..S, w s * deriv η s ^ 2) = 0 ↔ ∀ s ∈ Icc 0 S, η s = η 0 := by
  constructor
  · intro h
    obtain ⟨g, hg, hrep⟩ := hη
    have hd := (weighted_gap_eq_zero_iff hD (IsH1Phase.deriv_memLp ⟨g, hg, hrep⟩)).1 h
    have hg0 : g =ᵐ[volume.restrict (Ioc 0 S)] 0 := by
      filter_upwards [hd, IsH1Phase.deriv_ae_eq hg hrep] with t ht ht'
      rw [← ht', ht]
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioc] at hg0
    intro s hs
    rw [hrep s hs]
    have : (∫ t in (0:ℝ)..s, g t) = 0 := by
      rw [intervalIntegral.integral_congr_ae (g := fun _ => (0:ℝ)) ?_]
      · simp
      filter_upwards [hg0] with t ht htmem
      rw [uIoc_of_le hs.1] at htmem
      exact ht ⟨htmem.1, htmem.2.trans hs.2⟩
    rw [this, add_zero]
  · intro hconst
    rw [weighted_gap_eq_zero_iff hD hη.deriv_memLp]
    have hIoo : ∀ᵐ s ∂(volume.restrict (Ioc 0 S)), s ∈ Ioo 0 S := by
      rw [ae_restrict_iff' measurableSet_Ioc]
      have : ∀ᵐ s ∂volume, s ≠ S := by
        rw [ae_iff]
        simp
      filter_upwards [this] with s hs h
      exact ⟨h.1, lt_of_le_of_ne h.2 hs⟩
    filter_upwards [hIoo] with s hs
    have hloc : η =ᶠ[𝓝 s] fun _ => η 0 := by
      filter_upwards [Ioo_mem_nhds hs.1 hs.2] with x hx
      exact hconst x ⟨hx.1.le, hx.2.le⟩
    exact ((hasDerivAt_const s (η 0)).congr_of_eventuallyEq hloc).deriv

/-- The minimum energy of winding sector `n`. -/
noncomputable def sectorMinimum (S : ℝ) (w Ω σ : ℝ → ℝ) (m n : ℤ) : ℝ :=
  closureMismatch S Ω σ m n ^ 2 / inverseWeightIntegral S w

/-- `ζ = (mΦ + J) / (2π)`. -/
noncomputable def windingCenter (S : ℝ) (Ω σ : ℝ → ℝ) (m : ℤ) : ℝ :=
  (m * (∫ s in (0:ℝ)..S, Ω s) + ∫ s in (0:ℝ)..S, σ s) / (2 * Real.pi)

theorem sectorMinimum_eq (S : ℝ) (w Ω σ : ℝ → ℝ) (m n : ℤ) :
    sectorMinimum S w Ω σ m n =
      4 * Real.pi ^ 2 / inverseWeightIntegral S w * ((n : ℝ) - windingCenter S Ω σ m) ^ 2 := by
  unfold sectorMinimum closureMismatch windingCenter
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-- **Proposition (conditional comparison of winding sectors).** The sectors of least
minimum energy are exactly the integers nearest to `ζ`. -/
theorem sector_selection (hD : PhaseLockingData S w Ω σ) (m : ℤ) :
    {n : ℤ | ∀ n' : ℤ, sectorMinimum S w Ω σ m n ≤ sectorMinimum S w Ω σ m n'} =
      {n : ℤ | ∀ n' : ℤ, |(n : ℝ) - windingCenter S Ω σ m| ≤
        |(n' : ℝ) - windingCenter S Ω σ m|} := by
  have hc : 0 < 4 * Real.pi ^ 2 / inverseWeightIntegral S w := by
    have := inverseWeightIntegral_pos hD
    positivity
  ext n
  simp only [Set.mem_setOf_eq, sectorMinimum_eq]
  refine forall_congr' fun n' => ?_
  rw [mul_le_mul_iff_of_pos_left hc, sq_le_sq]

theorem nearest_integers_unique (ζ : ℝ) (hζ : ∀ k : ℤ, ζ ≠ k + 1 / 2) :
    {n : ℤ | ∀ n' : ℤ, |(n : ℝ) - ζ| ≤ |(n' : ℝ) - ζ|} = {round ζ} := by
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · intro hn
    by_contra hne
    have h1 := hn (round ζ)
    have h2 : |ζ - round ζ| ≤ 1 / 2 := abs_sub_round ζ
    have h3 : (1 : ℝ) ≤ |(n : ℝ) - round ζ| := by
      have : n - round ζ ≠ 0 := sub_ne_zero.2 hne
      have h := Int.one_le_abs this
      exact_mod_cast h
    have h4 : |(n : ℝ) - round ζ| ≤ |(n : ℝ) - ζ| + |ζ - round ζ| := abs_sub_le _ _ _
    rw [abs_sub_comm ((round ζ : ℤ) : ℝ) ζ] at h1
    have h5 : |(n : ℝ) - ζ| = 1 / 2 := by linarith
    rcases abs_eq (by norm_num : (0:ℝ) ≤ 1 / 2) |>.1 h5 with h | h
    · exact hζ (n - 1) (by push_cast; linarith)
    · exact hζ n (by linarith)
  · rintro rfl n'
    rw [abs_sub_comm, abs_sub_comm (n' : ℝ)]
    exact round_le ζ n'

theorem nearest_integers_tie (k : ℤ) :
    {n : ℤ | ∀ n' : ℤ, |(n : ℝ) - (k + 1 / 2)| ≤ |(n' : ℝ) - (k + 1 / 2)|} = {k, k + 1} := by
  have key : ∀ j : ℤ, (1 / 2 : ℝ) ≤ |(j : ℝ) - (k + 1 / 2)| := by
    intro j
    rcases le_or_gt j k with h | h
    · have : (j : ℝ) ≤ k := by exact_mod_cast h
      rw [abs_of_neg (by linarith)]
      linarith
    · have : (k : ℝ) + 1 ≤ j := by exact_mod_cast h
      rw [abs_of_pos (by linarith)]
      linarith
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro hn
    have h := hn k
    have hk : |(k : ℝ) - (k + 1 / 2)| = 1 / 2 := by
      rw [show (k : ℝ) - (k + 1 / 2) = -(1 / 2) by ring, abs_neg, abs_of_pos (by norm_num)]
    rw [hk, abs_le] at h
    have h1 : (k : ℝ) ≤ n := by linarith [h.1]
    have h2 : (n : ℝ) ≤ k + 1 := by linarith [h.2]
    have h1' : k ≤ n := by exact_mod_cast h1
    have h2' : n ≤ k + 1 := by exact_mod_cast h2
    omega
  · rintro (rfl | rfl) n'
    · have hk : |(n : ℝ) - (n + 1 / 2)| = 1 / 2 := by
        rw [show (n : ℝ) - (n + 1 / 2) = -(1 / 2) by ring, abs_neg, abs_of_pos (by norm_num)]
      rw [hk]
      exact key n'
    · have hk : |((k + 1 : ℤ) : ℝ) - (k + 1 / 2)| = 1 / 2 := by
        push_cast
        rw [show (k : ℝ) + 1 - (k + 1 / 2) = 1 / 2 by ring, abs_of_pos (by norm_num)]
      rw [hk]
      exact key n'

/-- **Uniform-weight example.** -/
theorem uniform_weight_example {S w₀ σ₀ : ℝ} (hS : 0 < S) (hw : 0 < w₀) (m n : ℤ) :
    sectorMinimum S (fun _ => w₀) (fun _ => 0) (fun _ => σ₀) m n =
        w₀ / S * (2 * Real.pi * n - S * σ₀) ^ 2 ∧
      ∀ s, optimalGradient S (fun _ => w₀) (fun _ => 0) (fun _ => σ₀) m n s =
        2 * Real.pi * n / S := by
  have hI : inverseWeightIntegral S (fun _ => w₀) = S / w₀ := by
    simp [inverseWeightIntegral, div_eq_mul_inv]
  have hΔ : closureMismatch S (fun _ => 0) (fun _ => σ₀) m n = 2 * Real.pi * n - S * σ₀ := by
    simp [closureMismatch]
  refine ⟨?_, fun s => ?_⟩
  · rw [sectorMinimum, hI, hΔ]
    field_simp
  · rw [optimalGradient, hI, hΔ]
    field_simp
    ring

end ReyesMath
