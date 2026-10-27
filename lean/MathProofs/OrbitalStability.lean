import Mathlib
import MathProofs.CubicQuinticFlow

/-!
# Existence, compactness and full-set orbital stability (F01/T3)

Formalization of `papers/orbital-stability-fourth-order-cubic-quintic/main.tex` on `H²(ℝ²; ℂ)`
(`MathProofs.SobolevH2`), with `H(u) = ‖(Δ + k²)u‖² − (β/2)‖u‖⁴_{L⁴} + (γ/3)‖u‖⁶_{L⁶}`,
`I(m) = inf {H(u) : M(u) = m}` and `𝒢_m = {u : M(u) = m, H(u) = I(m)}`.

* Lemma (coercivity at fixed mass): `OrbitalStability.coercivity` and
  `OrbitalStability.bounded_of_mass_energy`.
* Lemma (strict negativity): `NegativeEnergy.negative_constrained_energy`; the energy-per-mass
  lemmas and Proposition (strict binding) are in `MathProofs.StrictBinding`
  (`StrictBinding.exists_stationary_minimizing_seq`, `Sobolev.H2.S_le_of_stationary`,
  `StrictBinding.gap`, `StrictBinding.strict_binding`); Proposition (compactness modulo
  translations) is `WholeSpace.compactness`.
* Proposition (global well-posedness and conservation): `OrbitalStability.global_flow`, from
  `MathProofs.CubicQuinticFlow`.
* `OrbitalStability.Gset` (`𝒢_m`) and `OrbitalStability.distX` (`dist_X(v, E) = inf_{g ∈ E}
  ‖v − g‖_{H²}`, with the equivalent `H²` distance `Sobolev.H2.distH2`).
* `OrbitalStability.stable_core`: the Cazenave–Lions argument (conservation, mass normalization
  `wₙ = √(m/M(vₙ)) vₙ`, compactness modulo translations), valid for perturbations of any mass;
  `OrbitalStability.orbital_stability`: Theorem (iv).
* **Theorem** `OrbitalStability.main`: parts (i)–(iv) for `β, γ > 0`, every `k` and
  `0 < m ≤ m_B = 3β/(γ√(k⁴ + 3β²/(32γ)))`.
-/

open Filter Topology Complex InnerProductSpace MeasureTheory Set
open scoped ContDiff FourierTransform NNReal

namespace ReyesMath

namespace OrbitalStability

open Sobolev Sobolev.H2

local notation "R2" => EuclideanSpace ℝ (Fin 2)

variable {β γ k : ℝ}

/-- **Lemma (coercivity at fixed mass).**  With `C₀ = 3β²/(16γ)`:
`H(u) ≥ T(u) − C₀ M(u)`, `‖Δu‖₂ ≤ √(H(u) + C₀M(u)) + k²√M(u)`, and the `H²` norm is controlled by
mass and energy. -/
theorem coercivity (hγ : 0 < γ) (U : H2 2) :
    T k U - 3 * β ^ 2 / (16 * γ) * M U ≤ energy β γ k U ∧
    ‖U.lap‖ ≤ Real.sqrt (energy β γ k U + 3 * β ^ 2 / (16 * γ) * M U) + k ^ 2 * Real.sqrt (M U) ∧
    ‖toSp U‖ ^ 2 ≤ Bd β γ k (M U) (energy β γ k U) := by
  refine ⟨energy_ge β γ k hγ U, ?_, norm_toSp_sq_le hγ U⟩
  have h := (StrictBinding.bounded_of_energy_le (k := k) hγ (m := M U)
    (C₀ := energy β γ k U) rfl le_rfl).1
  have hnn : 0 ≤ Real.sqrt (energy β γ k U + 3 * β ^ 2 / (16 * γ) * M U) +
      k ^ 2 * Real.sqrt (M U) := by positivity
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hnn two_ne_zero).1 h

/-- On a set of bounded mass and bounded-above energy the `H²` norm is uniformly bounded. -/
theorem bounded_of_mass_energy (hγ : 0 < γ) (m₀ E₀ : ℝ) :
    ∃ C, ∀ U : H2 2, M U ≤ m₀ → energy β γ k U ≤ E₀ → ‖toSp U‖ ≤ C := by
  refine ⟨Real.sqrt (Bd β γ k m₀ E₀), fun U hM hE => Real.le_sqrt_of_sq_le ?_⟩
  refine (norm_toSp_sq_le (β := β) (k := k) hγ U).trans ?_
  have hc : 0 ≤ 3 * β ^ 2 / (16 * γ) := by positivity
  have hk : 0 ≤ 2 + 3 * k ^ 4 := by positivity
  unfold Bd
  nlinarith [mul_le_mul_of_nonneg_left hM hc, mul_le_mul_of_nonneg_left hM hk]

/-- The minimizing set `𝒢_m = {u ∈ H² : M(u) = m, H(u) = I(m)}`. -/
def Gset (β γ k m : ℝ) : Set (H2 2) := {U | M U = m ∧ energy β γ k U = Imin β γ k m}

/-- `dist_X(v, E) = inf_{g ∈ E} ‖v − g‖_{H²}`. -/
noncomputable def distX (v : H2 2) (E : Set (H2 2)) : ℝ := ⨅ g : E, distH2 v g

theorem distX_nonneg (v : H2 2) (E : Set (H2 2)) : 0 ≤ distX v E :=
  Real.iInf_nonneg fun _ => distH2_nonneg _ _

theorem distX_le {v g : H2 2} {E : Set (H2 2)} (hg : g ∈ E) : distX v E ≤ distH2 v g := by
  refine ciInf_le ⟨0, ?_⟩ (⟨g, hg⟩ : E)
  rintro _ ⟨g', rfl⟩
  exact distH2_nonneg _ _

theorem exists_of_distX_lt {v : H2 2} {E : Set (H2 2)} (hE : E.Nonempty) {δ : ℝ}
    (h : distX v E < δ) : ∃ g ∈ E, distH2 v g < δ := by
  haveI : Nonempty E := hE.to_subtype
  obtain ⟨⟨g, hg⟩, h'⟩ := exists_lt_of_ciInf_lt h
  exact ⟨g, hg, h'⟩

theorem translate_mem_Gset {m : ℝ} {U : H2 2} (hU : U ∈ Gset β γ k m) (y : R2) :
    translate y U ∈ Gset β γ k m :=
  ⟨by rw [M_translate]; exact hU.1, by rw [energy_translate]; exact hU.2⟩

theorem norm_toSp_le_of_mem (hγ : 0 < γ) {m : ℝ} {U : H2 2} (hU : U ∈ Gset β γ k m) :
    ‖toSp U‖ ≤ Real.sqrt (Bd β γ k m (Imin β γ k m)) := by
  have h := norm_toSp_sq_le (β := β) (k := k) hγ U
  rw [hU.1, hU.2] at h
  exact Real.le_sqrt_of_sq_le h

/-- **Cazenave–Lions step:** data close to `𝒢_m` stay close, for every pair of states with equal
mass and energy (mass changes are allowed). -/
theorem stable_core (hβ : 0 < β) (hγ : 0 < γ) {m : ℝ} (hm : 0 < m)
    (hmB : m ≤ StrictBinding.mB β γ k) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ v₀ v : H2 2, M v = M v₀ → energy β γ k v = energy β γ k v₀ →
      distX v₀ (Gset β γ k m) < δ → distX v (Gset β γ k m) < ε := by
  by_contra hcon
  push_neg at hcon
  have hseq : ∀ n : ℕ, ∃ v₀ v : H2 2, M v = M v₀ ∧ energy β γ k v = energy β γ k v₀ ∧
      distX v₀ (Gset β γ k m) < 1 / ((n : ℝ) + 1) ∧ ε ≤ distX v (Gset β γ k m) :=
    fun n => hcon _ (by positivity)
  choose v₀ v hMv hEv hd₀ hdv using hseq
  obtain ⟨G₀, hG₀m, hG₀E⟩ := WholeSpace.exists_minimizer (k := k) hβ hγ hm hmB
  have hGne : (Gset β γ k m).Nonempty := ⟨G₀, hG₀m, hG₀E⟩
  have hgex : ∀ n, ∃ g ∈ Gset β γ k m, distH2 (v₀ n) g < 1 / ((n : ℝ) + 1) :=
    fun n => exists_of_distX_lt hGne (hd₀ n)
  choose g hgG hgd using hgex
  -- uniform bounds near `𝒢_m`
  obtain ⟨C₀, hC₀⟩ : ∃ C₀, C₀ = Bd β γ k m (Imin β γ k m) := ⟨_, rfl⟩
  obtain ⟨R₁, hR₁⟩ : ∃ R₁, R₁ = Real.sqrt C₀ + 1 := ⟨_, rfl⟩
  have hR₁0 : 0 ≤ R₁ := by rw [hR₁]; positivity
  have hg_le : ∀ n, ‖toSp (g n)‖ ≤ R₁ := fun n => by
    have h := norm_toSp_le_of_mem hγ (hgG n)
    rw [← hC₀] at h
    rw [hR₁]
    linarith
  have hdist : ∀ n, ‖toSp (v₀ n) - toSp (g n)‖ ≤ 1 / ((n : ℝ) + 1) := fun n =>
    (norm_le_distH2 _ _).trans (hgd n).le
  have hone : ∀ n : ℕ, 1 / ((n : ℝ) + 1) ≤ 1 := fun n => by
    rw [div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hv₀_le : ∀ n, ‖toSp (v₀ n)‖ ≤ R₁ + 1 := fun n => by
    have h1 := norm_le_norm_add_norm_sub' (toSp (v₀ n)) (toSp (g n))
    linarith [hg_le n, hdist n, hone n]
  have h1n : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  -- the masses and energies converge
  have hM₀ : Tendsto (fun n => M (v₀ n)) atTop (𝓝 m) := by
    have hb : Tendsto (fun n : ℕ => 2 * (R₁ + 1) * (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
      have h := h1n.const_mul (2 * (R₁ + 1))
      rwa [mul_zero] at h
    refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun n => norm_nonneg _)
      (fun n => ?_) hb)
    have h := mass_lip (hv₀_le n) ((hg_le n).trans (by linarith))
    rw [← M_eq_vl, ← M_eq_vl, (hgG n).1] at h
    rw [Real.norm_eq_abs]
    exact h.trans (mul_le_mul_of_nonneg_left (hdist n) (by positivity))
  have hE₀ : Tendsto (fun n => energy β γ k (v₀ n)) atTop (𝓝 (Imin β γ k m)) := by
    have hb : Tendsto (fun n : ℕ => Lam β γ k (R₁ + 1) * (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
      have h := h1n.const_mul (Lam β γ k (R₁ + 1))
      rwa [mul_zero] at h
    refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun n => norm_nonneg _)
      (fun n => ?_) hb)
    have h := Esp_lip β γ k (by linarith) (hv₀_le n) ((hg_le n).trans (by linarith))
    rw [← energy_eq_Esp, ← energy_eq_Esp, (hgG n).2] at h
    rw [Real.norm_eq_abs]
    refine h.trans (mul_le_mul_of_nonneg_left (hdist n) ?_)
    unfold Lam
    have := LF_nonneg β γ (R := R₁ + 1)
    positivity
  have hMv' : Tendsto (fun n => M (v n)) atTop (𝓝 m) := hM₀.congr fun n => (hMv n).symm
  have hEv' : Tendsto (fun n => energy β γ k (v n)) atTop (𝓝 (Imin β γ k m)) :=
    hE₀.congr fun n => (hEv n).symm
  -- mass normalization
  have hBd : Tendsto (fun n => Bd β γ k (M (v n)) (energy β γ k (v n))) atTop (𝓝 C₀) := by
    rw [hC₀]
    unfold Bd
    exact ((hEv'.add (hMv'.const_mul _)).const_mul 3).add (hMv'.const_mul _)
  have hα : Tendsto (fun n => Real.sqrt (m / M (v n))) atTop (𝓝 1) := by
    have h := (Real.continuous_sqrt.tendsto _).comp ((tendsto_const_nhds (x := m)).div hMv' hm.ne')
    rwa [div_self hm.ne', Real.sqrt_one] at h
  have hev : ∀ᶠ n in atTop, m / 2 < M (v n) ∧
      Bd β γ k (M (v n)) (energy β γ k (v n)) < C₀ + 1 ∧ Real.sqrt (m / M (v n)) < 2 :=
    (hMv'.eventually (lt_mem_nhds (half_lt_self hm))).and
      ((hBd.eventually (gt_mem_nhds (lt_add_one _))).and
        (hα.eventually (gt_mem_nhds one_lt_two)))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  obtain ⟨R₂, hR₂⟩ : ∃ R₂, R₂ = Real.sqrt (C₀ + 1) := ⟨_, rfl⟩
  have hR₂0 : 0 ≤ R₂ := by rw [hR₂]; positivity
  obtain ⟨α, hαd⟩ : ∃ α : ℕ → ℝ, α = fun n => Real.sqrt (m / M (v (n + N))) := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : ℕ → H2 2, w = fun n => H2.smul (α n : ℂ) (v (n + N)) := ⟨_, rfl⟩
  have hα0 : ∀ n, 0 ≤ α n := fun n => by rw [hαd]; exact Real.sqrt_nonneg _
  have hα2 : ∀ n, α n < 2 := fun n => by rw [hαd]; exact (hN (n + N) (Nat.le_add_left _ _)).2.2
  have hvR : ∀ n, ‖toSp (v (n + N))‖ ≤ R₂ := fun n => by
    have h := norm_toSp_sq_le (β := β) (k := k) hγ (v (n + N))
    rw [hR₂]
    exact Real.le_sqrt_of_sq_le (h.trans (hN (n + N) (Nat.le_add_left _ _)).2.1.le)
  have hMw : ∀ n, M (w n) = m := fun n => by
    have hpos := (hN (n + N) (Nat.le_add_left _ _)).1
    have hMpos : 0 < M (v (n + N)) := lt_trans (half_pos hm) hpos
    rw [hw]
    show M (H2.smul (α n : ℂ) (v (n + N))) = m
    rw [H2.M_smul, Complex.norm_real, Real.norm_eq_abs, sq_abs, hαd]
    show Real.sqrt (m / M (v (n + N))) ^ 2 * M (v (n + N)) = m
    rw [Real.sq_sqrt (div_nonneg hm.le hMpos.le), div_mul_cancel₀ _ hMpos.ne']
  have hwv : ∀ n, ‖toSp (w n) - toSp (v (n + N))‖ ≤ |α n - 1| * R₂ := fun n => by
    have e : toSp (w n) - toSp (v (n + N)) = ((α n - 1 : ℝ) : ℂ) • toSp (v (n + N)) := by
      rw [hw]
      show toSp (H2.smul (α n : ℂ) (v (n + N))) - toSp (v (n + N)) = _
      rw [toSp_smul, Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul]
    rw [e, norm_smul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hvR n) (abs_nonneg _)
  have hwR : ∀ n, ‖toSp (w n)‖ ≤ 2 * R₂ := fun n => by
    have e : toSp (w n) = ((α n : ℝ) : ℂ) • toSp (v (n + N)) := by
      rw [hw]
      exact toSp_smul _ _
    rw [e, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hα0 n)]
    exact mul_le_mul (hα2 n).le (hvR n) (norm_nonneg _) zero_le_two
  have hαN : Tendsto (fun n => |α n - 1| * R₂) atTop (𝓝 0) := by
    have h := (hα.comp (tendsto_add_atTop_nat N)).sub_const 1
    rw [sub_self] at h
    have h' := h.abs.mul_const R₂
    rw [abs_zero, zero_mul] at h'
    refine h'.congr fun n => ?_
    rw [hαd]
    rfl
  have hEw : Tendsto (fun n => energy β γ k (w n)) atTop (𝓝 (Imin β γ k m)) := by
    have hEvN := hEv'.comp (tendsto_add_atTop_nat N)
    have hdiff : Tendsto (fun n => energy β γ k (w n) - energy β γ k (v (n + N))) atTop
        (𝓝 0) := by
      have hb := hαN.const_mul (Lam β γ k (2 * R₂))
      rw [mul_zero] at hb
      refine squeeze_zero_norm (fun n => ?_) hb
      have h := Esp_lip β γ k (by positivity) (hwR n) ((hvR n).trans (by linarith))
      rw [← energy_eq_Esp, ← energy_eq_Esp] at h
      rw [Real.norm_eq_abs]
      refine h.trans (mul_le_mul_of_nonneg_left (hwv n) ?_)
      unfold Lam
      have := LF_nonneg β γ (R := 2 * R₂)
      positivity
    have h := hdiff.add hEvN
    rw [zero_add] at h
    refine h.congr fun n => ?_
    simp only [Function.comp_apply, sub_add_cancel]
  -- compactness of minimizing sequences
  obtain ⟨φ, hφ, y, U, hUm, hUE, hconv⟩ :=
    WholeSpace.compactness (k := k) hβ hγ hm hmB hMw hEw
  have hUG : U ∈ Gset β γ k m := ⟨hUm, hUE⟩
  have hφt : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have hdvw : Tendsto (fun n => distH2 (v (φ n + N)) (w (φ n))) atTop (𝓝 0) := by
    have hb := (hαN.comp hφt).const_mul 4
    rw [mul_zero] at hb
    refine squeeze_zero (fun n => distH2_nonneg _ _) (fun n => ?_) hb
    rw [distH2_comm]
    refine (distH2_le_four _ _).trans ?_
    exact mul_le_mul_of_nonneg_left (hwv (φ n)) (by norm_num)
  have hlim : Tendsto (fun n => distX (v (φ n + N)) (Gset β γ k m)) atTop (𝓝 0) := by
    have hb := hdvw.add hconv
    rw [add_zero] at hb
    refine squeeze_zero (fun n => distX_nonneg _ _) (fun n => ?_) hb
    have hmem := translate_mem_Gset hUG (-y n)
    refine (distX_le hmem).trans ((distH2_triangle _ (w (φ n)) _).trans ?_)
    have e : distH2 (w (φ n)) (translate (-y n) U) = distH2 (translate (y n) (w (φ n))) U := by
      rw [← distH2_translate (y n), translate_translate_neg]
    rw [e]
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds hε)).exists
  exact absurd (hdv (φ n + N)) (not_le.2 hn)

/-- **Theorem (iv): orbital stability of the full minimizing set** `𝒢_m`, for perturbations of
arbitrary mass. -/
theorem orbital_stability (hβ : 0 < β) (hγ : 0 < γ) {m : ℝ} (hm : 0 < m)
    (hmB : m ≤ StrictBinding.mB β γ k) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ u : ℝ → H2 2, IsSolution β γ k u → distX (u 0) (Gset β γ k m) < δ →
      BddAbove (Set.range fun t => distX (u t) (Gset β γ k m)) ∧
      ⨆ t, distX (u t) (Gset β γ k m) < ε := by
  obtain ⟨δ, hδ, hcore⟩ := stable_core hβ hγ hm hmB (half_pos hε)
  refine ⟨δ, hδ, fun u hu h0 => ?_⟩
  have hall : ∀ t, distX (u t) (Gset β γ k m) < ε / 2 := fun t =>
    hcore (u 0) (u t) (conservation hu t).1 (conservation hu t).2 h0
  refine ⟨⟨ε / 2, ?_⟩, ?_⟩
  · rintro _ ⟨t, rfl⟩
    exact (hall t).le
  · calc ⨆ t, distX (u t) (Gset β γ k m) ≤ ε / 2 := ciSup_le fun t => (hall t).le
      _ < ε := half_lt_self hε

/-- **Theorem (existence, compactness, and full-set orbital stability).**  For `β, γ > 0`, every
`k` and every `0 < m ≤ m_B = 3β/(γ√(k⁴ + 3β²/(32γ)))`:
(i) `−∞ < I(m) < 0` (with the explicit bound `I(m) ≥ −(3β²/(16γ)) m`), and
`I(m) < I(a) + I(m − a)` for `0 < a < m`;
(ii) `𝒢_m ≠ ∅`, and every mass-`m` minimizing sequence has a subsequence converging strongly
in `H²` after spatial translations to an element of `𝒢_m`;
(iii) every datum `u₀ ∈ H²(ℝ²)` generates a unique global solution `u ∈ C(ℝ; H²)` of
`i ∂ₜu = (Δ + k²)²u − β|u|²u + γ|u|⁴u`, and every solution conserves `M` and `H`;
(iv) for every `ε > 0` there is `δ > 0` with
`dist(u₀, 𝒢_m) < δ ⟹ sup_t dist(u(t), 𝒢_m) < ε` (no mass constraint on `u₀`). -/
theorem main (hβ : 0 < β) (hγ : 0 < γ) {m : ℝ} (hm : 0 < m)
    (hmB : m ≤ StrictBinding.mB β γ k) :
    ((-(3 * β ^ 2 / (16 * γ)) * m ≤ Imin β γ k m ∧ Imin β γ k m < 0) ∧
      ∀ a, 0 < a → a < m → Imin β γ k m < Imin β γ k a + Imin β γ k (m - a)) ∧
    ((Gset β γ k m).Nonempty ∧
      ∀ u : ℕ → H2 2, (∀ n, M (u n) = m) →
        Tendsto (fun n => energy β γ k (u n)) atTop (𝓝 (Imin β γ k m)) →
        ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ y : ℕ → R2, ∃ U ∈ Gset β γ k m,
          Tendsto (fun n => distH2 (translate (y n) (u (φ n))) U) atTop (𝓝 0)) ∧
    ((∀ u₀ : H2 2, ∃! u : ℝ → H2 2, IsSolution β γ k u ∧ u 0 = u₀) ∧
      ∀ u : ℝ → H2 2, IsSolution β γ k u → ∀ t,
        M (u t) = M (u 0) ∧ energy β γ k (u t) = energy β γ k (u 0)) ∧
    ∀ ε > 0, ∃ δ > 0, ∀ u : ℝ → H2 2, IsSolution β γ k u → distX (u 0) (Gset β γ k m) < δ →
      BddAbove (Set.range fun t => distX (u t) (Gset β γ k m)) ∧
      ⨆ t, distX (u t) (Gset β γ k m) < ε := by
  obtain ⟨hi, hbind, hcomp, hex⟩ := WholeSpace.main (k := k) hβ hγ hm hmB
  refine ⟨⟨hi, hbind⟩, ⟨?_, fun u hM hE => ?_⟩, ⟨fun u₀ => global_wellposed hγ u₀,
    fun u hu t => conservation hu t⟩, fun ε hε => orbital_stability hβ hγ hm hmB hε⟩
  · obtain ⟨U, hU1, hU2⟩ := hex
    exact ⟨U, hU1, hU2⟩
  · obtain ⟨φ, hφ, y, U, hU1, hU2, hU⟩ := hcomp u hM hE
    exact ⟨φ, hφ, y, U, ⟨hU1, hU2⟩, hU⟩

end OrbitalStability

namespace OrbitalStability

open Sobolev Sobolev.H2

variable {β γ k : ℝ}

/-- **Proposition (global well-posedness and conservation).**  For `γ > 0`, every datum
`u₀ ∈ H²(ℝ²)` generates a unique global solution `u ∈ C(ℝ; H²)`; solutions depend continuously
on the data uniformly on bounded time intervals; and `M(u(t)) = M(u₀)`, `H(u(t)) = H(u₀)`. -/
theorem global_flow (hγ : 0 < γ) :
    (∀ u₀ : H2 2, ∃! u : ℝ → H2 2, IsSolution β γ k u ∧ u 0 = u₀) ∧
    (∀ u : ℝ → H2 2, IsSolution β γ k u → ∀ T ε : ℝ, 0 < ε → ∃ δ > 0, ∀ v : ℝ → H2 2,
      IsSolution β γ k v → distH2 (v 0) (u 0) < δ → ∀ t ∈ Icc (-T) T, distH2 (v t) (u t) < ε) ∧
    (∀ u : ℝ → H2 2, IsSolution β γ k u → ∀ t,
      M (u t) = M (u 0) ∧ energy β γ k (u t) = energy β γ k (u 0)) :=
  ⟨fun u₀ => global_wellposed hγ u₀, fun _ hu T _ hε => continuous_dependence hγ hu T hε,
    fun _ hu t => conservation hu t⟩

end OrbitalStability

end ReyesMath
