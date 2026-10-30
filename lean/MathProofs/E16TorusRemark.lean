import MathProofs.TorusFourier

/-!
# E16: the flat-torus remark

Manuscript: `papers/e16-linear-spectral-concentration/main.tex`, Remark (Flat tori).

On `𝕋_L^d = (ℝ/Lℤ)^d` with Fourier lattice `ξ_n = (2π/L)n`, `n ∈ ℤ^d`:

* the linear flow `A(t) = Σ_n e^{tλ(ξ_n)} Â_n(0) e_n` (`E16Torus.flow`, a bounded Fourier
  multiplier for `t ≥ 0`, `b > 0`) has the exact coefficientwise law
  `Â_n(t) = e^{tλ(ξ_n)}Â_n(0)`, `P_n(t) = P_n(0)e^{2λ(ξ_n)t}`, and each coefficient solves
  `∂ₜÂ_n = λ(ξ_n)Â_n` (`E16Torus.coef_flow`, `E16Torus.power_law`, `E16Torus.coef_ode`);
* the dominant asymptotic modes are the initially populated lattice frequencies maximizing
  `λ(ξ_n)`: their normalized spectral power tends to one, with an exponential rate
  (`E16Torus.dominant_concentration`);
* this dominant set need not contain a point with `|ξ_n| = k⋆`: on `𝕋_{2π}¹` with `a = 4`,
  `b = 1` (`k⋆² = 2`) no lattice frequency lies on the shell (`E16Torus.shell_missed`).
-/

open Filter Topology Complex InnerProductSpace MeasureTheory Set
open scoped ComplexConjugate Real

noncomputable section

namespace ReyesMath
namespace E16Torus

open TorusL2

variable {d : ℕ}

/-- `|ξ_n|²` for the lattice frequency `ξ_n = (2π/L)n`. -/
def xi2 (L : ℝ) (n : Fin d → ℤ) : ℝ := ∑ j, (2 * π / L * n j) ^ 2

/-- The modal growth rate `λ(ξ_n) = r + a|ξ_n|² − b|ξ_n|⁴`. -/
def lamT (L a b r : ℝ) (n : Fin d → ℤ) : ℝ := r + a * xi2 L n - b * xi2 L n ^ 2

theorem quad_le (a r : ℝ) {b : ℝ} (hb : 0 < b) (q : ℝ) :
    r + a * q - b * q ^ 2 ≤ r + a ^ 2 / (4 * b) := by
  have h0 : 0 ≤ b * (q - a / (2 * b)) ^ 2 := mul_nonneg hb.le (sq_nonneg _)
  have e : b * (q - a / (2 * b)) ^ 2 = b * q ^ 2 - a * q + a ^ 2 / (4 * b) := by
    field_simp; ring
  linarith

theorem lamT_le (L a r : ℝ) {b : ℝ} (hb : 0 < b) (n : Fin d → ℤ) :
    lamT L a b r n ≤ r + a ^ 2 / (4 * b) := quad_le a r hb _

/-- The symbol `e^{t⁺λ(ξ_n)}` of the torus flow. -/
def esymT (L a b r t : ℝ) (n : Fin d → ℤ) : ℂ := (Real.exp (max t 0 * lamT L a b r n) : ℂ)

theorem norm_esymT_le (L a r : ℝ) {b : ℝ} (hb : 0 < b) (t : ℝ) (n : Fin d → ℤ) :
    ‖esymT L a b r t n‖ ≤ Real.exp (max t 0 * (r + a ^ 2 / (4 * b))) := by
  rw [esymT, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (lamT_le L a r hb n) (le_max_right _ _))

/-- The torus flow `A(t) = Σ_n e^{tλ(ξ_n)} Â_n(0) e_n`. -/
def flow (L : ℝ) [Fact (0 < L)] (a r : ℝ) {b : ℝ} (hb : 0 < b) (t : ℝ) (A₀ : L2 L d) :
    L2 L d :=
  mult L d (esymT L a b r t) (norm_esymT_le L a r hb t) A₀

variable {L : ℝ} [hL : Fact (0 < L)] {a b r : ℝ}

theorem coef_flow (hb : 0 < b) {t : ℝ} (ht : 0 ≤ t) (A₀ : L2 L d) (n : Fin d → ℤ) :
    coef (flow L a r hb t A₀) n = (Real.exp (t * lamT L a b r n) : ℂ) * coef A₀ n := by
  rw [flow, coef_mult, esymT, max_eq_left ht]

/-- The exact coefficientwise power law `P_n(t) = P_n(0) e^{2λ(ξ_n)t}`. -/
theorem power_law (hb : 0 < b) {t : ℝ} (ht : 0 ≤ t) (A₀ : L2 L d) (n : Fin d → ℤ) :
    ‖coef (flow L a r hb t A₀) n‖ ^ 2 = ‖coef A₀ n‖ ^ 2 * Real.exp (2 * lamT L a b r n * t) := by
  rw [coef_flow hb ht, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), mul_pow, ← Real.exp_nat_mul]
  push_cast; ring_nf

/-- Each coefficient solves `∂ₜÂ_n = λ(ξ_n)Â_n` for `t > 0`. -/
theorem coef_ode (hb : 0 < b) {t : ℝ} (ht : 0 < t) (A₀ : L2 L d) (n : Fin d → ℤ) :
    HasDerivAt (fun s => coef (flow L a r hb s A₀) n)
      ((lamT L a b r n : ℂ) * coef (flow L a r hb t A₀) n) t := by
  have heq : (fun s => coef (flow L a r hb s A₀) n) =ᶠ[𝓝 t]
      fun s => (Real.exp (s * lamT L a b r n) : ℂ) * coef A₀ n := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact coef_flow hb (le_of_lt hs) A₀ n
  have h1 : HasDerivAt (fun s : ℝ => (Real.exp (s * lamT L a b r n) : ℂ))
      ((Real.exp (t * lamT L a b r n) * lamT L a b r n : ℝ) : ℂ) t := by
    have h0 := ((hasDerivAt_id t).mul_const (lamT L a b r n)).exp
    simp only [id, one_mul] at h0
    exact h0.ofReal_comp
  refine ((h1.mul_const (coef A₀ n)).congr_of_eventuallyEq heq).congr_deriv ?_
  rw [coef_flow hb ht.le]; push_cast; ring

/-! ### Dominant modes -/

/-- `E_tot = E_S + E_{Sᶜ}`. -/
theorem Etot_split (S : Set (Fin d → ℤ)) (A : L2 L d) : Etot A = Estar S A + Estar Sᶜ A := by
  have h1 := (hasSum_Estar S A).add (hasSum_Estar Sᶜ A)
  have h2 : (fun k => S.indicator (fun k => ‖coef A k‖ ^ 2) k +
      Sᶜ.indicator (fun k => ‖coef A k‖ ^ 2) k) = fun k => ‖coef A k‖ ^ 2 := by
    funext k; by_cases hk : k ∈ S <;> simp [hk]
  rw [h2] at h1
  rw [Etot, h1.tsum_eq, Estar_eq, Estar_eq]


/-- The initially populated lattice frequencies. -/
def populated (A₀ : L2 L d) : Set (Fin d → ℤ) := {n | coef A₀ n ≠ 0}

theorem populated_nonempty {A₀ : L2 L d} (hA₀ : A₀ ≠ 0) : (populated A₀).Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  apply hA₀
  apply ext_coef; intro n
  have : n ∉ populated A₀ := by rw [h]; exact Set.notMem_empty n
  simpa [populated, coef_zero] using this

theorem tendsto_xi2 : Tendsto (xi2 (d := d) L) cofinite atTop := by
  refine tendsto_atTop.2 fun M => eventually_cofinite.2 ?_
  have hc : 0 < 2 * π / L := div_pos Real.two_pi_pos hL.out
  set K : ℤ := ⌈M / (2 * π / L) ^ 2⌉
  refine (Set.Finite.pi (t := fun _ : Fin d => Icc (-K) K) fun _ => finite_Icc _ _).subset ?_
  intro n hn
  simp only [mem_setOf_eq, not_le] at hn
  simp only [Set.mem_pi, mem_univ, mem_Icc, true_implies]
  intro j
  have h1 : (2 * π / L * n j) ^ 2 ≤ xi2 L n :=
    Finset.single_le_sum (f := fun j => (2 * π / L * n j) ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ j)
  have h2 : ((n j : ℤ) : ℝ) ^ 2 < M / (2 * π / L) ^ 2 := by
    rw [lt_div_iff₀ (by positivity)]
    nlinarith
  have h3 : (n j) ^ 2 ≤ K := by
    have := h2.le.trans (Int.le_ceil _)
    exact_mod_cast this
  constructor
  · rcases le_or_gt 0 (n j) with h | h <;> nlinarith
  · rcases le_or_gt (n j) 0 with h | h <;> nlinarith

theorem tendsto_quad (a r : ℝ) {b : ℝ} (hb : 0 < b) :
    Tendsto (fun q : ℝ => r + a * q - b * q ^ 2) atTop atBot := by
  have h1 : Tendsto (fun q : ℝ => a + -(b * q)) atTop atBot :=
    tendsto_atBot_add_const_left atTop a
      (tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop hb))
  have h2 : Tendsto (fun q : ℝ => q * (a + -(b * q))) atTop atBot :=
    tendsto_id.atTop_mul_atBot₀ h1
  refine (tendsto_atBot_add_const_left atTop r h2).congr fun q => ?_
  ring

theorem tendsto_lamT (hb : 0 < b) : Tendsto (lamT (d := d) L a b r) cofinite atBot :=
  (tendsto_quad a r hb).comp tendsto_xi2

/-- The maximal populated growth rate exists. -/
theorem exists_max (hb : 0 < b) {A₀ : L2 L d} (hA₀ : A₀ ≠ 0) :
    ∃ n₀ ∈ populated A₀, ∀ n ∈ populated A₀, lamT L a b r n ≤ lamT L a b r n₀ :=
  (tendsto_lamT (d := d) (L := L) (a := a) (r := r) (b := b) hb).exists_within_forall_ge (populated_nonempty hA₀)

/-- The dominant set: populated frequencies attaining the maximal growth rate `M`. -/
def dominant (L : ℝ) [Fact (0 < L)] (a b r M : ℝ) (A₀ : L2 L d) : Set (Fin d → ℤ) :=
  {n | n ∈ populated A₀ ∧ lamT L a b r n = M}

/-- A strict spectral gap below the maximal populated rate. -/
theorem exists_gap (hb : 0 < b) {A₀ : L2 L d} {M : ℝ}
    (hM : ∀ n ∈ populated A₀, lamT L a b r n ≤ M) :
    ∃ g > 0, ∀ n ∈ populated A₀, n ∉ dominant L a b r M A₀ → lamT L a b r n ≤ M - g := by
  have hfin : {n : Fin d → ℤ | M - 1 < lamT L a b r n}.Finite := by
    have := (tendsto_lamT (d := d) (L := L) (a := a) (r := r) (b := b) hb).eventually
      (eventually_le_atBot (M - 1))
    simpa [Filter.eventually_cofinite, not_le] using this
  classical
  set F := (hfin.toFinset.filter fun n => n ∈ populated A₀ ∧ n ∉ dominant L a b r M A₀)
  by_cases hF : F.Nonempty
  · refine ⟨min 1 (F.inf' hF fun n => M - lamT L a b r n), ?_, fun n hn hnd => ?_⟩
    · refine lt_min one_pos ((Finset.lt_inf'_iff hF).2 fun n hnF => ?_)
      simp only [F, Finset.mem_filter, Set.Finite.mem_toFinset, mem_setOf_eq] at hnF
      have h1 := hM n hnF.2.1
      have h2 : lamT L a b r n ≠ M := fun h => hnF.2.2 ⟨hnF.2.1, h⟩
      linarith [lt_of_le_of_ne h1 h2]
    · by_cases hbig : M - 1 < lamT L a b r n
      · have hnF : n ∈ F := by
          simp only [F, Finset.mem_filter, Set.Finite.mem_toFinset, mem_setOf_eq]
          exact ⟨hbig, hn, hnd⟩
        have := Finset.inf'_le (fun n => M - lamT L a b r n) hnF
        have := min_le_right 1 (F.inf' hF fun n => M - lamT L a b r n)
        linarith
      · push_neg at hbig
        have := min_le_left 1 (F.inf' hF fun n => M - lamT L a b r n)
        linarith
  · refine ⟨1, one_pos, fun n hn hnd => ?_⟩
    by_contra hbig
    push_neg at hbig
    apply hF
    refine ⟨n, ?_⟩
    simp only [F, Finset.mem_filter, Set.Finite.mem_toFinset, mem_setOf_eq]
    exact ⟨by linarith, hn, hnd⟩

/-- **Remark (flat tori): the dominant asymptotic modes.** For nonzero data and `b > 0`, let
`M` be the maximal growth rate over the populated lattice frequencies. The normalized spectral
power of the populated maximizers tends to one: `η_{dom}(t) → 1`, and the complementary
fraction is at most `C e^{-2gt}` for a gap `g > 0`. -/
theorem dominant_concentration (hb : 0 < b) {A₀ : L2 L d} (hA₀ : A₀ ≠ 0) :
    ∃ M : ℝ, (∃ n₀ ∈ populated A₀, lamT L a b r n₀ = M) ∧
      (∀ n ∈ populated A₀, lamT L a b r n ≤ M) ∧
      (dominant L a b r M A₀).Nonempty ∧
      (∃ g > 0, ∃ C : ℝ, ∀ t ≥ 0,
        eta (dominant L a b r M A₀)ᶜ (flow L a r hb t A₀) ≤ C * Real.exp (-2 * g * t)) ∧
      Tendsto (fun t => eta (dominant L a b r M A₀) (flow L a r hb t A₀)) atTop (𝓝 1) := by
  obtain ⟨n₀, hn₀, hmax⟩ := exists_max (L := L) (a := a) (r := r) hb hA₀
  set M := lamT L a b r n₀
  obtain ⟨g, hg, hgap⟩ := exists_gap (L := L) (a := a) (r := r) hb hmax
  set D := dominant L a b r M A₀
  have hD : n₀ ∈ D := ⟨hn₀, rfl⟩
  -- the selected energies along the flow
  have hEt : ∀ t ≥ 0, ∀ S : Set (Fin d → ℤ), Estar S (flow L a r hb t A₀) =
      ∑' n, S.indicator (fun n => ‖coef A₀ n‖ ^ 2 * Real.exp (2 * lamT L a b r n * t)) n := by
    intro t ht S
    rw [Estar]
    congr 1; funext n
    by_cases hn : n ∈ S <;> simp [hn, power_law hb ht]
  have hsum0 : Summable fun n => ‖coef A₀ n‖ ^ 2 := summable_sq A₀
  have hEstarD0 : 0 < Estar D A₀ := by
    rw [Estar]
    refine (hasSum_Estar D A₀).summable.tsum_pos (fun n => ?_) n₀ ?_
    · by_cases hn : n ∈ D <;> simp [hn]
    · simp only [Set.indicator_of_mem hD]
      exact pow_pos (norm_pos_iff.2 hn₀) 2
  -- dominant energy grows exactly like e^{2Mt}
  have hdom : ∀ t ≥ 0, Estar D (flow L a r hb t A₀) = Real.exp (2 * M * t) * Estar D A₀ := by
    intro t ht
    rw [hEt t ht, Estar, ← tsum_mul_left]
    congr 1; funext n
    by_cases hn : n ∈ D
    · simp only [Set.indicator_of_mem hn, hn.2]; ring
    · simp [hn]
  -- the complementary energy is controlled by e^{2(M-g)t}
  have hcomp : ∀ t ≥ 0, Estar Dᶜ (flow L a r hb t A₀) ≤
      Real.exp (2 * (M - g) * t) * Etot A₀ := by
    intro t ht
    rw [hEt t ht, Etot, ← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun n => ?_) ?_ (hsum0.mul_left _)
    · by_cases hn : n ∈ Dᶜ
      · simp only [Set.indicator_of_mem hn]
        by_cases hp : n ∈ populated A₀
        · have hl := hgap n hp hn
          rw [mul_comm (Real.exp _)]
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
          nlinarith
        · have : coef A₀ n = 0 := by simpa [populated] using hp
          simp [this]
      · simp only [Set.indicator_of_notMem hn]; positivity
    · refine (hsum0.mul_right (Real.exp (2 * M * t))).of_nonneg_of_le (fun n => ?_)
        (fun n => ?_)
      · by_cases hn : n ∈ Dᶜ
        · simp only [Set.indicator_of_mem hn]; positivity
        · simp [hn]
      · by_cases hn : n ∈ Dᶜ
        · simp only [Set.indicator_of_mem hn]
          by_cases hp : n ∈ populated A₀
          · refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
            nlinarith [hmax n hp]
          · have : coef A₀ n = 0 := by simpa [populated] using hp
            simp [this]
        · simp only [Set.indicator_of_notMem hn]; positivity
  -- normalized complementary fraction
  have hfrac : ∀ t ≥ 0, eta Dᶜ (flow L a r hb t A₀) ≤
      Etot A₀ / Estar D A₀ * Real.exp (-2 * g * t) := by
    intro t ht
    have hsplit := (Etot_split D (flow L a r hb t A₀))
    have hpos : 0 < Estar D (flow L a r hb t A₀) := by
      rw [hdom t ht]; exact mul_pos (Real.exp_pos _) hEstarD0
    rw [TorusL2.eta]
    calc Estar Dᶜ (flow L a r hb t A₀) / Etot (flow L a r hb t A₀)
        ≤ Estar Dᶜ (flow L a r hb t A₀) / Estar D (flow L a r hb t A₀) := by
          refine div_le_div_of_nonneg_left (by rw [Estar_eq]; positivity) hpos ?_
          rw [hsplit]; linarith [show 0 ≤ Estar Dᶜ (flow L a r hb t A₀) by rw [Estar_eq]; positivity]
      _ ≤ Real.exp (2 * (M - g) * t) * Etot A₀ / (Real.exp (2 * M * t) * Estar D A₀) := by
          rw [hdom t ht]
          exact div_le_div_of_nonneg_right (hcomp t ht) (by positivity)
      _ = Etot A₀ / Estar D A₀ * Real.exp (-2 * g * t) := by
          rw [show 2 * (M - g) * t = 2 * M * t + (-2 * g * t) by ring, Real.exp_add]
          field_simp
  refine ⟨M, ⟨n₀, hn₀, rfl⟩, hmax, ⟨n₀, hD⟩, ⟨g, hg, Etot A₀ / Estar D A₀, hfrac⟩, ?_⟩
  -- η_D = 1 − η_{Dᶜ} → 1
  have hlim : Tendsto (fun t => Etot A₀ / Estar D A₀ * Real.exp (-2 * g * t)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => -2 * g * t) atTop atBot := by
      have := tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop (by linarith : 0 < 2 * g))
      refine this.congr fun t => ?_
      simp only [Function.comp, id]; ring
    have h2 := (Real.tendsto_exp_atBot.comp h1).const_mul (Etot A₀ / Estar D A₀)
    rw [mul_zero] at h2
    exact h2
  have hcompl : Tendsto (fun t => eta Dᶜ (flow L a r hb t A₀)) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
    · filter_upwards with t; rw [TorusL2.eta, Estar_eq, Etot_eq]; positivity
    · filter_upwards [eventually_ge_atTop 0] with t ht; exact hfrac t ht
  have hone : ∀ t ≥ 0, eta D (flow L a r hb t A₀) = 1 - eta Dᶜ (flow L a r hb t A₀) := by
    intro t ht
    have hsplit := Etot_split D (flow L a r hb t A₀)
    have hpos : 0 < Etot (flow L a r hb t A₀) := by
      rw [hsplit]
      have : 0 < Estar D (flow L a r hb t A₀) := by
        rw [hdom t ht]; exact mul_pos (Real.exp_pos _) hEstarD0
      linarith [show 0 ≤ Estar Dᶜ (flow L a r hb t A₀) by rw [Estar_eq]; positivity]
    rw [TorusL2.eta, TorusL2.eta, eq_sub_iff_add_eq, ← add_div, ← hsplit, div_self hpos.ne']
  have := hcompl.const_sub 1
  rw [sub_zero] at this
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with t ht
  exact (hone t ht).symm

/-- **The shell need not be attained**: on `𝕋_{2π}¹` with `a = 4`, `b = 1`
(`k⋆² = a/(2b) = 2`), no lattice frequency satisfies `|ξ_n|² = k⋆²`; hence for every nonzero datum
the dominant modes miss the continuum shell. -/
theorem shell_missed :
    (∀ n : Fin 1 → ℤ, xi2 (2 * π) n ≠ 4 / (2 * 1)) ∧
    ∀ (r M : ℝ) (A₀ : L2 (2 * π) 1), ∀ n ∈ dominant (2 * π) 4 1 r M A₀, xi2 (2 * π) n ≠ 4 / (2 * 1) := by
  have h : ∀ n : Fin 1 → ℤ, xi2 (2 * π) n ≠ 4 / (2 * 1) := by
    intro n hn
    have e : xi2 (2 * π) n = ((n 0 : ℤ) : ℝ) ^ 2 := by
      simp only [xi2, Fin.sum_univ_one]
      rw [div_self Real.two_pi_pos.ne', one_mul]
    rw [e] at hn
    norm_num at hn
    have h2 : (n 0) ^ 2 = 2 := by exact_mod_cast hn
    have h3 : n 0 ≤ 1 := by nlinarith
    have h4 : -1 ≤ n 0 := by nlinarith
    interval_cases (n 0) <;> simp_all
  exact ⟨h, fun _ _ _ n _ => h n⟩

end E16Torus
end ReyesMath
