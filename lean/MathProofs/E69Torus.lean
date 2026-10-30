import MathProofs.E69Remarks
import MathProofs.BandPassFlow

/-!
# E69 on the flat torus

The remark *Other domains* of the E69 manuscript: the same reasoning works on a flat torus with
the periodic Sobolev embedding. On `𝕋_L^d = (ℝ/Lℤ)^d`, `d ≥ 1`, with the Fourier basis `e_k`
(`TorusL2.basis`), frequencies `ξ_k = 2πk/L` and weight `w_k = 1 + |ξ_k|²` (`BandPass.wt`):

* `MemHsT s A`, `hsNormT s A`: `A ∈ H^s(𝕋_L^d)` for real `s`, `‖A‖²_{H^s} = Σ w_k^s |Â_k|²`;
  `hsNormT_zero`: Parseval at `s = 0`.
* `coef_lapT`: the periodic Laplacian `BandPass.lap` has symbol `−|ξ_k|²`;
  `hsNormT_lap_le`: `‖ΔA‖_{H^{s-2}} ≤ ‖A‖_{H^s}`.
* `summable_wt_rpow_neg`: `Σ_{k ∈ ℤ^d} w_k^{-r} < ∞` for `r > d/2`, every `d ≥ 1`.
* `embeddingT`: the periodic embedding `H^r(𝕋^d) ↪ C(𝕋^d) ⊂ L^∞` for `r > d/2`, through the
  absolutely convergent Fourier series.
* `e69_torus`: `‖Θ_ε[A]‖_{L^∞(𝕋^d)} ≤ C_{L,d,s} M_{ε,α} ‖A‖_{H^s(𝕋^d)}` for `s > d/2 + 2`.
-/

open Filter Topology Complex MeasureTheory Set
open scoped ENNReal Real

namespace ReyesMath

namespace E69Torus

open TorusL2 BandPass E26

variable {L : ℝ} [hL : Fact (0 < L)] {d : ℕ}

/-! ### Lattice sums `Σ_{k ∈ ℤ^d} (1 + |ξ_k|²)^{-r}` -/

theorem summable_int_one_add_sq_rpow {p : ℝ} (hp : 1 / 2 < p) :
    Summable fun m : ℤ => (1 + (m : ℝ) ^ 2) ^ (-p) := by
  refine Summable.of_norm_bounded_eventually
    (Real.summable_abs_int_rpow (b := 2 * p) (by linarith)) ?_
  have : {(0 : ℤ)}ᶜ ∈ cofinite := (Set.finite_singleton 0).compl_mem_cofinite
  filter_upwards [this] with m hm
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have hpos : 0 < |(m : ℝ)| := abs_pos.2 hm0
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  calc (1 + (m : ℝ) ^ 2) ^ (-p) ≤ (|(m : ℝ)| ^ (2 : ℝ)) ^ (-p) := by
        refine Real.rpow_le_rpow_of_exponent_nonpos (Real.rpow_pos_of_pos hpos _) ?_
          (by linarith)
        rw [Real.rpow_two, sq_abs]
        linarith
    _ = |(m : ℝ)| ^ (-(2 * p)) := by
        rw [← Real.rpow_mul (abs_nonneg _)]
        congr 1
        ring

omit hL in
theorem prod_rpow_le_gen (hd : 1 ≤ d) {r : ℝ} (hr : 0 ≤ r) (k : Fin d → ℤ) :
    (1 + ∑ j, ((k j : ℝ)) ^ 2) ^ (-r) ≤ ∏ i, (1 + ((k i : ℝ)) ^ 2) ^ (-(r / d)) := by
  set N : ℝ := 1 + ∑ j, ((k j : ℝ)) ^ 2 with hN
  have hN1 : 1 ≤ N := by
    have : 0 ≤ ∑ j, ((k j : ℝ)) ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
    linarith
  have hle : ∀ i, 1 + ((k i : ℝ)) ^ 2 ≤ N := fun i => by
    have := Finset.single_le_sum (f := fun j => ((k j : ℝ)) ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ i)
    simp only at this
    linarith
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have h1 : ∏ i, (1 + ((k i : ℝ)) ^ 2) ^ (r / d) ≤ N ^ r := by
    calc ∏ i, (1 + ((k i : ℝ)) ^ 2) ^ (r / d) ≤ ∏ _i : Fin d, N ^ (r / d) :=
          Finset.prod_le_prod (fun i _ => by positivity)
            (fun i _ => Real.rpow_le_rpow (by positivity) (hle i) (by positivity))
      _ = N ^ ((r / d) * d) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.rpow_natCast,
            ← Real.rpow_mul (by linarith)]
      _ = N ^ r := by
          congr 1
          field_simp
  have h2 : 0 < ∏ i, (1 + ((k i : ℝ)) ^ 2) ^ (r / d) :=
    Finset.prod_pos fun i _ => by positivity
  have e : ∏ i, (1 + ((k i : ℝ)) ^ 2) ^ (-(r / d)) =
      (∏ i, (1 + ((k i : ℝ)) ^ 2) ^ (r / d))⁻¹ := by
    rw [← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl fun i _ => Real.rpow_neg (by positivity) _
  rw [Real.rpow_neg (by linarith), e]
  exact inv_anti₀ h2 h1

/-- **`Σ_{k ∈ ℤ^d} (1 + |ξ_k|²)^{-r} < ∞` for `r > d/2`**, in every dimension `d ≥ 1`. -/
theorem summable_wt_rpow_neg (hd : 1 ≤ d) {r : ℝ} (hr : (d : ℝ) / 2 < r) :
    Summable fun k : Fin d → ℤ => wt L k ^ (-r) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hr0 : 0 ≤ r := by linarith [div_pos hd0 two_pos]
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℝ, c₀ = min 1 ((2 * π / L) ^ 2) := ⟨_, rfl⟩
  have hπL : 0 < 2 * π / L := div_pos Real.two_pi_pos hL.out
  have hc₀pos : 0 < c₀ := by rw [hc₀]; exact lt_min one_pos (by positivity)
  have hwt : ∀ k : Fin d → ℤ, c₀ * (1 + ∑ j, ((k j : ℝ)) ^ 2) ≤ wt L k := by
    intro k
    have h1 : c₀ ≤ 1 := hc₀ ▸ min_le_left _ _
    have h2 : c₀ ≤ (2 * π / L) ^ 2 := hc₀ ▸ min_le_right _ _
    have hs : 0 ≤ ∑ j, ((k j : ℝ)) ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
    have e : xi2 L k = (2 * π / L) ^ 2 * ∑ j, ((k j : ℝ)) ^ 2 := by
      rw [xi2, Finset.mul_sum]
      simp only [xi]
      congr 1
      funext j
      ring
    rw [wt, e, mul_add, mul_one]
    have := mul_le_mul_of_nonneg_right h2 hs
    linarith
  have hp : 1 / 2 < r / d := by
    rw [lt_div_iff₀ hd0]
    linarith
  have hsum := (summable_pi_prod (fun m => Real.rpow_nonneg (by positivity) _)
    (summable_int_one_add_sq_rpow hp) d).mul_left (c₀ ^ (-r))
  refine Summable.of_nonneg_of_le (fun k => Real.rpow_nonneg (wt_pos k).le _) (fun k => ?_) hsum
  have hN : 0 < 1 + ∑ j, ((k j : ℝ)) ^ 2 := by
    have : 0 ≤ ∑ j, ((k j : ℝ)) ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
    linarith
  calc wt L k ^ (-r) ≤ (c₀ * (1 + ∑ j, ((k j : ℝ)) ^ 2)) ^ (-r) :=
        Real.rpow_le_rpow_of_exponent_nonpos (by positivity) (hwt k) (by linarith)
    _ = c₀ ^ (-r) * (1 + ∑ j, ((k j : ℝ)) ^ 2) ^ (-r) := Real.mul_rpow hc₀pos.le hN.le
    _ ≤ c₀ ^ (-r) * ∏ i, (1 + ((k i : ℝ)) ^ 2) ^ (-(r / d)) :=
        mul_le_mul_of_nonneg_left (prod_rpow_le_gen hd hr0 k) (by positivity)

/-! ### `H^s(𝕋_L^d)` for real `s` -/

/-- **`A ∈ H^s(𝕋_L^d)`**: `Σ_k (1 + |ξ_k|²)^s |Â_k|² < ∞`. -/
def MemHsT (s : ℝ) (A : L2 L d) : Prop := Summable fun k => wt L k ^ s * ‖coef A k‖ ^ 2

/-- `‖A‖_{H^s(𝕋^d)} = (Σ_k (1 + |ξ_k|²)^s |Â_k|²)^{1/2}`. -/
noncomputable def hsNormT (s : ℝ) (A : L2 L d) : ℝ := √(∑' k, wt L k ^ s * ‖coef A k‖ ^ 2)

theorem hsNormT_nonneg (s : ℝ) (A : L2 L d) : 0 ≤ hsNormT s A := Real.sqrt_nonneg _

omit hL in
theorem wt_rpow_mono {s t : ℝ} (h : t ≤ s) (k : Fin d → ℤ) : wt L k ^ t ≤ wt L k ^ s :=
  Real.rpow_le_rpow_of_exponent_le (one_le_wt k) h

theorem memHsT_zero (A : L2 L d) : MemHsT 0 A := by
  simpa [MemHsT] using summable_sq A

/-- Parseval: `‖A‖_{H⁰} = ‖A‖_{L²}`. -/
theorem hsNormT_zero (A : L2 L d) : hsNormT 0 A = ‖A‖ := by
  simp only [hsNormT, Real.rpow_zero, one_mul]
  rw [← norm_sq_eq_tsum, Real.sqrt_sq (norm_nonneg _)]

theorem MemHsT.mono {s t : ℝ} {A : L2 L d} (hA : MemHsT s A) (h : t ≤ s) : MemHsT t A :=
  Summable.of_nonneg_of_le (fun k => mul_nonneg (Real.rpow_nonneg (wt_pos k).le _) (sq_nonneg _))
    (fun k => mul_le_mul_of_nonneg_right (wt_rpow_mono h k) (sq_nonneg _)) hA

theorem hsNormT_mono {s t : ℝ} {A : L2 L d} (hA : MemHsT s A) (h : t ≤ s) :
    hsNormT t A ≤ hsNormT s A :=
  Real.sqrt_le_sqrt (Summable.tsum_le_tsum
    (fun k => mul_le_mul_of_nonneg_right (wt_rpow_mono h k) (sq_nonneg _)) (hA.mono h) hA)

/-! ### The periodic Laplacian -/

theorem memℓp_lapT {A : L2 L d} (hA : MemHsT 2 A) :
    Memℓp (fun k => -(xi2 L k : ℂ) * coef A k) 2 := by
  rw [memℓp_two_iff]
  refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => ?_) hA
  rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg (xi2_nonneg k), mul_pow,
    Real.rpow_two]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (xi2_nonneg k) (xi2_le_wt k) 2) (sq_nonneg _)

/-- The periodic Laplacian has symbol `−|ξ_k|²`. -/
theorem coef_lapT {A : L2 L d} (hA : MemHsT 2 A) (k : Fin d → ℤ) :
    coef (lap A) k = -(xi2 L k : ℂ) * coef A k :=
  coef_pmul (memℓp_lapT hA) k

omit hL in
theorem lapT_weight_le (s : ℝ) (k : Fin d → ℤ) (z : ℂ) :
    wt L k ^ (s - 2) * ‖-(xi2 L k : ℂ) * z‖ ^ 2 ≤ wt L k ^ s * ‖z‖ ^ 2 := by
  rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg (xi2_nonneg k), mul_pow]
  have h1 : xi2 L k ^ 2 ≤ wt L k ^ (2 : ℝ) := by
    rw [Real.rpow_two]
    exact pow_le_pow_left₀ (xi2_nonneg k) (xi2_le_wt k) 2
  have h2 : wt L k ^ s = wt L k ^ (s - 2) * wt L k ^ (2 : ℝ) := by
    rw [← Real.rpow_add (wt_pos k), sub_add_cancel]
  rw [h2, mul_assoc]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 (sq_nonneg _))
    (Real.rpow_nonneg (wt_pos k).le _)

theorem memHsT_lap {s : ℝ} {A : L2 L d} (hA : MemHsT s A) (hs : 2 ≤ s) :
    MemHsT (s - 2) (lap A) := by
  refine Summable.of_nonneg_of_le
    (fun k => mul_nonneg (Real.rpow_nonneg (wt_pos k).le _) (sq_nonneg _)) (fun k => ?_) hA
  rw [coef_lapT (hA.mono hs)]
  exact lapT_weight_le s k _

/-- **`‖ΔA‖_{H^{s-2}(𝕋^d)} ≤ ‖A‖_{H^s(𝕋^d)}`** for `s ≥ 2`. -/
theorem hsNormT_lap_le {s : ℝ} {A : L2 L d} (hA : MemHsT s A) (hs : 2 ≤ s) :
    hsNormT (s - 2) (lap A) ≤ hsNormT s A := by
  refine Real.sqrt_le_sqrt (Summable.tsum_le_tsum (fun k => ?_) (memHsT_lap hA hs) hA)
  rw [coef_lapT (hA.mono hs)]
  exact lapT_weight_le s k _

/-! ### The periodic Sobolev embedding `H^r(𝕋^d) ↪ C(𝕋^d)`, `r > d/2` -/

/-- The embedding constant `(Σ_k (1 + |ξ_k|²)^{-r})^{1/2}`. -/
noncomputable def CembT (L : ℝ) (d : ℕ) (r : ℝ) : ℝ := √(∑' k : Fin d → ℤ, wt L k ^ (-r))

theorem CembT_nonneg (L : ℝ) (d : ℕ) (r : ℝ) : 0 ≤ CembT L d r := Real.sqrt_nonneg _

/-- Cauchy–Schwarz: `Σ_k |Â_k| ≤ C(r) ‖A‖_{H^r}`. -/
theorem summable_norm_coef (hd : 1 ≤ d) {r : ℝ} (hr : (d : ℝ) / 2 < r) {A : L2 L d}
    (hA : MemHsT r A) :
    Summable (fun k => ‖coef A k‖) ∧ ∑' k, ‖coef A k‖ ≤ CembT L d r * hsNormT r A := by
  have hf : Summable fun k : Fin d → ℤ => (wt L k ^ (-r / 2)) ^ (2 : ℝ) := by
    refine (summable_wt_rpow_neg (L := L) hd hr).congr fun k => ?_
    rw [← Real.rpow_mul (wt_pos k).le]
    congr 1
    ring
  have hg : Summable fun k : Fin d → ℤ => (wt L k ^ (r / 2) * ‖coef A k‖) ^ (2 : ℝ) := by
    refine hA.congr fun k => ?_
    rw [Real.rpow_two, mul_pow, ← Real.rpow_natCast (wt L k ^ (r / 2)),
      ← Real.rpow_mul (wt_pos k).le]
    congr 2
    push_cast
    ring
  have h := Real.inner_le_Lp_mul_Lq_tsum_of_nonneg Real.HolderConjugate.two_two
    (fun k => Real.rpow_nonneg (wt_pos (L := L) k).le (-r / 2))
    (fun k => mul_nonneg (Real.rpow_nonneg (wt_pos (L := L) k).le (r / 2)) (norm_nonneg _)) hf hg
  have e : ∀ k : Fin d → ℤ, wt L k ^ (-r / 2) * (wt L k ^ (r / 2) * ‖coef A k‖) = ‖coef A k‖ :=
    fun k => by
      rw [← mul_assoc, ← Real.rpow_add (wt_pos k), show -r / 2 + r / 2 = 0 by ring,
        Real.rpow_zero, one_mul]
  simp_rw [e] at h
  refine ⟨h.1, h.2.trans (le_of_eq ?_)⟩
  rw [CembT, hsNormT, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  congr 2
  · congr 1
    funext k
    rw [← Real.rpow_mul (wt_pos k).le]
    congr 1
    ring
  · congr 1
    funext k
    rw [Real.rpow_two, mul_pow, ← Real.rpow_natCast (wt L k ^ (r / 2)),
      ← Real.rpow_mul (wt_pos k).le]
    congr 2
    push_cast
    ring

theorem summable_series {A : L2 L d} (hc : Summable fun k => ‖coef A k‖) :
    Summable fun k => coef A k • emode (L := L) k :=
  Summable.of_norm_bounded hc fun k => by
    rw [norm_smul]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_emode_le k)

/-- The continuous representative `Σ_k Â_k e_k`. -/
noncomputable def rep (A : L2 L d) : C(Tor L d, ℂ) := ∑' k, coef A k • emode (L := L) k

theorem toLp_rep {A : L2 L d} (hc : Summable fun k => ‖coef A k‖) :
    ContinuousMap.toLp (E := ℂ) 2 (μ L d) ℂ (rep A) = A := by
  have h1 := (summable_series hc).hasSum.mapL (ContinuousMap.toLp (E := ℂ) 2 (μ L d) ℂ)
  refine h1.unique ((hasSum_series A).congr_fun fun k => ?_)
  rw [map_smul, ← basis_eq_toLp]

theorem ae_eq_rep {A : L2 L d} (hc : Summable fun k => ‖coef A k‖) :
    (A : Tor L d → ℂ) =ᵐ[μ L d] rep A := by
  conv_lhs => rw [← toLp_rep hc]
  exact ContinuousMap.coeFn_toLp _ _

theorem norm_rep_le {A : L2 L d} (hc : Summable fun k => ‖coef A k‖) (x : Tor L d) :
    ‖rep A x‖ ≤ ∑' k, ‖coef A k‖ := by
  rw [rep, ← ContinuousMap.tsum_apply (summable_series hc)]
  refine (norm_tsum_le_tsum_norm ?_).trans (le_of_eq ?_)
  · refine hc.congr fun k => ?_
    rw [ContinuousMap.smul_apply, norm_smul, norm_emode_apply, mul_one]
  · congr 1
    funext k
    rw [ContinuousMap.smul_apply, norm_smul, norm_emode_apply, mul_one]

/-- **The periodic Sobolev embedding** `H^r(𝕋_L^d) ↪ C(𝕋_L^d) ⊂ L^∞`, `r > d/2`, `d ≥ 1`. -/
theorem embeddingT (hd : 1 ≤ d) {r : ℝ} (hr : (d : ℝ) / 2 < r) {A : L2 L d} (hA : MemHsT r A) :
    (∃ g : C(Tor L d, ℂ), (A : Tor L d → ℂ) =ᵐ[μ L d] g ∧
      ∀ x, ‖g x‖ ≤ CembT L d r * hsNormT r A) ∧
    (∀ᵐ x ∂(μ L d), ‖(A : Tor L d → ℂ) x‖ ≤ CembT L d r * hsNormT r A) ∧
    MemLp (A : Tor L d → ℂ) ∞ (μ L d) := by
  obtain ⟨hc, hle⟩ := summable_norm_coef (L := L) hd hr hA
  have hb : ∀ x, ‖rep A x‖ ≤ CembT L d r * hsNormT r A := fun x => (norm_rep_le hc x).trans hle
  have hbd : ∀ᵐ x ∂(μ L d), ‖(A : Tor L d → ℂ) x‖ ≤ CembT L d r * hsNormT r A := by
    filter_upwards [ae_eq_rep hc] with x hx
    rw [hx]
    exact hb x
  exact ⟨⟨rep A, ae_eq_rep hc, hb⟩, hbd,
    memLp_top_of_bound (Lp.aestronglyMeasurable A) _ hbd⟩

/-! ### Theorem E69 on the torus -/

/-- `Θ_ε[A] = −(ΔA) R_ε(A)` on `𝕋_L^d`. -/
noncomputable def ThetaT (ε α : ℝ) (A : L2 L d) (x : Tor L d) : ℂ :=
  -((lap A : Tor L d → ℂ) x) * Rε ε α ((A : Tor L d → ℂ) x)

/-- **Theorem E69 on the flat torus.** For `d ≥ 1`, `ε > 0`, `α ∈ ℝ`, `s > d/2 + 2` and
`A ∈ H^s(𝕋_L^d)`: `Θ_ε[A] ∈ L^∞(𝕋_L^d)` and
`‖Θ_ε[A]‖_∞ ≤ C_{L,d,s} M_{ε,α} ‖A‖_{H^s(𝕋^d)}`, `C_{L,d,s} = (Σ_k (1 + |ξ_k|²)^{-(s-2)})^{1/2}`. -/
theorem e69_torus (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) (α : ℝ) {s : ℝ}
    (hs : (d : ℝ) / 2 + 2 < s) {A : L2 L d} (hA : MemHsT s A) :
    MemLp (ThetaT ε α A) ∞ (μ L d) ∧
    (∀ᵐ x ∂(μ L d), ‖ThetaT ε α A x‖ ≤ CembT L d (s - 2) * E69.Mea ε α * hsNormT s A) ∧
    eLpNorm (ThetaT ε α A) ∞ (μ L d) ≤
      ENNReal.ofReal (CembT L d (s - 2) * E69.Mea ε α * hsNormT s A) := by
  have hs2 : 2 ≤ s := by
    have : (0 : ℝ) ≤ d / 2 := by positivity
    linarith
  obtain ⟨-, hbd, -⟩ := embeddingT (L := L) hd (r := s - 2) (by linarith) (memHsT_lap hA hs2)
  have hemb : ∀ᵐ x ∂(μ L d), ‖(lap A : Tor L d → ℂ) x‖ ≤ CembT L d (s - 2) * hsNormT s A := by
    filter_upwards [hbd] with x hx
    exact hx.trans (mul_le_mul_of_nonneg_left (hsNormT_lap_le hA hs2) (CembT_nonneg _ _ _))
  exact E69.theta_bound_of_linf (μ L d) hε α (Lp.aestronglyMeasurable A)
    (Lp.aestronglyMeasurable _) hemb

end E69Torus

end ReyesMath
