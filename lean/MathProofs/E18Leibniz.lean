import MathProofs.E18TorusCalculus
import MathProofs.E18Frechet

/-!
# E18: the Leibniz rule `Δ(wu) = wΔu + 2∇w·∇u + (Δw)u` on `𝕋_L^d`

For `u ∈ H²(𝕋_L^d)` (Fourier derivatives) and a continuous `w` with continuous classical partial
derivatives `∂_j w`, `∂_j∂_j w`, the product `wu` lies in `H²` and its Fourier Laplacian is
`wΔu + 2Σ_j (∂_j w)(∂_j u) + (Σ_j ∂_j∂_j w) u` (`leibniz`). The proof pairs `wu` with the modes
`e_k` and moves the derivatives from `w̄ e_k` onto `u` by periodic integration by parts
(`integral_dpart_conj`).
-/

open Filter Topology Complex MeasureTheory Set
open scoped ENNReal Real ComplexConjugate

namespace ReyesMath

namespace E18

open TorusL2 BandPass

variable {L : ℝ} [hL : Fact (0 < L)] {d : ℕ}

/-! ### Fourier derivatives of `H²` functions -/

theorem inH_one_iff (u : L2 L d) : InH 1 u ↔ Summable fun k => wt L k ^ 2 * ‖coef u k‖ ^ 2 := by
  simp [InH]

theorem memℓp_dpart {u : L2 L d} (hu : InH 1 u) (j : Fin d) :
    Memℓp (fun k => I * xi L k j * coef u k) 2 := by
  rw [memℓp_two_iff]
  refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => ?_) ((inH_one_iff u).1 hu)
  simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [mul_pow, sq_abs]
  refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  have h1 := xi_sq_le_xi2 (L := L) k j
  have h2 := xi2_le_wt (L := L) k
  have h3 := one_le_wt (L := L) k
  nlinarith

theorem coef_dpart {u : L2 L d} (hu : InH 1 u) (j : Fin d) (k : Fin d → ℤ) :
    coef (dpart j u) k = I * xi L k j * coef u k :=
  coef_pmul (memℓp_dpart hu j) k

theorem memℓp_dpart_dpart {u : L2 L d} (hu : InH 1 u) (j : Fin d) :
    Memℓp (fun k => I * xi L k j * coef (dpart j u) k) 2 := by
  rw [memℓp_two_iff]
  refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => ?_) ((inH_one_iff u).1 hu)
  rw [coef_dpart hu]
  simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [show (|xi L k j| * (|xi L k j| * ‖coef u k‖)) ^ 2 = (|xi L k j| ^ 2) ^ 2 * ‖coef u k‖ ^ 2 by
    ring, sq_abs]
  refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  have h1 := xi_sq_le_xi2 (L := L) k j
  have h2 := xi2_le_wt (L := L) k
  exact pow_le_pow_left₀ (sq_nonneg _) (h1.trans h2) 2

theorem coef_dpart_dpart {u : L2 L d} (hu : InH 1 u) (j : Fin d) (k : Fin d → ℤ) :
    coef (dpart j (dpart j u)) k = -((xi L k j) ^ 2 : ℝ) * coef u k := by
  rw [dpart, coef_pmul (memℓp_dpart_dpart hu j), coef_dpart hu]
  push_cast
  linear_combination (xi L k j : ℂ) ^ 2 * coef u k * Complex.I_sq

/-- `Δu = Σ_j ∂_j∂_j u` for `u ∈ H²`. -/
theorem lap_eq_sum {u : L2 L d} (hu : InH 1 u) : lap u = ∑ j, dpart j (dpart j u) := by
  apply ext_coef
  intro k
  rw [coef_lap hu]
  have hsum : ∀ (s : Finset (Fin d)) (f : Fin d → L2 L d),
      coef (∑ j ∈ s, f j) k = ∑ j ∈ s, coef (f j) k := by
    intro s f
    induction s using Finset.induction_on with
    | empty => simp [coef_zero]
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, coef_add, ih]
  rw [hsum]
  simp_rw [coef_dpart_dpart hu]
  rw [← Finset.sum_mul, xi2]
  push_cast
  rw [Finset.sum_neg_distrib]

theorem coeFn_sum (s : Finset (Fin d)) (f : Fin d → L2 L d) :
    ((∑ j ∈ s, f j : L2 L d) : Tor L d → ℂ) =ᵐ[μ L d] fun x => ∑ j ∈ s, (f j : Tor L d → ℂ) x := by
  induction s using Finset.induction_on with
  | empty =>
    filter_upwards [Lp.coeFn_zero ℂ 2 (μ L d)] with x hx
    simp only [Finset.sum_empty]
    exact hx
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    filter_upwards [Lp.coeFn_add (f a) (∑ j ∈ s, f j), ih] with x h1 h2
    rw [h1, Pi.add_apply, h2]

/-! ### Pairings with `w̄ e_k` -/

theorem integrable_cfun_term (A : L2 L d) {φ : Tor L d → ℂ} (hφ : Continuous φ)
    (k : Fin d → ℤ) : Integrable (fun x => φ x * A x * conj (emode k x)) (μ L d) := by
  refine (integrable_mul_continuous A (hφ.mul (Complex.continuous_conj.comp
    (emode k).continuous))).congr (Eventually.of_forall fun x => ?_)
  simp only [Function.comp_apply]
  ring

/-- `⨍ u · \overline{ā e_k} = (au)^_k`. -/
theorem integral_conj_basic (u : L2 L d) (a : Tor L d → ℂ) (k : Fin d → ℤ) :
    ∫ x, u x * conj (conj (a x) * emode k x) ∂(μ L d) = cfun (fun x => a x * u x) k := by
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [map_mul, Complex.conj_conj]
  ring

theorem integral_conj_add (u : L2 L d) {φ ψ : Tor L d → ℂ} (hφ : Continuous φ)
    (hψ : Continuous ψ) :
    ∫ x, u x * conj (φ x + ψ x) ∂(μ L d) =
      ∫ x, u x * conj (φ x) ∂(μ L d) + ∫ x, u x * conj (ψ x) ∂(μ L d) := by
  simp_rw [map_add, mul_add]
  exact integral_add (integrable_mul_continuous u (Complex.continuous_conj.comp hφ))
    (integrable_mul_continuous u (Complex.continuous_conj.comp hψ))

theorem integral_conj_smul (u : L2 L d) (c : ℂ) (φ : Tor L d → ℂ) :
    ∫ x, u x * conj (c * φ x) ∂(μ L d) = conj c * ∫ x, u x * conj (φ x) ∂(μ L d) := by
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [map_mul]
  ring

theorem cfun_eq_integral (u : L2 L d) (a : Tor L d → ℂ) (k : Fin d → ℤ) :
    cfun (fun x => a x * u x) k = ∫ x, u x * conj (conj (a x) * emode k x) ∂(μ L d) :=
  (integral_conj_basic u a k).symm

omit hL in
theorem HasPartial.congr' {j : Fin d} {f g g' : Tor L d → ℂ} (h : HasPartial j f g)
    (hg : ∀ x, g x = g' x) : HasPartial j f g' := fun x => by
  rw [← hg x]
  exact h x

/-! ### The Leibniz rule -/

/-- **The Leibniz rule.** Let `u ∈ H²(𝕋_L^d)` and let `w` be continuous with continuous classical
partial derivatives `w_j = ∂_j w`, `w_jj = ∂_j w_j`. If `P = wu` and
`Q = wΔu + 2Σ_j w_j ∂_j u + (Σ_j w_jj) u` (a.e.), then `P ∈ H²` and `ΔP = Q`. -/
theorem leibniz {u P Q : L2 L d} (hu : InH 1 u) {w : Tor L d → ℂ} (hw : Continuous w)
    {wj wjj : Fin d → Tor L d → ℂ} (hwj : ∀ j, Continuous (wj j)) (hwjj : ∀ j, Continuous (wjj j))
    (h1 : ∀ j, HasPartial j w (wj j)) (h2 : ∀ j, HasPartial j (wj j) (wjj j))
    (hP : (P : Tor L d → ℂ) =ᵐ[μ L d] fun x => w x * u x)
    (hQ : (Q : Tor L d → ℂ) =ᵐ[μ L d] fun x => w x * (lap u : Tor L d → ℂ) x +
      2 * ∑ j, wj j x * (dpart j u : Tor L d → ℂ) x + (∑ j, wjj j x) * u x) :
    InH 1 P ∧ lap P = Q := by
  -- the identity `−|ξ_k|² P̂_k = Q̂_k`
  have key : ∀ k, -(xi2 L k : ℂ) * coef P k = coef Q k := by
    intro k
    have hek : Continuous fun x => emode (L := L) k x := (emode k).continuous
    have hcP : coef P k = cfun (fun x => w x * u x) k := by
      rw [coef_eq_cfun]; exact cfun_congr_ae hP k
    -- first-order identities
    have hA : ∀ j, cfun (fun x => wj j x * (dpart j u : Tor L d → ℂ) x) k =
        I * xi L k j * cfun (fun x => wj j x * u x) k - cfun (fun x => wjj j x * u x) k := by
      intro j
      have hφ : HasPartial j (fun x => conj (wj j x) * emode k x)
          (fun x => conj (wjj j x) * emode k x + (I * xi L k j) * (conj (wj j x) * emode k x)) :=
        ((h2 j).conj.mul (hasPartial_emode k j)).congr' fun x => by ring
      have hc1 : Continuous fun x => conj (wj j x) * emode (L := L) k x :=
        (Complex.continuous_conj.comp (hwj j)).mul hek
      have hc2 : Continuous fun x => conj (wjj j x) * emode (L := L) k x :=
        (Complex.continuous_conj.comp (hwjj j)).mul hek
      have h := integral_dpart_conj (memℓp_dpart hu j) hc1 (hc2.add (continuous_const.mul hc1)) hφ
      rw [integral_conj_basic, integral_conj_add u hc2 (continuous_const.mul hc1),
        integral_conj_smul, integral_conj_basic, integral_conj_basic] at h
      rw [h, map_mul, Complex.conj_I, Complex.conj_ofReal]
      ring
    -- second-order identities
    have hB : ∀ j, cfun (fun x => w x * (dpart j (dpart j u) : Tor L d → ℂ) x) k =
        cfun (fun x => wjj j x * u x) k - 2 * (I * xi L k j) * cfun (fun x => wj j x * u x) k -
          ((xi L k j) ^ 2 : ℝ) * cfun (fun x => w x * u x) k := by
      intro j
      have hc0 : Continuous fun x => conj (w x) * emode (L := L) k x :=
        (Complex.continuous_conj.comp hw).mul hek
      have hc1 : Continuous fun x => conj (wj j x) * emode (L := L) k x :=
        (Complex.continuous_conj.comp (hwj j)).mul hek
      have hc2 : Continuous fun x => conj (wjj j x) * emode (L := L) k x :=
        (Complex.continuous_conj.comp (hwjj j)).mul hek
      have hφ0 : HasPartial j (fun x => conj (w x) * emode k x)
          (fun x => conj (wj j x) * emode k x + (I * xi L k j) * (conj (w x) * emode k x)) :=
        ((h1 j).conj.mul (hasPartial_emode k j)).congr' fun x => by ring
      have hφ1 : HasPartial j
          (fun x => conj (wj j x) * emode k x + (I * xi L k j) * (conj (w x) * emode k x))
          (fun x => conj (wjj j x) * emode k x + (2 * (I * xi L k j)) * (conj (wj j x) * emode k x)
            + (I * xi L k j) ^ 2 * (conj (w x) * emode k x)) :=
        (((h2 j).conj.mul (hasPartial_emode k j)).add
          (((h1 j).conj.mul (hasPartial_emode k j)).const_mul (I * xi L k j))).congr'
          fun x => by ring
      have hc01 : Continuous fun x =>
          conj (wj j x) * emode (L := L) k x + (I * xi L k j) * (conj (w x) * emode k x) :=
        hc1.add (continuous_const.mul hc0)
      have hA1 := integral_dpart_conj (memℓp_dpart_dpart hu j) hc0 hc01 hφ0
      have hA2 := integral_dpart_conj (memℓp_dpart hu j) hc01
        ((hc2.add (continuous_const.mul hc1)).add (continuous_const.mul hc0)) hφ1
      rw [integral_conj_basic] at hA1
      rw [hA1, hA2, neg_neg, integral_conj_add u (hc2.add (continuous_const.mul hc1))
        (continuous_const.mul hc0), integral_conj_add u hc2 (continuous_const.mul hc1),
        integral_conj_smul, integral_conj_smul, integral_conj_basic, integral_conj_basic,
        integral_conj_basic]
      simp only [map_mul, map_pow, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
      push_cast
      linear_combination ((xi L k j : ℂ) ^ 2 * cfun (fun x => w x * u x) k) * Complex.I_sq
    -- assemble
    have hlap : cfun (fun x => w x * (lap u : Tor L d → ℂ) x) k =
        ∑ j, cfun (fun x => w x * (dpart j (dpart j u) : Tor L d → ℂ) x) k := by
      have hae : (fun x => w x * (lap u : Tor L d → ℂ) x) =ᵐ[μ L d]
          fun x => ∑ j, w x * (dpart j (dpart j u) : Tor L d → ℂ) x := by
        rw [lap_eq_sum hu]
        filter_upwards [coeFn_sum Finset.univ fun j => dpart j (dpart j u)] with x hx
        rw [hx, Finset.mul_sum]
      rw [cfun_congr_ae hae, cfun]
      simp_rw [Finset.sum_mul]
      rw [integral_finset_sum _ fun j _ => integrable_cfun_term _ hw k]
      rfl
    have hQk : coef Q k = cfun (fun x => w x * (lap u : Tor L d → ℂ) x) k +
        2 * ∑ j, cfun (fun x => wj j x * (dpart j u : Tor L d → ℂ) x) k +
          ∑ j, cfun (fun x => wjj j x * u x) k := by
      rw [coef_eq_cfun, cfun_congr_ae hQ k]
      have hfun : (fun x => (w x * (lap u : Tor L d → ℂ) x +
            2 * ∑ j, wj j x * (dpart j u : Tor L d → ℂ) x + (∑ j, wjj j x) * u x) *
              conj (emode k x)) =
          fun x => w x * (lap u : Tor L d → ℂ) x * conj (emode k x) +
            2 * ∑ j, wj j x * (dpart j u : Tor L d → ℂ) x * conj (emode k x) +
              ∑ j, wjj j x * u x * conj (emode k x) := by
        funext x
        simp only [← Finset.sum_mul]
        ring
      have i1 := integrable_cfun_term (lap u) hw k
      have i2 : Integrable (fun x => 2 * ∑ j, wj j x * (dpart j u : Tor L d → ℂ) x *
          conj (emode k x)) (μ L d) :=
        (integrable_finset_sum _ fun j _ => integrable_cfun_term (dpart j u) (hwj j) k).const_mul 2
      have i3 : Integrable (fun x => ∑ j, wjj j x * u x * conj (emode k x)) (μ L d) :=
        integrable_finset_sum _ fun j _ => integrable_cfun_term u (hwjj j) k
      have i12 : Integrable (fun x => w x * (lap u : Tor L d → ℂ) x * conj (emode k x) +
          2 * ∑ j, wj j x * (dpart j u : Tor L d → ℂ) x * conj (emode k x)) (μ L d) := i1.add i2
      simp only [cfun]
      rw [hfun, integral_add i12 i3, integral_add i1 i2, integral_const_mul,
        integral_finset_sum _ fun j _ => integrable_cfun_term (dpart j u) (hwj j) k,
        integral_finset_sum _ fun j _ => integrable_cfun_term u (hwjj j) k]
    rw [hQk, hlap, hcP]
    simp_rw [hB, hA]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, xi2,
      Complex.ofReal_sum, neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring
  -- membership and the identification
  have hsum : Summable fun k => wt L k ^ 2 * ‖coef P k‖ ^ 2 := by
    refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
      (((summable_sq P).mul_left 2).add ((summable_sq Q).mul_left 2))
    have hk := congrArg norm (key k)
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg (xi2_nonneg k)] at hk
    rw [← hk, wt, mul_pow]
    nlinarith [mul_nonneg (sq_nonneg (1 - xi2 L k)) (sq_nonneg ‖coef P k‖)]
  have hP1 : InH 1 P := (inH_one_iff P).2 hsum
  refine ⟨hP1, ext_coef fun k => ?_⟩
  rw [coef_lap hP1, key k]

end E18

end ReyesMath
