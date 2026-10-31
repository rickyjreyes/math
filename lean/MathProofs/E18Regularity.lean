import MathProofs.E18Leibniz

/-!
# E18: regularity of the variational derivative on `H⁴(𝕋^d)`, `d ≤ 3`

For `ψ ∈ H⁴(𝕋_L^d)` with `d ≤ 3`:

* `summable_coef_mul_wt`: `Σ_k |ψ̂_k|(1 + |ξ_k|²) < ∞`, so `ψ` has the continuous representative
  `ψ_c = Σ ψ̂_k e_k` with continuous classical partial derivatives `∂_jψ_c`, `∂_j∂_jψ_c`, and `Δψ`
  has the continuous representative `Σ −|ξ_k|² ψ̂_k e_k` (`rep_facts`).
* The weight `w = F(|ψ_c|²)` has continuous classical partial derivatives
  `w_j = F′(ρ)ρ_j`, `w_jj = F″(ρ)ρ_j² + F′(ρ)ρ_jj`, `ρ = |ψ_c|²` (`weight_facts`).
* `Wt ψ = F(|ψ|²)Δψ ∈ H²` and `Δ(F(|ψ|²)Δψ) = wΔ²ψ + 2Σ_j w_j ∂_jΔψ + (Σ_j w_jj)Δψ`
  (`regularity`, by the Leibniz rule); `Vt ψ = F′(|ψ|²)ψ|Δψ|² ∈ L²`.
* `Gt c₁ c₂ ε α ψ = −c₁Δψ + c₂Δ(F(|ψ|²)Δψ) + c₂F′(|ψ|²)ψ|Δψ|²`, every term in `L²`.
-/

open Filter Topology Complex MeasureTheory Set
open scoped ENNReal Real ComplexConjugate

namespace ReyesMath

namespace E18

open TorusL2 BandPass E18FourierEnergy E18WeightDerivative

variable {L : ℝ} [hL : Fact (0 < L)] {d : ℕ}

/-! ### `L²` elements from functions -/

theorem memLp_of_continuous {f : Tor L d → ℂ} (hf : Continuous f) : MemLp f 2 (μ L d) :=
  (Lp.memLp ((⟨f, hf⟩ : C(Tor L d, ℂ)).toLp 2 (μ L d) ℂ)).ae_eq
    (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (μ L d) (⟨f, hf⟩ : C(Tor L d, ℂ)))

/-! ### The variational derivative -/

/-- `F(|ψ|²) Δψ`. -/
noncomputable def Wt (ε α : ℝ) (ψ : L2 L d) : L2 L d :=
  toL2' fun x => (F ε α (‖ψ x‖ ^ 2) : ℂ) * (lap ψ : Tor L d → ℂ) x

/-- `F′(|ψ|²) ψ |Δψ|²`. -/
noncomputable def Vt (ε α : ℝ) (ψ : L2 L d) : L2 L d :=
  toL2' fun x => (Fprime ε α (‖ψ x‖ ^ 2) : ℂ) * ψ x * ((‖(lap ψ : Tor L d → ℂ) x‖ ^ 2 : ℝ) : ℂ)

/-- **The variational derivative** `G[ψ] = δE/δψ̄ = −c₁Δψ + c₂Δ(F(|ψ|²)Δψ) + c₂F′(|ψ|²)ψ|Δψ|²`. -/
noncomputable def Gt (c₁ c₂ ε α : ℝ) (ψ : L2 L d) : L2 L d :=
  -((c₁ : ℂ) • lap ψ) + (c₂ : ℂ) • lap (Wt ε α ψ) + (c₂ : ℂ) • Vt ε α ψ

/-! ### Summability of the coefficients of `H⁴` fields -/

omit hL in
theorem abs_xi_le_wt (k : Fin d → ℤ) (j : Fin d) : |xi L k j| ≤ wt L k := by
  have h1 := abs_le_one_add_sq (xi L k j)
  have h2 := xi_sq_le_xi2 (L := L) k j
  unfold wt
  linarith

omit hL in
theorem xi_sq_le_wt (k : Fin d → ℤ) (j : Fin d) : xi L k j ^ 2 ≤ wt L k :=
  (xi_sq_le_xi2 k j).trans (xi2_le_wt k)

/-- **For `ψ ∈ H⁴(𝕋^d)`, `d ≤ 3`: `Σ_k |ψ̂_k|(1 + |ξ_k|²) < ∞`.** -/
theorem summable_coef_mul_wt (hd : d ≤ 3) {ψ : L2 L d} (h4 : InH 2 ψ) :
    Summable fun k => ‖coef ψ k‖ * wt L k := by
  have hf : Summable fun k : Fin d → ℤ => ((wt L k)⁻¹) ^ (2 : ℝ) := by
    simpa [Real.rpow_two] using summable_wt_inv_sq (L := L) hd
  have hg : Summable fun k => (wt L k ^ 2 * ‖coef ψ k‖) ^ (2 : ℝ) :=
    h4.congr fun k => by rw [Real.rpow_two]; ring
  have h := Real.inner_le_Lp_mul_Lq_tsum_of_nonneg Real.HolderConjugate.two_two
    (fun k => (inv_pos.2 (wt_pos (L := L) k)).le) (fun k => by positivity) hf hg
  refine h.1.congr fun k => ?_
  have := (wt_pos (L := L) k).ne'
  field_simp

theorem summable_of_le_wt (hd : d ≤ 3) {ψ : L2 L d} (h4 : InH 2 ψ) {a : (Fin d → ℤ) → ℂ}
    (ha : ∀ k, ‖a k‖ ≤ ‖coef ψ k‖ * wt L k) : Summable fun k => ‖a k‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ha (summable_coef_mul_wt hd h4)

/-- The coefficients of `∂_jψ`. -/
noncomputable def cD (ψ : L2 L d) (j : Fin d) (k : Fin d → ℤ) : ℂ := I * xi L k j * coef ψ k

/-- The coefficients of `∂_j∂_jψ`. -/
noncomputable def cDD (ψ : L2 L d) (j : Fin d) (k : Fin d → ℤ) : ℂ :=
  I * xi L k j * (I * xi L k j * coef ψ k)

/-- The coefficients of `Δψ`. -/
noncomputable def cL (ψ : L2 L d) (k : Fin d → ℤ) : ℂ := -(xi2 L k : ℂ) * coef ψ k

theorem norm_cD (ψ : L2 L d) (j : Fin d) (k : Fin d → ℤ) :
    ‖cD ψ j k‖ = |xi L k j| * ‖coef ψ k‖ := by
  rw [cD, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]

theorem norm_cDD (ψ : L2 L d) (j : Fin d) (k : Fin d → ℤ) :
    ‖cDD ψ j k‖ = xi L k j ^ 2 * ‖coef ψ k‖ := by
  rw [cDD, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
    ← cD, norm_cD, ← mul_assoc, ← sq, sq_abs]

theorem norm_cL (ψ : L2 L d) (k : Fin d → ℤ) : ‖cL ψ k‖ = xi2 L k * ‖coef ψ k‖ := by
  rw [cL, norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg (xi2_nonneg k)]

/-- The continuous representatives of `ψ`, `∂_jψ`, `∂_j∂_jψ` and `Δψ`. -/
theorem rep_facts (hd : d ≤ 3) {ψ : L2 L d} (h4 : InH 2 ψ) :
    (Summable fun k => ‖coef ψ k‖) ∧ (∀ j, Summable fun k => ‖cD ψ j k‖) ∧
    (∀ j, Summable fun k => ‖cDD ψ j k‖) ∧ (Summable fun k => ‖cL ψ k‖) ∧
    Continuous (ser (L := L) (coef ψ)) ∧ (∀ j, Continuous (ser (L := L) (cD ψ j))) ∧
    (∀ j, Continuous (ser (L := L) (cDD ψ j))) ∧ Continuous (ser (L := L) (cL ψ)) ∧
    (∀ j, HasPartial j (ser (L := L) (coef ψ)) (ser (cD ψ j))) ∧
    (∀ j, HasPartial j (ser (L := L) (cD ψ j)) (ser (cDD ψ j))) ∧
    ((ψ : Tor L d → ℂ) =ᵐ[μ L d] ser (coef ψ)) ∧
    (∀ j, (dpart j ψ : Tor L d → ℂ) =ᵐ[μ L d] ser (cD ψ j)) ∧
    ((lap ψ : Tor L d → ℂ) =ᵐ[μ L d] ser (cL ψ)) := by
  have hw := summable_coef_mul_wt (L := L) hd h4
  have h0 : Summable fun k => ‖coef ψ k‖ :=
    summable_of_le_wt hd h4 fun k => le_mul_of_one_le_right (norm_nonneg _) (one_le_wt k)
  have h1 : ∀ j, Summable fun k => ‖cD ψ j k‖ := fun j => summable_of_le_wt hd h4 fun k => by
    rw [norm_cD, mul_comm]
    exact mul_le_mul_of_nonneg_left (abs_xi_le_wt k j) (norm_nonneg _)
  have h2 : ∀ j, Summable fun k => ‖cDD ψ j k‖ := fun j => summable_of_le_wt hd h4 fun k => by
    rw [norm_cDD, mul_comm]
    exact mul_le_mul_of_nonneg_left (xi_sq_le_wt k j) (norm_nonneg _)
  have hL' : Summable fun k => ‖cL ψ k‖ := summable_of_le_wt hd h4 fun k => by
    rw [norm_cL, mul_comm]
    exact mul_le_mul_of_nonneg_left (xi2_le_wt k) (norm_nonneg _)
  have hp1 : ∀ j, HasPartial j (ser (L := L) (coef ψ)) (ser (cD ψ j)) := fun j =>
    hasPartial_ser h0 (Summable.of_nonneg_of_le (fun k => by positivity)
      (fun k => by rw [mul_comm, ← norm_cD]) (h1 j))
  have hp2 : ∀ j, HasPartial j (ser (L := L) (cD ψ j)) (ser (cDD ψ j)) := fun j => by
    have h := hasPartial_ser (L := L) (j := j) (h1 j) (Summable.of_nonneg_of_le
      (fun k => by positivity) (fun k => by
        rw [norm_cD, mul_comm, ← mul_assoc, ← sq, sq_abs, ← norm_cDD]) (h2 j))
    exact h
  have hψ1 : InH 1 ψ := inH_one_of_two h4
  refine ⟨h0, h1, h2, hL', continuous_ser h0, fun j => continuous_ser (h1 j),
    fun j => continuous_ser (h2 j), continuous_ser hL', hp1, hp2, ae_eq_ser h0, fun j => ?_, ?_⟩
  · have e : coef (dpart j ψ) = cD ψ j := funext fun k => coef_dpart hψ1 j k
    have h := ae_eq_ser (L := L) (A := dpart j ψ) (by rw [e]; exact h1 j)
    rwa [e] at h
  · have e : coef (lap ψ) = cL ψ := funext fun k => coef_lap hψ1 k
    have h := ae_eq_ser (L := L) (A := lap ψ) (by rw [e]; exact hL')
    rwa [e] at h

/-! ### The weight `F(|ψ_c|²)` and its partial derivatives -/

omit hL in
theorem continuous_comp_Uw {G : ℝ → ℝ} {f : Tor L d → ℂ} (hG : ContinuousOn G (Uw ε α))
    (hε : 0 < ε) (hf : Continuous f) : Continuous fun x => G (‖f x‖ ^ 2) :=
  hG.comp_continuous (hf.norm.pow 2) fun _ => mem_Uw hε α (sq_nonneg _)

omit hL in
/-- **The weight `w = F(|f|²)` has continuous partial derivatives of order `≤ 2`.** -/
theorem weight_facts (hε : 0 < ε) (α : ℝ) {f : Tor L d → ℂ} {fj fjj : Fin d → Tor L d → ℂ}
    (hf : Continuous f) (hfj : ∀ j, Continuous (fj j)) (hfjj : ∀ j, Continuous (fjj j))
    (h1 : ∀ j, HasPartial j f (fj j)) (h2 : ∀ j, HasPartial j (fj j) (fjj j)) :
    let ρj := fun (j : Fin d) x => 2 * (conj (f x) * fj j x).re
    let ρjj := fun (j : Fin d) x => 2 * (conj (fj j x) * fj j x + conj (f x) * fjj j x).re
    Continuous (fun x => (F ε α (‖f x‖ ^ 2) : ℂ)) ∧
    (∀ j, Continuous fun x => ((Fprime ε α (‖f x‖ ^ 2) * ρj j x : ℝ) : ℂ)) ∧
    (∀ j, Continuous fun x =>
      ((Fsecond ε α (‖f x‖ ^ 2) * ρj j x * ρj j x + Fprime ε α (‖f x‖ ^ 2) * ρjj j x : ℝ) : ℂ)) ∧
    (∀ j, HasPartial j (fun x => (F ε α (‖f x‖ ^ 2) : ℂ))
      (fun x => ((Fprime ε α (‖f x‖ ^ 2) * ρj j x : ℝ) : ℂ))) ∧
    (∀ j, HasPartial j (fun x => ((Fprime ε α (‖f x‖ ^ 2) * ρj j x : ℝ) : ℂ))
      (fun x => ((Fsecond ε α (‖f x‖ ^ 2) * ρj j x * ρj j x + Fprime ε α (‖f x‖ ^ 2) * ρjj j x : ℝ) :
        ℂ))) := by
  intro ρj ρjj
  have hρj : ∀ j, Continuous (ρj j) := fun j =>
    continuous_const.mul (Complex.continuous_re.comp
      ((Complex.continuous_conj.comp hf).mul (hfj j)))
  have hρjj : ∀ j, Continuous (ρjj j) := fun j =>
    continuous_const.mul (Complex.continuous_re.comp
      (((Complex.continuous_conj.comp (hfj j)).mul (hfj j)).add
        ((Complex.continuous_conj.comp hf).mul (hfjj j))))
  have cF := continuous_comp_Uw (continuousOn_F ε α) hε hf
  have cF' := continuous_comp_Uw (continuousOn_Fprime ε α) hε hf
  have cF'' := continuous_comp_Uw (continuousOn_Fsecond ε α) hε hf
  have pρ : ∀ j, HasPartialR j (fun x => ‖f x‖ ^ 2) (ρj j) := fun j => (h1 j).normSq
  have pρj : ∀ j, HasPartialR j (ρj j) (ρjj j) := fun j =>
    ((h1 j).re_conj_mul (h2 j)).const_mul 2
  refine ⟨Complex.continuous_ofReal.comp cF, fun j => Complex.continuous_ofReal.comp
    (cF'.mul (hρj j)), fun j => Complex.continuous_ofReal.comp
    (((cF''.mul (hρj j)).mul (hρj j)).add (cF'.mul (hρjj j))), fun j => ?_, fun j => ?_⟩
  · exact ((pρ j).comp (F := F ε α) (F' := Fprime ε α) fun x =>
      F_hasDerivAt_of_ne (D_pos hε (sq_nonneg _) α).ne').ofReal
  · exact (((pρ j).comp (F := Fprime ε α) (F' := Fsecond ε α) fun x =>
      Fprime_hasDerivAt (mem_Uw hε α (sq_nonneg _))).mul (pρj j)).ofReal

/-! ### Every term of `G[ψ]` lies in `L²` -/

/-- **Regularity of `G[ψ]` for `ψ ∈ H⁴(𝕋^d)`, `d ≤ 3`.** `F(|ψ|²)Δψ ∈ H²` with the Leibniz formula
for its Laplacian, and `F′(|ψ|²)ψ|Δψ|² ∈ L²` (it has a continuous representative). -/
theorem regularity (hd : d ≤ 3) (hε : 0 < ε) (α : ℝ) {ψ : L2 L d} (h4 : InH 2 ψ) :
    MemLp (fun x => (F ε α (‖ψ x‖ ^ 2) : ℂ) * (lap ψ : Tor L d → ℂ) x) 2 (μ L d) ∧
    (Wt ε α ψ : Tor L d → ℂ) =ᵐ[μ L d]
      (fun x => (F ε α (‖ψ x‖ ^ 2) : ℂ) * (lap ψ : Tor L d → ℂ) x) ∧
    InH 1 (Wt ε α ψ) ∧
    MemLp (fun x => (Fprime ε α (‖ψ x‖ ^ 2) : ℂ) * ψ x *
      ((‖(lap ψ : Tor L d → ℂ) x‖ ^ 2 : ℝ) : ℂ)) 2 (μ L d) ∧
    (Vt ε α ψ : Tor L d → ℂ) =ᵐ[μ L d] (fun x => (Fprime ε α (‖ψ x‖ ^ 2) : ℂ) * ψ x *
      ((‖(lap ψ : Tor L d → ℂ) x‖ ^ 2 : ℝ) : ℂ)) ∧
    ∃ wj wjj : Fin d → Tor L d → ℂ, (∀ j, Continuous (wj j)) ∧ (∀ j, Continuous (wjj j)) ∧
      (∀ j, HasPartial j (fun x => (F ε α (‖ser (coef ψ) x‖ ^ 2) : ℂ)) (wj j)) ∧
      (∀ j, HasPartial j (wj j) (wjj j)) ∧
      (lap (Wt ε α ψ) : Tor L d → ℂ) =ᵐ[μ L d] fun x =>
        (F ε α (‖ser (coef ψ) x‖ ^ 2) : ℂ) * (lap (lap ψ) : Tor L d → ℂ) x +
          2 * ∑ j, wj j x * (dpart j (lap ψ) : Tor L d → ℂ) x +
            (∑ j, wjj j x) * (lap ψ : Tor L d → ℂ) x := by
  obtain ⟨h0, h1, h2, hL', c0, c1, c2, cL', p1, p2, a0, -, aL⟩ := rep_facts (L := L) hd h4
  obtain ⟨cw, cwj, cwjj, pw, pwj⟩ := weight_facts (L := L) hε α c0 c1 c2 p1 p2
  set w : Tor L d → ℂ := fun x => (F ε α (‖ser (coef ψ) x‖ ^ 2) : ℂ)
  have hu : InH 1 (lap ψ) := inH_lap h4
  have hwu : (fun x => (F ε α (‖ψ x‖ ^ 2) : ℂ) * (lap ψ : Tor L d → ℂ) x) =ᵐ[μ L d]
      fun x => w x * (lap ψ : Tor L d → ℂ) x := by
    filter_upwards [a0] with x hx
    simp only [w, hx]
  have hmW : MemLp (fun x => (F ε α (‖ψ x‖ ^ 2) : ℂ) * (lap ψ : Tor L d → ℂ) x) 2 (μ L d) :=
    (memLp_mul_continuous (lap ψ) cw).ae_eq hwu.symm
  have hW : (Wt ε α ψ : Tor L d → ℂ) =ᵐ[μ L d]
      (fun x => (F ε α (‖ψ x‖ ^ 2) : ℂ) * (lap ψ : Tor L d → ℂ) x) := coeFn_toL2' hmW
  -- the Leibniz rule for `w Δψ`
  set Qf : Tor L d → ℂ := fun x => w x * (lap (lap ψ) : Tor L d → ℂ) x +
    2 * ∑ j, (fun j x => ((Fprime ε α (‖ser (coef ψ) x‖ ^ 2) *
      (2 * (conj (ser (coef ψ) x) * ser (cD ψ j) x).re) : ℝ) : ℂ)) j x *
        (dpart j (lap ψ) : Tor L d → ℂ) x +
    (∑ j, (fun j x => ((Fsecond ε α (‖ser (coef ψ) x‖ ^ 2) *
      (2 * (conj (ser (coef ψ) x) * ser (cD ψ j) x).re) *
        (2 * (conj (ser (coef ψ) x) * ser (cD ψ j) x).re) +
      Fprime ε α (‖ser (coef ψ) x‖ ^ 2) *
        (2 * (conj (ser (cD ψ j) x) * ser (cD ψ j) x +
          conj (ser (coef ψ) x) * ser (cDD ψ j) x).re) : ℝ) : ℂ)) j x) *
      (lap ψ : Tor L d → ℂ) x
  have hmQ : MemLp Qf 2 (μ L d) := by
    refine ((memLp_mul_continuous (lap (lap ψ)) cw).add ?_).add ?_
    · have : MemLp (fun x => ∑ j, (2 : ℂ) * ((fun j x => ((Fprime ε α (‖ser (coef ψ) x‖ ^ 2) *
          (2 * (conj (ser (coef ψ) x) * ser (cD ψ j) x).re) : ℝ) : ℂ)) j x *
            (dpart j (lap ψ) : Tor L d → ℂ) x)) 2 (μ L d) :=
        memLp_finset_sum _ fun j _ => (memLp_mul_continuous (dpart j (lap ψ)) (cwj j)).const_mul 2
      refine this.ae_eq (Eventually.of_forall fun x => ?_)
      simp only [Finset.mul_sum]
    · have : MemLp (fun x => ∑ j, (fun j x => ((Fsecond ε α (‖ser (coef ψ) x‖ ^ 2) *
          (2 * (conj (ser (coef ψ) x) * ser (cD ψ j) x).re) *
            (2 * (conj (ser (coef ψ) x) * ser (cD ψ j) x).re) +
          Fprime ε α (‖ser (coef ψ) x‖ ^ 2) *
            (2 * (conj (ser (cD ψ j) x) * ser (cD ψ j) x +
              conj (ser (coef ψ) x) * ser (cDD ψ j) x).re) : ℝ) : ℂ)) j x *
          (lap ψ : Tor L d → ℂ) x) 2 (μ L d) :=
        memLp_finset_sum _ fun j _ => memLp_mul_continuous (lap ψ) (cwjj j)
      refine this.ae_eq (Eventually.of_forall fun x => ?_)
      simp only [Finset.sum_mul]
  have hL := leibniz (P := Wt ε α ψ) (Q := hmQ.toLp Qf) hu cw cwj cwjj pw pwj
    (hW.trans hwu) hmQ.coeFn_toLp
  -- the potential term
  have hVf : (fun x => (Fprime ε α (‖ψ x‖ ^ 2) : ℂ) * ψ x *
      ((‖(lap ψ : Tor L d → ℂ) x‖ ^ 2 : ℝ) : ℂ)) =ᵐ[μ L d]
      fun x => (Fprime ε α (‖ser (coef ψ) x‖ ^ 2) : ℂ) * ser (coef ψ) x *
        ((‖ser (cL ψ) x‖ ^ 2 : ℝ) : ℂ) := by
    filter_upwards [a0, aL] with x h1 h2
    rw [h1, h2]
  have hcV : Continuous fun x => (Fprime ε α (‖ser (L := L) (coef ψ) x‖ ^ 2) : ℂ) *
      ser (coef ψ) x * ((‖ser (L := L) (cL ψ) x‖ ^ 2 : ℝ) : ℂ) :=
    ((Complex.continuous_ofReal.comp (continuous_comp_Uw (continuousOn_Fprime ε α) hε c0)).mul
      c0).mul (Complex.continuous_ofReal.comp (cL'.norm.pow 2))
  have hmV := (memLp_of_continuous hcV).ae_eq hVf.symm
  refine ⟨hmW, hW, hL.1, hmV, coeFn_toL2' hmV, _, _, cwj, cwjj, pw, pwj, ?_⟩
  rw [hL.2]
  exact hmQ.coeFn_toLp

end E18

end ReyesMath
