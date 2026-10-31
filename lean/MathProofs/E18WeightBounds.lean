import MathProofs.E18WeightDerivative
import MathProofs.E17Certification

/-!
# E18: bounds and higher derivatives of the curvature weight `F(ρ) = ρ / D(ρ)²`

Builds on `E18FourierEnergy.D`, `E18FourierEnergy.F` and the exact derivative
`E18WeightDerivative.Fprime` (`F_hasDerivAt`).

* `F_norm_sq`: `|R_ε(z)|² = F(|z|²)`; `F_le`: `0 ≤ F ≤ M_{ε,α}²` on `[0, ∞)`; `F_zero`: `F(0) = 0`.
* `Uw = {D > 0} ⊇ [0, ∞)` is open; `contDiffOn_F`: `F` is smooth there;
  `F_hasDerivAt_of_ne`: `F′` wherever `D ≠ 0`.
* `Fprime_hasDerivAt`, `continuousOn_Fsecond`: `F′` is differentiable on `Uw` with continuous
  derivative `F″ = Fsecond`.
* `bound_Fprime`: `F′` is bounded on `[0, A]`; `taylor_F`: the uniform second-order Taylor bound
  `|F(b) − F(a) − F′(a)(b − a)| ≤ K(b − a)²` on `[0, A]`.
-/

open Filter Topology Set

namespace ReyesMath

namespace E18

open E18FourierEnergy E18WeightDerivative

variable {ε α : ℝ}

/-- `F″ = (F′)′`. -/
noncomputable def Fsecond (ε α : ℝ) : ℝ → ℝ := deriv (Fprime ε α)

/-- `M_{ε,α} = max{1, e^{2α₊}/ε²}`. -/
noncomputable def Mw (ε α : ℝ) : ℝ := max 1 (Real.exp (2 * max α 0) / ε ^ 2)

/-- `F(0) = 0`: the curvature weight degenerates at nodes. -/
theorem F_zero (ε α : ℝ) : F ε α 0 = 0 := by simp [F]

theorem continuous_D (ε α : ℝ) : Continuous (D ε α) := by
  unfold D
  fun_prop

theorem contDiff_D (ε α : ℝ) : ContDiff ℝ ⊤ (D ε α) := by
  unfold D
  exact contDiff_id.add (contDiff_const.mul (Real.contDiff_exp.comp
    (contDiff_const.mul contDiff_id)))

/-- `|R_ε(z)|² = F(|z|²)`. -/
theorem F_norm_sq (hε : 0 < ε) (α : ℝ) (z : ℂ) : F ε α (‖z‖ ^ 2) = ‖E26.Rε ε α z‖ ^ 2 := by
  rw [E26.norm_Rε hε, F, D, div_pow]

/-- `F ≤ M_{ε,α}²` on `[0, ∞)`. -/
theorem F_le (hε : 0 < ε) (α : ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) : F ε α ρ ≤ Mw ε α ^ 2 := by
  have hz : ‖((Real.sqrt ρ : ℝ) : ℂ)‖ ^ 2 = ρ := by
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hρ]
  rw [← hz, F_norm_sq hε]
  exact pow_le_pow_left₀ (norm_nonneg _) ((E17Cert.main_theorem hε α).2.2.2.1 _) 2

/-- The open set `Uw = {D > 0}`, which contains `[0, ∞)`. -/
def Uw (ε α : ℝ) : Set ℝ := {ρ | 0 < D ε α ρ}

theorem isOpen_Uw (ε α : ℝ) : IsOpen (Uw ε α) := isOpen_lt continuous_const (continuous_D ε α)

theorem mem_Uw (hε : 0 < ε) (α : ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) : ρ ∈ Uw ε α := D_pos hε hρ α

/-- `F′ = (D − 2ρD′)/D³`, the first form of the manuscript. -/
theorem Fprime_eq_quotient (ε α ρ : ℝ) :
    Fprime ε α ρ = (D ε α ρ - 2 * ρ * Dprime ε α ρ) / D ε α ρ ^ 3 := by
  unfold Fprime D Dprime
  congr 1
  ring

/-- The derivative of `F` wherever `D ≠ 0` (in particular on `[0, ∞)`, `F_hasDerivAt`). -/
theorem F_hasDerivAt_of_ne {ρ : ℝ} (hD : D ε α ρ ≠ 0) : HasDerivAt (F ε α) (Fprime ε α ρ) ρ := by
  have h := (hasDerivAt_id ρ).div ((D_hasDerivAt ε α ρ).pow 2) (pow_ne_zero 2 hD)
  have e : F ε α = fun x => id x / D ε α x ^ 2 := rfl
  rw [e]
  convert h using 1
  rw [Fprime_eq_quotient]
  simp only [Pi.pow_apply, id, Nat.cast_ofNat]
  field_simp
  ring

theorem continuousOn_F (ε α : ℝ) : ContinuousOn (F ε α) (Uw ε α) := fun _ hρ =>
  (F_hasDerivAt_of_ne (ne_of_gt hρ)).continuousAt.continuousWithinAt

/-- `F` is smooth on `{D > 0} ⊇ [0, ∞)`. -/
theorem contDiffOn_F (ε α : ℝ) : ContDiffOn ℝ ⊤ (F ε α) (Uw ε α) :=
  contDiff_id.contDiffOn.div ((contDiff_D ε α).pow 2).contDiffOn
    fun ρ hρ => pow_ne_zero 2 (ne_of_gt hρ)

theorem contDiffOn_Fprime (ε α : ℝ) : ContDiffOn ℝ ⊤ (Fprime ε α) (Uw ε α) := by
  have hN : ContDiff ℝ ⊤ fun ρ : ℝ => ε ^ 2 * Real.exp (-2 * α * ρ) * (1 + 4 * α * ρ) - ρ :=
    ((contDiff_const.mul (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id))).mul
      (contDiff_const.add (contDiff_const.mul contDiff_id))).sub contDiff_id
  exact hN.contDiffOn.div ((contDiff_D ε α).pow 3).contDiffOn
    fun ρ hρ => pow_ne_zero 3 (ne_of_gt hρ)

theorem continuousOn_Fprime (ε α : ℝ) : ContinuousOn (Fprime ε α) (Uw ε α) :=
  (contDiffOn_Fprime ε α).continuousOn

theorem Fprime_hasDerivAt {ρ : ℝ} (hρ : ρ ∈ Uw ε α) :
    HasDerivAt (Fprime ε α) (Fsecond ε α ρ) ρ := by
  have h := ((contDiffOn_Fprime ε α).contDiffAt ((isOpen_Uw ε α).mem_nhds hρ)).differentiableAt
    (by simp)
  exact h.hasDerivAt

theorem continuousOn_Fsecond (ε α : ℝ) : ContinuousOn (Fsecond ε α) (Uw ε α) :=
  (contDiffOn_Fprime ε α).continuousOn_deriv_of_isOpen (isOpen_Uw ε α) (by simp)

/-- `F′` is bounded on `[0, A]`. -/
theorem bound_Fprime (hε : 0 < ε) (α A : ℝ) :
    ∃ K₁ : ℝ, 0 ≤ K₁ ∧ ∀ t ∈ Icc 0 A, |Fprime ε α t| ≤ K₁ := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((continuousOn_Fprime ε α).mono fun t ht => mem_Uw hε α ht.1)
  exact ⟨max C 0, le_max_right _ _, fun t ht => (hC t ht).trans (le_max_left _ _)⟩

/-- `F` is Lipschitz on `[0, A]`. -/
theorem lipschitz_F (hε : 0 < ε) (α A : ℝ) :
    ∃ K₁ : ℝ, 0 ≤ K₁ ∧ ∀ a ∈ Icc 0 A, ∀ b ∈ Icc 0 A, |F ε α b - F ε α a| ≤ K₁ * |b - a| := by
  obtain ⟨K₁, hK₁0, hK₁⟩ := bound_Fprime hε α A
  refine ⟨K₁, hK₁0, fun a ha b hb => ?_⟩
  have h := (convex_Icc 0 A).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := F ε α) (f' := Fprime ε α)
    (fun x hx => (F_hasDerivAt hε hx.1 α).hasDerivWithinAt)
    (fun x hx => by rw [Real.norm_eq_abs]; exact hK₁ x hx) ha hb
  simpa [Real.norm_eq_abs] using h

/-- `F′` is Lipschitz on `[0, A]`. -/
theorem lipschitz_Fprime (hε : 0 < ε) (α A : ℝ) :
    ∃ K₂ : ℝ, 0 ≤ K₂ ∧ ∀ a ∈ Icc 0 A, ∀ b ∈ Icc 0 A,
      |Fprime ε α b - Fprime ε α a| ≤ K₂ * |b - a| := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc 0 A)
    ((continuousOn_Fsecond ε α).mono fun t ht => mem_Uw hε α ht.1)
  refine ⟨max C 0, le_max_right _ _, fun a ha b hb => ?_⟩
  have h := (convex_Icc 0 A).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := Fprime ε α) (f' := Fsecond ε α) (C := max C 0)
    (fun x hx => (Fprime_hasDerivAt (mem_Uw hε α hx.1)).hasDerivWithinAt)
    (fun x hx => (hC x hx).trans (le_max_left C 0)) ha hb
  simpa [Real.norm_eq_abs] using h

/-- **Uniform Taylor bound on `[0, A]`**: `|F(b) − F(a) − F′(a)(b − a)| ≤ K (b − a)²`. -/
theorem taylor_F (hε : 0 < ε) (α A : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ a ∈ Icc 0 A, ∀ b ∈ Icc 0 A,
      |F ε α b - F ε α a - Fprime ε α a * (b - a)| ≤ K * (b - a) ^ 2 := by
  obtain ⟨K, hK0, hK⟩ := lipschitz_Fprime hε α A
  refine ⟨K, hK0, fun a ha b hb => ?_⟩
  have hsub : uIcc a b ⊆ Icc 0 A := Set.uIcc_subset_Icc ha hb
  have hg := (convex_uIcc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun t => F ε α t - Fprime ε α a * t) (f' := fun t => Fprime ε α t - Fprime ε α a)
    (C := K * |b - a|)
    (fun x hx => by
      have hx' := hsub hx
      exact (((F_hasDerivAt hε hx'.1 α).sub
        ((hasDerivAt_id x).const_mul (Fprime ε α a))).congr_deriv (by simp)).hasDerivWithinAt)
    (fun x hx => by
      rw [Real.norm_eq_abs]
      refine (hK a ha x (hsub hx)).trans (mul_le_mul_of_nonneg_left ?_ hK0)
      exact abs_sub_left_of_mem_uIcc hx)
    left_mem_uIcc right_mem_uIcc
  have e : F ε α b - F ε α a - Fprime ε α a * (b - a) =
      (F ε α b - Fprime ε α a * b) - (F ε α a - Fprime ε α a * a) := by ring
  rw [e, ← Real.norm_eq_abs]
  calc ‖(F ε α b - Fprime ε α a * b) - (F ε α a - Fprime ε α a * a)‖ ≤ K * |b - a| * ‖b - a‖ := hg
    _ = K * (b - a) ^ 2 := by rw [Real.norm_eq_abs, mul_assoc, ← sq, sq_abs]

end E18

end ReyesMath
