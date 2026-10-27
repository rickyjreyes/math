import Mathlib
import MathProofs.FourierLeakage

/-!
# Local well-posedness and the classification of invariant Fourier subspaces (F04)

Completes the formalization of
`papers/finite-fourier-coordinate-subspace-noninvariance/main.tex` for
`i∂ₜu = (Δ + κ²)²u − β|u|²u + γ|u|⁴u` on `𝕋^d = (ℝ/2πℤ)^d` (classical solutions in the sense of
`MathProofs.FourierLeakage.IsClassicalSolution`).

* Uniqueness: `integral_cube_pd_eq_zero` (periodic divergence identity on `[0,2π]^d`, from
  Mathlib's divergence theorem on boxes), `green` and `shiftLap_symm` (symmetry of `Δ` and
  `Δ + κ²` on periodic `C²` functions), `norm_nonlin_sub_le` (local Lipschitz bound of the
  nonlinearity), `hasDerivAt_diffEnergy` and `abs_energy_deriv_le` (the `L²` energy identity, in
  which the dispersive term drops out), `eq_zero_of_abs_deriv_le` (Gronwall), and
  `IsClassicalSolution.unique`: two classical solutions with the same datum coincide.
* Local existence: the weighted Wiener algebra `Σ (1 + |n|₁)⁸ |aₙ| < ∞` (`WS`, `wn`) with
  `wn_conv_le` (Young's inequality for convolution on `ℤ^d`), `ser_mul`, `ser_refl`, `ser_Nc`
  (the cubic–quintic nonlinearity of an absolutely convergent Fourier series is the series of
  `Nc`), `wn_Nc_sub_le` (local Lipschitz bound in the algebra); the series calculus
  `contDiff_ser`, `pd_ser`, `laplacian_ser`, `shiftLap_ser`, `ser_omul`; the free propagator
  `ph` with `tendsto_wn_ph`; the interaction-picture vector field `vf` on `ℓ¹(ℤ^d)` and
  `exists_ode_solution` (Picard–Lindelöf); `hasDerivAt_ser_ph` (time derivative of the solution
  series); `isClassicalSolution_of_ode` and `exists_classical_solution`: every trigonometric
  polynomial launches a classical solution.
* `IsInvariant`, `classification` (Corollary): `E_S` is invariant iff `|S| ≤ 1` (for `γ ≠ 0`).
* `noninvariance` (Theorem 1), `universal_leakage_solution` (Theorem 2) and
  `fifth_harmonic_solution` (Proposition): the leakage statements for the (existing and unique)
  classical solution launched from the stated data.
-/

open MeasureTheory Set Filter Topology Complex InnerProductSpace
open scoped NNReal ENNReal

namespace ReyesMath

namespace FourierLeakage

variable {d : ℕ}

local notation "Rd" => EuclideanSpace ℝ (Fin d)

/-- The coordinate partial derivative `∂ⱼf(x) = Df(x) eⱼ`. -/
noncomputable def pd (j : Fin d) (f : Rd → ℂ) (x : Rd) : ℂ :=
  fderiv ℝ f x (EuclideanSpace.single j 1)

/-- `f` is `2π`-periodic in every coordinate. -/
def IsPeriodic (f : Rd → ℂ) : Prop :=
  ∀ x (j : Fin d), f (x + (2 * Real.pi) • EuclideanSpace.single j 1) = f x

/-- `toE` as a continuous linear equivalence. -/
noncomputable def toECLE : (Fin d → ℝ) ≃L[ℝ] Rd :=
  (EuclideanSpace.equiv (Fin d) ℝ).symm

theorem toECLE_apply (y : Fin d → ℝ) : toECLE y = toE y := rfl

theorem toE_single (j : Fin d) : toE (Pi.single j (1 : ℝ)) = EuclideanSpace.single j 1 := by
  ext i
  simp [toE_apply, Pi.single_apply, EuclideanSpace.single_apply]

theorem cube_eq_Icc : cube d = Icc (0 : Fin d → ℝ) (fun _ => 2 * Real.pi) := by
  rw [cube, ← Set.pi_univ_Icc]
  rfl

theorem toE_insertNth {n : ℕ} (j : Fin (n + 1)) (x : Fin n → ℝ) (c : ℝ) :
    toE (Fin.insertNth j c x) = toE (Fin.insertNth j 0 x) + c • EuclideanSpace.single j 1 := by
  ext i
  simp only [toE_apply, PiLp.add_apply, PiLp.smul_apply, EuclideanSpace.single_apply,
    smul_eq_mul]
  rcases eq_or_ne i j with rfl | h
  · simp
  · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq h
    simp [Fin.insertNth_apply_succAbove, h]

/-- **Periodic divergence identity on the cube.**  For `C¹` `F`, `2π`-periodic in coordinate
`j`: `∫_{[0,2π]^d} ∂ⱼF = 0` (Mathlib's divergence theorem on boxes). -/
theorem integral_cube_pd_eq_zero (j : Fin d) {F : Rd → ℂ} (hF : ContDiff ℝ 1 F)
    (hp : ∀ x, F (x + (2 * Real.pi) • EuclideanSpace.single j 1) = F x) :
    ∫ y in cube d, pd j F (toE y) = 0 := by
  cases d with
  | zero => exact j.elim0
  | succ n =>
    have hdiff : Differentiable ℝ F := hF.differentiable le_rfl
    have hcF : Continuous (fderiv ℝ F) := hF.continuous_fderiv le_rfl
    have hle : (0 : Fin (n + 1) → ℝ) ≤ fun _ => 2 * Real.pi := fun _ => by
      simp only [Pi.zero_apply]
      positivity
    have key := integral_divergence_of_hasFDerivAt_off_countable' (0 : Fin (n + 1) → ℝ)
      (fun _ => 2 * Real.pi) hle
      (fun i y => if i = j then F (toE y) else 0)
      (fun i y => if i = j then (fderiv ℝ F (toE y)).comp
        (toECLE : (Fin (n + 1) → ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 1))).toContinuousLinearMap
        else 0)
      ∅ countable_empty
      (fun i => by
        dsimp only
        split_ifs
        · exact (hF.continuous.comp continuous_toE).continuousOn
        · exact continuousOn_const)
      (fun y _ i => by
        dsimp only
        split_ifs
        · exact (hdiff (toE y)).hasFDerivAt.comp y
            (toECLE : (Fin (n + 1) → ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 1))).hasFDerivAt
        · exact hasFDerivAt_const _ _)
      (by
        have hc : Continuous fun y : Fin (n + 1) → ℝ =>
            ∑ i, (if i = j then (fderiv ℝ F (toE y)).comp
              (toECLE : (Fin (n + 1) → ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 1))).toContinuousLinearMap
              else 0) (Pi.single i 1) := by
          refine continuous_finset_sum _ fun i _ => ?_
          split_ifs
          · exact ((hcF.comp continuous_toE).clm_comp continuous_const).clm_apply
              continuous_const
          · exact continuous_const
        exact hc.continuousOn.integrableOn_compact isCompact_Icc)
    have hL : (fun y : Fin (n + 1) → ℝ => ∑ i, (if i = j then (fderiv ℝ F (toE y)).comp
        (toECLE : (Fin (n + 1) → ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 1))).toContinuousLinearMap
        else 0) (Pi.single i 1)) = fun y => pd j F (toE y) := by
      funext y
      rw [Finset.sum_eq_single j (fun i _ hi => by simp [hi]) (by simp)]
      simp [toECLE_apply, toE_single, pd]
    rw [hL, ← cube_eq_Icc] at key
    rw [key]
    refine Finset.sum_eq_zero fun i _ => ?_
    rcases eq_or_ne i j with rfl | hij
    · simp only [Pi.zero_apply]
      rw [sub_eq_zero]
      refine setIntegral_congr_fun measurableSet_Icc fun x _ => ?_
      rw [toE_insertNth i x (2 * Real.pi), hp]
    · simp [hij]

/-! ### Calculus of coordinate derivatives -/

theorem pd_eq (j : Fin d) (f : Rd → ℂ) : pd j f = fun x => fderiv ℝ f x (EuclideanSpace.single j 1) :=
  rfl

theorem contDiff_pd (j : Fin d) {f : Rd → ℂ} {k : ℕ} (hf : ContDiff ℝ (k + 1) f) :
    ContDiff ℝ k (pd j f) := by
  rw [pd_eq]
  exact (hf.fderiv_right (by norm_cast)).clm_apply contDiff_const

theorem pd_mul (j : Fin d) {f g : Rd → ℂ} {x : Rd} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    pd j (fun y => f y * g y) x = pd j f x * g x + f x * pd j g x := by
  unfold pd
  rw [show (fun y => f y * g y) = f * g from rfl, (hf.hasFDerivAt.mul hg.hasFDerivAt).fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem pd_conj (j : Fin d) {f : Rd → ℂ} {x : Rd} (hf : DifferentiableAt ℝ f x) :
    pd j (fun y => (starRingEnd ℂ) (f y)) x = (starRingEnd ℂ) (pd j f x) := by
  unfold pd
  have h := (Complex.conjCLE.toContinuousLinearMap.hasFDerivAt (x := f x)).comp x hf.hasFDerivAt
  rw [show (fun y => (starRingEnd ℂ) (f y)) = Complex.conjCLE.toContinuousLinearMap ∘ f from rfl,
    h.fderiv]
  rfl

theorem pd_sub (j : Fin d) {f g : Rd → ℂ} {x : Rd} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) : pd j (fun y => f y - g y) x = pd j f x - pd j g x := by
  unfold pd
  rw [show (fun y => f y - g y) = f - g from rfl, (hf.hasFDerivAt.sub hg.hasFDerivAt).fderiv]
  rfl

theorem isPeriodic_pd {f : Rd → ℂ} (hf : IsPeriodic f) (j : Fin d) : IsPeriodic (pd j f) := by
  intro x i
  unfold pd
  have h : (fun y => f (y + (2 * Real.pi) • EuclideanSpace.single i 1)) = f := funext fun y => hf y i
  have := fderiv_comp_add_right (𝕜 := ℝ) (f := f) (x := x)
    ((2 * Real.pi) • EuclideanSpace.single i 1)
  rw [h] at this
  rw [← this]

/-- `Δf = Σⱼ ∂ⱼ∂ⱼf` for `C²` functions. -/
theorem laplacian_eq_sum_pd {f : Rd → ℂ} (hf : ContDiff ℝ 2 f) (x : Rd) :
    Δ f x = ∑ j, pd j (pd j f) x := by
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis f (EuclideanSpace.basisFun (Fin d) ℝ)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, EuclideanSpace.basisFun_apply]
  have hfd : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiable le_rfl
  unfold pd
  rw [fderiv_clm_apply (hfd x) (differentiableAt_const _), fderiv_const_apply]
  simp

theorem isPeriodic_sub {f g : Rd → ℂ} (hf : IsPeriodic f) (hg : IsPeriodic g) :
    IsPeriodic fun x => f x - g x := fun x j => by simp only [hf x j, hg x j]

theorem isPeriodic_laplacian {f : Rd → ℂ} (hf : IsPeriodic f) : IsPeriodic (Δ f) := by
  intro x i
  have h : (fun y => f (y + (2 * Real.pi) • EuclideanSpace.single i 1)) = f := funext fun y => hf y i
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis f (EuclideanSpace.basisFun (Fin d) ℝ)]
  have := iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := f) 2
    ((2 * Real.pi) • EuclideanSpace.single i (1 : ℝ)) x
  rw [h] at this
  dsimp only
  rw [← this]

theorem isPeriodic_shiftLap (κ : ℝ) {f : Rd → ℂ} (hf : IsPeriodic f) :
    IsPeriodic (shiftLap κ f) := fun x j => by
  simp only [shiftLap, isPeriodic_laplacian hf x j, hf x j]

theorem contDiff_laplacian {f : Rd → ℂ} {k : ℕ} (hf : ContDiff ℝ (k + 2) f) :
    ContDiff ℝ k (Δ f) := by
  have h : Δ f = fun x => ∑ j, pd j (pd j f) x :=
    funext (laplacian_eq_sum_pd (hf.of_le (by norm_cast; omega)))
  rw [h]
  refine ContDiff.sum fun j _ => contDiff_pd j (contDiff_pd j ?_)
  exact_mod_cast hf

theorem contDiff_shiftLap (κ : ℝ) {f : Rd → ℂ} {k : ℕ} (hf : ContDiff ℝ (k + 2) f) :
    ContDiff ℝ k (shiftLap κ f) := by
  unfold shiftLap
  exact (contDiff_laplacian hf).add (contDiff_const.mul (hf.of_le (by norm_cast; omega)))

theorem integrableOn_cube_of_continuous {F : Rd → ℂ} (hF : Continuous F) :
    IntegrableOn (fun y => F (toE y)) (cube d) :=
  (hF.comp continuous_toE).continuousOn.integrableOn_compact isCompact_cube

/-- **Green's identity on the torus:** `∫ \bar f Δg = ∫ \overline{Δf} g` for periodic `C²`
functions. -/
theorem green {f g : Rd → ℂ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (hpf : IsPeriodic f)
    (hpg : IsPeriodic g) :
    ∫ y in cube d, (starRingEnd ℂ) (f (toE y)) * Δ g (toE y) =
      ∫ y in cube d, (starRingEnd ℂ) (Δ f (toE y)) * g (toE y) := by
  have hf1 : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hg1 : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hpf1 : ∀ j, ContDiff ℝ 1 (pd j f) := fun j => contDiff_pd j (by exact_mod_cast hf)
  have hpg1 : ∀ j, ContDiff ℝ 1 (pd j g) := fun j => contDiff_pd j (by exact_mod_cast hg)
  set H : Fin d → Rd → ℂ := fun j x =>
    (starRingEnd ℂ) (f x) * pd j g x - (starRingEnd ℂ) (pd j f x) * g x with hH
  have hHc : ∀ j, ContDiff ℝ 1 (H j) := fun j =>
    ((Complex.conjCLE.contDiff.comp (hf.of_le (by norm_num))).mul (hpg1 j)).sub
      ((Complex.conjCLE.contDiff.comp (hpf1 j)).mul (hg.of_le (by norm_num)))
  have hHp : ∀ j, ∀ x, H j (x + (2 * Real.pi) • EuclideanSpace.single j 1) = H j x := by
    intro j x
    simp only [hH, hpf x j, hpg x j, isPeriodic_pd hpf j x j, isPeriodic_pd hpg j x j]
  have hpdH : ∀ j x, pd j (H j) x = (starRingEnd ℂ) (f x) * pd j (pd j g) x -
      (starRingEnd ℂ) (pd j (pd j f) x) * g x := by
    intro j x
    have hcf : DifferentiableAt ℝ (fun y => (starRingEnd ℂ) (f y)) x :=
      (Complex.conjCLE.differentiable.comp hf1) x
    have hcpf : DifferentiableAt ℝ (fun y => (starRingEnd ℂ) (pd j f y)) x :=
      (Complex.conjCLE.differentiable.comp ((hpf1 j).differentiable le_rfl)) x
    have hA : DifferentiableAt ℝ (fun y => (starRingEnd ℂ) (f y) * pd j g y) x :=
      hcf.mul (((hpg1 j).differentiable le_rfl) x)
    have hB : DifferentiableAt ℝ (fun y => (starRingEnd ℂ) (pd j f y) * g y) x :=
      hcpf.mul (hg1 x)
    rw [hH]
    simp only
    rw [pd_sub j hA hB, pd_mul j hcf (((hpg1 j).differentiable le_rfl) x), pd_mul j hcpf (hg1 x),
      pd_conj j (hf1 x), pd_conj j (((hpf1 j).differentiable le_rfl) x)]
    ring
  have hsum : ∀ x, (starRingEnd ℂ) (f x) * Δ g x - (starRingEnd ℂ) (Δ f x) * g x =
      ∑ j, pd j (H j) x := by
    intro x
    rw [laplacian_eq_sum_pd hg, laplacian_eq_sum_pd hf, map_sum, Finset.mul_sum, Finset.sum_mul,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => (hpdH j x).symm
  have hcont1 : Continuous fun x => (starRingEnd ℂ) (f x) * Δ g x :=
    (Complex.continuous_conj.comp hf.continuous).mul (contDiff_laplacian (k := 0) hg).continuous
  have hcont2 : Continuous fun x => (starRingEnd ℂ) (Δ f x) * g x :=
    (Complex.continuous_conj.comp (contDiff_laplacian (k := 0) hf).continuous).mul hg.continuous
  rw [← sub_eq_zero, ← integral_sub (integrableOn_cube_of_continuous hcont1)
    (integrableOn_cube_of_continuous hcont2)]
  simp_rw [hsum]
  rw [integral_finset_sum _ fun j _ => integrableOn_cube_of_continuous
    (contDiff_pd (k := 0) j (hHc j)).continuous]
  exact Finset.sum_eq_zero fun j _ => integral_cube_pd_eq_zero j (hHc j) (hHp j)

/-- `(Δ + κ²)` is symmetric on periodic `C²` functions. -/
theorem shiftLap_symm (κ : ℝ) {f g : Rd → ℂ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hpf : IsPeriodic f) (hpg : IsPeriodic g) :
    ∫ y in cube d, (starRingEnd ℂ) (f (toE y)) * shiftLap κ g (toE y) =
      ∫ y in cube d, (starRingEnd ℂ) (shiftLap κ f (toE y)) * g (toE y) := by
  have hc1 : Continuous fun x => (starRingEnd ℂ) (f x) * Δ g x :=
    (Complex.continuous_conj.comp hf.continuous).mul (contDiff_laplacian (k := 0) hg).continuous
  have hc2 : Continuous fun x => (starRingEnd ℂ) (f x) * (((κ ^ 2 : ℝ) : ℂ) * g x) :=
    (Complex.continuous_conj.comp hf.continuous).mul (continuous_const.mul hg.continuous)
  have hc3 : Continuous fun x => (starRingEnd ℂ) (Δ f x) * g x :=
    (Complex.continuous_conj.comp (contDiff_laplacian (k := 0) hf).continuous).mul hg.continuous
  have hc4 : Continuous fun x => (starRingEnd ℂ) (((κ ^ 2 : ℝ) : ℂ) * f x) * g x :=
    (Complex.continuous_conj.comp (continuous_const.mul hf.continuous)).mul hg.continuous
  have e1 : (fun y => (starRingEnd ℂ) (f (toE y)) * shiftLap κ g (toE y)) =
      fun y => (starRingEnd ℂ) (f (toE y)) * Δ g (toE y) +
        (starRingEnd ℂ) (f (toE y)) * (((κ ^ 2 : ℝ) : ℂ) * g (toE y)) := by
    funext y
    simp only [shiftLap]
    ring
  have e2 : (fun y => (starRingEnd ℂ) (shiftLap κ f (toE y)) * g (toE y)) =
      fun y => (starRingEnd ℂ) (Δ f (toE y)) * g (toE y) +
        (starRingEnd ℂ) (((κ ^ 2 : ℝ) : ℂ) * f (toE y)) * g (toE y) := by
    funext y
    simp only [shiftLap, map_add]
    ring
  rw [e1, e2, integral_add (integrableOn_cube_of_continuous hc1)
    (integrableOn_cube_of_continuous hc2), integral_add (integrableOn_cube_of_continuous hc3)
    (integrableOn_cube_of_continuous hc4), green hf hg hpf hpg]
  congr 1
  refine setIntegral_congr_fun measurableSet_cube fun y _ => ?_
  simp only [map_mul, Complex.conj_ofReal]
  ring

theorem shiftLap_sub (κ : ℝ) {f g : Rd → ℂ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) :
    shiftLap κ (fun x => f x - g x) = fun x => shiftLap κ f x - shiftLap κ g x := by
  have hfg : ContDiff ℝ 2 fun x => f x - g x := hf.sub hg
  have hpd : ∀ j, pd j (fun x => f x - g x) = fun x => pd j f x - pd j g x := fun j =>
    funext fun x => pd_sub j (hf.differentiable (by norm_num) x) (hg.differentiable (by norm_num) x)
  funext x
  simp only [shiftLap]
  rw [laplacian_eq_sum_pd hfg, laplacian_eq_sum_pd hf, laplacian_eq_sum_pd hg]
  simp_rw [hpd]
  have : ∀ j, pd j (fun x => pd j f x - pd j g x) x = pd j (pd j f) x - pd j (pd j g) x := fun j =>
    pd_sub j ((contDiff_pd (k := 1) j (by exact_mod_cast hf)).differentiable le_rfl x)
      ((contDiff_pd (k := 1) j (by exact_mod_cast hg)).differentiable le_rfl x)
  simp_rw [this]
  rw [Finset.sum_sub_distrib]
  ring

/-! ### Uniqueness of classical solutions -/

theorem IsClassicalSolution.mono {κ β γ τ τ' : ℝ} {u : ℝ → Rd → ℂ}
    (h : IsClassicalSolution κ β γ τ u) (hτ' : 0 < τ') (hle : τ' ≤ τ) :
    IsClassicalSolution κ β γ τ' u := by
  have hsub : Ioo (-τ') τ' ⊆ Ioo (-τ) τ := Ioo_subset_Ioo (by linarith) hle
  exact ⟨hτ', h.periodic, fun t ht => h.smooth t (hsub ht),
    h.cont.mono (prod_mono hsub subset_rfl), fun t ht => h.time_diff t (hsub ht),
    h.dt_cont.mono (prod_mono hsub subset_rfl), fun t ht => h.pde t (hsub ht)⟩

/-- **Local Lipschitz bound of the nonlinearity:** on `|z|, |w| ≤ R`,
`|N(z) − N(w)| ≤ (3|β|R² + 5|γ|R⁴)|z − w|`. -/
theorem norm_nonlin_sub_le (β γ : ℝ) {z w : ℂ} {R : ℝ} (hz : ‖z‖ ≤ R) (hw : ‖w‖ ≤ R) :
    ‖nonlin β γ z - nonlin β γ w‖ ≤ (3 * |β| * R ^ 2 + 5 * |γ| * R ^ 4) * ‖z - w‖ := by
  have hR : 0 ≤ R := (norm_nonneg _).trans hz
  have hab : |‖z‖ - ‖w‖| ≤ ‖z - w‖ := abs_norm_sub_norm_le z w
  have ha : 0 ≤ ‖z‖ := norm_nonneg _
  have hb : 0 ≤ ‖w‖ := norm_nonneg _
  have hδ : 0 ≤ ‖z - w‖ := norm_nonneg _
  have hsum : ‖z‖ + ‖w‖ ≤ 2 * R := by linarith
  -- the cubic difference
  have h3 : ‖((‖z‖ ^ 2 : ℝ) : ℂ) * z - ((‖w‖ ^ 2 : ℝ) : ℂ) * w‖ ≤ 3 * R ^ 2 * ‖z - w‖ := by
    have e : ((‖z‖ ^ 2 : ℝ) : ℂ) * z - ((‖w‖ ^ 2 : ℝ) : ℂ) * w =
        ((‖z‖ ^ 2 : ℝ) : ℂ) * (z - w) + ((‖z‖ ^ 2 - ‖w‖ ^ 2 : ℝ) : ℂ) * w := by
      push_cast
      ring
    have hd : |‖z‖ ^ 2 - ‖w‖ ^ 2| ≤ 2 * R * ‖z - w‖ := by
      rw [show ‖z‖ ^ 2 - ‖w‖ ^ 2 = (‖z‖ - ‖w‖) * (‖z‖ + ‖w‖) by ring, abs_mul,
        abs_of_nonneg (by positivity : 0 ≤ ‖z‖ + ‖w‖)]
      nlinarith [mul_le_mul hab hsum (by positivity) hδ]
    rw [e]
    calc _ ≤ ‖((‖z‖ ^ 2 : ℝ) : ℂ) * (z - w)‖ + ‖((‖z‖ ^ 2 - ‖w‖ ^ 2 : ℝ) : ℂ) * w‖ :=
          norm_add_le _ _
      _ = ‖z‖ ^ 2 * ‖z - w‖ + |‖z‖ ^ 2 - ‖w‖ ^ 2| * ‖w‖ := by
          rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
            Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖z‖)]
      _ ≤ R ^ 2 * ‖z - w‖ + (2 * R * ‖z - w‖) * R := by
          gcongr
      _ = 3 * R ^ 2 * ‖z - w‖ := by ring
  -- the quintic difference
  have h5 : ‖((‖z‖ ^ 4 : ℝ) : ℂ) * z - ((‖w‖ ^ 4 : ℝ) : ℂ) * w‖ ≤ 5 * R ^ 4 * ‖z - w‖ := by
    have e : ((‖z‖ ^ 4 : ℝ) : ℂ) * z - ((‖w‖ ^ 4 : ℝ) : ℂ) * w =
        ((‖z‖ ^ 4 : ℝ) : ℂ) * (z - w) + ((‖z‖ ^ 4 - ‖w‖ ^ 4 : ℝ) : ℂ) * w := by
      push_cast
      ring
    have hsq : ‖z‖ ^ 2 + ‖w‖ ^ 2 ≤ 2 * R ^ 2 := by
      have := pow_le_pow_left₀ ha hz 2
      have := pow_le_pow_left₀ hb hw 2
      linarith
    have hd : |‖z‖ ^ 4 - ‖w‖ ^ 4| ≤ 4 * R ^ 3 * ‖z - w‖ := by
      rw [show ‖z‖ ^ 4 - ‖w‖ ^ 4 = (‖z‖ - ‖w‖) * ((‖z‖ + ‖w‖) * (‖z‖ ^ 2 + ‖w‖ ^ 2)) by ring,
        abs_mul, abs_of_nonneg (by positivity : 0 ≤ (‖z‖ + ‖w‖) * (‖z‖ ^ 2 + ‖w‖ ^ 2))]
      have h1 : (‖z‖ + ‖w‖) * (‖z‖ ^ 2 + ‖w‖ ^ 2) ≤ 2 * R * (2 * R ^ 2) :=
        mul_le_mul hsum hsq (by positivity) (by positivity)
      nlinarith [mul_le_mul hab h1 (by positivity) hδ]
    rw [e]
    calc _ ≤ ‖((‖z‖ ^ 4 : ℝ) : ℂ) * (z - w)‖ + ‖((‖z‖ ^ 4 - ‖w‖ ^ 4 : ℝ) : ℂ) * w‖ :=
          norm_add_le _ _
      _ = ‖z‖ ^ 4 * ‖z - w‖ + |‖z‖ ^ 4 - ‖w‖ ^ 4| * ‖w‖ := by
          rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
            Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖z‖ ^ 4)]
      _ ≤ R ^ 4 * ‖z - w‖ + (4 * R ^ 3 * ‖z - w‖) * R := by
          gcongr
      _ = 5 * R ^ 4 * ‖z - w‖ := by ring
  have e : nonlin β γ z - nonlin β γ w =
      -(β : ℂ) * (((‖z‖ ^ 2 : ℝ) : ℂ) * z - ((‖w‖ ^ 2 : ℝ) : ℂ) * w) +
        (γ : ℂ) * (((‖z‖ ^ 4 : ℝ) : ℂ) * z - ((‖w‖ ^ 4 : ℝ) : ℂ) * w) := by
    unfold nonlin
    ring
  rw [e]
  calc _ ≤ ‖-(β : ℂ) * (((‖z‖ ^ 2 : ℝ) : ℂ) * z - ((‖w‖ ^ 2 : ℝ) : ℂ) * w)‖ +
        ‖(γ : ℂ) * (((‖z‖ ^ 4 : ℝ) : ℂ) * z - ((‖w‖ ^ 4 : ℝ) : ℂ) * w)‖ := norm_add_le _ _
    _ ≤ |β| * (3 * R ^ 2 * ‖z - w‖) + |γ| * (5 * R ^ 4 * ‖z - w‖) := by
        rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs]
        gcongr
    _ = _ := by ring

/-- A nonnegative function with `|E'| ≤ C E` that vanishes at `0` vanishes identically. -/
theorem eq_zero_of_abs_deriv_le {E E' : ℝ → ℝ} {T C : ℝ}
    (hd : ∀ s ∈ Ioo (-T) T, HasDerivAt E (E' s) s) (hb : ∀ s ∈ Ioo (-T) T, |E' s| ≤ C * E s)
    (h0 : E 0 = 0) (hnn : ∀ s ∈ Ioo (-T) T, 0 ≤ E s) : ∀ s ∈ Ioo (-T) T, E s = 0 := by
  intro s hs
  have hT : 0 < T := by linarith [hs.1, hs.2]
  have h0mem : (0 : ℝ) ∈ Ioo (-T) T := ⟨by linarith, hT⟩
  rcases le_total 0 s with hs0 | hs0
  · set φ : ℝ → ℝ := fun r => E r * Real.exp (-C * r) with hφ
    have hφd : ∀ r ∈ Ioo (-T) T, HasDerivAt φ ((E' r - C * E r) * Real.exp (-C * r)) r := by
      intro r hr
      have h1 : HasDerivAt (fun r : ℝ => Real.exp (-C * r)) (Real.exp (-C * r) * (-C)) r := by
        simpa using ((hasDerivAt_id r).const_mul (-C)).exp
      convert (hd r hr).mul h1 using 1
      ring
    have hsub : Icc 0 s ⊆ Ioo (-T) T := fun r hr => ⟨by linarith [hr.1], by linarith [hr.2, hs.2]⟩
    have hanti : AntitoneOn φ (Icc 0 s) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc 0 s)
        (fun r hr => (hφd r (hsub hr)).continuousAt.continuousWithinAt)
        (fun r hr => (hφd r (hsub (interior_subset hr))).differentiableAt.differentiableWithinAt)
        fun r hr => ?_
      have hr' := hsub (interior_subset hr)
      rw [(hφd r hr').deriv]
      have := hb r hr'
      have : E' r - C * E r ≤ 0 := by linarith [le_abs_self (E' r)]
      exact mul_nonpos_of_nonpos_of_nonneg this (Real.exp_pos _).le
    have h1 := hanti ⟨le_rfl, hs0⟩ ⟨hs0, le_rfl⟩ hs0
    simp only [hφ, h0, zero_mul] at h1
    have h2 := hnn s hs
    have h3 : E s * Real.exp (-C * s) ≥ 0 := mul_nonneg h2 (Real.exp_pos _).le
    have h4 : E s * Real.exp (-C * s) = 0 := le_antisymm h1 h3
    rcases mul_eq_zero.1 h4 with h | h
    · exact h
    · exact absurd h (Real.exp_pos _).ne'
  · set ψ : ℝ → ℝ := fun r => E (-r) * Real.exp (-C * r) with hψ
    have hψd : ∀ r ∈ Ioo (-T) T, HasDerivAt ψ ((-E' (-r) - C * E (-r)) * Real.exp (-C * r)) r := by
      intro r hr
      have hr' : -r ∈ Ioo (-T) T := ⟨by linarith [hr.2], by linarith [hr.1]⟩
      have h1 : HasDerivAt (fun r : ℝ => Real.exp (-C * r)) (Real.exp (-C * r) * (-C)) r := by
        simpa using ((hasDerivAt_id r).const_mul (-C)).exp
      have h2 : HasDerivAt (fun r : ℝ => E (-r)) (E' (-r) * (-1)) r :=
        (hd (-r) hr').comp r (hasDerivAt_neg r)
      convert h2.mul h1 using 1
      ring
    have hsub : Icc 0 (-s) ⊆ Ioo (-T) T := fun r hr =>
      ⟨by linarith [hr.1], by linarith [hr.2, hs.1]⟩
    have hanti : AntitoneOn ψ (Icc 0 (-s)) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc 0 (-s))
        (fun r hr => (hψd r (hsub hr)).continuousAt.continuousWithinAt)
        (fun r hr => (hψd r (hsub (interior_subset hr))).differentiableAt.differentiableWithinAt)
        fun r hr => ?_
      have hr' := hsub (interior_subset hr)
      rw [(hψd r hr').deriv]
      have hmr : -r ∈ Ioo (-T) T := ⟨by linarith [hr'.2], by linarith [hr'.1]⟩
      have := hb (-r) hmr
      have : -E' (-r) - C * E (-r) ≤ 0 := by linarith [neg_abs_le (E' (-r))]
      exact mul_nonpos_of_nonpos_of_nonneg this (Real.exp_pos _).le
    have hs0' : 0 ≤ -s := by linarith
    have h1 := hanti ⟨le_rfl, hs0'⟩ ⟨hs0', le_rfl⟩ hs0'
    simp only [hψ, neg_zero, h0, zero_mul, neg_neg] at h1
    have h2 := hnn s hs
    have h3 : E s * Real.exp (-C * -s) ≥ 0 := mul_nonneg h2 (Real.exp_pos _).le
    have h4 : E s * Real.exp (-C * -s) = 0 := le_antisymm h1 h3
    rcases mul_eq_zero.1 h4 with h | h
    · exact h
    · exact absurd h (Real.exp_pos _).ne'

/-- A continuous periodic function vanishing on the fundamental cube vanishes identically. -/
theorem eq_of_eqOn_cube {f g : Rd → ℂ} (hpf : IsPeriodic f) (hpg : IsPeriodic g)
    (h : ∀ y ∈ cube d, f (toE y) = g (toE y)) : f = g := by
  have hp : (0 : ℝ) < 2 * Real.pi := Real.two_pi_pos
  have hz : ∀ F : Rd → ℂ, IsPeriodic F → ∀ (j : Fin d) (k : ℤ) (x : Rd),
      F (x + (k : ℝ) • ((2 * Real.pi) • EuclideanSpace.single j (1 : ℝ))) = F x := by
    intro F hF j k x
    have hper : Function.Periodic F ((2 * Real.pi) • EuclideanSpace.single j (1 : ℝ)) :=
      fun x => hF x j
    have := hper.zsmul k x
    rwa [← Int.cast_smul_eq_zsmul ℝ] at this
  have hsum : ∀ F : Rd → ℂ, IsPeriodic F → ∀ (s : Finset (Fin d)) (k : Fin d → ℤ) (x : Rd),
      F (x + ∑ j ∈ s, (k j : ℝ) • ((2 * Real.pi) • EuclideanSpace.single j (1 : ℝ))) = F x := by
    intro F hF s k
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      intro x
      rw [Finset.sum_insert ha, add_comm ((k a : ℝ) • _) _, ← add_assoc, hz F hF a (k a), ih]
  funext x
  set k : Fin d → ℤ := fun j => toIcoDiv hp 0 (x j) with hk
  set y : Fin d → ℝ := fun j => toIcoMod hp 0 (x j) with hy
  have hymem : y ∈ cube d := fun j _ => by
    have := toIcoMod_mem_Ico hp 0 (x j)
    simp only [zero_add] at this
    exact ⟨this.1, this.2.le⟩
  have hx : x = toE y + ∑ j, (k j : ℝ) • ((2 * Real.pi) • EuclideanSpace.single j (1 : ℝ)) := by
    ext i
    have h1 := toIcoMod_add_toIcoDiv_zsmul hp 0 (x i)
    rw [zsmul_eq_mul] at h1
    have hS := map_sum (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin d) i)
      (fun j => (k j : ℝ) • ((2 * Real.pi) • EuclideanSpace.single j (1 : ℝ))) Finset.univ
    rw [PiLp.add_apply, show (∑ j, (k j : ℝ) • ((2 * Real.pi) • EuclideanSpace.single j (1 : ℝ))) i
      = _ from hS]
    simp [EuclideanSpace.single_apply, toE_apply, hy, hk]
    linarith
  rw [hx, hsum f hpf, hsum g hpg]
  exact h y hymem

theorem cube_subset_closure_interior : cube d ⊆ closure (interior (cube d)) := by
  rw [cube, interior_pi_set Set.finite_univ, closure_pi_set]
  intro y hy j _
  rw [interior_Icc, closure_Ioo Real.two_pi_pos.ne]
  exact hy j (mem_univ j)

/-- Vanishing `L²` distance on the cube forces equality of continuous periodic functions. -/
theorem eq_of_integral_normSq_eq_zero {f g : Rd → ℂ} (hf : Continuous f) (hg : Continuous g)
    (hpf : IsPeriodic f) (hpg : IsPeriodic g)
    (h : ∫ y in cube d, ‖f (toE y) - g (toE y)‖ ^ 2 = 0) : f = g := by
  have hc : Continuous fun y : Fin d → ℝ => ‖f (toE y) - g (toE y)‖ ^ 2 :=
    ((hf.comp continuous_toE).sub (hg.comp continuous_toE)).norm.pow 2
  have hae := (setIntegral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall fun y => by positivity)
    (hc.continuousOn.integrableOn_compact isCompact_cube)).1 h
  have heq := Measure.eqOn_of_ae_eq hae hc.continuousOn continuousOn_const
    cube_subset_closure_interior
  refine eq_of_eqOn_cube hpf hpg fun y hy => ?_
  have := heq hy
  simp only [Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff,
    norm_eq_zero] at this
  exact sub_eq_zero.1 this

theorem IsClassicalSolution.isPeriodic {κ β γ τ : ℝ} {u : ℝ → Rd → ℂ}
    (h : IsClassicalSolution κ β γ τ u) (t : ℝ) : IsPeriodic (u t) := fun x j => h.periodic t x j

theorem IsClassicalSolution.continuous_dt {κ β γ τ : ℝ} {u : ℝ → Rd → ℂ}
    (h : IsClassicalSolution κ β γ τ u) {t : ℝ} (ht : t ∈ Ioo (-τ) τ) :
    Continuous fun x : Rd => deriv (fun s => u s x) t :=
  h.dt_cont.comp_continuous (continuous_const.prodMk continuous_id) fun _ => ⟨ht, mem_univ _⟩

/-- The `L²(cube)` distance between two solutions. -/
noncomputable def diffEnergy (u₁ u₂ : ℝ → Rd → ℂ) (s : ℝ) : ℝ :=
  ∫ y in cube d, ‖u₁ s (toE y) - u₂ s (toE y)‖ ^ 2

/-- Differentiation of the `L²` distance under the integral sign. -/
theorem hasDerivAt_diffEnergy {κ β γ τ : ℝ} {u₁ u₂ : ℝ → Rd → ℂ}
    (h₁ : IsClassicalSolution κ β γ τ u₁) (h₂ : IsClassicalSolution κ β γ τ u₂) {t : ℝ}
    (ht : t ∈ Ioo (-τ) τ) :
    HasDerivAt (diffEnergy u₁ u₂)
      (∫ y in cube d, 2 * ((starRingEnd ℂ) (u₁ t (toE y) - u₂ t (toE y)) *
        (deriv (fun s => u₁ s (toE y)) t - deriv (fun s => u₂ s (toE y)) t)).re) t := by
  have hta : |t| < τ := abs_lt.2 ⟨ht.1, ht.2⟩
  set ε := (τ - |t|) / 2 with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  have hsub : ∀ s ∈ Metric.closedBall t ε, s ∈ Ioo (-τ) τ := by
    intro s hs
    rw [Metric.mem_closedBall, Real.dist_eq, abs_le] at hs
    have := neg_abs_le t
    have := le_abs_self t
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hmap : Continuous fun p : ℝ × (Fin d → ℝ) => (p.1, toE p.2) :=
    continuous_fst.prodMk (continuous_toE.comp continuous_snd)
  have hmaps : ∀ p ∈ Metric.closedBall t ε ×ˢ cube d, (p.1, toE p.2) ∈ Ioo (-τ) τ ×ˢ univ :=
    fun p hp => ⟨hsub p.1 hp.1, mem_univ _⟩
  have hu₁ : ContinuousOn (fun p : ℝ × (Fin d → ℝ) => u₁ p.1 (toE p.2))
      (Metric.closedBall t ε ×ˢ cube d) := h₁.cont.comp hmap.continuousOn hmaps
  have hu₂ : ContinuousOn (fun p : ℝ × (Fin d → ℝ) => u₂ p.1 (toE p.2))
      (Metric.closedBall t ε ×ˢ cube d) := h₂.cont.comp hmap.continuousOn hmaps
  have hd₁ : ContinuousOn (fun p : ℝ × (Fin d → ℝ) => deriv (fun s => u₁ s (toE p.2)) p.1)
      (Metric.closedBall t ε ×ˢ cube d) := h₁.dt_cont.comp hmap.continuousOn hmaps
  have hd₂ : ContinuousOn (fun p : ℝ × (Fin d → ℝ) => deriv (fun s => u₂ s (toE p.2)) p.1)
      (Metric.closedBall t ε ×ˢ cube d) := h₂.dt_cont.comp hmap.continuousOn hmaps
  have hcont : ContinuousOn (fun p : ℝ × (Fin d → ℝ) =>
      2 * ((starRingEnd ℂ) (u₁ p.1 (toE p.2) - u₂ p.1 (toE p.2)) *
        (deriv (fun s => u₁ s (toE p.2)) p.1 - deriv (fun s => u₂ s (toE p.2)) p.1)).re)
      (Metric.closedBall t ε ×ˢ cube d) :=
    continuousOn_const.mul (Complex.continuous_re.comp_continuousOn
      ((Complex.continuous_conj.comp_continuousOn (hu₁.sub hu₂)).mul (hd₁.sub hd₂)))
  obtain ⟨M, hM⟩ := ((isCompact_closedBall t ε).prod isCompact_cube).exists_bound_of_continuousOn
    hcont
  haveI := isFiniteMeasure_cube (d := d)
  have hslice : ∀ s ∈ Ioo (-τ) τ, Continuous fun y : Fin d → ℝ =>
      ‖u₁ s (toE y) - u₂ s (toE y)‖ ^ 2 := fun s hs =>
    ((((h₁.smooth s hs).continuous).comp continuous_toE).sub
      (((h₂.smooth s hs).continuous).comp continuous_toE)).norm.pow 2
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (cube d))
    (x₀ := t) (F := fun s y => ‖u₁ s (toE y) - u₂ s (toE y)‖ ^ 2)
    (F' := fun s y => 2 * ((starRingEnd ℂ) (u₁ s (toE y) - u₂ s (toE y)) *
      (deriv (fun s => u₁ s (toE y)) s - deriv (fun s => u₂ s (toE y)) s)).re)
    (bound := fun _ => M) hεpos
    (by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
      exact (hslice s hs).aestronglyMeasurable)
    ((hslice t ht).continuousOn.integrableOn_compact isCompact_cube)
    (by
      have hc : Continuous fun y : Fin d → ℝ =>
          2 * ((starRingEnd ℂ) (u₁ t (toE y) - u₂ t (toE y)) *
            (deriv (fun s => u₁ s (toE y)) t - deriv (fun s => u₂ s (toE y)) t)).re :=
        continuous_const.mul (Complex.continuous_re.comp
          ((Complex.continuous_conj.comp ((((h₁.smooth t ht).continuous).comp continuous_toE).sub
            (((h₂.smooth t ht).continuous).comp continuous_toE))).mul
            (((h₁.continuous_dt ht).comp continuous_toE).sub
              ((h₂.continuous_dt ht).comp continuous_toE))))
      exact hc.aestronglyMeasurable)
    (by
      filter_upwards [ae_restrict_mem measurableSet_cube] with y hy s hs
      exact hM (s, y) ⟨Metric.ball_subset_closedBall hs, hy⟩)
    (integrable_const M)
    (Eventually.of_forall fun y s hs => by
      have hs' := hsub s (Metric.ball_subset_closedBall hs)
      have hw := ((h₁.time_diff s hs' (toE y)).hasDerivAt.sub
        (h₂.time_diff s hs' (toE y)).hasDerivAt).norm_sq
      convert hw using 1
      rw [Complex.inner]
      beta_reduce
      congr 2
      simp only [Pi.sub_apply]
      ring)
  exact key.2

theorem continuous_nonlin (β γ : ℝ) : Continuous (nonlin β γ) := by
  unfold nonlin
  fun_prop

/-- The time derivative of a classical solution from the equation:
`∂ₜu = −i((Δ+κ²)²u + N(u))`. -/
theorem IsClassicalSolution.deriv_eq {κ β γ τ : ℝ} {u : ℝ → Rd → ℂ}
    (h : IsClassicalSolution κ β γ τ u) {s : ℝ} (hs : s ∈ Ioo (-τ) τ) (x : Rd) :
    deriv (fun s' => u s' x) s =
      -Complex.I * (shiftLap κ (shiftLap κ (u s)) x + nonlin β γ (u s x)) := by
  rw [← h.pde s hs x, ← mul_assoc, show -Complex.I * Complex.I = 1 by
    rw [neg_mul, Complex.I_mul_I, neg_neg], one_mul]

/-- **Energy estimate:** `|d/dt ‖u₁ − u₂‖²| ≤ 2C ‖u₁ − u₂‖²`, the dispersive term dropping out
by the symmetry of `(Δ+κ²)²`. -/
theorem abs_energy_deriv_le {κ β γ τ : ℝ} {u₁ u₂ : ℝ → Rd → ℂ}
    (h₁ : IsClassicalSolution κ β γ τ u₁) (h₂ : IsClassicalSolution κ β γ τ u₂) {s R : ℝ}
    (hs : s ∈ Ioo (-τ) τ) (hR₁ : ∀ y ∈ cube d, ‖u₁ s (toE y)‖ ≤ R)
    (hR₂ : ∀ y ∈ cube d, ‖u₂ s (toE y)‖ ≤ R) :
    |∫ y in cube d, 2 * ((starRingEnd ℂ) (u₁ s (toE y) - u₂ s (toE y)) *
        (deriv (fun s' => u₁ s' (toE y)) s - deriv (fun s' => u₂ s' (toE y)) s)).re| ≤
      2 * (3 * |β| * R ^ 2 + 5 * |γ| * R ^ 4) * diffEnergy u₁ u₂ s := by
  set C := 3 * |β| * R ^ 2 + 5 * |γ| * R ^ 4 with hC
  have hs₁ := h₁.smooth s hs
  have hs₂ := h₂.smooth s hs
  set w : Rd → ℂ := fun x => u₁ s x - u₂ s x with hw
  have hw4 : ContDiff ℝ 4 w := hs₁.sub hs₂
  have hwp : IsPeriodic w := isPeriodic_sub (h₁.isPeriodic s) (h₂.isPeriodic s)
  set A : Rd → ℂ := shiftLap κ w with hA
  have hA2 : ContDiff ℝ 2 A := contDiff_shiftLap (k := 2) κ hw4
  have hAp : IsPeriodic A := isPeriodic_shiftLap κ hwp
  have hAA0 : Continuous (shiftLap κ A) := (contDiff_shiftLap (k := 0) κ hA2).continuous
  have hlin : ∀ x, shiftLap κ (shiftLap κ (u₁ s)) x - shiftLap κ (shiftLap κ (u₂ s)) x =
      shiftLap κ A x := by
    intro x
    have e1 : A = fun x => shiftLap κ (u₁ s) x - shiftLap κ (u₂ s) x := by
      rw [hA, hw]
      exact shiftLap_sub κ (hs₁.of_le (by norm_num)) (hs₂.of_le (by norm_num))
    rw [e1, shiftLap_sub κ (contDiff_shiftLap (k := 2) κ hs₁) (contDiff_shiftLap (k := 2) κ hs₂)]
  have hD : ∀ x, deriv (fun s' => u₁ s' x) s - deriv (fun s' => u₂ s' x) s =
      -Complex.I * (shiftLap κ A x + (nonlin β γ (u₁ s x) - nonlin β γ (u₂ s x))) := by
    intro x
    rw [h₁.deriv_eq hs x, h₂.deriv_eq hs x, ← hlin x]
    ring
  -- split the integrand
  set Q₁ : (Fin d → ℝ) → ℝ := fun y =>
    2 * ((starRingEnd ℂ) (w (toE y)) * shiftLap κ A (toE y)).im with hQ₁
  set Q₂ : (Fin d → ℝ) → ℝ := fun y =>
    2 * ((starRingEnd ℂ) (w (toE y)) * (-Complex.I *
      (nonlin β γ (u₁ s (toE y)) - nonlin β γ (u₂ s (toE y))))).re with hQ₂
  have hsplit : (fun y : Fin d → ℝ => 2 * ((starRingEnd ℂ) (u₁ s (toE y) - u₂ s (toE y)) *
      (deriv (fun s' => u₁ s' (toE y)) s - deriv (fun s' => u₂ s' (toE y)) s)).re) =
      fun y => Q₁ y + Q₂ y := by
    funext y
    rw [hD (toE y), hQ₁, hQ₂]
    simp only [hw, mul_add, Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.neg_re,
      Complex.neg_im, Complex.I_re, Complex.I_im]
    ring
  have hwc : Continuous w := hw4.continuous
  have hcQ₁ : Continuous Q₁ :=
    continuous_const.mul (Complex.continuous_im.comp
      (((Complex.continuous_conj.comp hwc).mul hAA0).comp continuous_toE))
  have hcQ₂ : Continuous Q₂ := by
    have hN : Continuous fun x => nonlin β γ (u₁ s x) - nonlin β γ (u₂ s x) :=
      ((continuous_nonlin β γ).comp hs₁.continuous).sub ((continuous_nonlin β γ).comp hs₂.continuous)
    exact continuous_const.mul (Complex.continuous_re.comp
      (((Complex.continuous_conj.comp hwc).mul (continuous_const.mul hN)).comp continuous_toE))
  have hint₁ : IntegrableOn Q₁ (cube d) := hcQ₁.continuousOn.integrableOn_compact isCompact_cube
  have hint₂ : IntegrableOn Q₂ (cube d) := hcQ₂.continuousOn.integrableOn_compact isCompact_cube
  -- the dispersive part integrates to zero
  have hQ₁zero : ∫ y in cube d, Q₁ y = 0 := by
    have hcz : Continuous fun y : Fin d → ℝ => (starRingEnd ℂ) (w (toE y)) * shiftLap κ A (toE y) :=
      ((Complex.continuous_conj.comp hwc).mul hAA0).comp continuous_toE
    have hint : IntegrableOn (fun y : Fin d → ℝ =>
        (starRingEnd ℂ) (w (toE y)) * shiftLap κ A (toE y)) (cube d) :=
      hcz.continuousOn.integrableOn_compact isCompact_cube
    have him := integral_im hint
    simp only [RCLike.im_to_complex] at him
    rw [hQ₁]
    rw [integral_const_mul, him, shiftLap_symm κ (hw4.of_le (by norm_num)) hA2 hwp hAp]
    have : (fun y : Fin d → ℝ => (starRingEnd ℂ) (A (toE y)) * A (toE y)) =
        fun y => ((‖A (toE y)‖ ^ 2 : ℝ) : ℂ) := by
      funext y
      rw [Complex.conj_mul']
      push_cast
      ring
    rw [this, integral_complex_ofReal, Complex.ofReal_im, mul_zero]
  -- the nonlinear part is controlled by the local Lipschitz bound
  have hQ₂le : ∀ y ∈ cube d, |Q₂ y| ≤ 2 * C * ‖u₁ s (toE y) - u₂ s (toE y)‖ ^ 2 := by
    intro y hy
    have hL := norm_nonlin_sub_le β γ (hR₁ y hy) (hR₂ y hy)
    rw [hQ₂]
    simp only
    calc |2 * ((starRingEnd ℂ) (w (toE y)) * (-Complex.I *
          (nonlin β γ (u₁ s (toE y)) - nonlin β γ (u₂ s (toE y))))).re|
        ≤ 2 * ‖(starRingEnd ℂ) (w (toE y)) * (-Complex.I *
          (nonlin β γ (u₁ s (toE y)) - nonlin β γ (u₂ s (toE y))))‖ := by
          rw [abs_mul, abs_two]
          gcongr
          exact Complex.abs_re_le_norm _
      _ = 2 * (‖w (toE y)‖ * ‖nonlin β γ (u₁ s (toE y)) - nonlin β γ (u₂ s (toE y))‖) := by
          rw [norm_mul, norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_conj]
      _ ≤ 2 * (‖w (toE y)‖ * (C * ‖u₁ s (toE y) - u₂ s (toE y)‖)) := by
          gcongr
      _ = 2 * C * ‖u₁ s (toE y) - u₂ s (toE y)‖ ^ 2 := by
          rw [hw]
          ring
  rw [hsplit, integral_add hint₁ hint₂, hQ₁zero, zero_add]
  have hEint : IntegrableOn (fun y : Fin d → ℝ => 2 * C * ‖u₁ s (toE y) - u₂ s (toE y)‖ ^ 2)
      (cube d) :=
    ((continuous_const.mul ((((hs₁.continuous).comp continuous_toE).sub
      ((hs₂.continuous).comp continuous_toE)).norm.pow 2))).continuousOn.integrableOn_compact
      isCompact_cube
  calc |∫ y in cube d, Q₂ y| = ‖∫ y in cube d, Q₂ y‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ y in cube d, 2 * C * ‖u₁ s (toE y) - u₂ s (toE y)‖ ^ 2 := by
        refine norm_integral_le_of_norm_le hEint ?_
        filter_upwards [ae_restrict_mem measurableSet_cube] with y hy
        rw [Real.norm_eq_abs]
        exact hQ₂le y hy
    _ = 2 * C * diffEnergy u₁ u₂ s := by
        rw [diffEnergy, integral_const_mul]

/-- **Uniqueness of classical solutions** (`L²` energy method): two classical solutions on
`(−τ, τ) × 𝕋^d` with the same initial datum coincide on `(−τ, τ)`. -/
theorem IsClassicalSolution.unique {κ β γ τ : ℝ} {u₁ u₂ : ℝ → Rd → ℂ}
    (h₁ : IsClassicalSolution κ β γ τ u₁) (h₂ : IsClassicalSolution κ β γ τ u₂)
    (h0 : u₁ 0 = u₂ 0) : ∀ t ∈ Ioo (-τ) τ, u₁ t = u₂ t := by
  intro t ht
  have hta : |t| < τ := abs_lt.2 ⟨ht.1, ht.2⟩
  set T := (|t| + τ) / 2 with hT
  have hTτ : T < τ := by rw [hT]; linarith
  have htT : |t| < T := by rw [hT]; linarith
  have hsubT : Icc (-T) T ⊆ Ioo (-τ) τ := Icc_subset_Ioo (by linarith) hTτ
  have hmap : Continuous fun p : ℝ × (Fin d → ℝ) => (p.1, toE p.2) :=
    continuous_fst.prodMk (continuous_toE.comp continuous_snd)
  have hmaps : ∀ p ∈ Icc (-T) T ×ˢ cube d, (p.1, toE p.2) ∈ Ioo (-τ) τ ×ˢ univ :=
    fun p hp => ⟨hsubT hp.1, mem_univ _⟩
  obtain ⟨R₁, hR₁⟩ := (isCompact_Icc.prod isCompact_cube).exists_bound_of_continuousOn
    (h₁.cont.comp hmap.continuousOn hmaps)
  obtain ⟨R₂, hR₂⟩ := (isCompact_Icc.prod isCompact_cube).exists_bound_of_continuousOn
    (h₂.cont.comp hmap.continuousOn hmaps)
  have hzero : ∀ s ∈ Ioo (-T) T, diffEnergy u₁ u₂ s = 0 := by
    refine eq_zero_of_abs_deriv_le
      (C := 2 * (3 * |β| * max R₁ R₂ ^ 2 + 5 * |γ| * max R₁ R₂ ^ 4))
      (fun s hs => hasDerivAt_diffEnergy h₁ h₂ (hsubT (Ioo_subset_Icc_self hs)))
      (fun s hs => ?_) ?_ (fun s _ => setIntegral_nonneg measurableSet_cube fun y _ => by positivity)
    · have hs' := Ioo_subset_Icc_self hs
      exact abs_energy_deriv_le h₁ h₂ (hsubT hs')
        (fun y hy => (hR₁ (s, y) ⟨hs', hy⟩).trans (le_max_left _ _))
        (fun y hy => (hR₂ (s, y) ⟨hs', hy⟩).trans (le_max_right _ _))
    · simp [diffEnergy, h0]
  have hEt := hzero t ⟨by linarith [neg_abs_le t], lt_of_le_of_lt (le_abs_self t) htT⟩
  exact eq_of_integral_normSq_eq_zero (h₁.smooth t ht).continuous (h₂.smooth t ht).continuous
    (h₁.isPeriodic t) (h₂.isPeriodic t) hEt

/-! ### Lattice weights -/

/-- `|n|₁ = Σⱼ |nⱼ|`. -/
noncomputable def l1 (n : Fin d → ℤ) : ℝ := ∑ j, |(n j : ℝ)|

theorem l1_nonneg (n : Fin d → ℤ) : 0 ≤ l1 n :=
  Finset.sum_nonneg fun j _ => abs_nonneg ((n j : ℤ) : ℝ)

theorem l1_add_le (m n : Fin d → ℤ) : l1 (m + n) ≤ l1 m + l1 n := by
  unfold l1
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun j _ => by
    rw [Pi.add_apply, Int.cast_add]
    exact abs_add ((m j : ℤ) : ℝ) ((n j : ℤ) : ℝ)

theorem l1_neg (n : Fin d → ℤ) : l1 (-n) = l1 n := by
  unfold l1
  simp [abs_neg]

/-- The algebra weight `w(n) = (1 + |n|₁)⁸`. -/
noncomputable def wt (n : Fin d → ℤ) : ℝ := (1 + l1 n) ^ 8

theorem one_le_wt (n : Fin d → ℤ) : 1 ≤ wt n := one_le_pow₀ (by linarith [l1_nonneg n])

theorem wt_pos (n : Fin d → ℤ) : 0 < wt n := lt_of_lt_of_le one_pos (one_le_wt n)

theorem wt_add_le (m n : Fin d → ℤ) : wt (m + n) ≤ wt m * wt n := by
  unfold wt
  rw [← mul_pow]
  apply pow_le_pow_left₀ (by linarith [l1_nonneg (m + n)])
  nlinarith [l1_add_le m n, l1_nonneg m, l1_nonneg n]

theorem wt_neg (n : Fin d → ℤ) : wt (-n) = wt n := by simp [wt, l1_neg]

theorem nsq_le (n : Fin d → ℤ) : nsq n ≤ l1 n ^ 2 := by
  unfold nsq l1
  have h1 : ∑ j, ((n j : ℝ)) ^ 2 = ∑ j, |(n j : ℝ)| ^ 2 := by simp [sq_abs]
  rw [h1, sq, Finset.sum_mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [sq]
  exact Finset.single_le_sum (f := fun j => |(n i : ℝ)| * |(n j : ℝ)|)
    (fun j _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)) (Finset.mem_univ i)

theorem nsq_nonneg (n : Fin d → ℤ) : 0 ≤ nsq n := Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem norm_freq_sq (n : Fin d → ℤ) : ‖freq n‖ ^ 2 = nsq n := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  simp [nsq]

theorem norm_freq_le (n : Fin d → ℤ) : ‖freq n‖ ≤ l1 n := by
  have h := nsq_le n
  rw [← norm_freq_sq] at h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (l1_nonneg n) two_ne_zero).1 h

/-- The dispersion `ω(n) = (κ² − |n|²)²`. -/
noncomputable def omg (κ : ℝ) (n : Fin d → ℤ) : ℝ := (κ ^ 2 - nsq n) ^ 2

theorem omg_nonneg (κ : ℝ) (n : Fin d → ℤ) : 0 ≤ omg κ n := sq_nonneg _

theorem omg_le (κ : ℝ) (n : Fin d → ℤ) : omg κ n ≤ (1 + κ ^ 2) ^ 2 * wt n := by
  have h1 := nsq_le n
  have h0 := nsq_nonneg n
  have hl := l1_nonneg n
  have h2 : |κ ^ 2 - nsq n| ≤ (1 + κ ^ 2) * (1 + l1 n) ^ 2 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg κ]
  have h3 : omg κ n ≤ ((1 + κ ^ 2) * (1 + l1 n) ^ 2) ^ 2 := by
    unfold omg
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h2 2
  have h4 : (1 + l1 n) ^ 4 ≤ wt n := by
    unfold wt
    exact pow_le_pow_right₀ (by linarith) (by norm_num)
  calc omg κ n ≤ ((1 + κ ^ 2) * (1 + l1 n) ^ 2) ^ 2 := h3
    _ = (1 + κ ^ 2) ^ 2 * (1 + l1 n) ^ 4 := by ring
    _ ≤ (1 + κ ^ 2) ^ 2 * wt n := by gcongr

theorem pow_norm_freq_le (n : Fin d → ℤ) {k : ℕ} (hk : k ≤ 8) : ‖freq n‖ ^ k ≤ wt n := by
  have hl := l1_nonneg n
  calc ‖freq n‖ ^ k ≤ (1 + l1 n) ^ k :=
        pow_le_pow_left₀ (norm_nonneg _) (by linarith [norm_freq_le n]) k
    _ ≤ (1 + l1 n) ^ 8 := pow_le_pow_right₀ (by linarith) hk
    _ = wt n := rfl

/-! ### Weighted absolutely summable coefficient sequences -/

/-- `Σ w(n)|a(n)| < ∞`. -/
def WS (a : (Fin d → ℤ) → ℂ) : Prop := Summable fun n => wt n * ‖a n‖

/-- The weighted norm `‖a‖_w = Σ w(n)|a(n)|`. -/
noncomputable def wn (a : (Fin d → ℤ) → ℂ) : ℝ := ∑' n, wt n * ‖a n‖

theorem wn_nonneg (a : (Fin d → ℤ) → ℂ) : 0 ≤ wn a :=
  tsum_nonneg fun n => mul_nonneg (wt_pos n).le (norm_nonneg _)

theorem WS.summable_norm {a : (Fin d → ℤ) → ℂ} (ha : WS a) : Summable fun n => ‖a n‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun n => le_mul_of_one_le_left (norm_nonneg _) (one_le_wt n)) ha

theorem WS.summable {a : (Fin d → ℤ) → ℂ} (ha : WS a) : Summable a := ha.summable_norm.of_norm

theorem WS.of_norm_le {a c : (Fin d → ℤ) → ℂ} (hc : WS c) (h : ∀ n, ‖a n‖ ≤ ‖c n‖) : WS a :=
  Summable.of_nonneg_of_le (fun n => mul_nonneg (wt_pos n).le (norm_nonneg _))
    (fun n => mul_le_mul_of_nonneg_left (h n) (wt_pos n).le) hc

theorem wn_le_of_norm_le {a c : (Fin d → ℤ) → ℂ} (hc : WS c) (h : ∀ n, ‖a n‖ ≤ ‖c n‖) :
    wn a ≤ wn c :=
  (hc.of_norm_le h).tsum_le_tsum (fun n => mul_le_mul_of_nonneg_left (h n) (wt_pos n).le) hc

theorem WS.add {a c : (Fin d → ℤ) → ℂ} (ha : WS a) (hc : WS c) : WS (a + c) := by
  unfold WS
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (wt_pos n).le (norm_nonneg _))
    (fun n => ?_) (Summable.add ha hc)
  rw [Pi.add_apply, ← mul_add]
  exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (wt_pos n).le

theorem wn_add_le {a c : (Fin d → ℤ) → ℂ} (ha : WS a) (hc : WS c) : wn (a + c) ≤ wn a + wn c := by
  unfold wn
  rw [← Summable.tsum_add ha hc]
  refine Summable.tsum_le_tsum (fun n => ?_) (WS.add ha hc) (Summable.add ha hc)
  rw [Pi.add_apply, ← mul_add]
  exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (wt_pos n).le

theorem WS.smul {a : (Fin d → ℤ) → ℂ} (ha : WS a) (c : ℂ) : WS (c • a) := by
  unfold WS
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul]
  simpa [mul_left_comm] using ha.mul_left ‖c‖

theorem wn_smul (a : (Fin d → ℤ) → ℂ) (c : ℂ) : wn (c • a) = ‖c‖ * wn a := by
  unfold wn
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul]
  rw [← tsum_mul_left]
  congr 1
  funext n
  ring

theorem WS.neg {a : (Fin d → ℤ) → ℂ} (ha : WS a) : WS (-a) := by
  unfold WS
  simpa using ha

theorem wn_neg (a : (Fin d → ℤ) → ℂ) : wn (-a) = wn a := by
  unfold wn
  simp

theorem WS.sub {a c : (Fin d → ℤ) → ℂ} (ha : WS a) (hc : WS c) : WS (a - c) := by
  rw [sub_eq_add_neg]
  exact ha.add hc.neg

theorem wn_sub_le {a c : (Fin d → ℤ) → ℂ} (ha : WS a) (hc : WS c) : wn (a - c) ≤ wn a + wn c := by
  rw [sub_eq_add_neg, ← wn_neg c]
  exact wn_add_le ha hc.neg

theorem wn_sub_comm (a c : (Fin d → ℤ) → ℂ) : wn (a - c) = wn (c - a) := by
  rw [← wn_neg, neg_sub]

theorem norm_le_wn {a : (Fin d → ℤ) → ℂ} (ha : WS a) (n : Fin d → ℤ) : ‖a n‖ ≤ wn a :=
  calc ‖a n‖ ≤ wt n * ‖a n‖ := le_mul_of_one_le_left (norm_nonneg _) (one_le_wt n)
    _ ≤ wn a := ha.le_tsum n fun m _ => mul_nonneg (wt_pos m).le (norm_nonneg _)

theorem tsum_norm_le_wn {a : (Fin d → ℤ) → ℂ} (ha : WS a) : ∑' n, ‖a n‖ ≤ wn a :=
  ha.summable_norm.tsum_le_tsum (fun n => le_mul_of_one_le_left (norm_nonneg _) (one_le_wt n)) ha

theorem WS.zero : WS (0 : (Fin d → ℤ) → ℂ) := by
  unfold WS
  simpa using (summable_zero : Summable fun _ : Fin d → ℤ => (0 : ℝ))

/-! ### Convolution -/

/-- `(a ⋆ c)(k) = Σₙ a(n) c(k − n)`. -/
noncomputable def conv (a c : (Fin d → ℤ) → ℂ) (k : Fin d → ℤ) : ℂ := ∑' n, a n * c (k - n)

/-- The reindexing `(k, n) ↦ (n, k − n)`. -/
def convEquiv : (Fin d → ℤ) × (Fin d → ℤ) ≃ (Fin d → ℤ) × (Fin d → ℤ) where
  toFun q := (q.2, q.1 - q.2)
  invFun p := (p.1 + p.2, p.1)
  left_inv q := by simp
  right_inv p := by simp

theorem summable_convFamily {a c : (Fin d → ℤ) → ℂ} (ha : WS a) (hc : WS c) :
    Summable fun q : (Fin d → ℤ) × (Fin d → ℤ) =>
      (wt q.2 * ‖a q.2‖) * (wt (q.1 - q.2) * ‖c (q.1 - q.2)‖) := by
  have hP := Summable.mul_of_nonneg ha hc (fun n => mul_nonneg (wt_pos n).le (norm_nonneg _))
    (fun n => mul_nonneg (wt_pos n).le (norm_nonneg _))
  exact (convEquiv.summable_iff.2 hP :)

theorem summable_conv_norm {a c : (Fin d → ℤ) → ℂ} (ha : WS a) (hc : WS c) (k : Fin d → ℤ) :
    Summable fun n => ‖a n * c (k - n)‖ := by
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    ((summable_convFamily ha hc).prod_factor k)
  show ‖a n * c (k - n)‖ ≤ (wt n * ‖a n‖) * (wt (k - n) * ‖c (k - n)‖)
  rw [norm_mul, show (wt n * ‖a n‖) * (wt (k - n) * ‖c (k - n)‖) =
    (wt n * wt (k - n)) * (‖a n‖ * ‖c (k - n)‖) by ring]
  exact le_mul_of_one_le_left (by positivity)
    (one_le_mul_of_one_le_of_one_le (one_le_wt n) (one_le_wt (k - n)))

theorem WS_conv {a c : (Fin d → ℤ) → ℂ} (ha : WS a) (hc : WS c) : WS (conv a c) := by
  have hQ := summable_convFamily ha hc
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (wt_pos k).le (norm_nonneg _))
    (fun k => ?_) hQ.prod
  calc wt k * ‖conv a c k‖ ≤ wt k * ∑' n, ‖a n * c (k - n)‖ :=
        mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm (summable_conv_norm ha hc k))
          (wt_pos k).le
    _ = ∑' n, wt k * ‖a n * c (k - n)‖ := by rw [tsum_mul_left]
    _ ≤ ∑' n, (wt n * ‖a n‖) * (wt (k - n) * ‖c (k - n)‖) := by
        refine ((summable_conv_norm ha hc k).mul_left _).tsum_le_tsum (fun n => ?_)
          (hQ.prod_factor k)
        have hw : wt k ≤ wt n * wt (k - n) := by
          have := wt_add_le n (k - n)
          rwa [add_sub_cancel] at this
        rw [norm_mul]
        have := norm_nonneg (a n)
        have := norm_nonneg (c (k - n))
        calc wt k * (‖a n‖ * ‖c (k - n)‖) ≤ (wt n * wt (k - n)) * (‖a n‖ * ‖c (k - n)‖) :=
              mul_le_mul_of_nonneg_right hw (by positivity)
          _ = _ := by ring

theorem wn_conv_le {a c : (Fin d → ℤ) → ℂ} (ha : WS a) (hc : WS c) :
    wn (conv a c) ≤ wn a * wn c := by
  have hQ := summable_convFamily ha hc
  have hP := Summable.mul_of_nonneg ha hc (fun n => mul_nonneg (wt_pos n).le (norm_nonneg _))
    (fun n => mul_nonneg (wt_pos n).le (norm_nonneg _))
  have hpt : ∀ k, wt k * ‖conv a c k‖ ≤ ∑' n, (wt n * ‖a n‖) * (wt (k - n) * ‖c (k - n)‖) := by
    intro k
    calc wt k * ‖conv a c k‖ ≤ wt k * ∑' n, ‖a n * c (k - n)‖ :=
          mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm (summable_conv_norm ha hc k))
            (wt_pos k).le
      _ = ∑' n, wt k * ‖a n * c (k - n)‖ := by rw [tsum_mul_left]
      _ ≤ ∑' n, (wt n * ‖a n‖) * (wt (k - n) * ‖c (k - n)‖) := by
          refine ((summable_conv_norm ha hc k).mul_left _).tsum_le_tsum (fun n => ?_)
            (hQ.prod_factor k)
          have hw : wt k ≤ wt n * wt (k - n) := by
            have := wt_add_le n (k - n)
            rwa [add_sub_cancel] at this
          rw [norm_mul]
          have := norm_nonneg (a n)
          have := norm_nonneg (c (k - n))
          calc wt k * (‖a n‖ * ‖c (k - n)‖) ≤ (wt n * wt (k - n)) * (‖a n‖ * ‖c (k - n)‖) :=
                mul_le_mul_of_nonneg_right hw (by positivity)
            _ = _ := by ring
  calc wn (conv a c) ≤ ∑' k, ∑' n, (wt n * ‖a n‖) * (wt (k - n) * ‖c (k - n)‖) :=
        (WS_conv ha hc).tsum_le_tsum hpt hQ.prod
    _ = ∑' q : (Fin d → ℤ) × (Fin d → ℤ), (wt q.2 * ‖a q.2‖) * (wt (q.1 - q.2) * ‖c (q.1 - q.2)‖) :=
        (hQ.tsum_prod).symm
    _ = ∑' p : (Fin d → ℤ) × (Fin d → ℤ), (wt p.1 * ‖a p.1‖) * (wt p.2 * ‖c p.2‖) :=
        convEquiv.tsum_eq (fun p : (Fin d → ℤ) × (Fin d → ℤ) =>
          (wt p.1 * ‖a p.1‖) * (wt p.2 * ‖c p.2‖))
    _ = wn a * wn c := by
        unfold wn
        rw [ha.tsum_mul_tsum hc hP]

theorem conv_sub_left {a a' c : (Fin d → ℤ) → ℂ} (ha : WS a) (ha' : WS a') (hc : WS c) :
    conv a c - conv a' c = conv (a - a') c := by
  funext k
  simp only [Pi.sub_apply, conv, sub_mul]
  rw [((summable_conv_norm ha hc k).of_norm).tsum_sub ((summable_conv_norm ha' hc k).of_norm)]

theorem conv_sub_right {a c c' : (Fin d → ℤ) → ℂ} (ha : WS a) (hc : WS c) (hc' : WS c') :
    conv a c - conv a c' = conv a (c - c') := by
  funext k
  simp only [Pi.sub_apply, conv, mul_sub]
  rw [((summable_conv_norm ha hc k).of_norm).tsum_sub ((summable_conv_norm ha hc' k).of_norm)]

/-- `‖a ⋆ c − a' ⋆ c'‖_w ≤ ‖a − a'‖_w ‖c‖_w + ‖a'‖_w ‖c − c'‖_w`. -/
theorem wn_conv_sub_le {a a' c c' : (Fin d → ℤ) → ℂ} (ha : WS a) (ha' : WS a') (hc : WS c)
    (hc' : WS c') :
    wn (conv a c - conv a' c') ≤ wn (a - a') * wn c + wn a' * wn (c - c') := by
  have e : conv a c - conv a' c' = conv (a - a') c + conv a' (c - c') := by
    rw [← conv_sub_left ha ha' hc, ← conv_sub_right ha' hc hc']
    abel
  rw [e]
  calc wn (conv (a - a') c + conv a' (c - c')) ≤ wn (conv (a - a') c) + wn (conv a' (c - c')) :=
        wn_add_le (WS_conv (ha.sub ha') hc) (WS_conv ha' (hc.sub hc'))
    _ ≤ wn (a - a') * wn c + wn a' * wn (c - c') :=
        add_le_add (wn_conv_le (ha.sub ha') hc) (wn_conv_le ha' (hc.sub hc'))

/-- The reflection `ā(k) = \overline{a(−k)}` (coefficients of the complex conjugate). -/
noncomputable def refl (a : (Fin d → ℤ) → ℂ) (k : Fin d → ℤ) : ℂ := (starRingEnd ℂ) (a (-k))

theorem WS_refl {a : (Fin d → ℤ) → ℂ} (ha : WS a) : WS (refl a) := by
  unfold WS refl
  simp only [Complex.norm_conj]
  have := (Equiv.neg (Fin d → ℤ)).summable_iff.2 ha
  simpa [Function.comp_def, wt_neg] using this

theorem wn_refl (a : (Fin d → ℤ) → ℂ) : wn (refl a) = wn a := by
  unfold wn refl
  simp only [Complex.norm_conj]
  have := (Equiv.neg (Fin d → ℤ)).tsum_eq (fun n => wt n * ‖a n‖)
  simpa [wt_neg] using this

theorem refl_sub (a a' : (Fin d → ℤ) → ℂ) : refl a - refl a' = refl (a - a') := by
  funext k
  simp [refl]

/-! ### Absolutely convergent Fourier series -/

/-- `ser a x = Σₙ a(n) e^{in·x}`. -/
noncomputable def ser (a : (Fin d → ℤ) → ℂ) (x : Rd) : ℂ := ∑' n, a n * E n x

theorem summable_norm_ser {a : (Fin d → ℤ) → ℂ} (ha : WS a) (x : Rd) :
    Summable fun n => ‖a n * E n x‖ := by
  simpa [norm_mul, norm_E] using ha.summable_norm

theorem norm_ser_le {a : (Fin d → ℤ) → ℂ} (ha : WS a) (x : Rd) : ‖ser a x‖ ≤ wn a := by
  calc ‖ser a x‖ ≤ ∑' n, ‖a n * E n x‖ := norm_tsum_le_tsum_norm (summable_norm_ser ha x)
    _ = ∑' n, ‖a n‖ := by simp [norm_E]
    _ ≤ wn a := tsum_norm_le_wn ha

theorem ser_sub {a c : (Fin d → ℤ) → ℂ} (ha : WS a) (hc : WS c) (x : Rd) :
    ser a x - ser c x = ser (a - c) x := by
  unfold ser
  rw [← ((summable_norm_ser ha x).of_norm).tsum_sub ((summable_norm_ser hc x).of_norm)]
  simp [sub_mul]

theorem ser_add {a c : (Fin d → ℤ) → ℂ} (ha : WS a) (hc : WS c) (x : Rd) :
    ser a x + ser c x = ser (a + c) x := by
  unfold ser
  rw [← ((summable_norm_ser ha x).of_norm).tsum_add ((summable_norm_ser hc x).of_norm)]
  simp [add_mul]

theorem ser_smul (c : ℂ) (a : (Fin d → ℤ) → ℂ) (x : Rd) : ser (c • a) x = c * ser a x := by
  unfold ser
  rw [← tsum_mul_left]
  simp [mul_assoc]

/-- **Product of absolutely convergent Fourier series:** `(Σ aₙeₙ)(Σ cₘeₘ) = Σ (a⋆c)ₖ eₖ`. -/
theorem ser_mul {a c : (Fin d → ℤ) → ℂ} (ha : WS a) (hc : WS c) (x : Rd) :
    ser a x * ser c x = ser (conv a c) x := by
  unfold ser
  rw [tsum_mul_tsum_of_summable_norm (summable_norm_ser ha x) (summable_norm_ser hc x)]
  have hpt : ∀ p : (Fin d → ℤ) × (Fin d → ℤ), (a p.1 * E p.1 x) * (c p.2 * E p.2 x) =
      a p.1 * c p.2 * E (p.1 + p.2) x := fun p => by rw [E_add]; ring
  simp_rw [hpt]
  rw [← convEquiv.tsum_eq (fun p : (Fin d → ℤ) × (Fin d → ℤ) => a p.1 * c p.2 * E (p.1 + p.2) x)]
  have hG : Summable fun q : (Fin d → ℤ) × (Fin d → ℤ) =>
      a (convEquiv q).1 * c (convEquiv q).2 * E ((convEquiv q).1 + (convEquiv q).2) x := by
    refine Summable.of_norm_bounded (summable_convFamily ha hc) fun q => ?_
    simp only [convEquiv, Equiv.coe_fn_mk, norm_mul, norm_E, mul_one]
    rw [show (wt q.2 * ‖a q.2‖) * (wt (q.1 - q.2) * ‖c (q.1 - q.2)‖) =
      (wt q.2 * wt (q.1 - q.2)) * (‖a q.2‖ * ‖c (q.1 - q.2)‖) by ring]
    exact le_mul_of_one_le_left (by positivity)
      (one_le_mul_of_one_le_of_one_le (one_le_wt _) (one_le_wt _))
  rw [hG.tsum_prod]
  refine tsum_congr fun k => ?_
  simp only [convEquiv, Equiv.coe_fn_mk, add_sub_cancel]
  rw [conv, ← tsum_mul_right]

/-- The conjugate series: `\overline{Σ aₙeₙ} = Σ \overline{a_{−k}} eₖ`. -/
theorem ser_refl (a : (Fin d → ℤ) → ℂ) (x : Rd) :
    (starRingEnd ℂ) (ser a x) = ser (refl a) x := by
  unfold ser refl
  rw [Complex.conj_tsum]
  simp_rw [map_mul, ← E_neg]
  rw [← (Equiv.neg (Fin d → ℤ)).tsum_eq (fun k => (starRingEnd ℂ) (a (-k)) * E k x)]
  simp

/-! ### The cubic–quintic nonlinearity in Fourier space -/

/-- Coefficients of `|u|²u = u·u·ū`. -/
noncomputable def cub (a : (Fin d → ℤ) → ℂ) : (Fin d → ℤ) → ℂ := conv (conv a a) (refl a)

/-- Coefficients of `|u|⁴u = u³ū²`. -/
noncomputable def qui (a : (Fin d → ℤ) → ℂ) : (Fin d → ℤ) → ℂ :=
  conv (conv (conv (conv a a) a) (refl a)) (refl a)

/-- Coefficients of `N(u) = −β|u|²u + γ|u|⁴u`. -/
noncomputable def Nc (β γ : ℝ) (a : (Fin d → ℤ) → ℂ) : (Fin d → ℤ) → ℂ :=
  (-(β : ℂ)) • cub a + (γ : ℂ) • qui a

theorem WS_cub {a : (Fin d → ℤ) → ℂ} (ha : WS a) : WS (cub a) :=
  WS_conv (WS_conv ha ha) (WS_refl ha)

theorem WS_qui {a : (Fin d → ℤ) → ℂ} (ha : WS a) : WS (qui a) :=
  WS_conv (WS_conv (WS_conv (WS_conv ha ha) ha) (WS_refl ha)) (WS_refl ha)

theorem WS_Nc (β γ : ℝ) {a : (Fin d → ℤ) → ℂ} (ha : WS a) : WS (Nc β γ a) :=
  ((WS_cub ha).smul _).add ((WS_qui ha).smul _)

/-- The nonlinearity of an absolutely convergent series is the series of `Nc`. -/
theorem ser_Nc (β γ : ℝ) {a : (Fin d → ℤ) → ℂ} (ha : WS a) (x : Rd) :
    ser (Nc β γ a) x = nonlin β γ (ser a x) := by
  have h2 := WS_conv ha ha
  have h3 := WS_conv h2 ha
  have h4 := WS_conv h3 (WS_refl ha)
  have hr := WS_refl ha
  rw [Nc, ← ser_add ((WS_cub ha).smul _) ((WS_qui ha).smul _), ser_smul, ser_smul, cub, qui,
    ← ser_mul h2 hr, ← ser_mul h4 hr, ← ser_mul h3 hr, ← ser_mul h2 ha, ← ser_mul ha ha,
    ← ser_refl]
  set z := ser a x
  have hz : z * (starRingEnd ℂ) z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj']
    push_cast
    ring
  unfold nonlin
  have h4' : ((‖z‖ ^ 4 : ℝ) : ℂ) = ((‖z‖ ^ 2 : ℝ) : ℂ) ^ 2 := by push_cast; ring
  rw [h4', ← hz]
  ring

theorem wn_cub_le {a : (Fin d → ℤ) → ℂ} (ha : WS a) : wn (cub a) ≤ wn a ^ 3 := by
  have h0 := wn_nonneg a
  calc wn (cub a) ≤ wn (conv a a) * wn (refl a) := wn_conv_le (WS_conv ha ha) (WS_refl ha)
    _ ≤ (wn a * wn a) * wn a := by
        rw [wn_refl]
        exact mul_le_mul_of_nonneg_right (wn_conv_le ha ha) h0
    _ = wn a ^ 3 := by ring

theorem wn_qui_le {a : (Fin d → ℤ) → ℂ} (ha : WS a) : wn (qui a) ≤ wn a ^ 5 := by
  have h0 := wn_nonneg a
  have h2 := wn_conv_le ha ha
  have h3 := wn_conv_le (WS_conv ha ha) ha
  have h4 := wn_conv_le (WS_conv (WS_conv ha ha) ha) (WS_refl ha)
  have h5 := wn_conv_le (WS_conv (WS_conv (WS_conv ha ha) ha) (WS_refl ha)) (WS_refl ha)
  rw [wn_refl] at h4 h5
  have e3 : wn (conv (conv a a) a) ≤ wn a ^ 3 := by
    calc _ ≤ wn (conv a a) * wn a := h3
      _ ≤ (wn a * wn a) * wn a := mul_le_mul_of_nonneg_right h2 h0
      _ = wn a ^ 3 := by ring
  have e4 : wn (conv (conv (conv a a) a) (refl a)) ≤ wn a ^ 4 := by
    calc _ ≤ wn (conv (conv a a) a) * wn a := h4
      _ ≤ wn a ^ 3 * wn a := mul_le_mul_of_nonneg_right e3 h0
      _ = wn a ^ 4 := by ring
  calc wn (qui a) ≤ wn (conv (conv (conv a a) a) (refl a)) * wn a := h5
    _ ≤ wn a ^ 4 * wn a := mul_le_mul_of_nonneg_right e4 h0
    _ = wn a ^ 5 := by ring

theorem wn_Nc_le (β γ : ℝ) {a : (Fin d → ℤ) → ℂ} (ha : WS a) :
    wn (Nc β γ a) ≤ |β| * wn a ^ 3 + |γ| * wn a ^ 5 := by
  calc wn (Nc β γ a) ≤ wn ((-(β : ℂ)) • cub a) + wn ((γ : ℂ) • qui a) :=
        wn_add_le ((WS_cub ha).smul _) ((WS_qui ha).smul _)
    _ = |β| * wn (cub a) + |γ| * wn (qui a) := by
        rw [wn_smul, wn_smul, norm_neg, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs]
    _ ≤ |β| * wn a ^ 3 + |γ| * wn a ^ 5 := by
        gcongr
        · exact wn_cub_le ha
        · exact wn_qui_le ha

/-- **Local Lipschitz bound in the weighted algebra.** -/
theorem wn_Nc_sub_le (β γ : ℝ) {a a' : (Fin d → ℤ) → ℂ} (ha : WS a) (ha' : WS a') {R : ℝ}
    (hR : wn a ≤ R) (hR' : wn a' ≤ R) :
    wn (Nc β γ a - Nc β γ a') ≤ (3 * |β| * R ^ 2 + 5 * |γ| * R ^ 4) * wn (a - a') := by
  have h0 := wn_nonneg a
  have h0' := wn_nonneg a'
  have hR0 : 0 ≤ R := h0.trans hR
  set δ := wn (a - a') with hδ
  have hδ0 : 0 ≤ δ := wn_nonneg _
  have hrr : wn (refl a - refl a') = δ := by rw [refl_sub, wn_refl]
  -- degree-two
  have p2 : wn (conv a a - conv a' a') ≤ 2 * R * δ := by
    have := wn_conv_sub_le ha ha' ha ha'
    nlinarith [mul_le_mul_of_nonneg_left hR hδ0, mul_le_mul_of_nonneg_left hR' hδ0]
  have q2 : wn (conv a' a') ≤ R ^ 2 := by
    calc _ ≤ wn a' * wn a' := wn_conv_le ha' ha'
      _ ≤ R * R := mul_le_mul hR' hR' h0' hR0
      _ = R ^ 2 := by ring
  have q2a : wn (conv a a) ≤ R ^ 2 := by
    calc _ ≤ wn a * wn a := wn_conv_le ha ha
      _ ≤ R * R := mul_le_mul hR hR h0 hR0
      _ = R ^ 2 := by ring
  -- cubic
  have hcub : wn (cub a - cub a') ≤ 3 * R ^ 2 * δ := by
    have := wn_conv_sub_le (WS_conv ha ha) (WS_conv ha' ha') (WS_refl ha) (WS_refl ha')
    rw [wn_refl, hrr] at this
    calc wn (cub a - cub a') ≤ wn (conv a a - conv a' a') * wn a + wn (conv a' a') * δ := this
      _ ≤ (2 * R * δ) * R + R ^ 2 * δ := by
          gcongr
      _ = 3 * R ^ 2 * δ := by ring
  -- quintic
  have p3 : wn (conv (conv a a) a - conv (conv a' a') a') ≤ 3 * R ^ 2 * δ := by
    have := wn_conv_sub_le (WS_conv ha ha) (WS_conv ha' ha') ha ha'
    calc _ ≤ wn (conv a a - conv a' a') * wn a + wn (conv a' a') * δ := this
      _ ≤ (2 * R * δ) * R + R ^ 2 * δ := by
          gcongr
      _ = 3 * R ^ 2 * δ := by ring
  have q3 : wn (conv (conv a' a') a') ≤ R ^ 3 := by
    calc _ ≤ wn (conv a' a') * wn a' := wn_conv_le (WS_conv ha' ha') ha'
      _ ≤ R ^ 2 * R := mul_le_mul q2 hR' h0' (by positivity)
      _ = R ^ 3 := by ring
  have p4 : wn (conv (conv (conv a a) a) (refl a) - conv (conv (conv a' a') a') (refl a')) ≤
      4 * R ^ 3 * δ := by
    have := wn_conv_sub_le (WS_conv (WS_conv ha ha) ha) (WS_conv (WS_conv ha' ha') ha')
      (WS_refl ha) (WS_refl ha')
    rw [wn_refl, hrr] at this
    calc _ ≤ wn (conv (conv a a) a - conv (conv a' a') a') * wn a +
          wn (conv (conv a' a') a') * δ := this
      _ ≤ (3 * R ^ 2 * δ) * R + R ^ 3 * δ := by
          gcongr
      _ = 4 * R ^ 3 * δ := by ring
  have q4 : wn (conv (conv (conv a' a') a') (refl a')) ≤ R ^ 4 := by
    calc _ ≤ wn (conv (conv a' a') a') * wn (refl a') :=
          wn_conv_le (WS_conv (WS_conv ha' ha') ha') (WS_refl ha')
      _ ≤ R ^ 3 * R := by rw [wn_refl]; exact mul_le_mul q3 hR' h0' (by positivity)
      _ = R ^ 4 := by ring
  have hqui : wn (qui a - qui a') ≤ 5 * R ^ 4 * δ := by
    have := wn_conv_sub_le (WS_conv (WS_conv (WS_conv ha ha) ha) (WS_refl ha))
      (WS_conv (WS_conv (WS_conv ha' ha') ha') (WS_refl ha')) (WS_refl ha) (WS_refl ha')
    rw [wn_refl, hrr] at this
    calc wn (qui a - qui a') ≤ wn (conv (conv (conv a a) a) (refl a) -
          conv (conv (conv a' a') a') (refl a')) * wn a +
          wn (conv (conv (conv a' a') a') (refl a')) * δ := this
      _ ≤ (4 * R ^ 3 * δ) * R + R ^ 4 * δ := by
          gcongr
      _ = 5 * R ^ 4 * δ := by ring
  have e : Nc β γ a - Nc β γ a' = (-(β : ℂ)) • (cub a - cub a') + (γ : ℂ) • (qui a - qui a') := by
    unfold Nc
    rw [smul_sub, smul_sub]
    abel
  rw [e]
  calc wn ((-(β : ℂ)) • (cub a - cub a') + (γ : ℂ) • (qui a - qui a')) ≤
      wn ((-(β : ℂ)) • (cub a - cub a')) + wn ((γ : ℂ) • (qui a - qui a')) :=
        wn_add_le (((WS_cub ha).sub (WS_cub ha')).smul _) (((WS_qui ha).sub (WS_qui ha')).smul _)
    _ = |β| * wn (cub a - cub a') + |γ| * wn (qui a - qui a') := by
        rw [wn_smul, wn_smul, norm_neg, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs]
    _ ≤ |β| * (3 * R ^ 2 * δ) + |γ| * (5 * R ^ 4 * δ) := by gcongr
    _ = (3 * |β| * R ^ 2 + 5 * |γ| * R ^ 4) * δ := by ring

/-! ### Derivatives of the modes -/

/-- `e^{in·x} = exp(L x)`, `L v = i⟨n, v⟩`. -/
noncomputable def Lmode (n : Fin d → ℤ) : Rd →L[ℝ] ℂ := (innerSL ℝ (freq n)).smulRight Complex.I

theorem Lmode_apply (n : Fin d → ℤ) (v : Rd) :
    Lmode n v = ((inner ℝ (freq n) v : ℝ) : ℂ) * Complex.I := by
  simp [Lmode, Complex.real_smul]

theorem E_eq_comp (n : Fin d → ℤ) : E n = Complex.exp ∘ Lmode n := by
  funext x
  simp [E, Lmode_apply]

theorem norm_Lmode_le (n : Fin d → ℤ) : ‖Lmode n‖ ≤ ‖freq n‖ := by
  rw [Lmode, ContinuousLinearMap.norm_smulRight_apply, Complex.norm_I, mul_one,
    innerSL_apply_norm]

theorem norm_iteratedFDeriv_cexp (k : ℕ) (z : ℂ) :
    ‖iteratedFDeriv ℝ k Complex.exp z‖ = ‖Complex.exp z‖ := by
  have h := (Complex.contDiff_exp (𝕜 := ℂ) (n := k)).contDiffAt (x := z)
  rw [← h.restrictScalars_iteratedFDeriv (𝕜 := ℝ), Function.comp_apply,
    ContinuousMultilinearMap.norm_restrictScalars, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  have : iteratedDeriv k Complex.exp = Complex.exp := by
    have := iteratedDeriv_cexp_const_mul k 1
    simp only [one_mul, one_pow] at this
    exact this
  rw [this]

theorem norm_iteratedFDeriv_E_le (n : Fin d → ℤ) (k : ℕ) (x : Rd) :
    ‖iteratedFDeriv ℝ k (E n) x‖ ≤ ‖freq n‖ ^ k := by
  rw [E_eq_comp, ContinuousLinearMap.iteratedFDeriv_comp_right (Lmode n)
    (Complex.contDiff_exp (𝕜 := ℝ) (n := k)) x le_rfl]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [norm_iteratedFDeriv_cexp, Lmode_apply, Complex.norm_exp_ofReal_mul_I, one_mul,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_Lmode_le n) k

theorem contDiff_E' (n : Fin d → ℤ) : ContDiff ℝ ⊤ (E n) := by
  rw [E_eq_comp]
  exact Complex.contDiff_exp.comp (Lmode n).contDiff

/-! ### Polynomially weighted summability and smoothness of series -/

/-- `Σ (1 + |n|₁)^m |a(n)| < ∞`. -/
def SumW (m : ℕ) (a : (Fin d → ℤ) → ℂ) : Prop := Summable fun n => (1 + l1 n) ^ m * ‖a n‖

theorem one_le_one_add_l1_pow (n : Fin d → ℤ) (m : ℕ) : 1 ≤ (1 + l1 n) ^ m :=
  one_le_pow₀ (by linarith [l1_nonneg n])

theorem SumW.mono {m m' : ℕ} {a : (Fin d → ℤ) → ℂ} (ha : SumW m a) (h : m' ≤ m) : SumW m' a :=
  Summable.of_nonneg_of_le
    (fun n => mul_nonneg (pow_nonneg (by linarith [l1_nonneg n]) _) (norm_nonneg _))
    (fun n => mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by linarith [l1_nonneg n]) h) (norm_nonneg _)) ha

theorem SumW.summable_norm {m : ℕ} {a : (Fin d → ℤ) → ℂ} (ha : SumW m a) :
    Summable fun n => ‖a n‖ := by
  have := ha.mono (Nat.zero_le m)
  simpa [SumW] using this

theorem WS.sumW {a : (Fin d → ℤ) → ℂ} (ha : WS a) {m : ℕ} (hm : m ≤ 8) : SumW m a :=
  SumW.mono (m := 8) (by simpa [SumW, WS, wt] using ha) hm

theorem SumW.of_norm_le {m : ℕ} {a c : (Fin d → ℤ) → ℂ} (hc : SumW m c)
    (h : ∀ n, ‖a n‖ ≤ (1 + l1 n) ^ 2 * ‖c n‖) (hm : 2 ≤ m) : SumW (m - 2) a := by
  refine Summable.of_nonneg_of_le
    (fun n => mul_nonneg (pow_nonneg (by linarith [l1_nonneg n]) _) (norm_nonneg _))
    (fun n => ?_) hc
  have hl := l1_nonneg n
  calc (1 + l1 n) ^ (m - 2) * ‖a n‖ ≤ (1 + l1 n) ^ (m - 2) * ((1 + l1 n) ^ 2 * ‖c n‖) :=
        mul_le_mul_of_nonneg_left (h n) (pow_nonneg (by linarith) _)
    _ = (1 + l1 n) ^ m * ‖c n‖ := by
        rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hm]

theorem summable_norm_ser' {a : (Fin d → ℤ) → ℂ} (ha : Summable fun n => ‖a n‖) (x : Rd) :
    Summable fun n => ‖a n * E n x‖ := by
  simpa [norm_E] using ha

theorem norm_ser_le' {a : (Fin d → ℤ) → ℂ} (ha : Summable fun n => ‖a n‖) (x : Rd) :
    ‖ser a x‖ ≤ ∑' n, ‖a n‖ := by
  calc ‖ser a x‖ ≤ ∑' n, ‖a n * E n x‖ := norm_tsum_le_tsum_norm (summable_norm_ser' ha x)
    _ = ∑' n, ‖a n‖ := by simp [norm_E]

theorem ser_sub' {a c : (Fin d → ℤ) → ℂ} (ha : Summable fun n => ‖a n‖)
    (hc : Summable fun n => ‖c n‖) (x : Rd) : ser a x - ser c x = ser (a - c) x := by
  unfold ser
  rw [← ((summable_norm_ser' ha x).of_norm).tsum_sub ((summable_norm_ser' hc x).of_norm)]
  simp [sub_mul]

theorem ser_add' {a c : (Fin d → ℤ) → ℂ} (ha : Summable fun n => ‖a n‖)
    (hc : Summable fun n => ‖c n‖) (x : Rd) : ser a x + ser c x = ser (a + c) x := by
  unfold ser
  rw [← ((summable_norm_ser' ha x).of_norm).tsum_add ((summable_norm_ser' hc x).of_norm)]
  simp [add_mul]

theorem continuous_ser {a : (Fin d → ℤ) → ℂ} (ha : Summable fun n => ‖a n‖) :
    Continuous (ser a) :=
  continuous_tsum (fun n => continuous_const.mul (continuous_E n)) ha
    (fun n x => by rw [norm_mul, norm_E, mul_one])

theorem isPeriodic_ser (a : (Fin d → ℤ) → ℂ) : IsPeriodic (ser a) := fun x j => by
  unfold ser
  simp_rw [E_periodic]

/-- **Smoothness:** `Σ (1+|n|₁)^m |aₙ| < ∞` makes `Σ aₙ e^{in·x}` a `C^m` function. -/
theorem contDiff_ser {m : ℕ} {a : (Fin d → ℤ) → ℂ} (ha : SumW m a) : ContDiff ℝ m (ser a) := by
  have hf : ∀ n, ContDiff ℝ (m : ℕ∞) fun x => a n * E n x := fun n =>
    contDiff_const.mul ((contDiff_E' n).of_le le_top)
  refine contDiff_tsum (v := fun k n => ‖a n‖ * ‖freq n‖ ^ k) hf (fun k hk => ?_)
    (fun k n x hk => ?_)
  · have hk' : k ≤ m := by exact_mod_cast hk
    refine Summable.of_nonneg_of_le (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) _))
      (fun n => ?_) ha
    have hl := l1_nonneg n
    calc ‖a n‖ * ‖freq n‖ ^ k ≤ ‖a n‖ * (1 + l1 n) ^ m := by
          gcongr
          calc ‖freq n‖ ^ k ≤ (1 + l1 n) ^ k :=
                pow_le_pow_left₀ (norm_nonneg _) (by linarith [norm_freq_le n]) k
            _ ≤ (1 + l1 n) ^ m := pow_le_pow_right₀ (by linarith) hk'
      _ = (1 + l1 n) ^ m * ‖a n‖ := by ring
  · have h1 : iteratedFDeriv ℝ k (fun x => a n * E n x) x =
        a n • iteratedFDeriv ℝ k (E n) x := by
      have := iteratedFDeriv_const_smul_apply (𝕜 := ℝ) (i := k) (a := a n) (f := E n) (x := x)
        ((contDiff_E' n).of_le le_top).contDiffAt
      simpa [smul_eq_mul] using this
    rw [h1, norm_smul]
    exact mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_E_le n k x) (norm_nonneg _)

/-! ### Termwise differentiation -/

theorem hasDerivAt_E_line (n : Fin d → ℤ) (x : Rd) (j : Fin d) (τ : ℝ) :
    HasDerivAt (fun σ : ℝ => E n (x + σ • EuclideanSpace.single j 1))
      (Complex.I * ((n j : ℝ) : ℂ) * E n (x + τ • EuclideanSpace.single j 1)) τ := by
  have hl : HasDerivAt (fun σ : ℝ => x + σ • EuclideanSpace.single j (1 : ℝ))
      (EuclideanSpace.single j 1) τ := by
    simpa using ((hasDerivAt_id τ).smul_const (EuclideanSpace.single j (1 : ℝ))).const_add x
  have := (hasFDerivAt_E n (x + τ • EuclideanSpace.single j 1)).comp_hasDerivAt τ hl
  convert this using 1
  simp [EuclideanSpace.inner_single_right]
  ring

/-- `∂ⱼ Σ aₙ e^{in·x} = Σ i nⱼ aₙ e^{in·x}`. -/
theorem pd_ser (j : Fin d) {a : (Fin d → ℤ) → ℂ} (ha : SumW 1 a) :
    pd j (ser a) = ser (fun n => Complex.I * ((n j : ℝ) : ℂ) * a n) := by
  funext x
  have hdiff : DifferentiableAt ℝ (ser a) x :=
    ((contDiff_ser ha).differentiable (by norm_num)) x
  have hl : HasDerivAt (fun σ : ℝ => x + σ • EuclideanSpace.single j (1 : ℝ))
      (EuclideanSpace.single j 1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (EuclideanSpace.single j (1 : ℝ))).const_add x
  have h1 : HasDerivAt (fun σ : ℝ => ser a (x + σ • EuclideanSpace.single j 1))
      (pd j (ser a) x) 0 := by
    have := hdiff.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
    simpa [pd] using this
  have hb : ∀ n, ‖a n‖ * |(n j : ℝ)| ≤ (1 + l1 n) ^ 1 * ‖a n‖ := by
    intro n
    have : |(n j : ℝ)| ≤ l1 n :=
      Finset.single_le_sum (f := fun i => |(n i : ℝ)|) (fun i _ => abs_nonneg _) (Finset.mem_univ j)
    nlinarith [norm_nonneg (a n), l1_nonneg n]
  have h2 : HasDerivAt (fun σ : ℝ => ser a (x + σ • EuclideanSpace.single j 1))
      (∑' n, a n * (Complex.I * ((n j : ℝ) : ℂ) * E n (x + (0 : ℝ) • EuclideanSpace.single j 1))) 0 := by
    refine hasDerivAt_tsum (u := fun n => ‖a n‖ * |(n j : ℝ)|)
      (g := fun n σ => a n * E n (x + σ • EuclideanSpace.single j 1))
      (g' := fun n σ => a n * (Complex.I * ((n j : ℝ) : ℂ) * E n (x + σ • EuclideanSpace.single j 1)))
      ?_ (fun n τ => (hasDerivAt_E_line n x j τ).const_mul (a n)) (fun n τ => ?_)
      (y₀ := 0) ((summable_norm_ser' ha.summable_norm _).of_norm) 0
    · exact Summable.of_nonneg_of_le (fun n => mul_nonneg (norm_nonneg _) (abs_nonneg _)) hb ha
    · rw [norm_mul, norm_mul, norm_mul, norm_E, Complex.norm_I, Complex.norm_real,
        Real.norm_eq_abs]
      ring_nf
      exact le_refl _
  rw [h1.unique h2]
  unfold ser
  refine tsum_congr fun n => ?_
  simp only [zero_smul, add_zero]
  ring

theorem sumW_pd {m : ℕ} (j : Fin d) {a : (Fin d → ℤ) → ℂ} (ha : SumW (m + 1) a) :
    SumW m (fun n => Complex.I * ((n j : ℝ) : ℂ) * a n) := by
  refine Summable.of_nonneg_of_le
    (fun n => mul_nonneg (pow_nonneg (by linarith [l1_nonneg n]) _) (norm_nonneg _))
    (fun n => ?_) ha
  have hj : |(n j : ℝ)| ≤ l1 n :=
    Finset.single_le_sum (f := fun i => |(n i : ℝ)|) (fun i _ => abs_nonneg _) (Finset.mem_univ j)
  have hl := l1_nonneg n
  rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, pow_succ]
  have : |(n j : ℝ)| ≤ 1 + l1 n := by linarith
  calc (1 + l1 n) ^ m * (|(n j : ℝ)| * ‖a n‖) ≤ (1 + l1 n) ^ m * ((1 + l1 n) * ‖a n‖) := by
        gcongr
    _ = (1 + l1 n) ^ m * (1 + l1 n) * ‖a n‖ := by ring

/-- `Δ Σ aₙ e^{in·x} = Σ (−|n|²) aₙ e^{in·x}`. -/
theorem laplacian_ser {a : (Fin d → ℤ) → ℂ} (ha : SumW 2 a) :
    Δ (ser a) = ser (fun n => -((nsq n : ℝ) : ℂ) * a n) := by
  funext x
  rw [laplacian_eq_sum_pd (contDiff_ser ha)]
  have h1 : ∀ j, pd j (pd j (ser a)) x =
      ser (fun n => Complex.I * ((n j : ℝ) : ℂ) * (Complex.I * ((n j : ℝ) : ℂ) * a n)) x := by
    intro j
    rw [pd_ser j (ha.mono (by norm_num)), pd_ser j (sumW_pd (m := 1) j ha)]
  simp_rw [h1]
  unfold ser
  rw [← Summable.tsum_finsetSum ?_]
  · refine tsum_congr fun n => ?_
    rw [← Finset.sum_mul]
    congr 1
    have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
    calc ∑ j, Complex.I * ((n j : ℝ) : ℂ) * (Complex.I * ((n j : ℝ) : ℂ) * a n) =
        ∑ j, (Complex.I * Complex.I) * (((n j : ℝ) ^ 2 : ℝ) : ℂ) * a n := by
          refine Finset.sum_congr rfl fun j _ => ?_
          push_cast
          ring
      _ = -((nsq n : ℝ) : ℂ) * a n := by
          rw [hI, ← Finset.sum_mul]
          congr 1
          rw [nsq]
          push_cast
          simp [Finset.sum_neg_distrib]
  · intro j _
    exact (summable_norm_ser' ((sumW_pd (m := 0) j (sumW_pd (m := 1) j ha)).summable_norm) x).of_norm

theorem shiftLap_ser (κ : ℝ) {a : (Fin d → ℤ) → ℂ} (ha : SumW 2 a) :
    shiftLap κ (ser a) = ser (fun n => ((κ ^ 2 - nsq n : ℝ) : ℂ) * a n) := by
  funext x
  have hs1 : Summable fun n => ‖-((nsq n : ℝ) : ℂ) * a n‖ := by
    have hb : ∀ n, ‖-((nsq n : ℝ) : ℂ) * a n‖ ≤ (1 + l1 n) ^ 2 * ‖a n‖ := fun n => by
      rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (nsq_nonneg n)]
      have h1 := nsq_le n
      have hl := l1_nonneg n
      have h2 : nsq n ≤ (1 + l1 n) ^ 2 := by nlinarith
      exact mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
    exact Summable.of_nonneg_of_le (fun n => norm_nonneg _) hb ha
  have hs2 : Summable fun n => ‖(((κ ^ 2 : ℝ) : ℂ) • a) n‖ := by
    refine (ha.summable_norm.mul_left ‖((κ ^ 2 : ℝ) : ℂ)‖).congr fun n => ?_
    rw [Pi.smul_apply, smul_eq_mul, norm_mul]
  have e1 : ((κ ^ 2 : ℝ) : ℂ) * ser a x = ser (((κ ^ 2 : ℝ) : ℂ) • a) x := (ser_smul _ a x).symm
  rw [shiftLap, laplacian_ser ha, e1, ser_add' hs1 hs2]
  congr 1
  funext n
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

/-! ### The free propagator `e^{−itL}` in Fourier space -/

/-- `(e^{−itL}a)(n) = e^{−itω(n)} a(n)`, `ω(n) = (κ² − |n|²)²`. -/
noncomputable def ph (κ t : ℝ) (a : (Fin d → ℤ) → ℂ) (n : Fin d → ℤ) : ℂ :=
  Complex.exp (-((omg κ n * t : ℝ) : ℂ) * Complex.I) * a n

theorem norm_cexp_neg_real_mul_I (r : ℝ) : ‖Complex.exp (-(r : ℂ) * Complex.I)‖ = 1 := by
  rw [show -(r : ℂ) * Complex.I = ((-r : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

theorem norm_ph (κ t : ℝ) (a : (Fin d → ℤ) → ℂ) (n : Fin d → ℤ) : ‖ph κ t a n‖ = ‖a n‖ := by
  rw [ph, norm_mul, norm_cexp_neg_real_mul_I, one_mul]

theorem WS_ph {a : (Fin d → ℤ) → ℂ} (ha : WS a) (κ t : ℝ) : WS (ph κ t a) :=
  ha.of_norm_le fun n => (norm_ph κ t a n).le

theorem wn_ph (κ t : ℝ) (a : (Fin d → ℤ) → ℂ) : wn (ph κ t a) = wn a := by
  unfold wn
  simp_rw [norm_ph]

theorem ph_sub (κ t : ℝ) (a c : (Fin d → ℤ) → ℂ) : ph κ t a - ph κ t c = ph κ t (a - c) := by
  funext n
  simp [ph, mul_sub]

theorem ph_ph (κ s t : ℝ) (a : (Fin d → ℤ) → ℂ) : ph κ s (ph κ t a) = ph κ (s + t) a := by
  funext n
  simp only [ph, ← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem ph_zero (κ : ℝ) (a : (Fin d → ℤ) → ℂ) : ph κ 0 a = a := by
  funext n
  simp [ph]

theorem ph_smul (κ t : ℝ) (c : ℂ) (a : (Fin d → ℤ) → ℂ) : ph κ t (c • a) = c • ph κ t a := by
  funext n
  simp only [ph, Pi.smul_apply, smul_eq_mul]
  ring

/-- Strong continuity of the propagator on the weighted algebra. -/
theorem tendsto_wn_ph {a : (Fin d → ℤ) → ℂ} (ha : WS a) (κ s : ℝ) :
    Tendsto (fun t => wn (ph κ t a - ph κ s a)) (𝓝 s) (𝓝 0) := by
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := 𝓝 s)
    (f := fun t n => wt n * ‖ph κ t a n - ph κ s a n‖) (g := fun _ => (0 : ℝ))
    (bound := fun n => 2 * (wt n * ‖a n‖)) (ha.mul_left 2) (fun n => ?_)
    (Eventually.of_forall fun t n => ?_)
  · simpa [wn] using h
  · have hc : Continuous fun t : ℝ => ph κ t a n := by
      unfold ph
      fun_prop
    have hc2 : Continuous fun t : ℝ => ‖ph κ t a n - ph κ s a n‖ := (hc.sub continuous_const).norm
    have := (hc2.tendsto s).const_mul (wt n)
    simpa using this
  · rw [Real.norm_of_nonneg (mul_nonneg (wt_pos n).le (norm_nonneg _))]
    calc wt n * ‖ph κ t a n - ph κ s a n‖ ≤ wt n * (‖ph κ t a n‖ + ‖ph κ s a n‖) :=
          mul_le_mul_of_nonneg_left (norm_sub_le _ _) (wt_pos n).le
      _ = 2 * (wt n * ‖a n‖) := by rw [norm_ph, norm_ph]; ring

/-! ### The phase space `ℓ¹` and the interaction-picture vector field -/

/-- The phase space `ℓ¹(ℤ^d)`, carrying the weighted coefficients `b(n) = w(n) a(n)`. -/
abbrev Xs (d : ℕ) := lp (fun _ : Fin d → ℤ => ℂ) 1

theorem memℓp_one_iff {f : (Fin d → ℤ) → ℂ} : Memℓp f 1 ↔ Summable fun n => ‖f n‖ := by
  rw [memℓp_gen_iff (by norm_num : 0 < (1 : ℝ≥0∞).toReal)]
  simp

theorem norm_Xs (b : Xs d) : ‖b‖ = ∑' n, ‖b n‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (1 : ℝ≥0∞).toReal)]
  simp

theorem summable_norm_Xs (b : Xs d) : Summable fun n => ‖b n‖ := memℓp_one_iff.1 (lp.memℓp b)

/-- Encoding `a ↦ w·a`. -/
noncomputable def enc (a : (Fin d → ℤ) → ℂ) (ha : WS a) : Xs d :=
  ⟨fun n => (wt n : ℂ) * a n, memℓp_one_iff.2 (by
    refine ha.congr fun n => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (wt_pos n)])⟩

@[simp] theorem enc_apply (a : (Fin d → ℤ) → ℂ) (ha : WS a) (n : Fin d → ℤ) :
    enc a ha n = (wt n : ℂ) * a n := rfl

/-- Decoding `b ↦ b/w`. -/
noncomputable def dec (b : Xs d) : (Fin d → ℤ) → ℂ := fun n => b n / (wt n : ℂ)

theorem wt_ne_zero (n : Fin d → ℤ) : (wt n : ℂ) ≠ 0 := by
  exact_mod_cast (wt_pos n).ne'

theorem norm_dec_mul (b : Xs d) (n : Fin d → ℤ) : wt n * ‖dec b n‖ = ‖b n‖ := by
  rw [dec, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (wt_pos n)]
  field_simp [(wt_pos n).ne']

theorem WS_dec (b : Xs d) : WS (dec b) := by
  unfold WS
  simp_rw [norm_dec_mul]
  exact summable_norm_Xs b

theorem wn_dec (b : Xs d) : wn (dec b) = ‖b‖ := by
  rw [wn, norm_Xs]
  simp_rw [norm_dec_mul]

theorem dec_enc (a : (Fin d → ℤ) → ℂ) (ha : WS a) : dec (enc a ha) = a := by
  funext n
  simp [dec, wt_ne_zero n]

theorem norm_enc (a : (Fin d → ℤ) → ℂ) (ha : WS a) : ‖enc a ha‖ = wn a := by
  rw [← wn_dec, dec_enc]

theorem dec_sub (b b' : Xs d) : dec (b - b') = dec b - dec b' := by
  funext n
  simp only [dec, lp.coeFn_sub, Pi.sub_apply]
  ring

theorem dec_smul (c : ℂ) (b : Xs d) : dec (c • b) = c • dec b := by
  funext n
  simp only [dec, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  ring

theorem dec_add (b b' : Xs d) : dec (b + b') = dec b + dec b' := by
  funext n
  simp only [dec, lp.coeFn_add, Pi.add_apply]
  ring

theorem WS_vf (κ β γ t : ℝ) (b : Xs d) :
    WS ((-Complex.I) • ph κ (-t) (Nc β γ (ph κ t (dec b)))) :=
  (WS_ph (WS_Nc β γ (WS_ph (WS_dec b) κ t)) κ (-t)).smul _

/-- The interaction-picture vector field `F(t, b) = w · (−i e^{itL} N(e^{−itL}(b/w)))`. -/
noncomputable def vf (κ β γ t : ℝ) (b : Xs d) : Xs d :=
  enc ((-Complex.I) • ph κ (-t) (Nc β γ (ph κ t (dec b)))) (WS_vf κ β γ t b)

theorem dec_vf (κ β γ t : ℝ) (b : Xs d) :
    dec (vf κ β γ t b) = (-Complex.I) • ph κ (-t) (Nc β γ (ph κ t (dec b))) := dec_enc _ _

theorem norm_vf_sub (κ β γ t : ℝ) (b b' : Xs d) :
    ‖vf κ β γ t b - vf κ β γ t b'‖ =
      wn (Nc β γ (ph κ t (dec b)) - Nc β γ (ph κ t (dec b'))) := by
  rw [← wn_dec, dec_sub, dec_vf, dec_vf, ← smul_sub, wn_smul, norm_neg, Complex.norm_I, one_mul,
    ph_sub, wn_ph]

theorem norm_vf_le (κ β γ t : ℝ) (b : Xs d) :
    ‖vf κ β γ t b‖ ≤ |β| * ‖b‖ ^ 3 + |γ| * ‖b‖ ^ 5 := by
  rw [vf, norm_enc, wn_smul, norm_neg, Complex.norm_I, one_mul, wn_ph]
  have := wn_Nc_le β γ (WS_ph (WS_dec b) κ t)
  rwa [wn_ph, wn_dec] at this

theorem dist_vf_le (κ β γ t : ℝ) {b b' : Xs d} {R : ℝ} (hb : ‖b‖ ≤ R) (hb' : ‖b'‖ ≤ R) :
    ‖vf κ β γ t b - vf κ β γ t b'‖ ≤ (3 * |β| * R ^ 2 + 5 * |γ| * R ^ 4) * ‖b - b'‖ := by
  rw [norm_vf_sub]
  have := wn_Nc_sub_le β γ (WS_ph (WS_dec b) κ t) (WS_ph (WS_dec b') κ t)
    (R := R) (by rw [wn_ph, wn_dec]; exact hb) (by rw [wn_ph, wn_dec]; exact hb')
  rwa [ph_sub, wn_ph, ← dec_sub, wn_dec] at this

theorem continuous_vf (κ β γ : ℝ) (b : Xs d) : Continuous fun t => vf κ β γ t b := by
  rw [continuous_iff_continuousAt]
  intro s
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  set a := dec b
  have ha := WS_dec b
  set Ns := Nc β γ (ph κ s a)
  have hNs : WS Ns := WS_Nc β γ (WS_ph ha κ s)
  have hR : ∀ t, wn (ph κ t a) ≤ ‖b‖ := fun t => by rw [wn_ph, wn_dec]
  have hbound : ∀ t, ‖vf κ β γ t b - vf κ β γ s b‖ ≤
      (3 * |β| * ‖b‖ ^ 2 + 5 * |γ| * ‖b‖ ^ 4) * wn (ph κ t a - ph κ s a) +
        wn (ph κ (-t) Ns - ph κ (-s) Ns) := by
    intro t
    have e : dec (vf κ β γ t b - vf κ β γ s b) = (-Complex.I) •
        (ph κ (-t) (Nc β γ (ph κ t a) - Ns) + (ph κ (-t) Ns - ph κ (-s) Ns)) := by
      rw [dec_sub, dec_vf, dec_vf, ← smul_sub, ← ph_sub]
      congr 1
      abel
    rw [← wn_dec, e, wn_smul, norm_neg, Complex.norm_I, one_mul]
    refine (wn_add_le (WS_ph ((WS_Nc β γ (WS_ph ha κ t)).sub hNs) κ (-t))
      ((WS_ph hNs κ (-t)).sub (WS_ph hNs κ (-s)))).trans ?_
    rw [wn_ph]
    gcongr
    exact wn_Nc_sub_le β γ (WS_ph ha κ t) (WS_ph ha κ s) (hR t) (hR s)
  have h1 := (tendsto_wn_ph ha κ s).const_mul (3 * |β| * ‖b‖ ^ 2 + 5 * |γ| * ‖b‖ ^ 4)
  have h2 : Tendsto (fun t => wn (ph κ (-t) Ns - ph κ (-s) Ns)) (𝓝 s) (𝓝 0) :=
    (tendsto_wn_ph hNs κ (-s)).comp (continuous_neg.tendsto s)
  have h3 := h1.add h2
  rw [mul_zero, zero_add] at h3
  exact squeeze_zero (fun t => norm_nonneg _) hbound h3

/-- **Local existence for the interaction-picture ODE** (Picard–Lindelöf in `ℓ¹`). -/
theorem exists_ode_solution (κ β γ : ℝ) (b₀ : Xs d) :
    ∃ T > 0, ∃ α : ℝ → Xs d, α 0 = b₀ ∧ ∀ t ∈ Ioo (-T) T, HasDerivAt α (vf κ β γ t (α t)) t := by
  set R := ‖b₀‖ + 1 with hR
  have hR0 : 0 ≤ R := by positivity
  set Lc := 3 * |β| * R ^ 2 + 5 * |γ| * R ^ 4 with hLc
  set M := |β| * R ^ 3 + |γ| * R ^ 5 with hM
  have hLc0 : 0 ≤ Lc := by positivity
  have hM0 : 0 ≤ M := by positivity
  set T := 1 / (M + 1) with hT
  have hTpos : 0 < T := by positivity
  have hball : ∀ b ∈ Metric.closedBall b₀ 1, ‖b‖ ≤ R := fun b hb => by
    rw [Metric.mem_closedBall, dist_eq_norm] at hb
    have := norm_le_insert' b b₀
    linarith [norm_sub_norm_le b b₀]
  have ht0 : (0 : ℝ) ∈ Icc (-T) T := ⟨by linarith, hTpos.le⟩
  have hPL : IsPicardLindelof (vf κ β γ) (tmin := -T) (tmax := T) ⟨0, ht0⟩ b₀ 1 0
      M.toNNReal Lc.toNNReal := by
    refine ⟨fun t _ => ?_, fun b _ => (continuous_vf κ β γ b).continuousOn, fun t _ b hb => ?_, ?_⟩
    · refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
      rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hLc0]
      exact dist_vf_le κ β γ t (hball x hx) (hball y hy)
    · rw [Real.coe_toNNReal _ hM0]
      have hb := hball b hb
      have hb0 := norm_nonneg b
      calc ‖vf κ β γ t b‖ ≤ |β| * ‖b‖ ^ 3 + |γ| * ‖b‖ ^ 5 := norm_vf_le κ β γ t b
        _ ≤ M := by
            rw [hM]
            gcongr
    · rw [Real.coe_toNNReal _ hM0]
      simp only [NNReal.coe_one, NNReal.coe_zero, sub_zero, sub_neg_eq_add, zero_add, max_self]
      rw [hT]
      rw [mul_one_div, div_le_one (by linarith)]
      linarith
  obtain ⟨α, hα0, hα⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  refine ⟨T, hTpos, α, hα0, fun t ht => ?_⟩
  exact (hα t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)

/-! ### Plain `ℓ¹` norms of coefficient sequences -/

/-- `Σ |c(n)|`. -/
noncomputable def l1n (c : (Fin d → ℤ) → ℂ) : ℝ := ∑' n, ‖c n‖

theorem l1n_nonneg (c : (Fin d → ℤ) → ℂ) : 0 ≤ l1n c := tsum_nonneg fun _ => norm_nonneg _

theorem l1n_le_wn {c : (Fin d → ℤ) → ℂ} (hc : WS c) : l1n c ≤ wn c := tsum_norm_le_wn hc

theorem l1n_add_le {a c : (Fin d → ℤ) → ℂ} (ha : Summable fun n => ‖a n‖)
    (hc : Summable fun n => ‖c n‖) : l1n (a + c) ≤ l1n a + l1n c := by
  unfold l1n
  rw [← ha.tsum_add hc]
  exact Summable.tsum_le_tsum (fun n => norm_add_le _ _)
    (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => norm_add_le _ _) (ha.add hc))
    (ha.add hc)

theorem l1n_ph (κ t : ℝ) (c : (Fin d → ℤ) → ℂ) : l1n (ph κ t c) = l1n c := by
  unfold l1n
  simp_rw [norm_ph]

theorem summable_norm_ph {c : (Fin d → ℤ) → ℂ} (hc : Summable fun n => ‖c n‖) (κ t : ℝ) :
    Summable fun n => ‖ph κ t c n‖ := by
  simpa [norm_ph] using hc

theorem norm_cexp_mul_I_sub_one_le (θ : ℝ) : ‖Complex.exp ((θ : ℂ) * Complex.I) - 1‖ ≤ |θ| := by
  have hd : ∀ s ∈ (univ : Set ℝ), HasDerivWithinAt (fun s : ℝ => Complex.exp ((s : ℂ) * Complex.I))
      (Complex.exp ((s : ℂ) * Complex.I) * Complex.I) univ s := by
    intro s _
    have h1 : HasDerivAt (fun s : ℝ => (s : ℂ) * Complex.I) Complex.I s := by
      simpa using (hasDerivAt_id s).ofReal_comp.mul_const Complex.I
    exact h1.cexp.hasDerivWithinAt
  have hb : ∀ s ∈ (univ : Set ℝ), ‖Complex.exp ((s : ℂ) * Complex.I) * Complex.I‖ ≤ 1 := by
    intro s _
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_I, one_mul]
  have := convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb (mem_univ 0) (mem_univ θ)
  simpa [Real.norm_eq_abs] using this

/-- `ω · a`. -/
noncomputable def omul (κ : ℝ) (a : (Fin d → ℤ) → ℂ) (n : Fin d → ℤ) : ℂ := (omg κ n : ℂ) * a n

theorem norm_omul_le (κ : ℝ) (a : (Fin d → ℤ) → ℂ) (n : Fin d → ℤ) :
    ‖omul κ a n‖ ≤ (1 + κ ^ 2) ^ 2 * (wt n * ‖a n‖) := by
  rw [omul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (omg_nonneg κ n), ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (omg_le κ n) (norm_nonneg _)

theorem summable_omul {a : (Fin d → ℤ) → ℂ} (ha : WS a) (κ : ℝ) :
    Summable fun n => ‖omul κ a n‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_omul_le κ a) (ha.mul_left _)

theorem l1n_omul_le {a : (Fin d → ℤ) → ℂ} (ha : WS a) (κ : ℝ) :
    l1n (omul κ a) ≤ (1 + κ ^ 2) ^ 2 * wn a := by
  unfold l1n wn
  rw [← tsum_mul_left]
  exact Summable.tsum_le_tsum (norm_omul_le κ a) (summable_omul ha κ) (ha.mul_left _)

theorem omul_sub (κ : ℝ) (a c : (Fin d → ℤ) → ℂ) : omul κ a - omul κ c = omul κ (a - c) := by
  funext n
  simp [omul, mul_sub]

theorem omul_ph (κ t : ℝ) (a : (Fin d → ℤ) → ℂ) : omul κ (ph κ t a) = ph κ t (omul κ a) := by
  funext n
  simp only [omul, ph]
  ring

/-- `Σ ω(n) aₙ e^{in·x} = (Δ + κ²)² Σ aₙ e^{in·x}`. -/
theorem ser_omul (κ : ℝ) {a : (Fin d → ℤ) → ℂ} (ha : WS a) (x : Rd) :
    ser (omul κ a) x = shiftLap κ (shiftLap κ (ser a)) x := by
  have h4 : SumW 4 a := ha.sumW (by norm_num)
  have hb : ∀ n, ‖((κ ^ 2 - nsq n : ℝ) : ℂ) * a n‖ ≤ (1 + κ ^ 2) * ((1 + l1 n) ^ 2 * ‖a n‖) := by
    intro n
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, ← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    have h1 := nsq_le n
    have h0 := nsq_nonneg n
    have hl := l1_nonneg n
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg κ]
  have h2 : SumW 2 (fun n => ((κ ^ 2 - nsq n : ℝ) : ℂ) * a n) := by
    refine Summable.of_nonneg_of_le
      (fun n => mul_nonneg (pow_nonneg (by linarith [l1_nonneg n]) _) (norm_nonneg _))
      (fun n => ?_) (h4.mul_left (1 + κ ^ 2))
    have hl := l1_nonneg n
    calc (1 + l1 n) ^ 2 * ‖((κ ^ 2 - nsq n : ℝ) : ℂ) * a n‖ ≤
        (1 + l1 n) ^ 2 * ((1 + κ ^ 2) * ((1 + l1 n) ^ 2 * ‖a n‖)) :=
          mul_le_mul_of_nonneg_left (hb n) (by positivity)
      _ = (1 + κ ^ 2) * ((1 + l1 n) ^ 4 * ‖a n‖) := by ring
  rw [shiftLap_ser κ (h4.mono (by norm_num)), shiftLap_ser κ h2]
  unfold ser omul omg
  refine tsum_congr fun n => ?_
  push_cast
  ring

/-! ### Time differentiation of `Σ e^{−itω} aₙ(t) e^{in·x}` -/

theorem ser_eq_tsum (c : (Fin d → ℤ) → ℂ) (x : Rd) : ser c x = ∑' n, c n * E n x := rfl

theorem dec_real_smul (r : ℝ) (b : Xs d) : dec (r • b) = (r : ℂ) • dec b := by
  funext n
  simp only [dec, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, Complex.real_smul]
  ring

/-- `(e^{−ihω} − 1)/h + iω`, coefficientwise. -/
noncomputable def errT3 (κ : ℝ) (c : (Fin d → ℤ) → ℂ) (h : ℝ) (n : Fin d → ℤ) : ℂ :=
  (h : ℂ)⁻¹ * (ph κ h c n - c n) + Complex.I * (omg κ n : ℂ) * c n

theorem tendsto_phase_slope (κ : ℝ) {c : (Fin d → ℤ) → ℂ} (hc : WS c) :
    Tendsto (fun h : ℝ => l1n (errT3 κ c h)) (𝓝[≠] 0) (𝓝 0) := by
  have hpt : ∀ n, Tendsto (fun h : ℝ => ‖errT3 κ c h n‖) (𝓝[≠] 0) (𝓝 0) := by
    intro n
    have hd : HasDerivAt (fun h : ℝ => Complex.exp (-((omg κ n * h : ℝ) : ℂ) * Complex.I))
        (-(omg κ n : ℂ) * Complex.I) 0 := by
      have h1 : HasDerivAt (fun h : ℝ => -((omg κ n * h : ℝ) : ℂ) * Complex.I)
          (-(omg κ n : ℂ) * Complex.I) 0 := by
        have := ((hasDerivAt_id (0 : ℝ)).ofReal_comp.const_mul (-(omg κ n : ℂ) * Complex.I))
        convert this using 1
        · funext h
          simp only [id]
          push_cast
          ring
        · simp
      have := h1.cexp
      simpa using this
    have hs := hasDerivAt_iff_tendsto_slope.1 hd
    have hs' : Tendsto (fun h : ℝ => (h : ℂ)⁻¹ *
        (Complex.exp (-((omg κ n * h : ℝ) : ℂ) * Complex.I) - 1))
        (𝓝[≠] 0) (𝓝 (-(omg κ n : ℂ) * Complex.I)) := by
      refine hs.congr' (Eventually.of_forall fun h => ?_)
      simp [slope_def_module, Complex.real_smul]
    have h3 := (hs'.mul_const (c n)).add_const (Complex.I * (omg κ n : ℂ) * c n)
    have h4 : -(omg κ n : ℂ) * Complex.I * c n + Complex.I * (omg κ n : ℂ) * c n = 0 := by ring
    rw [h4] at h3
    have h5 := h3.norm
    rw [norm_zero] at h5
    refine h5.congr' (Eventually.of_forall fun h => ?_)
    simp only [errT3, ph]
    ring_nf
  have hbound : ∀ᶠ h in 𝓝[≠] (0 : ℝ), ∀ n,
      ‖‖errT3 κ c h n‖‖ ≤ 2 * ((1 + κ ^ 2) ^ 2 * (wt n * ‖c n‖)) := by
    filter_upwards [self_mem_nhdsWithin] with h hh n
    rw [norm_norm]
    have hω := omg_nonneg κ n
    have hchord : ‖Complex.exp (-((omg κ n * h : ℝ) : ℂ) * Complex.I) - 1‖ ≤ omg κ n * |h| := by
      have := norm_cexp_mul_I_sub_one_le (-(omg κ n * h))
      rw [abs_neg, abs_mul, abs_of_nonneg hω] at this
      simpa [neg_mul] using this
    have hh' : (0 : ℝ) < |h| := abs_pos.2 hh
    calc ‖errT3 κ c h n‖
        ≤ ‖(h : ℂ)⁻¹ * (ph κ h c n - c n)‖ + ‖Complex.I * (omg κ n : ℂ) * c n‖ := norm_add_le _ _
      _ = |h|⁻¹ * ‖Complex.exp (-((omg κ n * h : ℝ) : ℂ) * Complex.I) - 1‖ * ‖c n‖ +
          omg κ n * ‖c n‖ := by
          simp only [ph, ← sub_one_mul, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
            Complex.norm_I, one_mul, abs_of_nonneg hω]
          ring
      _ ≤ |h|⁻¹ * (omg κ n * |h|) * ‖c n‖ + omg κ n * ‖c n‖ := by gcongr
      _ = 2 * (omg κ n * ‖c n‖) := by field_simp; ring
      _ ≤ 2 * ((1 + κ ^ 2) ^ 2 * (wt n * ‖c n‖)) := by
          have := mul_le_mul_of_nonneg_right (omg_le κ n) (norm_nonneg (c n))
          linarith [this, show ((1 + κ ^ 2) ^ 2 * wt n) * ‖c n‖ =
            (1 + κ ^ 2) ^ 2 * (wt n * ‖c n‖) by ring]
  have := tendsto_tsum_of_dominated_convergence (𝓕 := 𝓝[≠] (0 : ℝ))
    (f := fun h n => ‖errT3 κ c h n‖)
    (g := fun _ => (0 : ℝ)) (bound := fun n => 2 * ((1 + κ ^ 2) ^ 2 * (wt n * ‖c n‖)))
    ((hc.mul_left _).mul_left 2) hpt hbound
  simpa [l1n] using this

theorem summable_errT3 (κ : ℝ) {c : (Fin d → ℤ) → ℂ} (hc : WS c) (h : ℝ) :
    Summable fun n => ‖errT3 κ c h n‖ := by
  have h1 : Summable fun n => ‖(h : ℂ)⁻¹ * (ph κ h c n - c n)‖ := by
    refine (((WS_ph hc κ h).sub hc).summable_norm.mul_left ‖(h : ℂ)⁻¹‖).congr fun n => ?_
    rw [norm_mul]
    rfl
  have h2 : Summable fun n => ‖Complex.I * (omg κ n : ℂ) * c n‖ := by
    refine (summable_omul hc κ).congr fun n => ?_
    simp [omul]
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => norm_add_le _ _) (h1.add h2)

/-- The exact error decomposition of the difference quotient. -/
theorem slope_coeff_identity (κ t s : ℝ) (hst : s - t ≠ 0) (a c c' : (Fin d → ℤ) → ℂ)
    (n : Fin d → ℤ) :
    ((s - t : ℝ) : ℂ)⁻¹ * (ph κ s a n - ph κ t c n) -
        (-Complex.I * omul κ (ph κ t c) n + ph κ t c' n) =
      Complex.exp (-((omg κ n * t : ℝ) : ℂ) * Complex.I) *
        (Complex.exp (-((omg κ n * (s - t) : ℝ) : ℂ) * Complex.I) *
            (((s - t : ℝ) : ℂ)⁻¹ * (a n - c n) - c' n) +
          (ph κ (s - t) c' n - c' n) + errT3 κ c (s - t) n) := by
  have hst' : ((s - t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hst
  have e : Complex.exp (-((omg κ n * s : ℝ) : ℂ) * Complex.I) =
      Complex.exp (-((omg κ n * t : ℝ) : ℂ) * Complex.I) *
        Complex.exp (-((omg κ n * (s - t) : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp only [errT3, ph, omul, e]
  field_simp
  ring

theorem norm_slope_ser_le (κ : ℝ) (α : ℝ → Xs d) {t s : ℝ} (hst : s ≠ t) (D : Xs d) (x : Rd) :
    ‖slope (fun s => ser (ph κ s (dec (α s))) x) t s -
        ser (fun n => -Complex.I * omul κ (ph κ t (dec (α t))) n + ph κ t (dec D) n) x‖ ≤
      ‖(s - t)⁻¹ • (α s - α t) - D‖ + wn (ph κ (s - t) (dec D) - ph κ 0 (dec D)) +
        l1n (errT3 κ (dec (α t)) (s - t)) := by
  have hst' : s - t ≠ 0 := sub_ne_zero.2 hst
  have haW := WS_dec (α s)
  have hcW := WS_dec (α t)
  have hc'W := WS_dec D
  -- the three pieces and their summability
  have hT1 : WS (dec ((s - t)⁻¹ • (α s - α t) - D)) := WS_dec _
  have hT1e : ∀ n, dec ((s - t)⁻¹ • (α s - α t) - D) n =
      ((s - t : ℝ) : ℂ)⁻¹ * (dec (α s) n - dec (α t) n) - dec D n := by
    intro n
    rw [dec_sub, dec_real_smul, dec_sub]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    ring
  have hs1 : Summable fun n => ‖((s - t : ℝ) : ℂ)⁻¹ * (dec (α s) n - dec (α t) n) - dec D n‖ := by
    refine hT1.summable_norm.congr fun n => ?_
    rw [hT1e]
  have hs2 : Summable fun n => ‖ph κ (s - t) (dec D) n - dec D n‖ :=
    ((WS_ph hc'W κ (s - t)).sub hc'W).summable_norm
  have hs3 := summable_errT3 κ hcW (s - t)
  have hpt : ∀ n, ‖(((s - t : ℝ) : ℂ)⁻¹ * (ph κ s (dec (α s)) n - ph κ t (dec (α t)) n) -
      (-Complex.I * omul κ (ph κ t (dec (α t))) n + ph κ t (dec D) n)) * E n x‖ ≤
      ‖((s - t : ℝ) : ℂ)⁻¹ * (dec (α s) n - dec (α t) n) - dec D n‖ +
        ‖ph κ (s - t) (dec D) n - dec D n‖ + ‖errT3 κ (dec (α t)) (s - t) n‖ := by
    intro n
    rw [norm_mul, norm_E, mul_one, slope_coeff_identity κ t s hst', norm_mul,
      norm_cexp_neg_real_mul_I, one_mul]
    refine (norm_add_le _ _).trans (add_le_add_right ((norm_add_le _ _).trans ?_) _)
    rw [norm_mul, norm_cexp_neg_real_mul_I, one_mul]
  have hsum := (hs1.add hs2).add hs3
  -- the series identity for the slope
  have hS1 := (summable_norm_ser' (summable_norm_ph haW.summable_norm κ s) x).of_norm
  have hS2 := (summable_norm_ser' (summable_norm_ph hcW.summable_norm κ t) x).of_norm
  have hS3 : Summable fun n => (-Complex.I * omul κ (ph κ t (dec (α t))) n +
      ph κ t (dec D) n) * E n x := by
    refine (summable_norm_ser' ?_ x).of_norm
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => norm_add_le _ _) ?_
    refine Summable.add ?_ (summable_norm_ph hc'W.summable_norm κ t)
    refine (summable_omul (WS_ph hcW κ t) κ).congr fun n => ?_
    simp
  have hser : slope (fun s => ser (ph κ s (dec (α s))) x) t s -
      ser (fun n => -Complex.I * omul κ (ph κ t (dec (α t))) n + ph κ t (dec D) n) x =
      ∑' n, (((s - t : ℝ) : ℂ)⁻¹ * (ph κ s (dec (α s)) n - ph κ t (dec (α t)) n) -
        (-Complex.I * omul κ (ph κ t (dec (α t))) n + ph κ t (dec D) n)) * E n x := by
    rw [slope_def_module, ser_eq_tsum, ser_eq_tsum, ser_eq_tsum, ← hS1.tsum_sub hS2,
      Complex.real_smul, ← tsum_mul_left, ← ((hS1.sub hS2).mul_left _).tsum_sub hS3]
    refine tsum_congr fun n => ?_
    push_cast
    ring
  rw [hser]
  calc _ ≤ ∑' n, ‖(((s - t : ℝ) : ℂ)⁻¹ * (ph κ s (dec (α s)) n - ph κ t (dec (α t)) n) -
        (-Complex.I * omul κ (ph κ t (dec (α t))) n + ph κ t (dec D) n)) * E n x‖ :=
        norm_tsum_le_tsum_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpt hsum)
    _ ≤ ∑' n, (‖((s - t : ℝ) : ℂ)⁻¹ * (dec (α s) n - dec (α t) n) - dec D n‖ +
          ‖ph κ (s - t) (dec D) n - dec D n‖ + ‖errT3 κ (dec (α t)) (s - t) n‖) :=
        Summable.tsum_le_tsum hpt (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpt hsum) hsum
    _ = l1n (dec ((s - t)⁻¹ • (α s - α t) - D)) + l1n (ph κ (s - t) (dec D) - dec D) +
          l1n (errT3 κ (dec (α t)) (s - t)) := by
        rw [(hs1.add hs2).tsum_add hs3, hs1.tsum_add hs2]
        unfold l1n
        congr 2
        · exact tsum_congr fun n => by rw [hT1e]
    _ ≤ ‖(s - t)⁻¹ • (α s - α t) - D‖ + wn (ph κ (s - t) (dec D) - ph κ 0 (dec D)) +
          l1n (errT3 κ (dec (α t)) (s - t)) := by
        rw [ph_zero]
        gcongr
        · rw [← wn_dec]
          exact l1n_le_wn hT1
        · exact l1n_le_wn ((WS_ph hc'W κ (s - t)).sub hc'W)

/-- **Time derivative of the interaction-picture series.** -/
theorem hasDerivAt_ser_ph (κ : ℝ) {α : ℝ → Xs d} {t : ℝ} {D : Xs d} (hα : HasDerivAt α D t)
    (x : Rd) :
    HasDerivAt (fun s => ser (ph κ s (dec (α s))) x)
      (ser (fun n => -Complex.I * omul κ (ph κ t (dec (α t))) n + ph κ t (dec D) n) x) t := by
  rw [hasDerivAt_iff_tendsto_slope, tendsto_iff_norm_sub_tendsto_zero]
  have hA : Tendsto (fun s => ‖(s - t)⁻¹ • (α s - α t) - D‖) (𝓝[≠] t) (𝓝 0) := by
    have := hasDerivAt_iff_tendsto_slope.1 hα
    rw [tendsto_iff_norm_sub_tendsto_zero] at this
    simpa [slope_def_module] using this
  have hshift : Tendsto (fun s : ℝ => s - t) (𝓝[≠] t) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have hc : Continuous fun s : ℝ => s - t := continuous_id.sub continuous_const
      have := (hc.tendsto t).mono_left (nhdsWithin_le_nhds (s := {t}ᶜ))
      simpa using this
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact sub_ne_zero.2 hs
  have hB : Tendsto (fun s : ℝ => wn (ph κ (s - t) (dec D) - ph κ 0 (dec D))) (𝓝[≠] t) (𝓝 0) :=
    (tendsto_wn_ph (WS_dec D) κ 0).comp (hshift.mono_right nhdsWithin_le_nhds)
  have hC := (tendsto_phase_slope κ (WS_dec (α t))).comp hshift
  have hsum := (hA.add hB).add hC
  simp only [add_zero] at hsum
  refine squeeze_zero' (Eventually.of_forall fun s => norm_nonneg _) ?_ hsum
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact norm_slope_ser_le κ α hs D x

/-! ### From the interaction-picture ODE to a classical solution -/

theorem norm_ser_sub_le {a c : (Fin d → ℤ) → ℂ} (ha : Summable fun n => ‖a n‖)
    (hc : Summable fun n => ‖c n‖) (x : Rd) : ‖ser a x - ser c x‖ ≤ l1n (a - c) := by
  rw [ser_sub' ha hc]
  have hac : Summable fun n => ‖(a - c) n‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => norm_sub_le _ _) (ha.add hc)
  exact norm_ser_le' hac x

/-- Joint continuity of `(t, x) ↦ Σ cₙ(t) e^{in·x}` from `ℓ¹`-continuity in `t`. -/
theorem continuousOn_ser_param {c : ℝ → (Fin d → ℤ) → ℂ} {S : Set ℝ}
    (hc : ∀ t, Summable fun n => ‖c t n‖)
    (hcont : ∀ t ∈ S, Tendsto (fun s => l1n (c s - c t)) (𝓝 t) (𝓝 0)) :
    ContinuousOn (fun p : ℝ × Rd => ser (c p.1) p.2) (S ×ˢ univ) := by
  intro p hp
  refine ContinuousAt.continuousWithinAt ?_
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have h1 : Tendsto (fun q : ℝ × Rd => l1n (c q.1 - c p.1)) (𝓝 p) (𝓝 0) :=
    (hcont p.1 hp.1).comp (continuous_fst.tendsto p)
  have h2 : Tendsto (fun q : ℝ × Rd => ‖ser (c p.1) q.2 - ser (c p.1) p.2‖) (𝓝 p) (𝓝 0) := by
    have hcs := continuous_ser (hc p.1)
    have := ((hcs.comp continuous_snd).sub
      (continuous_const (y := ser (c p.1) p.2))).norm.tendsto p
    simpa using this
  refine squeeze_zero (fun _ => norm_nonneg _) (fun q => ?_) (by simpa using h1.add h2)
  calc ‖ser (c q.1) q.2 - ser (c p.1) p.2‖ ≤ ‖ser (c q.1) q.2 - ser (c p.1) q.2‖ +
        ‖ser (c p.1) q.2 - ser (c p.1) p.2‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ l1n (c q.1 - c p.1) + ‖ser (c p.1) q.2 - ser (c p.1) p.2‖ := by
        gcongr
        exact norm_ser_sub_le (hc _) (hc _) _

theorem ph_dec_vf (κ β γ t : ℝ) (b : Xs d) :
    ph κ t (dec (vf κ β γ t b)) = (-Complex.I) • Nc β γ (ph κ t (dec b)) := by
  rw [dec_vf, ph_smul, ph_ph, add_neg_cancel, ph_zero]

/-- The physical coefficients `û(t) = e^{−itL} (b(t)/w)`. -/
noncomputable def uhat (κ : ℝ) (α : ℝ → Xs d) (t : ℝ) : (Fin d → ℤ) → ℂ := ph κ t (dec (α t))

theorem WS_uhat (κ : ℝ) (α : ℝ → Xs d) (t : ℝ) : WS (uhat κ α t) := WS_ph (WS_dec (α t)) κ t

theorem wn_uhat (κ : ℝ) (α : ℝ → Xs d) (t : ℝ) : wn (uhat κ α t) = ‖α t‖ := by
  rw [uhat, wn_ph, wn_dec]

theorem tendsto_wn_uhat (κ : ℝ) {α : ℝ → Xs d} {t : ℝ} (hα : ContinuousAt α t) :
    Tendsto (fun s => wn (uhat κ α s - uhat κ α t)) (𝓝 t) (𝓝 0) := by
  have h1 : Tendsto (fun s => ‖α s - α t‖) (𝓝 t) (𝓝 0) := by
    have := ((hα.sub (continuousAt_const (y := α t))).norm).tendsto
    simpa using this
  have h2 := tendsto_wn_ph (WS_dec (α t)) κ t
  refine squeeze_zero (fun _ => wn_nonneg _) (fun s => ?_) (by simpa using h1.add h2)
  have e : uhat κ α s - uhat κ α t =
      ph κ s (dec (α s) - dec (α t)) + (ph κ s (dec (α t)) - ph κ t (dec (α t))) := by
    rw [uhat, uhat, ← ph_sub]
    abel
  rw [e]
  refine (wn_add_le (WS_ph ((WS_dec _).sub (WS_dec _)) κ s)
    ((WS_ph (WS_dec _) κ s).sub (WS_ph (WS_dec _) κ t))).trans ?_
  rw [wn_ph, ← dec_sub, wn_dec]

/-- The coefficients of `∂ₜu = −i((Δ+κ²)²u + N(u))`. -/
noncomputable def uhatD (κ β γ : ℝ) (α : ℝ → Xs d) (t : ℝ) : (Fin d → ℤ) → ℂ :=
  fun n => -Complex.I * (omul κ (uhat κ α t) n + Nc β γ (uhat κ α t) n)

theorem summable_uhatD (κ β γ : ℝ) (α : ℝ → Xs d) (t : ℝ) :
    Summable fun n => ‖uhatD κ β γ α t n‖ := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    ((summable_omul (WS_uhat κ α t) κ).add (WS_Nc β γ (WS_uhat κ α t)).summable_norm)
  rw [uhatD, norm_mul, norm_neg, Complex.norm_I, one_mul]
  exact norm_add_le _ _

theorem uhatD_eq (κ β γ : ℝ) (α : ℝ → Xs d) (t : ℝ) :
    (fun n => -Complex.I * omul κ (ph κ t (dec (α t))) n +
      ph κ t (dec (vf κ β γ t (α t))) n) = uhatD κ β γ α t := by
  funext n
  rw [ph_dec_vf, uhatD, uhat]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem tendsto_l1n_uhatD (κ β γ : ℝ) {α : ℝ → Xs d} {t : ℝ} (hα : ContinuousAt α t) :
    Tendsto (fun s => l1n (uhatD κ β γ α s - uhatD κ β γ α t)) (𝓝 t) (𝓝 0) := by
  set R := ‖α t‖ + 1 with hR
  have hev : ∀ᶠ s in 𝓝 t, ‖α s‖ ≤ R := by
    have := (hα.norm).eventually (Iio_mem_nhds (show ‖α t‖ < R by rw [hR]; linarith))
    filter_upwards [this] with s hs
    exact hs.le
  set C := (1 + κ ^ 2) ^ 2 + (3 * |β| * R ^ 2 + 5 * |γ| * R ^ 4) with hC
  have hlim := (tendsto_wn_uhat κ hα).const_mul C
  rw [mul_zero] at hlim
  refine squeeze_zero' (Eventually.of_forall fun _ => l1n_nonneg _) ?_ hlim
  filter_upwards [hev] with s hs
  have hW := (WS_uhat κ α s).sub (WS_uhat κ α t)
  have e : uhatD κ β γ α s - uhatD κ β γ α t =
      (-Complex.I) • (omul κ (uhat κ α s - uhat κ α t) +
        (Nc β γ (uhat κ α s) - Nc β γ (uhat κ α t))) := by
    funext n
    simp only [uhatD, Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul, omul]
    ring
  have hN := wn_Nc_sub_le β γ (WS_uhat κ α s) (WS_uhat κ α t) (R := R)
    (by rw [wn_uhat]; exact hs) (by rw [wn_uhat, hR]; linarith)
  have hs1 := summable_omul hW κ
  have hs2 := ((WS_Nc β γ (WS_uhat κ α s)).sub (WS_Nc β γ (WS_uhat κ α t))).summable_norm
  calc l1n (uhatD κ β γ α s - uhatD κ β γ α t)
      = l1n (omul κ (uhat κ α s - uhat κ α t) +
          (Nc β γ (uhat κ α s) - Nc β γ (uhat κ α t))) := by
        rw [e]
        unfold l1n
        simp
    _ ≤ l1n (omul κ (uhat κ α s - uhat κ α t)) +
          l1n (Nc β γ (uhat κ α s) - Nc β γ (uhat κ α t)) := l1n_add_le hs1 hs2
    _ ≤ (1 + κ ^ 2) ^ 2 * wn (uhat κ α s - uhat κ α t) +
          (3 * |β| * R ^ 2 + 5 * |γ| * R ^ 4) * wn (uhat κ α s - uhat κ α t) :=
        add_le_add (l1n_omul_le hW κ)
          ((l1n_le_wn ((WS_Nc β γ (WS_uhat κ α s)).sub (WS_Nc β γ (WS_uhat κ α t)))).trans hN)
    _ = C * wn (uhat κ α s - uhat κ α t) := by rw [hC]; ring

/-- **Classical solutions from the interaction-picture ODE.** -/
theorem isClassicalSolution_of_ode (κ β γ : ℝ) {T : ℝ} (hT : 0 < T) {α : ℝ → Xs d}
    (hα : ∀ t ∈ Ioo (-T) T, HasDerivAt α (vf κ β γ t (α t)) t) :
    IsClassicalSolution κ β γ T (fun t x => ser (uhat κ α t) x) := by
  have hderiv : ∀ t ∈ Ioo (-T) T, ∀ x, HasDerivAt (fun s => ser (uhat κ α s) x)
      (ser (uhatD κ β γ α t) x) t := by
    intro t ht x
    have := hasDerivAt_ser_ph κ (hα t ht) x
    rwa [uhatD_eq] at this
  have hcontα : ∀ t ∈ Ioo (-T) T, ContinuousAt α t := fun t ht => (hα t ht).continuousAt
  refine ⟨hT, fun t x j => isPeriodic_ser _ x j, fun t _ => ?_, ?_, fun t ht x =>
    (hderiv t ht x).differentiableAt, ?_, fun t ht x => ?_⟩
  · exact_mod_cast contDiff_ser ((WS_uhat κ α t).sumW (by norm_num : 4 ≤ 8))
  · exact continuousOn_ser_param (fun t => (WS_uhat κ α t).summable_norm)
      (fun t ht => squeeze_zero (fun _ => l1n_nonneg _)
        (fun s => l1n_le_wn ((WS_uhat κ α s).sub (WS_uhat κ α t))) (tendsto_wn_uhat κ (hcontα t ht)))
  · refine (continuousOn_ser_param (summable_uhatD κ β γ α)
      (fun t ht => tendsto_l1n_uhatD κ β γ (hcontα t ht))).congr fun p hp => ?_
    exact (hderiv p.1 hp.1 p.2).deriv
  · rw [(hderiv t ht x).deriv]
    have hW := WS_uhat κ α t
    have hs1 := summable_omul hW κ
    have hs2 := (WS_Nc β γ hW).summable_norm
    have e : uhatD κ β γ α t = (-Complex.I) • (omul κ (uhat κ α t) + Nc β γ (uhat κ α t)) := by
      funext n
      simp [uhatD]
    rw [e, ser_smul, ← ser_add' hs1 hs2, ser_omul κ hW, ser_Nc β γ hW, ← mul_assoc,
      show Complex.I * -Complex.I = 1 by rw [mul_neg, Complex.I_mul_I, neg_neg], one_mul]

/-! ### Local existence for trigonometric data -/

/-- The coefficient sequence of `Σ_{n∈T} cₙ e^{in·x}`. -/
noncomputable def trigCoeff (T : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℂ) (n : Fin d → ℤ) : ℂ :=
  if n ∈ T then c n else 0

theorem WS_trigCoeff (T : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℂ) : WS (trigCoeff T c) := by
  unfold WS
  refine summable_of_ne_finset_zero (s := T) fun n hn => ?_
  simp [trigCoeff, hn]

theorem ser_trigCoeff (T : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℂ) :
    ser (trigCoeff T c) = trig T c := by
  funext x
  rw [ser, tsum_eq_sum (s := T) fun n hn => by simp [trigCoeff, hn], trig]
  exact Finset.sum_congr rfl fun n hn => by simp [trigCoeff, hn]

/-- **Local existence:** every trigonometric polynomial launches a classical solution. -/
theorem exists_classical_solution (κ β γ : ℝ) (T : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℂ) :
    ∃ τ > 0, ∃ u : ℝ → Rd → ℂ, IsClassicalSolution κ β γ τ u ∧ u 0 = trig T c := by
  obtain ⟨τ, hτ, α, hα0, hα⟩ :=
    exists_ode_solution κ β γ (enc (trigCoeff T c) (WS_trigCoeff T c))
  refine ⟨τ, hτ, fun t x => ser (uhat κ α t) x, isClassicalSolution_of_ode κ β γ hτ hα, ?_⟩
  funext x
  simp only [uhat, hα0, dec_enc, ph_zero]
  rw [ser_trigCoeff]

/-! ### Invariance and the classification corollary -/

/-- `E_S` is **invariant** under the flow: every classical solution starting in `E_S` remains in
`E_S` for as long as it exists. -/
def IsInvariant (κ β γ : ℝ) (S : Finset (Fin d → ℤ)) : Prop :=
  ∀ τ (u : ℝ → Rd → ℂ), IsClassicalSolution κ β γ τ u → u 0 ∈ coordSubspace S →
    ∀ t ∈ Ioo (-τ) τ, u t ∈ coordSubspace S

/-- Uniqueness for solutions on different intervals. -/
theorem IsClassicalSolution.unique' {κ β γ τ₁ τ₂ : ℝ} {u₁ u₂ : ℝ → Rd → ℂ}
    (h₁ : IsClassicalSolution κ β γ τ₁ u₁) (h₂ : IsClassicalSolution κ β γ τ₂ u₂)
    (h0 : u₁ 0 = u₂ 0) : ∀ t ∈ Ioo (-(min τ₁ τ₂)) (min τ₁ τ₂), u₁ t = u₂ t := by
  have hpos : 0 < min τ₁ τ₂ := lt_min h₁.pos h₂.pos
  exact (h₁.mono hpos (min_le_left _ _)).unique (h₂.mono hpos (min_le_right _ _)) h0

theorem trig_empty (c : (Fin d → ℤ) → ℂ) : trig (∅ : Finset (Fin d → ℤ)) c = 0 := by
  funext x
  simp [trig]

theorem trig_singleton (p : Fin d → ℤ) (c : (Fin d → ℤ) → ℂ) :
    trig {p} c = trig {p} (fun _ => c p) := by
  funext x
  simp [trig]

theorem isInvariant_of_card_le_one (κ β γ : ℝ) {S : Finset (Fin d → ℤ)} (hS : S.card ≤ 1) :
    IsInvariant κ β γ S := by
  intro τ u hu h0 t ht
  obtain ⟨c, hc⟩ := h0
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hS with h | h
  · -- `E_∅ = {0}` carries the zero solution
    rw [Finset.card_eq_zero.1 h] at hc ⊢
    have hz := singleMode_isClassicalSolution κ β γ (0 : Fin d → ℤ) 0 hu.pos
    have hz0 : u 0 = singleMode κ β γ 0 0 0 := by
      rw [hc, trig_empty]
      funext x
      simp [singleMode]
    have := hu.unique hz hz0 t ht
    refine ⟨fun _ => 0, ?_⟩
    rw [this, trig_empty]
    funext x
    simp [singleMode]
  · obtain ⟨p, rfl⟩ := Finset.card_eq_one.1 h
    have hv := singleMode_isClassicalSolution κ β γ p (c p) hu.pos
    have hv0 : u 0 = singleMode κ β γ p (c p) 0 := by
      rw [hc, singleMode_zero, trig_singleton]
    rw [hu.unique hv hv0 t ht]
    exact singleMode_mem κ β γ p (c p) t

theorem not_isInvariant_of_two_le_card {κ β γ : ℝ} (hγ : γ ≠ 0) {S : Finset (Fin d → ℤ)}
    (hS : 2 ≤ S.card) : ¬ IsInvariant κ β γ S := by
  intro hinv
  obtain ⟨p, hp, q, hq, hpq, -, hmem, -, hleak⟩ :=
    no_multimode_invariance (κ := κ) (β := β) hγ hS (a := 1) (b := 1) one_ne_zero one_ne_zero
  obtain ⟨τ, hτ, u, hu, hu0⟩ := exists_classical_solution κ β γ {p, q} (twoMode p q 1 1)
  have hl := (hleak τ u hu hu0).2.2
  have hin : ∀ᶠ t in 𝓝[≠] (0 : ℝ), t ∈ Ioo (-τ) τ :=
    nhdsWithin_le_nhds (Ioo_mem_nhds (by linarith) hτ)
  obtain ⟨t, ht1, ht2⟩ := (hl.and hin).exists
  exact ht1 (hinv τ u hu (hu0 ▸ hmem) t ht2)

/-- **Corollary (complete classification of finite Fourier coordinate subspaces).**  For
`γ ≠ 0` and every finite `S ⊂ ℤ^d`: `E_S` is invariant under the flow iff `|S| ≤ 1`. -/
theorem classification {κ β γ : ℝ} (hγ : γ ≠ 0) (S : Finset (Fin d → ℤ)) :
    IsInvariant κ β γ S ↔ S.card ≤ 1 := by
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    exact not_isInvariant_of_two_le_card hγ hc h
  · exact isInvariant_of_card_le_one κ β γ

/-- **Theorem 1 (no finite multimode Fourier coordinate subspace is invariant)**, with the
corresponding local solution: for `|S| ≥ 2`, `E_S` is not invariant; there are `u₀ ∈ E_S`,
`r ∉ S` and a classical solution `u` with `u(0) = u₀`, unique among classical solutions, such that
`û(r,0) = 0`, `∂ₜû(r,0) ≠ 0`, and `u(t) ∉ E_S` for all small `t ≠ 0`. -/
theorem noninvariance {κ β γ : ℝ} (hγ : γ ≠ 0) {S : Finset (Fin d → ℤ)} (hS : 2 ≤ S.card) :
    ¬ IsInvariant κ β γ S ∧
    ∃ u₀ ∈ coordSubspace S, ∃ r ∉ S, ∃ τ > 0, ∃ u : ℝ → Rd → ℂ,
      IsClassicalSolution κ β γ τ u ∧ u 0 = u₀ ∧
      (∀ τ' (v : ℝ → Rd → ℂ), IsClassicalSolution κ β γ τ' v → v 0 = u₀ →
        ∀ t ∈ Ioo (-(min τ' τ)) (min τ' τ), v t = u t) ∧
      coeff (u 0) r = 0 ∧ (∃ D : ℂ, D ≠ 0 ∧ HasDerivAt (fun t => coeff (u t) r) D 0) ∧
      ∀ᶠ t in 𝓝[≠] (0 : ℝ), u t ∉ coordSubspace S := by
  refine ⟨not_isInvariant_of_two_le_card hγ hS, ?_⟩
  obtain ⟨p, hp, q, hq, hpq, hr, hmem, hD, hleak⟩ :=
    no_multimode_invariance (κ := κ) (β := β) hγ hS (a := 1) (b := 1) one_ne_zero one_ne_zero
  obtain ⟨τ, hτ, u, hu, hu0⟩ := exists_classical_solution κ β γ {p, q} (twoMode p q 1 1)
  obtain ⟨h1, h2, h3⟩ := hleak τ u hu hu0
  exact ⟨_, hmem, _, hr, τ, hτ, u, hu, hu0,
    fun τ' v hv hv0 t ht => hv.unique' hu (hv0.trans hu0.symm) t ht, h1, ⟨_, hD, h2⟩, h3⟩

/-- **Theorem 2 (universal instantaneous leakage)**, with existence: every trigonometric
polynomial with `|T| ≥ 2` nonzero coefficients launches a classical solution (unique among
classical solutions) that leaks into some `r ∉ T` with `∂ₜû(r,0) = −iγ c_p³ \bar c_q² ≠ 0`. -/
theorem universal_leakage_solution {κ β γ : ℝ} (hγ : γ ≠ 0) {T : Finset (Fin d → ℤ)}
    (hT : 2 ≤ T.card) {c : (Fin d → ℤ) → ℂ} (hc : ∀ n ∈ T, c n ≠ 0) :
    ∃ r ∉ T, ∃ τ > 0, ∃ u : ℝ → Rd → ℂ,
      IsClassicalSolution κ β γ τ u ∧ u 0 = trig T c ∧
      (∀ τ' (v : ℝ → Rd → ℂ), IsClassicalSolution κ β γ τ' v → v 0 = trig T c →
        ∀ t ∈ Ioo (-(min τ' τ)) (min τ' τ), v t = u t) ∧
      coeff (u 0) r = 0 ∧ (∃ D : ℂ, D ≠ 0 ∧ HasDerivAt (fun t => coeff (u t) r) D 0) ∧
      ∀ᶠ t in 𝓝[≠] (0 : ℝ), u t ∉ coordSubspace T := by
  obtain ⟨p, -, q, -, -, hr, hD, hleak⟩ := universal_leakage (κ := κ) (β := β) hγ hT hc
  obtain ⟨τ, hτ, u, hu, hu0⟩ := exists_classical_solution κ β γ T c
  obtain ⟨h1, h2, h3⟩ := hleak τ u hu hu0
  exact ⟨_, hr, τ, hτ, u, hu, hu0,
    fun τ' v hv hv0 t ht => hv.unique' hu (hv0.trans hu0.symm) t ht, h1, ⟨_, hD, h2⟩, h3⟩

theorem cos_eq_trig :
    (fun x : EuclideanSpace ℝ (Fin 1) => (Real.cos (x 0) : ℂ)) =
      trig {(fun _ => 1 : Fin 1 → ℤ), -(fun _ => 1 : Fin 1 → ℤ)}
        (twoMode (fun _ => 1) (-(fun _ => 1)) (1 / 2) (1 / 2)) := by
  set e : Fin 1 → ℤ := fun _ => 1
  have hpq : e ≠ -e := by
    intro h
    have := congrFun h 0
    simp [e] at this
  funext x
  rw [trig_twoMode hpq]
  have hE : ∀ x : EuclideanSpace ℝ (Fin 1), E e x = Complex.exp ((x 0 : ℂ) * Complex.I) := by
    intro x
    simp [E, e, PiLp.inner_apply]
  have hE' : ∀ x : EuclideanSpace ℝ (Fin 1), E (-e) x = Complex.exp (-(x 0 : ℂ) * Complex.I) := by
    intro x
    simp [E, e, PiLp.inner_apply]
  rw [hE, hE', Complex.ofReal_cos, Complex.cos]
  ring

/-- **Proposition (fifth-harmonic generation from a cosine)**, with existence: `u₀ = cos x`
launches a classical solution (unique among classical solutions) with `û(5,0) = 0` and
`∂ₜû(5,0) = −iγ/32`, i.e. `û(5,t) = −(iγ/32)t + o(t)`. -/
theorem fifth_harmonic_solution (κ β γ : ℝ) :
    ∃ τ > 0, ∃ u : ℝ → EuclideanSpace ℝ (Fin 1) → ℂ,
      IsClassicalSolution κ β γ τ u ∧ u 0 = (fun x => (Real.cos (x 0) : ℂ)) ∧
      (∀ τ' (v : ℝ → EuclideanSpace ℝ (Fin 1) → ℂ), IsClassicalSolution κ β γ τ' v →
        v 0 = (fun x => (Real.cos (x 0) : ℂ)) →
        ∀ t ∈ Ioo (-(min τ' τ)) (min τ' τ), v t = u t) ∧
      coeff (u 0) (fun _ => 5) = 0 ∧
      HasDerivAt (fun t => coeff (u t) (fun _ => 5)) (-Complex.I * (γ : ℂ) / 32) 0 := by
  obtain ⟨τ, hτ, u, hu, hu0⟩ := exists_classical_solution κ β γ
    {(fun _ => 1 : Fin 1 → ℤ), -(fun _ => 1 : Fin 1 → ℤ)}
    (twoMode (fun _ => 1) (-(fun _ => 1)) (1 / 2) (1 / 2))
  rw [← cos_eq_trig] at hu0
  exact ⟨τ, hτ, u, hu, hu0, fun τ' v hv hv0 t ht => hv.unique' hu (hv0.trans hu0.symm) t ht,
    fifth_harmonic hu hu0⟩

end FourierLeakage

end ReyesMath
