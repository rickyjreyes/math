import Mathlib
import MathProofs.E68Classification
import MathProofs.E68Radial

/-!
# E68: the fixed singular `H¹` counterexample for `n > 2`

For `n > 2` and `0 < a < (n-2)/2`, the single field
`ψ(x) = χ(|x|) |x|^{-a}` (value `0` at `x = 0`)
with a smooth cutoff `χ = 1` on `[0,1]`, `χ = 0` on `[2,∞)`, is in `H¹(ℝⁿ)`, and
`R^{2-n} ∫_{B_R} |∇ψ|² = σ_{n-1} a² R^{-2a} / (n-2-2a) → ∞` as `R ↓ 0`.
So one fixed `H¹` field defeats every finite constant at arbitrarily small radii.

The cutoff is `χ(r) = cut(r²)` with `cut(s) = smoothTransition((4 - s)/3)`, so the field is
`ψ(x) = F₀(|x|²)`, `F_δ(s) = cut(s) (s + δ²)^{-a/2}`, and every derivative is a one-variable
derivative in `s` composed with `x ↦ |x|²`.

* `contDiffAt_psi`, `hasGradientAt_psi`, `gradient_psi_of_lt_one`: `ψ` is `C^∞` away from
  `0`, its classical gradient there is `2F₀'(|x|²) x`, and `∇ψ(x) = -a|x|^{-a-2} x` on
  `0 < |x| < 1`.
* `memLp_psi`, `memLp_gradC`: `ψ` and its gradient are in `L²` (the gradient needs
  `a < (n-2)/2`).
* `weak_deriv`, `isH1`: the classical gradient is the weak gradient across the origin. The
  smooth regularizations `ψ_δ(x) = F_δ(|x|²)` satisfy integration by parts, and the identity
  passes to the limit `δ → 0` by dominated convergence, with the integrable majorants
  `|x|^{-a}` and `|x|^{1-a}, |x|^{-a-1}` on `B₂`.
* `integral_sq_ball_one`, `integral_grad_sq_ball_one`, `integral_grad_sq_ball_sphere`: the
  exact radial integrals `σ_{n-1}/(n-2a)`, `σ_{n-1}a²/(n-2-2a)` and
  `σ_{n-1}a²R^{n-2-2a}/(n-2-2a)`, with `σ_{n-1}` the surface measure of the unit sphere.
* `blowup`, `no_constant`, `defeats_every_constant`, `not_e68`: the fixed field defeats every
  constant as `R ↓ 0`, so it alone refutes `E68(n)` for `n > 2`.
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ContDiff

namespace ReyesMath.E68

namespace Singular

/-! ### The cutoff -/

/-- The cutoff in the squared radius: `cut s = 1` for `s ≤ 1` and `cut s = 0` for `s ≥ 4`. -/
def cut (s : ℝ) : ℝ := Real.smoothTransition ((4 - s) / 3)

theorem contDiff_cut : ContDiff ℝ ∞ cut :=
  (Real.smoothTransition.contDiff (n := ⊤)).comp (by fun_prop)

theorem cut_eq_one {s : ℝ} (hs : s ≤ 1) : cut s = 1 :=
  Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ (by norm_num)]; linarith)

theorem cut_eq_zero {s : ℝ} (hs : 4 ≤ s) : cut s = 0 :=
  Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) (by norm_num))

theorem cut_nonneg (s : ℝ) : 0 ≤ cut s := Real.smoothTransition.nonneg _

theorem cut_le_one (s : ℝ) : cut s ≤ 1 := Real.smoothTransition.le_one _

theorem deriv_cut_of_lt_one {s : ℝ} (hs : s < 1) : deriv cut s = 0 := by
  have h : cut =ᶠ[𝓝 s] fun _ => 1 := by
    filter_upwards [Iio_mem_nhds hs] with u hu
    exact cut_eq_one (le_of_lt hu)
  rw [h.deriv_eq, deriv_const]

theorem deriv_cut_of_four_lt {s : ℝ} (hs : 4 < s) : deriv cut s = 0 := by
  have h : cut =ᶠ[𝓝 s] fun _ => 0 := by
    filter_upwards [Ioi_mem_nhds hs] with u hu
    exact cut_eq_zero (le_of_lt hu)
  rw [h.deriv_eq, deriv_const]

theorem exists_bound_deriv_cut : ∃ K, 0 ≤ K ∧ ∀ s, |deriv cut s| ≤ K := by
  have hc : Continuous (deriv cut) := contDiff_cut.continuous_deriv (by simp)
  have hs : HasCompactSupport (deriv cut) :=
    HasCompactSupport.intro (isCompact_Icc (a := (1 : ℝ)) (b := 4)) fun s hs => by
      simp only [mem_Icc, not_and_or, not_le] at hs
      rcases hs with h | h
      · exact deriv_cut_of_lt_one h
      · exact deriv_cut_of_four_lt h
  obtain ⟨K, hK⟩ := hc.bounded_above_of_compact_support hs
  exact ⟨K, (norm_nonneg _).trans (hK 0), fun s => by simpa [Real.norm_eq_abs] using hK s⟩

/-- The radial cutoff profile `χ(r) = cut(r²)`: `C^∞`, `χ = 1` on `[0,1]`, `χ = 0` on
`[2,∞)`. -/
def chi (r : ℝ) : ℝ := cut (r ^ 2)

theorem contDiff_chi : ContDiff ℝ ∞ chi := contDiff_cut.comp (contDiff_id.pow 2)

theorem chi_eq_one {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) : chi r = 1 := cut_eq_one (by nlinarith)

theorem chi_eq_zero {r : ℝ} (h2 : 2 ≤ r) : chi r = 0 := cut_eq_zero (by nlinarith)

/-! ### The radial profiles -/

/-- `F_δ(s) = cut(s) (s + δ²)^{-a/2}`; `F₀(|x|²) = χ(|x|)|x|^{-a}`. -/
def F (a δ s : ℝ) : ℝ := cut s * (s + δ ^ 2) ^ (-a / 2)

/-- `F_δ'(s)`. -/
def F' (a δ s : ℝ) : ℝ :=
  deriv cut s * (s + δ ^ 2) ^ (-a / 2) + cut s * ((-a / 2) * (s + δ ^ 2) ^ (-a / 2 - 1))

theorem hasDerivAt_F (a δ : ℝ) {s : ℝ} (hs : 0 < s + δ ^ 2) :
    HasDerivAt (F a δ) (F' a δ s) s := by
  have h1 : HasDerivAt cut (deriv cut s) s :=
    ((contDiff_cut.differentiable (by simp)) s).hasDerivAt
  have h2 := ((hasDerivAt_id' s).add_const (δ ^ 2)).rpow_const (p := -a / 2) (Or.inl hs.ne')
  have h3 := h1.mul h2
  rw [one_mul] at h3
  exact h3

theorem F'_eq_zero (a δ : ℝ) {s : ℝ} (hs : 4 < s) : F' a δ s = 0 := by
  rw [F', deriv_cut_of_four_lt hs, cut_eq_zero hs.le]
  ring

theorem measurable_F' (a δ : ℝ) : Measurable (F' a δ) :=
  ((measurable_deriv cut).mul ((measurable_id.add_const _).pow_const _)).add
    (contDiff_cut.continuous.measurable.mul
      (measurable_const.mul ((measurable_id.add_const _).pow_const _)))

theorem sq_rpow {r : ℝ} (hr : 0 ≤ r) (p : ℝ) : (r ^ 2) ^ p = r ^ (2 * p) := by
  rw [← Real.rpow_natCast_mul hr]
  norm_num

/-- `|F_δ(s)| ≤ s^{-a/2}` for `s > 0`, uniformly in `δ`. -/
theorem abs_F_le {a δ s : ℝ} (ha : 0 ≤ a) (hs : 0 < s) : |F a δ s| ≤ s ^ (-a / 2) := by
  have h1 : 0 < s + δ ^ 2 := by positivity
  have h2 : (s + δ ^ 2) ^ (-a / 2) ≤ s ^ (-a / 2) :=
    Real.rpow_le_rpow_of_nonpos hs (le_add_of_nonneg_right (sq_nonneg δ)) (by linarith)
  have hp := Real.rpow_nonneg h1.le (-a / 2)
  rw [F, abs_mul, abs_of_nonneg (cut_nonneg s), abs_of_nonneg hp]
  calc cut s * (s + δ ^ 2) ^ (-a / 2) ≤ 1 * s ^ (-a / 2) :=
        mul_le_mul (cut_le_one s) h2 hp zero_le_one
    _ = s ^ (-a / 2) := one_mul _

/-- `|F_δ'(s)| ≤ K s^{-a/2} + (a/2) s^{-a/2-1}` for `s > 0`, uniformly in `δ`. -/
theorem abs_F'_le {a δ s K : ℝ} (ha : 0 ≤ a) (hs : 0 < s) (hK : ∀ s, |deriv cut s| ≤ K) :
    |F' a δ s| ≤ K * s ^ (-a / 2) + a / 2 * s ^ (-a / 2 - 1) := by
  have h1 : 0 < s + δ ^ 2 := by positivity
  have hle : s ≤ s + δ ^ 2 := le_add_of_nonneg_right (sq_nonneg δ)
  have h2 : (s + δ ^ 2) ^ (-a / 2) ≤ s ^ (-a / 2) :=
    Real.rpow_le_rpow_of_nonpos hs hle (by linarith)
  have h3 : (s + δ ^ 2) ^ (-a / 2 - 1) ≤ s ^ (-a / 2 - 1) :=
    Real.rpow_le_rpow_of_nonpos hs hle (by linarith)
  have hp1 := Real.rpow_nonneg h1.le (-a / 2)
  have hp2 := Real.rpow_nonneg h1.le (-a / 2 - 1)
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0)
  have ha2 : 0 ≤ a / 2 := by linarith
  calc |F' a δ s| ≤ |deriv cut s * (s + δ ^ 2) ^ (-a / 2)| +
        |cut s * (-a / 2 * (s + δ ^ 2) ^ (-a / 2 - 1))| := abs_add _ _
    _ = |deriv cut s| * (s + δ ^ 2) ^ (-a / 2) +
        cut s * (a / 2 * (s + δ ^ 2) ^ (-a / 2 - 1)) := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hp1, abs_of_nonneg (cut_nonneg s),
          abs_of_nonneg hp2, abs_of_nonpos (by linarith : -a / 2 ≤ 0)]
        ring
    _ ≤ K * s ^ (-a / 2) + 1 * (a / 2 * s ^ (-a / 2 - 1)) :=
        add_le_add (mul_le_mul (hK s) h2 hp1 hK0)
          (mul_le_mul (cut_le_one s) (mul_le_mul_of_nonneg_left h3 ha2)
            (mul_nonneg ha2 hp2) zero_le_one)
    _ = K * s ^ (-a / 2) + a / 2 * s ^ (-a / 2 - 1) := by ring

/-- The regularization parameters `δ_k = 1/(k+1) → 0`. -/
def dseq (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)

theorem dseq_ne_zero (k : ℕ) : dseq k ≠ 0 := by
  unfold dseq
  positivity

theorem tendsto_dseq_sq : Tendsto (fun k => dseq k ^ 2) atTop (𝓝 0) := by
  have h := tendsto_one_div_add_atTop_nhds_zero_nat.pow 2
  rw [zero_pow two_ne_zero] at h
  exact h

theorem tendsto_F (a : ℝ) {s : ℝ} (hs : 0 < s) :
    Tendsto (fun k => F a (dseq k) s) atTop (𝓝 (F a 0 s)) := by
  have h1 : Tendsto (fun k => s + dseq k ^ 2) atTop (𝓝 (s + 0 ^ 2)) := by
    rw [zero_pow two_ne_zero]
    exact tendsto_dseq_sq.const_add s
  have hne : s + (0 : ℝ) ^ 2 ≠ 0 := by positivity
  exact (h1.rpow_const (p := -a / 2) (Or.inl hne)).const_mul (cut s)

theorem tendsto_F' (a : ℝ) {s : ℝ} (hs : 0 < s) :
    Tendsto (fun k => F' a (dseq k) s) atTop (𝓝 (F' a 0 s)) := by
  have h1 : Tendsto (fun k => s + dseq k ^ 2) atTop (𝓝 (s + 0 ^ 2)) := by
    rw [zero_pow two_ne_zero]
    exact tendsto_dseq_sq.const_add s
  have hne : s + (0 : ℝ) ^ 2 ≠ 0 := by positivity
  exact ((h1.rpow_const (p := -a / 2) (Or.inl hne)).const_mul (deriv cut s)).add
    (((h1.rpow_const (p := -a / 2 - 1) (Or.inl hne)).const_mul (-a / 2)).const_mul (cut s))

/-! ### The field, its regularizations and its classical gradient -/

variable {n : ℕ}

/-- The singular field `ψ(x) = χ(|x|) |x|^{-a}` (Lean's convention gives `ψ(0) = 0`). -/
def psi (a : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ := chi ‖x‖ * ‖x‖ ^ (-a)

/-- The regularizations `ψ_δ(x) = F_δ(|x|²) = χ(|x|) (|x|² + δ²)^{-a/2}`. -/
def psiR (a δ : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ := F a δ (‖x‖ ^ 2)

theorem psi_eq_psiR (a : ℝ) : (psi a : EuclideanSpace ℝ (Fin n) → ℝ) = psiR a 0 := by
  funext x
  rw [psi, psiR, F, chi, zero_pow two_ne_zero, add_zero, sq_rpow (norm_nonneg x)]
  congr 2
  ring

theorem psi_of_le_one (a : ℝ) {x : EuclideanSpace ℝ (Fin n)} (hx : ‖x‖ ≤ 1) :
    psi a x = ‖x‖ ^ (-a) := by
  rw [psi, chi_eq_one (norm_nonneg x) hx, one_mul]

theorem psi_of_two_le (a : ℝ) {x : EuclideanSpace ℝ (Fin n)} (hx : 2 ≤ ‖x‖) : psi a x = 0 := by
  rw [psi, chi_eq_zero hx, zero_mul]

theorem psiR_eq_zero (a δ : ℝ) {x : EuclideanSpace ℝ (Fin n)} (hx : 2 < ‖x‖) :
    psiR a δ x = 0 := by
  rw [psiR, F, cut_eq_zero (by nlinarith), zero_mul]

theorem sq_add_pos {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) (δ : ℝ) : 0 < ‖x‖ ^ 2 + δ ^ 2 := by
  have := norm_pos_iff.2 hx
  positivity

theorem contDiff_psiR (a : ℝ) {δ : ℝ} (hδ : δ ≠ 0) :
    ContDiff ℝ ∞ (psiR a δ : EuclideanSpace ℝ (Fin n) → ℝ) := by
  have h1 : ContDiff ℝ ∞ fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ 2 := contDiff_norm_sq ℝ
  have h2 : ContDiff ℝ ∞ fun x : EuclideanSpace ℝ (Fin n) => (‖x‖ ^ 2 + δ ^ 2) ^ (-a / 2) :=
    (h1.add contDiff_const).rpow_const_of_ne fun x => by positivity
  exact (contDiff_cut.comp h1).mul h2

theorem hasCompactSupport_psiR (a δ : ℝ) :
    HasCompactSupport (psiR a δ : EuclideanSpace ℝ (Fin n) → ℝ) :=
  HasCompactSupport.intro (isCompact_closedBall 0 2) fun x hx =>
    psiR_eq_zero a δ (by simpa [mem_closedBall, dist_zero_right] using hx)

/-- `ψ` is `C^∞` away from the origin. -/
theorem contDiffAt_psi (a : ℝ) {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ (psi a) x := by
  rw [psi_eq_psiR]
  have h1 : ContDiff ℝ ∞ fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ 2 := contDiff_norm_sq ℝ
  have h : ContDiffAt ℝ ∞ (fun x : EuclideanSpace ℝ (Fin n) =>
      cut (‖x‖ ^ 2) * (‖x‖ ^ 2 + (0 : ℝ) ^ 2) ^ (-a / 2)) x :=
    (contDiff_cut.comp h1).contDiffAt.mul
      ((h1.add contDiff_const).contDiffAt.rpow_const_of_ne (sq_add_pos hx 0).ne')
  exact h

theorem hasFDerivAt_psiR (a δ : ℝ) (x : EuclideanSpace ℝ (Fin n)) (hx : 0 < ‖x‖ ^ 2 + δ ^ 2) :
    HasFDerivAt (psiR a δ) (F' a δ (‖x‖ ^ 2) • (2 • innerSL ℝ x)) x :=
  (hasDerivAt_F a δ hx).comp_hasFDerivAt x (hasStrictFDerivAt_norm_sq x).hasFDerivAt

theorem fderiv_psiR_apply (a δ : ℝ) (x : EuclideanSpace ℝ (Fin n)) (hx : 0 < ‖x‖ ^ 2 + δ ^ 2)
    (i : Fin n) : fderiv ℝ (psiR a δ) x (ev i) = 2 * F' a δ (‖x‖ ^ 2) * x i := by
  rw [(hasFDerivAt_psiR a δ x hx).fderiv]
  simp [ev, EuclideanSpace.inner_single_right]
  ring

/-- The classical gradient `∇ψ(x) = 2F₀'(|x|²) x` (equal to `0` at the origin). -/
def grad (a : ℝ) (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  (2 * F' a 0 (‖x‖ ^ 2)) • x

/-- The gradient of `ψ` as a vector of `ℂⁿ`: the weak gradient (`isH1`). -/
def gradC (a : ℝ) (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℂ (Fin n) :=
  WithLp.toLp 2 fun i => ((grad a x i : ℝ) : ℂ)

theorem grad_apply (a : ℝ) (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    grad a x i = 2 * F' a 0 (‖x‖ ^ 2) * x i := by
  simp [grad]

theorem gradC_apply (a : ℝ) (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    gradC a x i = ((2 * F' a 0 (‖x‖ ^ 2) * x i : ℝ) : ℂ) := by
  rw [gradC, PiLp.toLp_apply, grad_apply]

/-- Away from the origin, `grad a x` is the classical gradient of `ψ`. -/
theorem hasGradientAt_psi (a : ℝ) {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) :
    HasGradientAt (psi a) (grad a x) x := by
  have h := hasFDerivAt_psiR a 0 x (sq_add_pos hx 0)
  rw [← psi_eq_psiR] at h
  rw [hasGradientAt_iff_hasFDerivAt]
  convert h using 1
  ext v
  simp [grad]
  ring

theorem gradient_psi (a : ℝ) {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) :
    gradient (psi a) x = grad a x :=
  (hasGradientAt_psi a hx).gradient

/-- The complex gradient vector `gradC` is the classical gradient vector `gradVec` of the
complexified field away from the origin. -/
theorem gradC_eq_gradVec (a : ℝ) {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) :
    gradC a x = gradVec (ofRealFn (psi a)) x := by
  have h := sq_add_pos hx 0
  ext i
  rw [psi_eq_psiR, gradVec_ofRealFn_apply (hasFDerivAt_psiR a 0 x h).differentiableAt,
    fderiv_psiR_apply a 0 x h i, gradC_apply]

theorem two_F'_of_lt_one (a : ℝ) {x : EuclideanSpace ℝ (Fin n)} (hx1 : ‖x‖ < 1) :
    2 * F' a 0 (‖x‖ ^ 2) = -a * ‖x‖ ^ (-a - 2) := by
  have hs1 : ‖x‖ ^ 2 < 1 := by nlinarith [norm_nonneg x]
  rw [F', deriv_cut_of_lt_one hs1, cut_eq_one hs1.le, zero_pow two_ne_zero, add_zero]
  simp only [sq_rpow (norm_nonneg x)]
  rw [show 2 * (-a / 2 - 1) = -a - 2 by ring]
  ring

/-- `∇ψ(x) = -a |x|^{-a-2} x` on `|x| < 1`. -/
theorem grad_eq_of_lt_one (a : ℝ) {x : EuclideanSpace ℝ (Fin n)} (hx1 : ‖x‖ < 1) :
    grad a x = (-a * ‖x‖ ^ (-a - 2)) • x := by
  rw [grad, two_F'_of_lt_one a hx1]

/-- On `0 < |x| < 1`, the classical gradient of `ψ` is `-a |x|^{-a-2} x`. -/
theorem gradient_psi_of_lt_one (a : ℝ) {x : EuclideanSpace ℝ (Fin n)} (hx0 : x ≠ 0)
    (hx1 : ‖x‖ < 1) : gradient (psi a) x = (-a * ‖x‖ ^ (-a - 2)) • x := by
  rw [gradient_psi a hx0, grad_eq_of_lt_one a hx1]

/-! ### Integrable majorants -/

/-- The truncated power `|x|^t 1_{|x| ≤ 2}`. -/
def ib (t : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (closedBall (0 : EuclideanSpace ℝ (Fin n)) 2).indicator (fun x => ‖x‖ ^ t) x

theorem ib_nonneg (t : ℝ) (x : EuclideanSpace ℝ (Fin n)) : 0 ≤ ib t x :=
  indicator_nonneg (fun x _ => Real.rpow_nonneg (norm_nonneg x) t) x

theorem ib_of_le {t : ℝ} {x : EuclideanSpace ℝ (Fin n)} (hx : ‖x‖ ≤ 2) : ib t x = ‖x‖ ^ t :=
  indicator_of_mem (mem_closedBall_zero_iff.2 hx) _

theorem ib_of_lt {t : ℝ} {x : EuclideanSpace ℝ (Fin n)} (hx : 2 < ‖x‖) : ib t x = 0 :=
  indicator_of_notMem (fun h => (not_le.2 hx) (mem_closedBall_zero_iff.1 h)) _

theorem measurable_ib (t : ℝ) : Measurable (ib t : EuclideanSpace ℝ (Fin n) → ℝ) :=
  (measurable_norm.pow_const t).indicator measurableSet_closedBall

theorem integrable_ib (hn : 1 ≤ n) {t : ℝ} (ht : -(n : ℝ) < t) :
    Integrable (ib t : EuclideanSpace ℝ (Fin n) → ℝ) volume :=
  integrable_indicator_closedBall_rpow hn ht 2

theorem memLp_ib (hn : 1 ≤ n) {t : ℝ} (ht : -(n : ℝ) < 2 * t) :
    MemLp (ib t : EuclideanSpace ℝ (Fin n) → ℝ) 2 volume := by
  rw [memLp_two_iff_integrable_sq (measurable_ib t).aestronglyMeasurable]
  refine (integrable_ib hn ht).congr (Eventually.of_forall fun x => ?_)
  show ib (2 * t) x = ib t x ^ 2
  by_cases hx : ‖x‖ ≤ 2
  · rw [ib_of_le hx, ib_of_le hx, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg x)]
    congr 1
    push_cast
    ring
  · rw [ib_of_lt (not_le.1 hx), ib_of_lt (not_le.1 hx)]
    norm_num

theorem ae_ne_zero (hn : 1 ≤ n) : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), x ≠ 0 := by
  haveI := nontrivial_euclidean hn
  simpa using (Set.countable_singleton (0 : EuclideanSpace ℝ (Fin n))).ae_notMem volume

theorem abs_apply_le_norm (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) : |x i| ≤ ‖x‖ := by
  simpa [Real.norm_eq_abs] using PiLp.norm_apply_le x i

/-- `|ψ_δ(x)| ≤ |x|^{-a} 1_{|x| ≤ 2}` for `x ≠ 0`, uniformly in `δ`. -/
theorem abs_psiR_le {a : ℝ} (ha : 0 ≤ a) (δ : ℝ) {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) :
    |psiR a δ x| ≤ ib (-a) x := by
  by_cases h2 : ‖x‖ ≤ 2
  · rw [ib_of_le h2, psiR]
    have hs : 0 < ‖x‖ ^ 2 := pow_pos (norm_pos_iff.2 hx) 2
    calc |F a δ (‖x‖ ^ 2)| ≤ (‖x‖ ^ 2) ^ (-a / 2) := abs_F_le ha hs
      _ = ‖x‖ ^ (-a) := by rw [sq_rpow (norm_nonneg x)]; congr 1; ring
  · rw [ib_of_lt (not_le.1 h2), psiR_eq_zero a δ (not_le.1 h2), abs_zero]

/-- `|∇ψ_δ(x)| = |2F_δ'(|x|²)| |x| ≤ (2K|x|^{1-a} + a|x|^{-a-1}) 1_{|x| ≤ 2}` for `x ≠ 0`,
uniformly in `δ`. -/
theorem abs_dpsi_le {a K : ℝ} (ha : 0 ≤ a) (hK : ∀ s, |deriv cut s| ≤ K) (δ : ℝ)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) :
    |2 * F' a δ (‖x‖ ^ 2)| * ‖x‖ ≤ 2 * K * ib (1 - a) x + a * ib (-a - 1) x := by
  have hr : 0 < ‖x‖ := norm_pos_iff.2 hx
  by_cases h2 : ‖x‖ ≤ 2
  · rw [ib_of_le h2, ib_of_le h2]
    have h := abs_F'_le (δ := δ) ha (pow_pos hr 2) hK
    rw [sq_rpow hr.le, sq_rpow hr.le] at h
    have e1 : ‖x‖ ^ (1 - a) = ‖x‖ ^ (2 * (-a / 2)) * ‖x‖ := by
      rw [← Real.rpow_add_one hr.ne']
      congr 1
      ring
    have e2 : ‖x‖ ^ (-a - 1) = ‖x‖ ^ (2 * (-a / 2 - 1)) * ‖x‖ := by
      rw [← Real.rpow_add_one hr.ne']
      congr 1
      ring
    rw [e1, e2, abs_mul, abs_two]
    have := mul_le_mul_of_nonneg_right h hr.le
    linarith
  · have h2' := not_le.1 h2
    rw [ib_of_lt h2', ib_of_lt h2', F'_eq_zero a δ (by nlinarith)]
    simp

theorem measurable_psi (a : ℝ) : Measurable (psi a : EuclideanSpace ℝ (Fin n) → ℝ) :=
  (contDiff_chi.continuous.measurable.comp measurable_norm).mul (measurable_norm.pow_const _)

theorem measurable_dpsi (a δ : ℝ) (i : Fin n) :
    Measurable fun x : EuclideanSpace ℝ (Fin n) => 2 * F' a δ (‖x‖ ^ 2) * x i :=
  (measurable_const.mul ((measurable_F' a δ).comp (measurable_norm.pow_const 2))).mul
    (by fun_prop : Continuous fun x : EuclideanSpace ℝ (Fin n) => x i).measurable

theorem two_lt_of {a : ℝ} (ha : 0 < a) (ha' : a < ((n : ℝ) - 2) / 2) : 2 < n := by
  have : (2 : ℝ) < n := by linarith
  exact_mod_cast this

/-- `ψ ∈ L²(ℝⁿ)`. -/
theorem memLp_psi {a : ℝ} (ha : 0 < a) (ha' : a < ((n : ℝ) - 2) / 2) :
    MemLp (psi a : EuclideanSpace ℝ (Fin n) → ℝ) 2 volume := by
  have hn : 1 ≤ n := by have := two_lt_of ha ha'; omega
  refine (memLp_ib hn (t := -a) (by linarith)).of_le (measurable_psi a).aestronglyMeasurable ?_
  filter_upwards [ae_ne_zero hn] with x hx
  rw [psi_eq_psiR, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (ib_nonneg _ _)]
  exact abs_psiR_le ha.le 0 hx

/-- Each component of the gradient is in `L²(ℝⁿ)` (here `a < (n-2)/2` is used). -/
theorem memLp_gradC_apply {a : ℝ} (ha : 0 < a) (ha' : a < ((n : ℝ) - 2) / 2) (i : Fin n) :
    MemLp (fun x => gradC a x i) 2 volume := by
  have hn : 1 ≤ n := by have := two_lt_of ha ha'; omega
  obtain ⟨K, hK0, hK⟩ := exists_bound_deriv_cut
  have hM : MemLp (fun x : EuclideanSpace ℝ (Fin n) =>
      2 * K * ib (1 - a) x + a * ib (-a - 1) x) 2 volume :=
    ((memLp_ib hn (t := 1 - a) (by linarith)).const_mul (2 * K)).add
      ((memLp_ib hn (t := -a - 1) (by linarith)).const_mul a)
  have hmeas : AEStronglyMeasurable (fun x => gradC a x i) volume := by
    simp_rw [gradC_apply]
    exact (Complex.measurable_ofReal.comp (measurable_dpsi a 0 i)).aestronglyMeasurable
  refine hM.of_le hmeas ?_
  filter_upwards [ae_ne_zero hn] with x hx
  have hM0 : 0 ≤ 2 * K * ib (1 - a) x + a * ib (-a - 1) x :=
    add_nonneg (mul_nonneg (by linarith) (ib_nonneg _ _)) (mul_nonneg ha.le (ib_nonneg _ _))
  rw [gradC_apply, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hM0,
    abs_mul]
  exact (mul_le_mul_of_nonneg_left (abs_apply_le_norm x i) (abs_nonneg _)).trans
    (abs_dpsi_le ha.le hK 0 hx)

/-- `∇ψ ∈ L²(ℝⁿ; ℂⁿ)`. -/
theorem memLp_gradC {a : ℝ} (ha : 0 < a) (ha' : a < ((n : ℝ) - 2) / 2) :
    MemLp (gradC a : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin n)) 2 volume :=
  MemLp.of_eval_piLp fun i => memLp_gradC_apply ha ha' i

/-! ### The weak derivative across the origin -/

/-- **The distributional extension across the origin.** For every coordinate `i` and every
real test function `φ ∈ C_c^∞(ℝⁿ)`, including those whose support contains `0`,
`∫ ψ ∂ᵢφ = -∫ (∂ᵢψ) φ`, where `∂ᵢψ` is the classical derivative off the origin.

Proof: `ψ_δ` is `C^∞` with compact support for `δ ≠ 0`, so integration by parts holds for
`ψ_δ`; both sides converge as `δ_k → 0` by dominated convergence. -/
theorem weak_deriv {a : ℝ} (ha : 0 < a) (ha' : a < ((n : ℝ) - 2) / 2) (i : Fin n)
    (φ : EuclideanSpace ℝ (Fin n) → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    ∫ x, ofRealFn (psi a) x * ((fderiv ℝ φ x (ev i) : ℝ) : ℂ) =
      -∫ x, gradC a x i * ((φ x : ℝ) : ℂ) := by
  have hn : 1 ≤ n := by have := two_lt_of ha ha'; omega
  have hae := ae_ne_zero hn
  obtain ⟨K, hK0, hK⟩ := exists_bound_deriv_cut
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by exact_mod_cast le_top)
  have hdφ : Continuous fun x => fderiv ℝ φ x (ev i) :=
    (hφ1.continuous_fderiv le_rfl).clm_apply continuous_const
  obtain ⟨C1, hC1⟩ :=
    hdφ.bounded_above_of_compact_support (hasCompactSupport_fderiv_apply hφc (ev i))
  obtain ⟨C2, hC2⟩ := hφ.continuous.bounded_above_of_compact_support hφc
  -- integration by parts for each smooth regularization
  have hk : ∀ k, (∫ x, ofRealFn (psiR a (dseq k)) x * ((fderiv ℝ φ x (ev i) : ℝ) : ℂ)) =
      -∫ x, ((2 * F' a (dseq k) (‖x‖ ^ 2) * x i : ℝ) : ℂ) * ((φ x : ℝ) : ℂ) := by
    intro k
    have hc := contDiff_psiR a (n := n) (dseq_ne_zero k)
    rw [(isH1_ofRealFn (hc.of_le (by exact_mod_cast le_top))
      (hasCompactSupport_psiR a (dseq k))).weak i φ hφ hφc]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    have hx : 0 < ‖x‖ ^ 2 + dseq k ^ 2 := by have := dseq_ne_zero k; positivity
    simp only
    rw [gradVec_ofRealFn_apply ((hc.differentiable (by simp)) x),
      fderiv_psiR_apply a (dseq k) x hx i]
  -- the left-hand sides converge
  have hL : Tendsto (fun k => ∫ x, ofRealFn (psiR a (dseq k)) x * ((fderiv ℝ φ x (ev i) : ℝ) : ℂ))
      atTop (𝓝 (∫ x, ofRealFn (psiR a 0) x * ((fderiv ℝ φ x (ev i) : ℝ) : ℂ))) := by
    refine tendsto_integral_of_dominated_convergence (fun x => ib (-a) x * C1) (fun k => ?_)
      ((integrable_ib hn (t := -a) (by linarith)).mul_const C1) (fun k => ?_) ?_
    · exact ((Complex.continuous_ofReal.comp (contDiff_psiR a (dseq_ne_zero k)).continuous).mul
        (Complex.continuous_ofReal.comp hdφ)).aestronglyMeasurable
    · filter_upwards [hae] with x hx
      rw [norm_mul, ofRealFn, Complex.norm_real, Complex.norm_real]
      exact mul_le_mul (by rw [Real.norm_eq_abs]; exact abs_psiR_le ha.le _ hx) (hC1 x)
        (norm_nonneg _) (ib_nonneg _ _)
    · filter_upwards [hae] with x hx
      exact ((Complex.continuous_ofReal.tendsto _).comp
        (tendsto_F a (pow_pos (norm_pos_iff.2 hx) 2))).mul_const _
  -- the right-hand sides converge
  have hR : Tendsto (fun k => ∫ x, ((2 * F' a (dseq k) (‖x‖ ^ 2) * x i : ℝ) : ℂ) *
      ((φ x : ℝ) : ℂ)) atTop (𝓝 (∫ x, gradC a x i * ((φ x : ℝ) : ℂ))) := by
    refine tendsto_integral_of_dominated_convergence
      (fun x => (2 * K * ib (1 - a) x + a * ib (-a - 1) x) * C2) (fun k => ?_) ?_ (fun k => ?_) ?_
    · exact ((Complex.measurable_ofReal.comp (measurable_dpsi a (dseq k) i)).mul
        (Complex.continuous_ofReal.comp hφ.continuous).measurable).aestronglyMeasurable
    · exact (((integrable_ib hn (t := 1 - a) (by linarith)).const_mul (2 * K)).add
        ((integrable_ib hn (t := -a - 1) (by linarith)).const_mul a)).mul_const C2
    · filter_upwards [hae] with x hx
      have hM0 : 0 ≤ 2 * K * ib (1 - a) x + a * ib (-a - 1) x :=
        add_nonneg (mul_nonneg (by linarith) (ib_nonneg _ _)) (mul_nonneg ha.le (ib_nonneg _ _))
      rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs (2 * _ * _), abs_mul]
      exact mul_le_mul ((mul_le_mul_of_nonneg_left (abs_apply_le_norm x i) (abs_nonneg _)).trans
        (abs_dpsi_le ha.le hK _ hx)) (hC2 x) (norm_nonneg _) hM0
    · filter_upwards [hae] with x hx
      simp_rw [gradC_apply]
      exact ((Complex.continuous_ofReal.tendsto _).comp
        (((tendsto_F' a (pow_pos (norm_pos_iff.2 hx) 2)).const_mul 2).mul_const (x i))).mul_const _
  have hR' := hR.neg
  rw [show (fun k => -∫ x, ((2 * F' a (dseq k) (‖x‖ ^ 2) * x i : ℝ) : ℂ) * ((φ x : ℝ) : ℂ)) =
      fun k => ∫ x, ofRealFn (psiR a (dseq k)) x * ((fderiv ℝ φ x (ev i) : ℝ) : ℂ) from
      funext fun k => (hk k).symm] at hR'
  rw [psi_eq_psiR]
  exact tendsto_nhds_unique hL hR'

/-- **`ψ ∈ H¹(ℝⁿ)`**, with weak gradient `gradC a`, for `0 < a < (n-2)/2`. -/
theorem isH1 {a : ℝ} (ha : 0 < a) (ha' : a < ((n : ℝ) - 2) / 2) :
    IsH1 (ofRealFn (psi a) : EuclideanSpace ℝ (Fin n) → ℂ) (gradC a) where
  memLp := (memLp_psi ha ha').ofReal
  memLp_grad := memLp_gradC ha ha'
  weak i φ hφ hφc := weak_deriv ha ha' i φ hφ hφc

/-! ### Exact radial integrals -/

/-- `σ_{n-1}`, the surface measure of the unit sphere `Sⁿ⁻¹ ⊂ ℝⁿ`. -/
def surfaceArea (n : ℕ) : ℝ :=
  (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere.real univ

/-- `σ_{n-1} = n ω_n`, with `ω_n = |B₁|`. -/
theorem surfaceArea_eq (n : ℕ) :
    surfaceArea n = n * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
  rw [surfaceArea, sphereArea_eq, finrank_euclidean]

theorem volume_real_ball_pos (n : ℕ) :
    0 < volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
  rw [measureReal_def]
  exact ENNReal.toReal_pos (measure_ball_pos volume 0 one_pos).ne' measure_ball_lt_top.ne

theorem norm_gradC_sq (a : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    ‖gradC a x‖ ^ 2 = (2 * F' a 0 (‖x‖ ^ 2)) ^ 2 * ‖x‖ ^ 2 := by
  have h1 : ‖gradC a x‖ ^ 2 = ∑ i, (2 * F' a 0 (‖x‖ ^ 2)) ^ 2 * x i ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq (gradC a x)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [gradC_apply, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    ring
  have h2 : ‖x‖ ^ 2 = ∑ i, x i ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq x]
    exact Finset.sum_congr rfl fun i _ => by rw [Real.norm_eq_abs, sq_abs]
  rw [h1, ← Finset.mul_sum, ← h2]

/-- `|∇ψ(x)|² = a² |x|^{-2a-2}` on `|x| < 1` (both sides vanish at `x = 0`). -/
theorem norm_gradC_sq_of_lt_one {a : ℝ} (ha : 0 < a) {x : EuclideanSpace ℝ (Fin n)}
    (hx1 : ‖x‖ < 1) : ‖gradC a x‖ ^ 2 = a ^ 2 * ‖x‖ ^ (-2 * a - 2) := by
  rw [norm_gradC_sq, two_F'_of_lt_one a hx1]
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [norm_zero, Real.zero_rpow (ne_of_lt (by linarith : -a - 2 < 0)),
      Real.zero_rpow (ne_of_lt (by linarith : -2 * a - 2 < 0))]
    ring
  · have hr := norm_pos_iff.2 hx0
    rw [mul_pow, neg_sq, ← Real.rpow_natCast (‖x‖ ^ (-a - 2)) 2, ← Real.rpow_mul hr.le,
      mul_assoc, ← Real.rpow_natCast ‖x‖ 2, ← Real.rpow_add hr]
    congr 2
    push_cast
    ring

/-- `∫_{B_R} |ψ|² = n ω_n R^{n-2a}/(n-2a)` for `0 < R ≤ 1`. -/
theorem integral_sq_ball {a : ℝ} (ha : 0 < a) (ha' : a < ((n : ℝ) - 2) / 2) {R : ℝ}
    (hR : 0 < R) (hR1 : R ≤ 1) :
    (∫ x in ball (0 : EuclideanSpace ℝ (Fin n)) R, ‖ofRealFn (psi a) x‖ ^ 2) =
      n * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1) *
        (R ^ ((n : ℝ) - 2 * a) / ((n : ℝ) - 2 * a)) := by
  have hn : 1 ≤ n := by have := two_lt_of ha ha'; omega
  have h : EqOn (fun x : EuclideanSpace ℝ (Fin n) => ‖ofRealFn (psi a) x‖ ^ 2)
      (fun x => ‖x‖ ^ (-2 * a)) (ball 0 R) := by
    intro x hx
    have hx1 : ‖x‖ ≤ 1 := (mem_ball_zero_iff.1 hx).le.trans hR1
    simp only
    rw [norm_ofRealFn, psi_of_le_one a hx1, ← Real.rpow_natCast,
      ← Real.rpow_mul (norm_nonneg x)]
    congr 1
    push_cast
    ring
  rw [setIntegral_congr_fun measurableSet_ball h,
    setIntegral_ball_rpow hn (t := -2 * a) (by linarith) hR,
    show (n : ℝ) + -2 * a = (n : ℝ) - 2 * a by ring]

/-- `∫_{B_R} |∇ψ|² = a² n ω_n R^{n-2-2a}/(n-2-2a)` for `0 < R ≤ 1`. -/
theorem integral_grad_sq_ball {a : ℝ} (ha : 0 < a) (ha' : a < ((n : ℝ) - 2) / 2) {R : ℝ}
    (hR : 0 < R) (hR1 : R ≤ 1) :
    (∫ x in ball (0 : EuclideanSpace ℝ (Fin n)) R, ‖gradC a x‖ ^ 2) =
      a ^ 2 * (n * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1) *
        (R ^ ((n : ℝ) - 2 - 2 * a) / ((n : ℝ) - 2 - 2 * a))) := by
  have hn : 1 ≤ n := by have := two_lt_of ha ha'; omega
  have h : EqOn (fun x : EuclideanSpace ℝ (Fin n) => ‖gradC a x‖ ^ 2)
      (fun x => a ^ 2 * ‖x‖ ^ (-2 * a - 2)) (ball 0 R) :=
    fun x hx => norm_gradC_sq_of_lt_one ha ((mem_ball_zero_iff.1 hx).trans_le hR1)
  rw [setIntegral_congr_fun measurableSet_ball h, integral_const_mul,
    setIntegral_ball_rpow hn (t := -2 * a - 2) (by linarith) hR,
    show (n : ℝ) + (-2 * a - 2) = (n : ℝ) - 2 - 2 * a by ring]

/-- **Manuscript formula.** `∫_{B₁} |ψ|² = σ_{n-1}/(n-2a)`. -/
theorem integral_sq_ball_one {a : ℝ} (ha : 0 < a) (ha' : a < ((n : ℝ) - 2) / 2) :
    (∫ x in ball (0 : EuclideanSpace ℝ (Fin n)) 1, ‖ofRealFn (psi a) x‖ ^ 2) =
      surfaceArea n / ((n : ℝ) - 2 * a) := by
  rw [integral_sq_ball ha ha' one_pos le_rfl, Real.one_rpow, surfaceArea_eq]
  ring

/-- **Manuscript formula.** `∫_{B₁} |∇ψ|² = σ_{n-1} a²/(n-2-2a)`. -/
theorem integral_grad_sq_ball_one {a : ℝ} (ha : 0 < a) (ha' : a < ((n : ℝ) - 2) / 2) :
    (∫ x in ball (0 : EuclideanSpace ℝ (Fin n)) 1, ‖gradC a x‖ ^ 2) =
      surfaceArea n * a ^ 2 / ((n : ℝ) - 2 - 2 * a) := by
  rw [integral_grad_sq_ball ha ha' one_pos le_rfl, Real.one_rpow, surfaceArea_eq]
  ring

/-- **Manuscript formula.** `∫_{B_R} |∇ψ|² = σ_{n-1} a² R^{n-2-2a}/(n-2-2a)` for `0 < R < 1`. -/
theorem integral_grad_sq_ball_sphere {a : ℝ} (ha : 0 < a) (ha' : a < ((n : ℝ) - 2) / 2)
    {R : ℝ} (hR : 0 < R) (hR1 : R < 1) :
    (∫ x in ball (0 : EuclideanSpace ℝ (Fin n)) R, ‖gradC a x‖ ^ 2) =
      surfaceArea n * a ^ 2 * R ^ ((n : ℝ) - 2 - 2 * a) / ((n : ℝ) - 2 - 2 * a) := by
  rw [integral_grad_sq_ball ha ha' hR hR1.le, surfaceArea_eq]
  ring

/-! ### Blow-up of the scale-invariant energy -/

theorem tendsto_rpow_neg_nhdsGT {y : ℝ} (hy : 0 < y) :
    Tendsto (fun R : ℝ => R ^ (-y)) (𝓝[>] 0) atTop := by
  refine ((tendsto_rpow_atTop hy).comp tendsto_inv_nhdsGT_zero).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with R hR
  simp only [Function.comp_apply]
  rw [Real.inv_rpow (le_of_lt hR), Real.rpow_neg (le_of_lt hR)]

/-- **Blow-up.** `R^{2-n} ∫_{B_R} |∇ψ|² = σ_{n-1} a² R^{-2a}/(n-2-2a) → +∞` as `R ↓ 0`. -/
theorem blowup {a : ℝ} (ha : 0 < a) (ha' : a < ((n : ℝ) - 2) / 2) :
    Tendsto (fun R : ℝ => R ^ ((2 : ℤ) - n) *
      ∫ x in ball (0 : EuclideanSpace ℝ (Fin n)) R, ‖gradC a x‖ ^ 2) (𝓝[>] 0) atTop := by
  have hn : 2 < n := two_lt_of ha ha'
  have hd : 0 < (n : ℝ) - 2 - 2 * a := by linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  set c : ℝ := a ^ 2 * (n * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1) /
    ((n : ℝ) - 2 - 2 * a)) with hc
  have hcpos : 0 < c :=
    mul_pos (pow_pos ha 2) (div_pos (mul_pos hn0 (volume_real_ball_pos n)) hd)
  refine ((tendsto_rpow_neg_nhdsGT (y := 2 * a) (by linarith)).const_mul_atTop hcpos).congr' ?_
  filter_upwards [Ioo_mem_nhdsGT one_pos] with R hR
  rw [integral_grad_sq_ball ha ha' hR.1 hR.2.le, ← Real.rpow_intCast]
  have key : R ^ (((2 - n : ℤ)) : ℝ) * R ^ ((n : ℝ) - 2 - 2 * a) = R ^ (-(2 * a)) := by
    rw [← Real.rpow_add hR.1]
    congr 1
    push_cast
    ring
  rw [← key, hc]
  ring

/-- **One fixed field defeats every constant.** For every proposed constant `C`, the
inequality `∫_{B_R} |∇ψ|² ≤ C R^{n-2} ‖ψ‖²_{H¹}` fails for all sufficiently small `R > 0`. -/
theorem no_constant {a : ℝ} (ha : 0 < a) (ha' : a < ((n : ℝ) - 2) / 2) (C : ℝ) :
    ∀ᶠ R in 𝓝[>] (0 : ℝ), C * R ^ ((n : ℤ) - 2) * h1sq (n := n) (ofRealFn (psi a)) (gradC a) <
      ∫ x in ball (0 : EuclideanSpace ℝ (Fin n)) R, ‖gradC a x‖ ^ 2 := by
  filter_upwards [(blowup ha ha').eventually_gt_atTop
    (C * h1sq (n := n) (ofRealFn (psi a)) (gradC a)), self_mem_nhdsWithin] with R hR hR0
  have hpos : 0 < R ^ ((n : ℤ) - 2) := zpow_pos hR0 _
  have hinv : R ^ ((2 : ℤ) - n) = (R ^ ((n : ℤ) - 2))⁻¹ := by
    rw [← zpow_neg]
    congr 1
    ring
  rw [hinv] at hR
  calc C * R ^ ((n : ℤ) - 2) * h1sq (n := n) (ofRealFn (psi a)) (gradC a) =
      R ^ ((n : ℤ) - 2) * (C * h1sq (n := n) (ofRealFn (psi a)) (gradC a)) := by ring
    _ < _ := (lt_inv_mul_iff₀ hpos).1 hR

/-- The same fixed field defeats every constant at arbitrarily small radii. -/
theorem defeats_every_constant {a : ℝ} (ha : 0 < a) (ha' : a < ((n : ℝ) - 2) / 2)
    (C ε : ℝ) (hε : 0 < ε) :
    ∃ R, 0 < R ∧ R < ε ∧ C * R ^ ((n : ℤ) - 2) * h1sq (n := n) (ofRealFn (psi a)) (gradC a) <
      ∫ x in ball (0 : EuclideanSpace ℝ (Fin n)) R, ‖gradC a x‖ ^ 2 := by
  obtain ⟨R, hR, hRε⟩ := ((no_constant ha ha' C).and (Ioo_mem_nhdsGT hε)).exists
  exact ⟨R, hRε.1, hRε.2, hR⟩

/-- **`E68(n)` fails for `n > 2`, witnessed by one fixed `H¹` field** (here `a = (n-2)/4`). -/
theorem not_e68 (hn : 2 < n) : ¬ E68Holds n := by
  rintro ⟨C, hC⟩
  have h2 : (2 : ℝ) < n := by exact_mod_cast hn
  have ha : (0 : ℝ) < ((n : ℝ) - 2) / 4 := by linarith
  have ha' : ((n : ℝ) - 2) / 4 < ((n : ℝ) - 2) / 2 := by linarith
  obtain ⟨R, hR0, -, hR⟩ := defeats_every_constant ha ha' C 1 one_pos
  exact absurd (hC _ _ (isH1 ha ha') 0 R hR0) (not_le.2 hR)

end Singular

end ReyesMath.E68
