import Mathlib

/-!
# Non-invariance of finite Fourier coordinate subspaces (F04)

Formalization of the nonlinear-coefficient and leakage statements of
`papers/finite-fourier-coordinate-subspace-noninvariance/main.tex` for the unprojected
equation `i∂ₜu = (Δ + κ²)²u − β|u|²u + γ|u|⁴u` on `𝕋^d = (ℝ/2πℤ)^d`, with Mathlib's
Laplacian `Δ` on `EuclideanSpace ℝ (Fin d)` and Fourier coefficients
`f̂(n) = (2π)^{−d} ∫_{[0,2π]^d} f e^{−in·x}` defined by Lebesgue integrals.

* `coeff_E`, `coeff_trig`, `laplacian_E`, `shiftLap_shiftLap_trig`: orthogonality of the
  modes and the diagonal action `(Δ+κ²)² e^{in·x} = (κ² − |n|²)² e^{in·x}`.
* `cubic_trig`, `quintic_trig`, `coeff_cubic_leak`, `coeff_quintic_leak`: exact Fourier
  convolutions; at the extremal frequency `r = 3p − 2q` (lexicographic maximum `p` and
  minimum `q`), the cubic coefficient vanishes and the quintic one is exactly `c_p³ ar c_q²`.
* `IsClassicalSolution`, `hasDerivAt_coeff`: classical solutions on `(−τ, τ) × 𝕋^d` and
  differentiation of their Fourier coefficients under the integral sign.
* `universal_leakage` (Theorem 2), `no_multimode_invariance` (Theorem 1),
  `fifth_harmonic` (Proposition): for **every** classical solution launched from the
  stated data, `û(r,0) = 0`, `∂ₜû(r,0) = −iγ c_p³ ar c_q² ≠ 0`, and `u(t) ∉ E_S` for all
  sufficiently small `t ≠ 0`; for `cos x`, `û(5,t) = −(iγ/32)t + o(t)`.
* `singleMode_isClassicalSolution`, `singleMode_mem`: each single-mode subspace carries the
  exact solution `A₀ e^{−iΩt} e^{ip·x}`.

Local existence of classical solutions for multimode trigonometric data, and uniqueness
of classical solutions (needed for the invariance direction `|S| ≤ 1` of the
classification corollary), are not formalized in this module.
-/

open MeasureTheory Set Filter Topology Complex InnerProductSpace

namespace ReyesMath

namespace FourierLeakage

variable {d : ℕ}

local notation "Rd" => EuclideanSpace ℝ (Fin d)

/-- A lattice frequency as a real vector. -/
noncomputable def freq (n : Fin d → ℤ) : Rd := (EuclideanSpace.equiv (Fin d) ℝ).symm fun j => (n j : ℝ)

@[simp] theorem freq_apply (n : Fin d → ℤ) (j : Fin d) : freq n j = (n j : ℝ) := by
  simp [freq]

theorem freq_add (m n : Fin d → ℤ) : freq (m + n) = freq m + freq n := by
  ext j
  simp

theorem freq_neg (n : Fin d → ℤ) : freq (-n) = -freq n := by
  ext j
  simp

theorem freq_sub (m n : Fin d → ℤ) : freq (m - n) = freq m - freq n := by
  ext j
  simp

/-- `|n|²`. -/
noncomputable def nsq (n : Fin d → ℤ) : ℝ := ∑ j, ((n j : ℝ)) ^ 2

/-- The Fourier mode `e^{i n·x}`. -/
noncomputable def E (n : Fin d → ℤ) (x : Rd) : ℂ :=
  Complex.exp ((inner ℝ (freq n) x : ℝ) * Complex.I)

theorem E_add (m n : Fin d → ℤ) (x : Rd) : E (m + n) x = E m x * E n x := by
  simp only [E, freq_add, inner_add_left, Complex.ofReal_add, add_mul, Complex.exp_add]

theorem E_neg (n : Fin d → ℤ) (x : Rd) : E (-n) x = (starRingEnd ℂ) (E n x) := by
  rw [E, E, ← Complex.exp_conj, freq_neg, inner_neg_left]
  congr 1
  simp

theorem E_sub (m n : Fin d → ℤ) (x : Rd) : E (m - n) x = E m x * (starRingEnd ℂ) (E n x) := by
  rw [sub_eq_add_neg, E_add, E_neg]

theorem norm_E (n : Fin d → ℤ) (x : Rd) : ‖E n x‖ = 1 := by
  rw [E, Complex.norm_exp_ofReal_mul_I]

theorem freq_zero : freq (0 : Fin d → ℤ) = 0 := by
  ext j
  simp

theorem E_zero_freq (x : Rd) : E (0 : Fin d → ℤ) x = 1 := by
  simp [E, freq_zero]

theorem continuous_E (n : Fin d → ℤ) : Continuous (E n) := by
  unfold E
  fun_prop

/-- `∂E_n = i E_n ⟨n, ·⟩`. -/
theorem hasFDerivAt_E (n : Fin d → ℤ) (x : Rd) :
    HasFDerivAt (E n) ((E n x * Complex.I) • (Complex.ofRealCLM.comp (innerSL ℝ (freq n)))) x := by
  have h1 : HasFDerivAt (fun y : Rd => ((inner ℝ (freq n) y : ℝ) : ℂ) * Complex.I)
      ((Complex.ofRealCLM.comp (innerSL ℝ (freq n))).smulRight Complex.I) x := by
    have := ((innerSL ℝ (freq n)).hasFDerivAt (x := x))
    have h2 := (Complex.ofRealCLM.hasFDerivAt (x := inner ℝ (freq n) x)).comp x this
    convert h2.mul_const Complex.I using 1
    ext v
    simp [mul_comm]
  have := h1.cexp
  convert this using 1
  ext v
  simp [E]
  ring

theorem fderiv_E (n : Fin d → ℤ) :
    fderiv ℝ (E n) = fun x =>
      (E n x * Complex.I) • (Complex.ofRealCLM.comp (innerSL ℝ (freq n))) :=
  funext fun x => (hasFDerivAt_E n x).fderiv

theorem fderiv_fderiv_E_apply (n : Fin d → ℤ) (x v w : Rd) :
    fderiv ℝ (fderiv ℝ (E n)) x v w =
      -(E n x) * ((inner ℝ (freq n) v : ℝ) : ℂ) * ((inner ℝ (freq n) w : ℝ) : ℂ) := by
  rw [fderiv_E]
  have h := ((hasFDerivAt_E n x).mul_const Complex.I).smul_const
    (Complex.ofRealCLM.comp (innerSL ℝ (freq n)))
  rw [h.fderiv]
  simp
  ring_nf
  rw [Complex.I_sq]
  ring

/-- `Δ e^{in·x} = −|n|² e^{in·x}` for Mathlib's Laplacian. -/
theorem laplacian_E (n : Fin d → ℤ) (x : Rd) : Δ (E n) x = -(nsq n : ℂ) * E n x := by
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis (E n) (EuclideanSpace.basisFun (Fin d) ℝ)]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    fderiv_fderiv_E_apply]
  simp only [EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_right, freq_apply,
    conj_trivial, one_mul]
  unfold nsq
  push_cast
  rw [neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-! ### Fourier coefficients on the torus `(ℝ/2πℤ)^d` -/

/-- The fundamental cube `[0, 2π]^d`, in coordinates. -/
def cube (d : ℕ) : Set (Fin d → ℝ) := Set.univ.pi fun _ => Set.Icc 0 (2 * Real.pi)

/-- Coordinates of a point of `ℝ^d`. -/
noncomputable def toE (y : Fin d → ℝ) : Rd := (EuclideanSpace.equiv (Fin d) ℝ).symm y

@[simp] theorem toE_apply (y : Fin d → ℝ) (j : Fin d) : toE y j = y j := by simp [toE]

/-- The Fourier coefficient on `(ℝ/2πℤ)^d`:
`f̂(n) = (2π)^{−d} ∫_{[0,2π]^d} f(x) e^{−i n·x} dx`. -/
noncomputable def coeff (f : Rd → ℂ) (n : Fin d → ℤ) : ℂ :=
  ((2 * Real.pi : ℂ) ^ d)⁻¹ * ∫ y in cube d, f (toE y) * E (-n) (toE y)

theorem E_toE (k : Fin d → ℤ) (y : Fin d → ℝ) :
    E k (toE y) = ∏ j, Complex.exp (((k j : ℝ) * y j : ℝ) * Complex.I) := by
  rw [E, ← Complex.exp_sum]
  congr 1
  simp only [PiLp.inner_apply, freq_apply, toE_apply, RCLike.inner_apply, conj_trivial]
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem integral_exp_int (k : ℤ) :
    ∫ t in Set.Icc (0:ℝ) (2 * Real.pi), Complex.exp (((k : ℝ) * t : ℝ) * Complex.I) =
      if k = 0 then (2 * Real.pi : ℂ) else 0 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by positivity)]
  split_ifs with hk
  · subst hk
    simp
  · have hc : (k : ℂ) * Complex.I ≠ 0 := mul_ne_zero (by exact_mod_cast hk) Complex.I_ne_zero
    have := integral_exp_mul_complex (a := 0) (b := 2 * Real.pi) hc
    have h2 : Complex.exp ((k : ℂ) * Complex.I * ((2 * Real.pi : ℝ) : ℂ)) = 1 := by
      rw [show (k : ℂ) * Complex.I * ((2 * Real.pi : ℝ) : ℂ) = k * (2 * Real.pi * Complex.I) by
        push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I k
    calc ∫ t in (0:ℝ)..(2 * Real.pi), Complex.exp (((k : ℝ) * t : ℝ) * Complex.I)
        = ∫ t in (0:ℝ)..(2 * Real.pi), Complex.exp ((k : ℂ) * Complex.I * t) := by
          congr 1
          funext t
          push_cast
          ring_nf
      _ = 0 := by rw [this, h2]; simp

/-- Orthogonality of the Fourier modes on the cube. -/
theorem integral_E (k : Fin d → ℤ) :
    ∫ y in cube d, E k (toE y) = if k = 0 then ((2 * Real.pi : ℂ) ^ d) else 0 := by
  simp_rw [E_toE]
  rw [cube, volume_pi, Measure.restrict_pi_pi,
    integral_fintype_prod_eq_prod (fun j t => Complex.exp (((k j : ℝ) * t : ℝ) * Complex.I))]
  simp_rw [integral_exp_int]
  split_ifs with hk
  · subst hk
    simp
  · obtain ⟨j, hj⟩ : ∃ j, k j ≠ 0 := by
      by_contra h
      push_neg at h
      exact hk (funext h)
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])

theorem coeff_E (m n : Fin d → ℤ) : coeff (E m) n = if m = n then 1 else 0 := by
  have hpt : (fun y => E m (toE y) * E (-n) (toE y)) = fun y => E (m - n) (toE y) := by
    funext y
    rw [← E_add, sub_eq_add_neg]
  rw [coeff, hpt, integral_E]
  have hπ : (2 * Real.pi : ℂ) ^ d ≠ 0 := pow_ne_zero _ (by
    exact_mod_cast (show (2 * Real.pi) ≠ 0 by positivity))
  by_cases h : m = n
  · simp [h, sub_self, hπ]
  · rw [if_neg (sub_ne_zero.2 h), if_neg h, mul_zero]

theorem isCompact_cube : IsCompact (cube d) := isCompact_univ_pi fun _ => isCompact_Icc

theorem continuous_toE : Continuous (toE (d := d)) :=
  (EuclideanSpace.equiv (Fin d) ℝ).symm.continuous

theorem integrableOn_cube {f : Rd → ℂ} (hf : Continuous f) (n : Fin d → ℤ) :
    IntegrableOn (fun y => f (toE y) * E (-n) (toE y)) (cube d) :=
  ((hf.comp continuous_toE).mul ((continuous_E _).comp continuous_toE)).continuousOn
    |>.integrableOn_compact isCompact_cube

theorem coeff_add {f g : Rd → ℂ} (hf : Continuous f) (hg : Continuous g) (n : Fin d → ℤ) :
    coeff (fun x => f x + g x) n = coeff f n + coeff g n := by
  unfold coeff
  rw [← mul_add, ← integral_add (integrableOn_cube hf n) (integrableOn_cube hg n)]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  ring

theorem coeff_const_mul (c : ℂ) (f : Rd → ℂ) (n : Fin d → ℤ) :
    coeff (fun x => c * f x) n = c * coeff f n := by
  unfold coeff
  simp_rw [mul_assoc, integral_const_mul]
  ring

theorem coeff_sum {ι : Type*} (s : Finset ι) {f : ι → Rd → ℂ} (hf : ∀ i, Continuous (f i))
    (n : Fin d → ℤ) : coeff (fun x => ∑ i ∈ s, f i x) n = ∑ i ∈ s, coeff (f i) n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [coeff]
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [coeff_add (hf a) (continuous_finset_sum _ fun i _ => hf i), ih]

/-- The coefficient of a finite exponential sum. -/
theorem coeff_expSum {ι : Type*} (s : Finset ι) (w : ι → ℂ) (φ : ι → Fin d → ℤ)
    (r : Fin d → ℤ) :
    coeff (fun x => ∑ i ∈ s, w i * E (φ i) x) r = ∑ i ∈ s, if φ i = r then w i else 0 := by
  rw [coeff_sum s (fun i => continuous_const.mul (continuous_E _))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coeff_const_mul, coeff_E]
  split_ifs <;> simp

/-! ### Trigonometric polynomials and Fourier coordinate subspaces -/

/-- The trigonometric polynomial `Σ_{m ∈ T} c_m e^{i m·x}`. -/
noncomputable def trig (T : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℂ) (x : Rd) : ℂ :=
  ∑ m ∈ T, c m * E m x

/-- The Fourier coordinate subspace `E_S = span {e^{i n·x} : n ∈ S}`. -/
def coordSubspace (S : Finset (Fin d → ℤ)) : Set (Rd → ℂ) := {f | ∃ c, f = trig S c}

theorem continuous_trig (T : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℂ) :
    Continuous (trig T c) :=
  continuous_finset_sum _ fun m _ => continuous_const.mul (continuous_E m)

theorem coeff_trig (T : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℂ) (n : Fin d → ℤ) :
    coeff (trig T c) n = if n ∈ T then c n else 0 := by
  unfold trig
  rw [coeff_expSum]
  split_ifs with h
  · rw [Finset.sum_eq_single n (fun b _ hb => if_neg hb) (fun hn => absurd h hn), if_pos rfl]
  · exact Finset.sum_eq_zero fun m hm => if_neg (fun hmn : m = n => h (hmn ▸ hm))

/-- A function in `E_S` has vanishing Fourier coefficients outside `S`. -/
theorem coeff_eq_zero_of_mem {S : Finset (Fin d → ℤ)} {f : Rd → ℂ} (hf : f ∈ coordSubspace S)
    {r : Fin d → ℤ} (hr : r ∉ S) : coeff f r = 0 := by
  obtain ⟨c, rfl⟩ := hf
  rw [coeff_trig, if_neg hr]

theorem conj_trig (T : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℂ) (x : Rd) :
    (starRingEnd ℂ) (trig T c x) = ∑ m ∈ T, (starRingEnd ℂ) (c m) * E (-m) x := by
  simp [trig, map_sum, E_neg]

theorem sum_mul_sum_product {α β : Type*} (s : Finset α) (t : Finset β) (f : α → ℂ)
    (g : β → ℂ) : (∑ i ∈ s, f i) * (∑ j ∈ t, g j) = ∑ p ∈ s ×ˢ t, f p.1 * g p.2 := by
  rw [Finset.sum_product, Finset.sum_mul_sum]

/-- `|P|²P = P·P·P̄` expanded over frequency triples. -/
theorem cubic_trig (T : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℂ) (x : Rd) :
    ((‖trig T c x‖ ^ 2 : ℝ) : ℂ) * trig T c x =
      ∑ t ∈ T ×ˢ T ×ˢ T,
        c t.1 * c t.2.1 * (starRingEnd ℂ) (c t.2.2) * E (t.1 + t.2.1 - t.2.2) x := by
  have hn : ((‖trig T c x‖ ^ 2 : ℝ) : ℂ) * trig T c x =
      trig T c x * (trig T c x * (starRingEnd ℂ) (trig T c x)) := by
    rw [Complex.mul_conj']
    push_cast
    ring
  rw [hn, conj_trig]
  unfold trig
  rw [sum_mul_sum_product, sum_mul_sum_product]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [E_sub, E_add, E_neg]
  ring

/-- `|P|⁴P = P³ P̄²` expanded over frequency quintuples. -/
theorem quintic_trig (T : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℂ) (x : Rd) :
    ((‖trig T c x‖ ^ 4 : ℝ) : ℂ) * trig T c x =
      ∑ t ∈ T ×ˢ T ×ˢ T ×ˢ T ×ˢ T,
        c t.1 * c t.2.1 * c t.2.2.1 * (starRingEnd ℂ) (c t.2.2.2.1) *
          (starRingEnd ℂ) (c t.2.2.2.2) *
          E (t.1 + t.2.1 + t.2.2.1 - t.2.2.2.1 - t.2.2.2.2) x := by
  have hn : ((‖trig T c x‖ ^ 4 : ℝ) : ℂ) * trig T c x =
      trig T c x * (trig T c x * (trig T c x * ((starRingEnd ℂ) (trig T c x) *
        (starRingEnd ℂ) (trig T c x)))) := by
    have : ((‖trig T c x‖ ^ 4 : ℝ) : ℂ) =
        (trig T c x * (starRingEnd ℂ) (trig T c x)) ^ 2 := by
      rw [Complex.mul_conj']
      push_cast
      ring
    rw [this]
    ring
  rw [hn, conj_trig]
  unfold trig
  rw [sum_mul_sum_product, sum_mul_sum_product, sum_mul_sum_product, sum_mul_sum_product]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [E_sub, E_sub, E_add, E_add, E_neg, E_neg]
  ring

/-! ### The linear operator `(Δ + κ²)²` on trigonometric polynomials -/

theorem contDiff_E (n : Fin d → ℤ) {k : WithTop ℕ∞} : ContDiff ℝ k (E n) := by
  unfold E
  have h1 : ContDiff ℝ k (fun y : Rd => ((inner ℝ (freq n) y : ℝ) : ℂ) * Complex.I) :=
    (Complex.ofRealCLM.contDiff.comp (innerSL ℝ (freq n)).contDiff).mul contDiff_const
  exact Complex.contDiff_exp.comp h1

theorem contDiff_trig (T : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℂ) {k : WithTop ℕ∞} :
    ContDiff ℝ k (trig T c) := by
  unfold trig
  exact ContDiff.sum fun m _ => contDiff_const.mul (contDiff_E m)

theorem laplacian_const_mul_E (a : ℂ) (m : Fin d → ℤ) (x : Rd) :
    Δ (fun y => a * E m y) x = a * Δ (E m) x := by
  have h := ((contDiff_E m (k := 2)).contDiffAt (x := x)).laplacian_CLM_comp_left
    (l := ContinuousLinearMap.mul ℝ ℂ a)
  simpa using h

theorem laplacian_zero_fun (x : Rd) : Δ (fun _ : Rd => (0 : ℂ)) x = 0 := by
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis _ (EuclideanSpace.basisFun (Fin d) ℝ)]
  simp

/-- `Δ` of a trigonometric polynomial. -/
theorem laplacian_trig (T : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℂ) (x : Rd) :
    Δ (trig T c) x = trig T (fun m => -(nsq m : ℂ) * c m) x := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa [trig] using laplacian_zero_fun x
  | insert a T ha ih =>
    have hsplit : trig (insert a T) c = (fun y => c a * E a y) + trig T c := by
      funext y
      simp [trig, Finset.sum_insert ha]
    rw [hsplit, ((contDiff_const.mul (contDiff_E a)).contDiffAt).laplacian_add
      ((contDiff_trig T c).contDiffAt), laplacian_const_mul_E, laplacian_E, ih]
    simp only [trig, Finset.sum_insert ha]
    ring

/-- `(Δ + κ²) f`. -/
noncomputable def shiftLap (κ : ℝ) (f : Rd → ℂ) (x : Rd) : ℂ :=
  Δ f x + ((κ ^ 2 : ℝ) : ℂ) * f x

theorem shiftLap_trig (κ : ℝ) (T : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℂ) :
    shiftLap κ (trig T c) = trig T (fun m => ((κ ^ 2 - nsq m : ℝ) : ℂ) * c m) := by
  funext x
  rw [shiftLap, laplacian_trig]
  simp only [trig, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  push_cast
  ring

/-- `(Δ + κ²)² e^{im·x} = (κ² − |m|²)² e^{im·x}`, extended to trigonometric polynomials. -/
theorem shiftLap_shiftLap_trig (κ : ℝ) (T : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℂ) :
    shiftLap κ (shiftLap κ (trig T c)) =
      trig T (fun m => (((κ ^ 2 - nsq m) ^ 2 : ℝ) : ℂ) * c m) := by
  rw [shiftLap_trig, shiftLap_trig]
  funext x
  simp only [trig]
  refine Finset.sum_congr rfl fun m _ => ?_
  push_cast
  ring

/-! ### Lexicographic extremes of a finite frequency set -/

/-- The lexicographically largest frequency. -/
noncomputable def lexMax (T : Finset (Fin d → ℤ)) (hT : T.Nonempty) : Fin d → ℤ :=
  ofLex ((T.image toLex).max' (hT.image _))

/-- The lexicographically smallest frequency. -/
noncomputable def lexMin (T : Finset (Fin d → ℤ)) (hT : T.Nonempty) : Fin d → ℤ :=
  ofLex ((T.image toLex).min' (hT.image _))

theorem lexMax_mem (T : Finset (Fin d → ℤ)) (hT : T.Nonempty) : lexMax T hT ∈ T := by
  have := (T.image toLex).max'_mem (hT.image _)
  rw [Finset.mem_image] at this
  obtain ⟨a, ha, h⟩ := this
  rw [lexMax, ← h]
  simpa using ha

theorem lexMin_mem (T : Finset (Fin d → ℤ)) (hT : T.Nonempty) : lexMin T hT ∈ T := by
  have := (T.image toLex).min'_mem (hT.image _)
  rw [Finset.mem_image] at this
  obtain ⟨a, ha, h⟩ := this
  rw [lexMin, ← h]
  simpa using ha

theorem le_lexMax {T : Finset (Fin d → ℤ)} (hT : T.Nonempty) {a : Fin d → ℤ} (ha : a ∈ T) :
    toLex a ≤ toLex (lexMax T hT) := by
  rw [lexMax, toLex_ofLex]
  exact (T.image toLex).le_max' _ (Finset.mem_image_of_mem _ ha)

theorem lexMin_le {T : Finset (Fin d → ℤ)} (hT : T.Nonempty) {a : Fin d → ℤ} (ha : a ∈ T) :
    toLex (lexMin T hT) ≤ toLex a := by
  rw [lexMin, toLex_ofLex]
  exact (T.image toLex).min'_le _ (Finset.mem_image_of_mem _ ha)

theorem lexMin_lt_lexMax {T : Finset (Fin d → ℤ)} (hT : 2 ≤ T.card) :
    toLex (lexMin T (Finset.card_pos.1 (by omega))) <
      toLex (lexMax T (Finset.card_pos.1 (by omega))) := by
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 (by omega : 1 < T.card)
  rcases lt_or_gt_of_ne (show toLex a ≠ toLex b from fun h => hab (toLex.injective h)) with h | h
  · exact lt_of_le_of_lt (lexMin_le _ ha) (lt_of_lt_of_le h (le_lexMax _ hb))
  · exact lt_of_le_of_lt (lexMin_le _ hb) (lt_of_lt_of_le h (le_lexMax _ ha))

/-- In an ordered additive group, if `aᵢ ≤ p`, `q ≤ bⱼ` and `Σaᵢ − Σbⱼ = 3p − 2q`, then all
`aᵢ = p` and all `bⱼ = q`. -/
theorem extremal_quintic {G : Type*} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    {p q a1 a2 a3 b1 b2 : G} (h1 : a1 ≤ p) (h2 : a2 ≤ p) (h3 : a3 ≤ p) (h4 : q ≤ b1)
    (h5 : q ≤ b2) (heq : a1 + a2 + a3 - b1 - b2 = 3 • p - 2 • q) :
    a1 = p ∧ a2 = p ∧ a3 = p ∧ b1 = q ∧ b2 = q := by
  have e1 : 0 ≤ p - a1 := sub_nonneg.2 h1
  have e2 : 0 ≤ p - a2 := sub_nonneg.2 h2
  have e3 : 0 ≤ p - a3 := sub_nonneg.2 h3
  have e4 : 0 ≤ b1 - q := sub_nonneg.2 h4
  have e5 : 0 ≤ b2 - q := sub_nonneg.2 h5
  have hsum : (p - a1) + ((p - a2) + ((p - a3) + ((b1 - q) + (b2 - q)))) = 0 := by
    have : (p - a1) + ((p - a2) + ((p - a3) + ((b1 - q) + (b2 - q)))) =
        (3 • p - 2 • q) - (a1 + a2 + a3 - b1 - b2) := by
      simp only [succ_nsmul, zero_nsmul, zero_add]
      abel
    rw [this, heq, sub_self]
  rw [add_eq_zero_iff_of_nonneg e1 (add_nonneg e2 (add_nonneg e3 (add_nonneg e4 e5)))] at hsum
  obtain ⟨z1, hsum⟩ := hsum
  rw [add_eq_zero_iff_of_nonneg e2 (add_nonneg e3 (add_nonneg e4 e5))] at hsum
  obtain ⟨z2, hsum⟩ := hsum
  rw [add_eq_zero_iff_of_nonneg e3 (add_nonneg e4 e5)] at hsum
  obtain ⟨z3, hsum⟩ := hsum
  rw [add_eq_zero_iff_of_nonneg e4 e5] at hsum
  obtain ⟨z4, z5⟩ := hsum
  exact ⟨(sub_eq_zero.1 z1).symm, (sub_eq_zero.1 z2).symm, (sub_eq_zero.1 z3).symm,
    sub_eq_zero.1 z4, sub_eq_zero.1 z5⟩

/-- No cubic interaction reaches `3p − 2q` when `q < p`. -/
theorem extremal_cubic {G : Type*} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    {p q a1 a2 b : G} (hqp : q < p) (h1 : a1 ≤ p) (h2 : a2 ≤ p) (h3 : q ≤ b) :
    a1 + a2 - b ≠ 3 • p - 2 • q := by
  intro heq
  have : a1 + a2 - b ≤ 2 • p - q := by
    simp only [succ_nsmul, zero_nsmul, zero_add]
    have := add_le_add (add_le_add h1 h2) (neg_le_neg h3)
    simpa [sub_eq_add_neg] using this
  have hlt : 2 • p - q < 3 • p - 2 • q := by
    simp only [succ_nsmul, zero_nsmul, zero_add]
    have : p + p - q + (q - q) < p + p - q + (p - q) := by
      simpa using sub_pos.2 hqp
    convert this using 1 <;> abel
  exact absurd heq (ne_of_lt (lt_of_le_of_lt this hlt))

/-- `3p − 2q` lies strictly beyond the lexicographic maximum. -/
theorem lt_extremal {G : Type*} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    {p q : G} (hqp : q < p) : p < 3 • p - 2 • q := by
  simp only [succ_nsmul, zero_nsmul, zero_add]
  have h := sub_pos.2 hqp
  have : p + 0 < p + ((p - q) + (p - q)) := add_lt_add_left (add_pos h h) p
  convert this using 1 <;> abel

/-! ### Fourier coefficients of the nonlinear terms at the extremal frequency -/

/-- The cubic–quintic nonlinearity `−β|z|²z + γ|z|⁴z`. -/
noncomputable def nonlin (β γ : ℝ) (z : ℂ) : ℂ :=
  -(β : ℂ) * (((‖z‖ ^ 2 : ℝ) : ℂ) * z) + (γ : ℂ) * (((‖z‖ ^ 4 : ℝ) : ℂ) * z)

/-- The leakage frequency `r = 3p − 2q`. -/
noncomputable def leakFreq (T : Finset (Fin d → ℤ)) (hT : T.Nonempty) : Fin d → ℤ :=
  3 • lexMax T hT - 2 • lexMin T hT

theorem toLex_leakFreq (T : Finset (Fin d → ℤ)) (hT : T.Nonempty) :
    toLex (leakFreq T hT) = 3 • toLex (lexMax T hT) - 2 • toLex (lexMin T hT) := by
  simp [leakFreq]

theorem leakFreq_not_mem {T : Finset (Fin d → ℤ)} (hT : 2 ≤ T.card) :
    leakFreq T (Finset.card_pos.1 (by omega)) ∉ T := by
  intro hr
  have h1 := le_lexMax (Finset.card_pos.1 (by omega)) hr
  rw [toLex_leakFreq] at h1
  exact absurd h1 (not_le.2 (lt_extremal (lexMin_lt_lexMax hT)))

theorem coeff_cubic_leak {T : Finset (Fin d → ℤ)} (hT : 2 ≤ T.card) (c : (Fin d → ℤ) → ℂ) :
    coeff (fun x => ((‖trig T c x‖ ^ 2 : ℝ) : ℂ) * trig T c x)
      (leakFreq T (Finset.card_pos.1 (by omega))) = 0 := by
  have hne : T.Nonempty := Finset.card_pos.1 (by omega)
  simp_rw [cubic_trig]
  rw [coeff_expSum]
  refine Finset.sum_eq_zero fun t ht => if_neg ?_
  simp only [Finset.mem_product] at ht
  intro heq
  have := congrArg toLex heq
  rw [toLex_leakFreq] at this
  simp only [toLex_sub, toLex_add] at this
  exact extremal_cubic (lexMin_lt_lexMax hT) (le_lexMax hne ht.1) (le_lexMax hne ht.2.1)
    (lexMin_le hne ht.2.2) this

/-- The single surviving quintic interaction: `(|P|⁴P)^(3p − 2q) = c_p³ \bar c_q²`. -/
theorem coeff_quintic_leak {T : Finset (Fin d → ℤ)} (hT : 2 ≤ T.card) (c : (Fin d → ℤ) → ℂ) :
    coeff (fun x => ((‖trig T c x‖ ^ 4 : ℝ) : ℂ) * trig T c x)
        (leakFreq T (Finset.card_pos.1 (by omega))) =
      c (lexMax T (Finset.card_pos.1 (by omega))) ^ 3 *
        (starRingEnd ℂ) (c (lexMin T (Finset.card_pos.1 (by omega)))) ^ 2 := by
  have hne : T.Nonempty := Finset.card_pos.1 (by omega)
  set p := lexMax T hne
  set q := lexMin T hne
  simp_rw [quintic_trig]
  rw [coeff_expSum]
  have hmem : (p, p, p, q, q) ∈ T ×ˢ T ×ˢ T ×ˢ T ×ˢ T := by
    simp [p, q, lexMax_mem, lexMin_mem]
  rw [Finset.sum_eq_single (p, p, p, q, q)]
  · rw [if_pos]
    · ring
    · simp only [leakFreq]
      simp only [succ_nsmul, zero_nsmul, zero_add]
      abel
  · intro t ht hne'
    refine if_neg fun heq => hne' ?_
    simp only [Finset.mem_product] at ht
    have := congrArg toLex heq
    rw [toLex_leakFreq] at this
    simp only [toLex_sub, toLex_add] at this
    obtain ⟨e1, e2, e3, e4, e5⟩ := extremal_quintic (le_lexMax hne ht.1) (le_lexMax hne ht.2.1)
      (le_lexMax hne ht.2.2.1) (lexMin_le hne ht.2.2.2.1) (lexMin_le hne ht.2.2.2.2) this
    obtain ⟨t1, t2, t3, t4, t5⟩ := t
    simp only [toLex_inj] at e1 e2 e3 e4 e5
    rw [e1, e2, e3, e4, e5]
  · intro h
    exact absurd hmem h

/-! ### Classical solutions and instantaneous leakage -/

/-- A classical solution of `i∂ₜu = (Δ+κ²)²u − β|u|²u + γ|u|⁴u` on `(−τ, τ) × 𝕋^d`,
`𝕋^d = (ℝ/2πℤ)^d`: `2π`-periodic in each coordinate, `C⁴` in space, with continuous
time derivative, satisfying the equation pointwise.  `Δ` is Mathlib's Laplacian. -/
structure IsClassicalSolution (κ β γ τ : ℝ) (u : ℝ → Rd → ℂ) : Prop where
  pos : 0 < τ
  periodic : ∀ t x (j : Fin d), u t (x + (2 * Real.pi) • EuclideanSpace.single j 1) = u t x
  smooth : ∀ t ∈ Ioo (-τ) τ, ContDiff ℝ 4 (u t)
  cont : ContinuousOn (fun p : ℝ × Rd => u p.1 p.2) (Ioo (-τ) τ ×ˢ univ)
  time_diff : ∀ t ∈ Ioo (-τ) τ, ∀ x, DifferentiableAt ℝ (fun s => u s x) t
  dt_cont : ContinuousOn (fun p : ℝ × Rd => deriv (fun s => u s p.2) p.1) (Ioo (-τ) τ ×ˢ univ)
  pde : ∀ t ∈ Ioo (-τ) τ, ∀ x,
    Complex.I * deriv (fun s => u s x) t = shiftLap κ (shiftLap κ (u t)) x + nonlin β γ (u t x)

theorem isFiniteMeasure_cube : IsFiniteMeasure (volume.restrict (cube d)) :=
  isFiniteMeasure_restrict.2 isCompact_cube.measure_lt_top.ne

theorem measurableSet_cube : MeasurableSet (cube d) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Icc

/-- Differentiation under the integral over the cube, with a uniform bound. -/
theorem hasDerivAt_cubeIntegral {U U' : ℝ → (Fin d → ℝ) → ℂ} {ε M : ℝ} (hε : 0 < ε)
    (hmeas : ∀ᶠ t in 𝓝 (0 : ℝ), AEStronglyMeasurable (U t) (volume.restrict (cube d)))
    (hint : IntegrableOn (U 0) (cube d))
    (hmeas' : AEStronglyMeasurable (U' 0) (volume.restrict (cube d)))
    (hbound : ∀ y ∈ cube d, ∀ t ∈ Metric.ball (0 : ℝ) ε, ‖U' t y‖ ≤ M)
    (hdiff : ∀ y, ∀ t ∈ Metric.ball (0 : ℝ) ε, HasDerivAt (fun t => U t y) (U' t y) t) :
    HasDerivAt (fun t => ∫ y in cube d, U t y) (∫ y in cube d, U' 0 y) 0 := by
  haveI := isFiniteMeasure_cube (d := d)
  have hb : ∀ᵐ y ∂(volume.restrict (cube d)), ∀ t ∈ Metric.ball (0 : ℝ) ε, ‖U' t y‖ ≤ M := by
    filter_upwards [ae_restrict_mem measurableSet_cube] with y hy t ht
    exact hbound y hy t ht
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hε hmeas hint hmeas' hb
    (integrable_const M) (Eventually.of_forall hdiff)).2

/-- Fourier coefficients of a classical solution are differentiable in time, with
derivative the coefficient of `∂ₜu` (differentiation under the integral sign). -/
theorem hasDerivAt_coeff {κ β γ τ : ℝ} {u : ℝ → Rd → ℂ} (h : IsClassicalSolution κ β γ τ u)
    (r : Fin d → ℤ) :
    HasDerivAt (fun t => coeff (u t) r) (coeff (fun x => deriv (fun s => u s x) 0) r) 0 := by
  have hτ := h.pos
  have hεpos : 0 < τ / 2 := by positivity
  have hsub : ∀ t ∈ Metric.closedBall (0 : ℝ) (τ / 2), t ∈ Ioo (-τ) τ := by
    intro t ht
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_le] at ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hmap : Continuous fun p : ℝ × (Fin d → ℝ) => (p.1, toE p.2) :=
    continuous_fst.prodMk (continuous_toE.comp continuous_snd)
  have hGcont : ContinuousOn (fun p : ℝ × (Fin d → ℝ) => deriv (fun s => u s (toE p.2)) p.1)
      (Metric.closedBall (0 : ℝ) (τ / 2) ×ˢ cube d) :=
    h.dt_cont.comp hmap.continuousOn fun p hp => ⟨hsub p.1 hp.1, mem_univ _⟩
  obtain ⟨M, hM⟩ := ((isCompact_closedBall (0 : ℝ) (τ / 2)).prod
    isCompact_cube).exists_bound_of_continuousOn hGcont
  have h0 : (0 : ℝ) ∈ Ioo (-τ) τ := ⟨by linarith, hτ⟩
  have hc0 : Continuous fun y : Fin d → ℝ => deriv (fun s => u s (toE y)) 0 :=
    h.dt_cont.comp_continuous (continuous_const.prodMk continuous_toE) fun y => ⟨h0, mem_univ _⟩
  have key := hasDerivAt_cubeIntegral (d := d)
    (U := fun t y => u t (toE y) * E (-r) (toE y))
    (U' := fun t y => deriv (fun s => u s (toE y)) t * E (-r) (toE y)) (M := M) hεpos
    (by
      filter_upwards [Ioo_mem_nhds (by linarith : -τ < (0:ℝ)) hτ] with t ht
      exact (((h.smooth t ht).continuous.comp continuous_toE).mul
        ((continuous_E _).comp continuous_toE)).aestronglyMeasurable)
    (integrableOn_cube ((h.smooth 0 h0).continuous) r)
    ((hc0.mul ((continuous_E _).comp continuous_toE)).aestronglyMeasurable)
    (fun y hy t ht => by
      rw [norm_mul, norm_E, mul_one]
      exact hM (t, y) ⟨Metric.ball_subset_closedBall ht, hy⟩)
    (fun y t ht =>
      (h.time_diff t (hsub t (Metric.ball_subset_closedBall ht)) (toE y)).hasDerivAt.mul_const _)
  unfold coeff
  exact key.const_mul _

/-- At `t = 0` the time derivative of every coefficient is read off from the equation. -/
theorem coeff_dt_zero {κ β γ τ : ℝ} {u : ℝ → Rd → ℂ} (h : IsClassicalSolution κ β γ τ u)
    {T : Finset (Fin d → ℤ)} {c : (Fin d → ℤ) → ℂ} (h0 : u 0 = trig T c) (r : Fin d → ℤ) :
    coeff (fun x => deriv (fun s => u s x) 0) r =
      -Complex.I * ((if r ∈ T then (((κ ^ 2 - nsq r) ^ 2 : ℝ) : ℂ) * c r else 0) +
        coeff (fun x => nonlin β γ (trig T c x)) r) := by
  have hτ := h.pos
  have h0' : (0 : ℝ) ∈ Ioo (-τ) τ := ⟨by linarith, hτ⟩
  have hpt : (fun x => deriv (fun s => u s x) 0) = fun x =>
      -Complex.I * (shiftLap κ (shiftLap κ (trig T c)) x + nonlin β γ (trig T c x)) := by
    funext x
    have := h.pde 0 h0' x
    rw [h0] at this
    rw [← this]
    ring_nf
    rw [Complex.I_sq]
    ring
  have hcN : Continuous fun x => nonlin β γ (trig T c x) := by
    unfold nonlin
    have := continuous_trig T c
    fun_prop
  rw [hpt, coeff_const_mul, coeff_add (by rw [shiftLap_shiftLap_trig]; exact continuous_trig _ _)
    hcN, shiftLap_shiftLap_trig, coeff_trig]

/-- The nonlinear coefficient at the extremal frequency. -/
theorem coeff_nonlin_leak {T : Finset (Fin d → ℤ)} (hT : 2 ≤ T.card) (c : (Fin d → ℤ) → ℂ)
    (β γ : ℝ) :
    coeff (fun x => nonlin β γ (trig T c x)) (leakFreq T (Finset.card_pos.1 (by omega))) =
      (γ : ℂ) * (c (lexMax T (Finset.card_pos.1 (by omega))) ^ 3 *
        (starRingEnd ℂ) (c (lexMin T (Finset.card_pos.1 (by omega)))) ^ 2) := by
  have hc1 : Continuous fun x => ((‖trig T c x‖ ^ 2 : ℝ) : ℂ) * trig T c x := by
    have := continuous_trig T c
    fun_prop
  have hc2 : Continuous fun x => ((‖trig T c x‖ ^ 4 : ℝ) : ℂ) * trig T c x := by
    have := continuous_trig T c
    fun_prop
  unfold nonlin
  rw [coeff_add (continuous_const.mul hc1) (continuous_const.mul hc2), coeff_const_mul,
    coeff_const_mul, coeff_cubic_leak hT, coeff_quintic_leak hT]
  ring

/-- A function with nonzero derivative and a zero at `0` is nonzero on a punctured
neighbourhood. -/
theorem eventually_ne_zero_of_hasDerivAt {f : ℝ → ℂ} {D : ℂ} (hf : HasDerivAt f D 0)
    (h0 : f 0 = 0) (hD : D ≠ 0) : ∀ᶠ t in 𝓝[≠] (0 : ℝ), f t ≠ 0 := by
  have hs := hasDerivAt_iff_tendsto_slope.1 hf
  filter_upwards [hs.eventually_ne hD] with t ht
  intro hft
  apply ht
  simp [slope_def_module, hft, h0]

/-- **Leakage for every classical solution** launched from a trigonometric polynomial:
at any `r ∉ T`, `û(r, 0) = 0` and `∂ₜû(r, 0) = −i (|u₀|-nonlinearity)^(r)`. -/
theorem leakage_core {κ β γ τ : ℝ} {u : ℝ → Rd → ℂ} (h : IsClassicalSolution κ β γ τ u)
    {T : Finset (Fin d → ℤ)} {c : (Fin d → ℤ) → ℂ} (h0 : u 0 = trig T c) {r : Fin d → ℤ}
    (hr : r ∉ T) :
    coeff (u 0) r = 0 ∧
      HasDerivAt (fun t => coeff (u t) r)
        (-Complex.I * coeff (fun x => nonlin β γ (trig T c x)) r) 0 := by
  refine ⟨by rw [h0, coeff_trig, if_neg hr], ?_⟩
  have := hasDerivAt_coeff h r
  rw [coeff_dt_zero h h0, if_neg hr, zero_add] at this
  exact this

/-- **Theorem (universal instantaneous leakage for trigonometric polynomials).**  For every
`u₀ = Σ_{n∈T} cₙ e^{in·x}` with `|T| ≥ 2` and all `cₙ ≠ 0`, there are `p ≠ q` in `T` such
that `r = 3p − 2q ∉ T` and every classical solution with `u(0) = u₀` satisfies
`û(r,0) = 0`, `∂ₜû(r,0) = −iγ c_p³ \bar c_q² ≠ 0`; hence `u(t) ∉ E_T` for all small `t ≠ 0`. -/
theorem universal_leakage {κ β γ : ℝ} (hγ : γ ≠ 0) {T : Finset (Fin d → ℤ)}
    (hT : 2 ≤ T.card) {c : (Fin d → ℤ) → ℂ} (hc : ∀ n ∈ T, c n ≠ 0) :
    ∃ p ∈ T, ∃ q ∈ T, p ≠ q ∧ 3 • p - 2 • q ∉ T ∧
      -Complex.I * (γ : ℂ) * (c p ^ 3 * (starRingEnd ℂ) (c q) ^ 2) ≠ 0 ∧
      ∀ τ (u : ℝ → Rd → ℂ), IsClassicalSolution κ β γ τ u → u 0 = trig T c →
        coeff (u 0) (3 • p - 2 • q) = 0 ∧
        HasDerivAt (fun t => coeff (u t) (3 • p - 2 • q))
          (-Complex.I * (γ : ℂ) * (c p ^ 3 * (starRingEnd ℂ) (c q) ^ 2)) 0 ∧
        ∀ᶠ t in 𝓝[≠] (0 : ℝ), u t ∉ coordSubspace T := by
  have hne : T.Nonempty := Finset.card_pos.1 (by omega)
  have hlt := lexMin_lt_lexMax hT
  refine ⟨lexMax T hne, lexMax_mem T hne, lexMin T hne, lexMin_mem T hne,
    fun h => (ne_of_gt hlt) (congrArg toLex h), leakFreq_not_mem hT, ?_, ?_⟩
  · have hp := hc _ (lexMax_mem T hne)
    have hq := hc _ (lexMin_mem T hne)
    have hq' : (starRingEnd ℂ) (c (lexMin T hne)) ≠ 0 := by
      rwa [map_ne_zero]
    have : (γ : ℂ) ≠ 0 := by exact_mod_cast hγ
    exact mul_ne_zero (mul_ne_zero (neg_ne_zero.2 Complex.I_ne_zero) this)
      (mul_ne_zero (pow_ne_zero _ hp) (pow_ne_zero _ hq'))
  · intro τ u h h0
    have hcore := leakage_core h h0 (leakFreq_not_mem hT)
    rw [coeff_nonlin_leak hT] at hcore
    have hD : -Complex.I * (γ : ℂ) * (c (lexMax T hne) ^ 3 *
        (starRingEnd ℂ) (c (lexMin T hne)) ^ 2) ≠ 0 := by
      have hp := hc _ (lexMax_mem T hne)
      have hq' : (starRingEnd ℂ) (c (lexMin T hne)) ≠ 0 := by
        rw [map_ne_zero]
        exact hc _ (lexMin_mem T hne)
      have : (γ : ℂ) ≠ 0 := by exact_mod_cast hγ
      exact mul_ne_zero (mul_ne_zero (neg_ne_zero.2 Complex.I_ne_zero) this)
        (mul_ne_zero (pow_ne_zero _ hp) (pow_ne_zero _ hq'))
    have hderiv : HasDerivAt (fun t => coeff (u t) (leakFreq T hne))
        (-Complex.I * (γ : ℂ) * (c (lexMax T hne) ^ 3 *
          (starRingEnd ℂ) (c (lexMin T hne)) ^ 2)) 0 := by
      have := hcore.2
      rwa [← mul_assoc] at this
    refine ⟨hcore.1, hderiv, ?_⟩
    filter_upwards [eventually_ne_zero_of_hasDerivAt hderiv hcore.1 hD] with t ht hmem
    exact ht (coeff_eq_zero_of_mem hmem (leakFreq_not_mem hT))

theorem lexMax_pair {p q : Fin d → ℤ} (hpq : toLex q < toLex p) :
    lexMax {p, q} (Finset.insert_nonempty p {q}) = p := by
  have hmem := lexMax_mem {p, q} (Finset.insert_nonempty p {q})
  have hle := le_lexMax (Finset.insert_nonempty p {q}) (show p ∈ ({p, q} : Finset _) by simp)
  rcases Finset.mem_insert.1 hmem with h | h
  · exact h
  · rw [Finset.mem_singleton] at h
    rw [h] at hle
    exact absurd hle (not_le.2 hpq)

theorem lexMin_pair {p q : Fin d → ℤ} (hpq : toLex q < toLex p) :
    lexMin {p, q} (Finset.insert_nonempty p {q}) = q := by
  have hmem := lexMin_mem {p, q} (Finset.insert_nonempty p {q})
  have hle := lexMin_le (Finset.insert_nonempty p {q}) (show q ∈ ({p, q} : Finset _) by simp)
  rcases Finset.mem_insert.1 hmem with h | h
  · rw [h] at hle
    exact absurd hle (not_le.2 hpq)
  · exact Finset.mem_singleton.1 h

/-- The two-mode coefficient function `a` at `p`, `b` at `q`. -/
noncomputable def twoMode (p q : Fin d → ℤ) (a b : ℂ) (n : Fin d → ℤ) : ℂ :=
  if n = p then a else if n = q then b else 0

theorem trig_twoMode {p q : Fin d → ℤ} (hpq : p ≠ q) (a b : ℂ) (x : Rd) :
    trig {p, q} (twoMode p q a b) x = a * E p x + b * E q x := by
  rw [trig, Finset.sum_pair hpq]
  simp [twoMode, Ne.symm hpq]

theorem twoMode_mem {S : Finset (Fin d → ℤ)} {p q : Fin d → ℤ} (hp : p ∈ S) (hq : q ∈ S)
    (a b : ℂ) :
    trig {p, q} (twoMode p q a b) ∈ coordSubspace S := by
  refine ⟨twoMode p q a b, ?_⟩
  funext x
  rw [trig, trig]
  refine Finset.sum_subset (by
    intro n hn
    rcases Finset.mem_insert.1 hn with h | h
    · rw [h]; exact hp
    · rw [Finset.mem_singleton.1 h]; exact hq) fun n _ hn => ?_
  have h1 : n ≠ p := fun h => hn (h ▸ Finset.mem_insert_self _ _)
  have h2 : n ≠ q := fun h => hn (h ▸ by simp)
  simp [twoMode, h1, h2]

/-- **Theorem (no finite multimode Fourier coordinate subspace is invariant).**  For every
finite `S ⊂ ℤ^d` with `|S| ≥ 2` and all `a, b ≠ 0` there are `p ≠ q` in `S` such that the
datum `u₀ = a e^{ip·x} + b e^{iq·x} ∈ E_S` and the frequency `r = 3p − 2q ∉ S` satisfy, for
every classical solution with `u(0) = u₀`: `û(r,0) = 0` and `∂ₜû(r,0) = −iγa³\bar b² ≠ 0`;
consequently `u(t) ∉ E_S` for every sufficiently small `t ≠ 0`. -/
theorem no_multimode_invariance {κ β γ : ℝ} (hγ : γ ≠ 0) {S : Finset (Fin d → ℤ)}
    (hS : 2 ≤ S.card) {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ p ∈ S, ∃ q ∈ S, p ≠ q ∧ 3 • p - 2 • q ∉ S ∧
      trig {p, q} (twoMode p q a b) ∈ coordSubspace S ∧
      -Complex.I * (γ : ℂ) * (a ^ 3 * (starRingEnd ℂ) b ^ 2) ≠ 0 ∧
      ∀ τ (u : ℝ → Rd → ℂ), IsClassicalSolution κ β γ τ u → u 0 = trig {p, q} (twoMode p q a b) →
        coeff (u 0) (3 • p - 2 • q) = 0 ∧
        HasDerivAt (fun t => coeff (u t) (3 • p - 2 • q))
          (-Complex.I * (γ : ℂ) * (a ^ 3 * (starRingEnd ℂ) b ^ 2)) 0 ∧
        ∀ᶠ t in 𝓝[≠] (0 : ℝ), u t ∉ coordSubspace S := by
  have hne : S.Nonempty := Finset.card_pos.1 (by omega)
  set p := lexMax S hne
  set q := lexMin S hne
  have hlt : toLex q < toLex p := lexMin_lt_lexMax hS
  have hpq : p ≠ q := fun h => (ne_of_gt hlt) (congrArg toLex h)
  have hr : 3 • p - 2 • q ∉ S := leakFreq_not_mem hS
  have hD : -Complex.I * (γ : ℂ) * (a ^ 3 * (starRingEnd ℂ) b ^ 2) ≠ 0 := by
    have : (γ : ℂ) ≠ 0 := by exact_mod_cast hγ
    have hb' : (starRingEnd ℂ) b ≠ 0 := by rwa [map_ne_zero]
    exact mul_ne_zero (mul_ne_zero (neg_ne_zero.2 Complex.I_ne_zero) this)
      (mul_ne_zero (pow_ne_zero _ ha) (pow_ne_zero _ hb'))
  refine ⟨p, lexMax_mem S hne, q, lexMin_mem S hne, hpq, hr,
    twoMode_mem (lexMax_mem S hne) (lexMin_mem S hne) a b, hD, ?_⟩
  intro τ u h h0
  have hT2 : 2 ≤ ({p, q} : Finset (Fin d → ℤ)).card := by
    rw [Finset.card_pair hpq]
  have hrT : 3 • p - 2 • q ∉ ({p, q} : Finset (Fin d → ℤ)) := by
    intro hm
    rcases Finset.mem_insert.1 hm with h' | h'
    · exact hr (by rw [h']; exact lexMax_mem S hne)
    · exact hr (by rw [Finset.mem_singleton.1 h']; exact lexMin_mem S hne)
  have hcore := leakage_core h h0 hrT
  have hleak : leakFreq {p, q} (Finset.card_pos.1 (by omega)) = 3 • p - 2 • q := by
    rw [leakFreq, lexMax_pair hlt, lexMin_pair hlt]
  have hN := coeff_nonlin_leak hT2 (twoMode p q a b) β γ
  rw [hleak, lexMax_pair hlt, lexMin_pair hlt] at hN
  simp only [twoMode, if_neg (Ne.symm hpq)] at hN
  rw [hN] at hcore
  have hderiv : HasDerivAt (fun t => coeff (u t) (3 • p - 2 • q))
      (-Complex.I * (γ : ℂ) * (a ^ 3 * (starRingEnd ℂ) b ^ 2)) 0 := by
    have := hcore.2
    rwa [← mul_assoc] at this
  refine ⟨hcore.1, hderiv, ?_⟩
  filter_upwards [eventually_ne_zero_of_hasDerivAt hderiv hcore.1 hD] with t ht hmem
  exact ht (coeff_eq_zero_of_mem hmem hr)

/-- **Proposition (fifth-harmonic generation from a cosine).**  In one dimension, every
classical solution with `u(0, x) = cos x` has `û(5, 0) = 0` and
`û(5, t) = −(iγ/32) t + o(t)`. -/
theorem fifth_harmonic {κ β γ τ : ℝ} {u : ℝ → EuclideanSpace ℝ (Fin 1) → ℂ}
    (h : IsClassicalSolution κ β γ τ u) (h0 : u 0 = fun x => (Real.cos (x 0) : ℂ)) :
    coeff (u 0) (fun _ => 5) = 0 ∧
      HasDerivAt (fun t => coeff (u t) (fun _ => 5)) (-Complex.I * (γ : ℂ) / 32) 0 := by
  set e : Fin 1 → ℤ := fun _ => 1
  have hlt' : -e < e := Pi.lt_def.2 ⟨fun _ => by simp [e], 0, by simp [e]⟩
  have hlt : toLex (-e) < toLex e := Pi.toLex_strictMono hlt'
  have hpq : e ≠ -e := fun h => (ne_of_gt hlt) (congrArg toLex h)
  have hcos : (fun x : EuclideanSpace ℝ (Fin 1) => (Real.cos (x 0) : ℂ)) =
      trig {e, -e} (twoMode e (-e) (1 / 2) (1 / 2)) := by
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
  have hr : (3 • e - 2 • (-e) : Fin 1 → ℤ) = fun _ => 5 := by
    funext j
    simp [e]
  have hS : 2 ≤ ({e, -e} : Finset (Fin 1 → ℤ)).card := by rw [Finset.card_pair hpq]
  have hrS : (3 • e - 2 • (-e) : Fin 1 → ℤ) ∉ ({e, -e} : Finset (Fin 1 → ℤ)) := by
    rw [hr]
    intro hm
    rcases Finset.mem_insert.1 hm with h' | h'
    · have := congrFun h' 0
      simp [e] at this
    · have := congrFun (Finset.mem_singleton.1 h') 0
      simp [e] at this
  rw [hcos] at h0
  have hcore := leakage_core h h0 hrS
  have hleak : leakFreq {e, -e} (Finset.card_pos.1 (by omega)) = 3 • e - 2 • (-e) := by
    rw [leakFreq, lexMax_pair hlt, lexMin_pair hlt]
  have hN := coeff_nonlin_leak hS (twoMode e (-e) (1 / 2) (1 / 2)) β γ
  rw [hleak, lexMax_pair hlt, lexMin_pair hlt] at hN
  simp only [twoMode, if_neg (Ne.symm hpq)] at hN
  rw [hN, hr] at hcore
  refine ⟨hcore.1, ?_⟩
  convert hcore.2 using 1
  simp only [if_true]
  rw [show (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 by simp [map_ofNat]]
  ring

/-! ### Single-mode subspaces carry exact solutions -/

/-- The single-mode solution `A(t) e^{ip·x}`, `A(t) = A₀ e^{−iΩt}`,
`Ω = (κ² − |p|²)² − β|A₀|² + γ|A₀|⁴`. -/
noncomputable def singleMode (κ β γ : ℝ) (p : Fin d → ℤ) (A₀ : ℂ) (t : ℝ) (x : Rd) : ℂ :=
  A₀ * Complex.exp (-(((κ ^ 2 - nsq p) ^ 2 - β * ‖A₀‖ ^ 2 + γ * ‖A₀‖ ^ 4 : ℝ) : ℂ) *
    Complex.I * t) * E p x

theorem E_periodic (n : Fin d → ℤ) (x : Rd) (j : Fin d) :
    E n (x + (2 * Real.pi) • EuclideanSpace.single j 1) = E n x := by
  rw [E, E, inner_add_right, inner_smul_right, EuclideanSpace.inner_single_right, freq_apply]
  simp only [conj_trivial, one_mul, Complex.ofReal_add, add_mul, Complex.exp_add]
  have : Complex.exp ((((2 * Real.pi) * (n j : ℝ) : ℝ) : ℂ) * Complex.I) = 1 := by
    rw [show ((((2 * Real.pi) * (n j : ℝ) : ℝ) : ℂ) * Complex.I) = (n j : ℂ) * (2 * Real.pi * Complex.I)
      by push_cast; ring]
    exact Complex.exp_int_mul_two_pi_mul_I (n j)
  rw [this, mul_one]

/-- The frequency of the single-mode solution. -/
noncomputable def singleFreq (κ β γ : ℝ) (p : Fin d → ℤ) (A₀ : ℂ) : ℝ :=
  (κ ^ 2 - nsq p) ^ 2 - β * ‖A₀‖ ^ 2 + γ * ‖A₀‖ ^ 4

theorem singleMode_eq (κ β γ : ℝ) (p : Fin d → ℤ) (A₀ : ℂ) (t : ℝ) :
    singleMode κ β γ p A₀ t =
      trig {p} (fun _ => A₀ * Complex.exp (-(singleFreq κ β γ p A₀ : ℂ) * Complex.I * t)) := by
  funext x
  simp [singleMode, trig, singleFreq]

theorem norm_phase (Ω t : ℝ) : ‖Complex.exp (-(Ω : ℂ) * Complex.I * t)‖ = 1 := by
  rw [show -(Ω : ℂ) * Complex.I * t = ((-Ω * t : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- The single-mode subspace `E_{p}` carries the exact solution `A(t) e^{ip·x}`. -/
theorem singleMode_isClassicalSolution (κ β γ : ℝ) (p : Fin d → ℤ) (A₀ : ℂ) {τ : ℝ}
    (hτ : 0 < τ) : IsClassicalSolution κ β γ τ (singleMode κ β γ p A₀) := by
  set Ω := singleFreq κ β γ p A₀ with hΩ
  have hform : ∀ (t : ℝ) (x : Rd), singleMode κ β γ p A₀ t x =
      A₀ * Complex.exp (-(Ω : ℂ) * Complex.I * (t : ℂ)) * E p x := fun t x => by
    simp [singleMode, hΩ, singleFreq]
  have hdt : ∀ (t : ℝ) (x : Rd), HasDerivAt (fun s => singleMode κ β γ p A₀ s x)
      (A₀ * (Complex.exp (-(Ω : ℂ) * Complex.I * (t : ℂ)) * (-(Ω : ℂ) * Complex.I)) * E p x) t := by
    intro t x
    simp_rw [hform]
    have h1 : HasDerivAt (fun s : ℝ => -(Ω : ℂ) * Complex.I * (s : ℂ)) (-(Ω : ℂ) * Complex.I) t := by
      simpa using ((hasDerivAt_id t).ofReal_comp).const_mul (-(Ω : ℂ) * Complex.I)
    exact (h1.cexp.const_mul A₀).mul_const (E p x)
  have hderiv : ∀ (t : ℝ) (x : Rd), deriv (fun s => singleMode κ β γ p A₀ s x) t =
      A₀ * (Complex.exp (-(Ω : ℂ) * Complex.I * (t : ℂ)) * (-(Ω : ℂ) * Complex.I)) * E p x :=
    fun t x => (hdt t x).deriv
  refine ⟨hτ, fun t x j => ?_, fun t _ => ?_, ?_, fun t _ x => (hdt t x).differentiableAt, ?_,
    fun t _ x => ?_⟩
  · rw [hform, hform, E_periodic]
  · rw [singleMode_eq]
    exact contDiff_trig _ _
  · refine Continuous.continuousOn ?_
    simp_rw [hform]
    have := continuous_E p
    fun_prop
  · refine Continuous.continuousOn ?_
    simp_rw [hderiv]
    have := continuous_E p
    fun_prop
  · rw [hderiv, singleMode_eq, shiftLap_shiftLap_trig, ← singleMode_eq]
    simp only [trig, Finset.sum_singleton]
    rw [hform]
    have hn : ‖A₀ * Complex.exp (-(Ω : ℂ) * Complex.I * t) * E p x‖ = ‖A₀‖ := by
      rw [norm_mul, norm_mul, norm_phase, norm_E, mul_one, mul_one]
    unfold nonlin
    rw [hn]
    have hΩ' : (Ω : ℂ) = (((κ ^ 2 - nsq p) ^ 2 : ℝ) : ℂ) - (β : ℂ) * ((‖A₀‖ ^ 2 : ℝ) : ℂ) +
        (γ : ℂ) * ((‖A₀‖ ^ 4 : ℝ) : ℂ) := by
      rw [hΩ, singleFreq]
      push_cast
      ring
    have hI : Complex.I * (Complex.I : ℂ) = -1 := Complex.I_mul_I
    calc Complex.I * (A₀ * (Complex.exp (-(Ω : ℂ) * Complex.I * t) * (-(Ω : ℂ) * Complex.I)) * E p x)
        = -(Complex.I * Complex.I) * (Ω : ℂ) *
            (A₀ * Complex.exp (-(Ω : ℂ) * Complex.I * t) * E p x) := by ring
      _ = _ := by rw [hI, hΩ']; ring

theorem singleMode_mem (κ β γ : ℝ) (p : Fin d → ℤ) (A₀ : ℂ) (t : ℝ) :
    singleMode κ β γ p A₀ t ∈ coordSubspace {p} :=
  ⟨_, singleMode_eq κ β γ p A₀ t⟩

theorem singleMode_zero (κ β γ : ℝ) (p : Fin d → ℤ) (A₀ : ℂ) :
    singleMode κ β γ p A₀ 0 = trig {p} (fun _ => A₀) := by
  rw [singleMode_eq]
  simp

end FourierLeakage

end ReyesMath
