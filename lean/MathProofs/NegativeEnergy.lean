import Mathlib
import MathProofs.SobolevH2
import MathProofs.UVWholeSpace

/-!
# Negative constrained energy at every positive mass (F01/T7)

Formalization of `papers/negative-constrained-energy-cubic-quintic/main.tex` on the Sobolev
space `H²(ℝ²; ℂ)` of `MathProofs.SobolevH2`.

* `Sobolev.H2.energy`: `H(u) = ‖(Δ + k²)u‖² − (β/2)‖u‖⁴_{L⁴} + (γ/3)‖u‖⁶_{L⁶}`;
  `Sobolev.H2.Imin`: `I(m) = inf {H(u) : u ∈ H²(ℝ²; ℂ), ‖u‖²₂ = m}`.
* `Sobolev.H2.square_completion`, `Sobolev.H2.energy_ge`, `Sobolev.H2.energy_ge_mass`: the
  pointwise square completion and the coercive bound `H(u) ≥ ‖(Δ+k²)u‖² − (3β²/(16γ))M(u)`.
* `trial`: the anisotropic plane-wave carrier trial `u(x) = A g(x₀/a) g(x₁/b) e^{ikx₀}` built on
  a smooth compactly supported bump `g` (in place of the paper's Gaussian, which has no
  Schwartz-class instance in Mathlib); `laplacian_trial`, `shift_trial`
  (`(Δ+k²)u = A e^{ikx₀}(P + iQ)`), and the exact integrals `integral_shift_trial`,
  `integral_trial_sq`, `integral_trial_four`, `integral_trial_six`.  With `a = LR`, `b = R`
  and `‖u‖² = m`, the energy is the exact two-term polynomial `c₂/R² + c₄/R⁴`, with `c₂ < 0`
  once the anisotropy `L` is large (`exists_negative`).
* `negative_constrained_energy` (Theorem): for `β, γ > 0`, every `k`, and every `m > 0`,
  `−(3β²/(16γ)) m ≤ I(m) < 0`.
-/

open Filter Topology Complex InnerProductSpace MeasureTheory Set
open scoped ContDiff

namespace ReyesMath

namespace NegativeEnergy

local notation "R2" => EuclideanSpace ℝ (Fin 2)

/-- `∫_{ℝ²} F(x₀) G(x₁) dx = (∫F)(∫G)`. -/
theorem integral_prod_coords (F G : ℝ → ℝ) :
    ∫ x : R2, F (x 0) * G (x 1) = (∫ s, F s) * ∫ t, G t := by
  have h := EuclideanSpace.volume_preserving_measurableEquiv (Fin 2)
  have h1 := h.integral_comp' (fun y : Fin 2 → ℝ => F (y 0) * G (y 1))
  have h3 : ∫ y : Fin 2 → ℝ, F (y 0) * G (y 1) = (∫ s, F s) * ∫ t, G t := by
    have := integral_fintype_prod_eq_prod (ι := Fin 2) (E := fun _ => ℝ) (𝕜 := ℝ)
      (fun i => ![F, G] i) (μ := fun _ => volume)
    rw [← volume_pi] at this
    simpa [Fin.prod_univ_two] using this
  rw [← h3, ← h1]
  rfl

theorem integrable_prod_coords {F G : ℝ → ℝ} (hF : Integrable F) (hG : Integrable G) :
    Integrable fun x : R2 => F (x 0) * G (x 1) := by
  have h := EuclideanSpace.volume_preserving_measurableEquiv (Fin 2)
  have hpi : Integrable (fun y : Fin 2 → ℝ => ∏ i : Fin 2, (![F, G] i) (y i))
      (Measure.pi fun _ => volume) :=
    Integrable.fintype_prod (f := fun i => ![F, G] i) (fun i => by fin_cases i <;> simpa)
  rw [← volume_pi] at hpi
  have := (h.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 hpi
  simpa [Fin.prod_univ_two, Function.comp_def] using this

/-! ### The one-dimensional profile -/

/-- A smooth bump on `ℝ`: `g = 1` on `[−1, 1]`, support `(−2, 2)`. -/
noncomputable def bump1 : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩

noncomputable def g (s : ℝ) : ℝ := bump1 s

noncomputable def g1 : ℝ → ℝ := deriv g

noncomputable def g2 : ℝ → ℝ := deriv g1

theorem contDiff_g : ContDiff ℝ ∞ g := bump1.contDiff

theorem contDiff_g1 : ContDiff ℝ ∞ g1 := by
  have := contDiff_g.iterate_deriv 1
  simpa [g1] using this

theorem contDiff_g2 : ContDiff ℝ ∞ g2 := by
  have := contDiff_g.iterate_deriv 2
  simpa [g2, g1] using this

theorem one_le_infty : (1 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.2 le_top

theorem hasDerivAt_g (s : ℝ) : HasDerivAt g (g1 s) s :=
  ((contDiff_g.differentiable one_le_infty) s).hasDerivAt

theorem hasDerivAt_g1 (s : ℝ) : HasDerivAt g1 (g2 s) s :=
  ((contDiff_g1.differentiable one_le_infty) s).hasDerivAt

theorem hasCompactSupport_g : HasCompactSupport g := bump1.hasCompactSupport

theorem hasCompactSupport_g1 : HasCompactSupport g1 := hasCompactSupport_g.deriv

theorem hasCompactSupport_g2 : HasCompactSupport g2 := hasCompactSupport_g1.deriv

theorem g_zero : g 0 = 1 := bump1.one_of_mem_closedBall (by simp [bump1])

theorem g_nonneg (s : ℝ) : 0 ≤ g s := bump1.nonneg

/-- Integrability of continuous compactly supported profiles. -/
theorem integrable_of_cs {F : ℝ → ℝ} (hF : Continuous F) (hc : HasCompactSupport F) :
    Integrable F := hF.integrable_of_hasCompactSupport hc

/-- `∫ F(s/a) ds = a ∫ F`. -/
theorem integral_scale (F : ℝ → ℝ) {a : ℝ} (ha : 0 < a) : ∫ s, F (s / a) = a * ∫ s, F s := by
  rw [Measure.integral_comp_div, abs_of_pos ha, smul_eq_mul]

/-! ### The carrier profile `G(s) = g(s/a) e^{iks}` -/

/-- The plane-wave carrier `e^{iks}`. -/
noncomputable def ecar (k s : ℝ) : ℂ := Complex.exp (((k * s : ℝ) : ℂ) * Complex.I)

theorem norm_ecar (k s : ℝ) : ‖ecar k s‖ = 1 := Complex.norm_exp_ofReal_mul_I _

theorem hasDerivAt_ecar (k s : ℝ) :
    HasDerivAt (ecar k) (ecar k s * ((k : ℂ) * Complex.I)) s := by
  have h1 : HasDerivAt (fun s : ℝ => ((k * s : ℝ) : ℂ) * Complex.I) ((k : ℂ) * Complex.I) s := by
    have := (((hasDerivAt_id s).const_mul k).ofReal_comp).mul_const Complex.I
    simpa using this
  exact h1.cexp

theorem hasDerivAt_scaled (F F' : ℝ → ℝ) (hF : ∀ s, HasDerivAt F (F' s) s) {a : ℝ} (s : ℝ) :
    HasDerivAt (fun s => ((F (s / a) : ℝ) : ℂ)) (((F' (s / a) / a : ℝ)) : ℂ) s := by
  have h := ((hF (s / a)).comp s ((hasDerivAt_id s).div_const a)).ofReal_comp
  simpa [div_eq_mul_inv] using h

/-- `G(s) = g(s/a) e^{iks}`. -/
noncomputable def Gc (a k s : ℝ) : ℂ := ((g (s / a) : ℝ) : ℂ) * ecar k s

/-- `G'`. -/
noncomputable def Gc1 (a k s : ℝ) : ℂ :=
  ((g1 (s / a) / a : ℝ) : ℂ) * ecar k s + ((g (s / a) : ℝ) : ℂ) * ((k : ℂ) * Complex.I) * ecar k s

/-- `G''`. -/
noncomputable def Gc2 (a k s : ℝ) : ℂ :=
  ((g2 (s / a) / a / a : ℝ) : ℂ) * ecar k s +
    2 * ((g1 (s / a) / a : ℝ) : ℂ) * ((k : ℂ) * Complex.I) * ecar k s +
    ((g (s / a) : ℝ) : ℂ) * ((k : ℂ) * Complex.I) ^ 2 * ecar k s

theorem hasDerivAt_Gc (a k s : ℝ) : HasDerivAt (Gc a k) (Gc1 a k s) s := by
  have h := (hasDerivAt_scaled g g1 hasDerivAt_g (a := a) s).mul (hasDerivAt_ecar k s)
  convert h using 1
  unfold Gc1
  ring

theorem hasDerivAt_Gc1 (a k s : ℝ) : HasDerivAt (Gc1 a k) (Gc2 a k s) s := by
  have h1 := (hasDerivAt_scaled (fun s => g1 s / a) (fun s => g2 s / a)
    (fun s => (hasDerivAt_g1 s).div_const a) (a := a) s).mul (hasDerivAt_ecar k s)
  have h2 := ((hasDerivAt_scaled g g1 hasDerivAt_g (a := a) s).mul_const
    ((k : ℂ) * Complex.I)).mul (hasDerivAt_ecar k s)
  have h := h1.add h2
  have hfun : Gc1 a k = fun s => ((g1 (s / a) / a : ℝ) : ℂ) * ecar k s +
      ((g (s / a) : ℝ) : ℂ) * ((k : ℂ) * Complex.I) * ecar k s := by
    funext s
    rfl
  rw [hfun]
  convert h using 1
  unfold Gc2
  push_cast
  ring

/-- `(d²/dτ²) [C F(x₀ + τ)]_{τ=0} = C F''(x₀)`. -/
theorem deriv2_shift {F F1 F2 : ℝ → ℂ} (h1 : ∀ s, HasDerivAt F (F1 s) s)
    (h2 : ∀ s, HasDerivAt F1 (F2 s) s) (C : ℂ) (x₀ : ℝ) :
    deriv (deriv fun τ : ℝ => C * F (x₀ + τ)) 0 = C * F2 x₀ := by
  have hd : deriv (fun τ : ℝ => C * F (x₀ + τ)) = fun τ => C * F1 (x₀ + τ) := by
    funext τ
    exact (((h1 (x₀ + τ)).comp_const_add x₀ τ).const_mul C).deriv
  rw [hd]
  have := (((h2 (x₀ + 0)).comp_const_add x₀ 0).const_mul C).deriv
  rw [this, add_zero]

/-! ### The anisotropic carrier trial -/

/-- The trial `u(x) = A g(x₀/a) g(x₁/b) e^{ikx₀}`. -/
noncomputable def trial (A a b k : ℝ) (x : R2) : ℂ :=
  (A : ℂ) * ((g (x 1 / b) : ℝ) : ℂ) * Gc a k (x 0)

theorem contDiff_trial (A a b k : ℝ) : ContDiff ℝ ∞ (trial A a b k) := by
  have hc0 : ContDiff ℝ ∞ fun x : R2 => x 0 :=
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 0).contDiff
  have hc1 : ContDiff ℝ ∞ fun x : R2 => x 1 :=
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 1).contDiff
  have hg0 : ContDiff ℝ ∞ fun x : R2 => ((g (x 0 / a) : ℝ) : ℂ) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_g.comp (hc0.div_const a))
  have hg1 : ContDiff ℝ ∞ fun x : R2 => ((g (x 1 / b) : ℝ) : ℂ) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_g.comp (hc1.div_const b))
  have he : ContDiff ℝ ∞ fun x : R2 => ecar k (x 0) := by
    unfold ecar
    exact Complex.contDiff_exp.comp ((Complex.ofRealCLM.contDiff.comp
      (contDiff_const.mul hc0)).mul contDiff_const)
  unfold trial Gc
  exact (contDiff_const.mul hg1).mul (hg0.mul he)

theorem trial_shift0 (A a b k : ℝ) (x : R2) (τ : ℝ) :
    trial A a b k (x + τ • EuclideanSpace.single 0 (1 : ℝ)) =
      ((A : ℂ) * ((g (x 1 / b) : ℝ) : ℂ)) * Gc a k (x 0 + τ) := by
  simp [trial, EuclideanSpace.single_apply]

theorem trial_shift1 (A a b k : ℝ) (x : R2) (τ : ℝ) :
    trial A a b k (x + τ • EuclideanSpace.single 1 (1 : ℝ)) =
      ((A : ℂ) * Gc a k (x 0)) * ((g ((x 1 + τ) / b) : ℝ) : ℂ) := by
  simp [trial, EuclideanSpace.single_apply]
  ring

theorem laplacian_trial (A a b k : ℝ) (x : R2) :
    Δ (trial A a b k) x = (A : ℂ) * ((g (x 1 / b) : ℝ) : ℂ) * Gc2 a k (x 0) +
      (A : ℂ) * Gc a k (x 0) * ((g2 (x 1 / b) / b / b : ℝ) : ℂ) := by
  rw [UVIllPosed.laplacian_eq_sum_second_deriv ((contDiff_trial A a b k).of_le
    (WithTop.coe_le_coe.2 le_top)) x, Fin.sum_univ_two]
  congr 1
  · simp_rw [trial_shift0]
    exact deriv2_shift (hasDerivAt_Gc a k) (hasDerivAt_Gc1 a k) _ (x 0)
  · simp_rw [trial_shift1]
    have h1 : ∀ s, HasDerivAt (fun s => ((g (s / b) : ℝ) : ℂ)) (((g1 (s / b) / b : ℝ)) : ℂ) s :=
      fun s => hasDerivAt_scaled g g1 hasDerivAt_g s
    have h2 : ∀ s, HasDerivAt (fun s => ((g1 (s / b) / b : ℝ) : ℂ))
        (((g2 (s / b) / b / b : ℝ)) : ℂ) s :=
      fun s => hasDerivAt_scaled (fun s => g1 s / b) (fun s => g2 s / b)
        (fun s => (hasDerivAt_g1 s).div_const b) s
    have := deriv2_shift h1 h2 ((A : ℂ) * Gc a k (x 0)) (x 1)
    simpa [add_div] using this

/-- `(Δ + k²)u = A e^{ikx₀} (P + iQ)` with real `P, Q`. -/
noncomputable def Pt (a b : ℝ) (x : R2) : ℝ :=
  g2 (x 0 / a) / a / a * g (x 1 / b) + g (x 0 / a) * (g2 (x 1 / b) / b / b)

noncomputable def Qt (a b k : ℝ) (x : R2) : ℝ := 2 * k * (g1 (x 0 / a) / a) * g (x 1 / b)

theorem shift_trial (A a b k : ℝ) (x : R2) :
    Δ (trial A a b k) x + ((k ^ 2 : ℝ) : ℂ) * trial A a b k x =
      (A : ℂ) * ecar k (x 0) * ((Pt a b x : ℂ) + (Qt a b k x : ℂ) * Complex.I) := by
  rw [laplacian_trial]
  unfold trial Gc Gc2 Pt Qt
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  push_cast
  linear_combination ((A : ℂ) * (g (x 1 / b) : ℂ) * (g (x 0 / a) : ℂ) * (k : ℂ) ^ 2 *
    ecar k (x 0)) * hI

theorem norm_shift_trial_sq (A a b k : ℝ) (x : R2) :
    ‖Δ (trial A a b k) x + ((k ^ 2 : ℝ) : ℂ) * trial A a b k x‖ ^ 2 =
      A ^ 2 * (Pt a b x ^ 2 + Qt a b k x ^ 2) := by
  rw [shift_trial, norm_mul, norm_mul, norm_ecar, Complex.norm_real, Real.norm_eq_abs, mul_one,
    mul_pow, sq_abs, ← Complex.normSq_eq_norm_sq, Complex.normSq_add_mul_I]

theorem norm_trial (A a b k : ℝ) (x : R2) :
    ‖trial A a b k x‖ = |A| * (g (x 0 / a) * g (x 1 / b)) := by
  unfold trial Gc
  rw [norm_mul, norm_mul, norm_mul, norm_ecar, Complex.norm_real, Complex.norm_real,
    Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (g_nonneg _), abs_of_nonneg (g_nonneg _)]
  ring

/-! ### Integrals of the trial -/

theorem continuous_g : Continuous g := contDiff_g.continuous

theorem continuous_g1 : Continuous g1 := contDiff_g1.continuous

theorem continuous_g2 : Continuous g2 := contDiff_g2.continuous

/-- `∫_{ℝ²} f(x₀/a) h(x₁/b) = (a∫f)(b∫h)`. -/
theorem integral_scaled_prod {f h : ℝ → ℝ} {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ x : R2, f (x 0 / a) * h (x 1 / b) = (a * ∫ s, f s) * (b * ∫ t, h t) := by
  rw [integral_prod_coords (fun s => f (s / a)) (fun t => h (t / b)), integral_scale f ha,
    integral_scale h hb]

theorem integrable_scaled_prod {f h : ℝ → ℝ} (hf : Integrable f) (hh : Integrable h) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) : Integrable fun x : R2 => f (x 0 / a) * h (x 1 / b) :=
  integrable_prod_coords (hf.comp_div ha.ne') (hh.comp_div hb.ne')

/-- One-dimensional profile integrals. -/
noncomputable def I0 : ℝ := ∫ s, g s ^ 2
noncomputable def I1 : ℝ := ∫ s, g1 s ^ 2
noncomputable def I2 : ℝ := ∫ s, g2 s ^ 2
noncomputable def I20 : ℝ := ∫ s, g2 s * g s
noncomputable def I4 : ℝ := ∫ s, g s ^ 4
noncomputable def I6 : ℝ := ∫ s, g s ^ 6

theorem cs_pow {F : ℝ → ℝ} (hF : Continuous F) (hc : HasCompactSupport F) (n : ℕ) (hn : n ≠ 0) :
    Integrable fun s => F s ^ n :=
  integrable_of_cs (hF.pow n) (hc.comp_left (g := fun x : ℝ => x ^ n) (by simp [hn]))

theorem I0_pos : 0 < I0 := by
  unfold I0
  refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 0) (continuous_g.pow 2)
    (hasCompactSupport_g.comp_left (g := fun x : ℝ => x ^ 2) (by simp)) (fun s => sq_nonneg _) ?_
  simp [g_zero]

theorem I4_pos : 0 < I4 := by
  unfold I4
  refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 0) (continuous_g.pow 4)
    (hasCompactSupport_g.comp_left (g := fun x : ℝ => x ^ 4) (by simp)) (fun s => by positivity) ?_
  simp [g_zero]

theorem I1_nonneg : 0 ≤ I1 := integral_nonneg fun _ => sq_nonneg _

theorem I6_nonneg : 0 ≤ I6 := integral_nonneg fun _ => by positivity

theorem I2_nonneg : 0 ≤ I2 := integral_nonneg fun _ => sq_nonneg _

/-- `∫ ‖(Δ + k²)u‖² = A² ab [I₂I₀/a⁴ + 2I₂₀²/(a²b²) + I₀I₂/b⁴ + 4k²I₁I₀/a²]`. -/
theorem integral_shift_trial (A k : ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ x, ‖Δ (trial A a b k) x + ((k ^ 2 : ℝ) : ℂ) * trial A a b k x‖ ^ 2 =
      A ^ 2 * (a * b) * (I2 * I0 / a ^ 4 + 2 * I20 ^ 2 / (a ^ 2 * b ^ 2) + I0 * I2 / b ^ 4 +
        4 * k ^ 2 * I1 * I0 / a ^ 2) := by
  simp_rw [norm_shift_trial_sq]
  have hint : ∀ {f h : ℝ → ℝ}, Continuous f → HasCompactSupport f → Continuous h →
      HasCompactSupport h → Integrable fun x : R2 => f (x 0 / a) * h (x 1 / b) :=
    fun hf hfc hh hhc => integrable_scaled_prod (integrable_of_cs hf hfc) (integrable_of_cs hh hhc)
      ha hb
  have hpt : ∀ x : R2, Pt a b x ^ 2 + Qt a b k x ^ 2 =
      (fun s => g2 s ^ 2 / a ^ 4) (x 0 / a) * (fun t => g t ^ 2) (x 1 / b) +
      (fun s => 2 * (g2 s * g s) / (a ^ 2 * b ^ 2)) (x 0 / a) * (fun t => g t * g2 t) (x 1 / b) +
      (fun s => g s ^ 2) (x 0 / a) * (fun t => g2 t ^ 2 / b ^ 4) (x 1 / b) +
      (fun s => 4 * k ^ 2 * g1 s ^ 2 / a ^ 2) (x 0 / a) * (fun t => g t ^ 2) (x 1 / b) := by
    intro x
    unfold Pt Qt
    field_simp
    ring
  simp_rw [hpt]
  have c2 : Continuous fun s => g2 s ^ 2 / a ^ 4 := (continuous_g2.pow 2).div_const _
  have c0 : Continuous fun t => g t ^ 2 := continuous_g.pow 2
  have c20 : Continuous fun s => 2 * (g2 s * g s) / (a ^ 2 * b ^ 2) :=
    (continuous_const.mul (continuous_g2.mul continuous_g)).div_const _
  have c02 : Continuous fun t => g t * g2 t := continuous_g.mul continuous_g2
  have c2b : Continuous fun t => g2 t ^ 2 / b ^ 4 := (continuous_g2.pow 2).div_const _
  have c1 : Continuous fun s => 4 * k ^ 2 * g1 s ^ 2 / a ^ 2 :=
    (continuous_const.mul (continuous_g1.pow 2)).div_const _
  have s2 : HasCompactSupport fun s => g2 s ^ 2 / a ^ 4 :=
    hasCompactSupport_g2.comp_left (g := fun x : ℝ => x ^ 2 / a ^ 4) (by simp)
  have s0 : HasCompactSupport fun t => g t ^ 2 :=
    hasCompactSupport_g.comp_left (g := fun x : ℝ => x ^ 2) (by simp)
  have s20 : HasCompactSupport fun s => 2 * (g2 s * g s) / (a ^ 2 * b ^ 2) := by
    have : HasCompactSupport fun s => g2 s * g s := hasCompactSupport_g.mul_left
    exact this.comp_left (g := fun x : ℝ => 2 * x / (a ^ 2 * b ^ 2)) (by simp)
  have s02 : HasCompactSupport fun t => g t * g2 t := hasCompactSupport_g2.mul_left
  have s2b : HasCompactSupport fun t => g2 t ^ 2 / b ^ 4 :=
    hasCompactSupport_g2.comp_left (g := fun x : ℝ => x ^ 2 / b ^ 4) (by simp)
  have s1 : HasCompactSupport fun s => 4 * k ^ 2 * g1 s ^ 2 / a ^ 2 :=
    hasCompactSupport_g1.comp_left (g := fun x : ℝ => 4 * k ^ 2 * x ^ 2 / a ^ 2) (by simp)
  have h1 := hint c2 s2 c0 s0
  have h2 := hint c20 s20 c02 s02
  have h3 := hint c0 s0 c2b s2b
  have h4 := hint c1 s1 c0 s0
  have h12 : Integrable fun x : R2 =>
      g2 (x 0 / a) ^ 2 / a ^ 4 * g (x 1 / b) ^ 2 +
        2 * (g2 (x 0 / a) * g (x 0 / a)) / (a ^ 2 * b ^ 2) * (g (x 1 / b) * g2 (x 1 / b)) :=
    h1.add h2
  have h123 : Integrable fun x : R2 =>
      g2 (x 0 / a) ^ 2 / a ^ 4 * g (x 1 / b) ^ 2 +
        2 * (g2 (x 0 / a) * g (x 0 / a)) / (a ^ 2 * b ^ 2) * (g (x 1 / b) * g2 (x 1 / b)) +
        g (x 0 / a) ^ 2 * (g2 (x 1 / b) ^ 2 / b ^ 4) :=
    h12.add h3
  rw [integral_const_mul, integral_add h123 h4, integral_add h12 h3, integral_add h1 h2,
    integral_scaled_prod (f := fun s => g2 s ^ 2 / a ^ 4) (h := fun t => g t ^ 2) ha hb,
    integral_scaled_prod (f := fun s => 2 * (g2 s * g s) / (a ^ 2 * b ^ 2))
      (h := fun t => g t * g2 t) ha hb,
    integral_scaled_prod (f := fun s => g s ^ 2) (h := fun t => g2 t ^ 2 / b ^ 4) ha hb,
    integral_scaled_prod (f := fun s => 4 * k ^ 2 * g1 s ^ 2 / a ^ 2) (h := fun t => g t ^ 2)
      ha hb]
  unfold I0 I1 I2 I20
  simp only [integral_div, integral_const_mul]
  have hI20 : ∫ t, g t * g2 t = ∫ s, g2 s * g s := by
    congr 1
    funext t
    ring
  rw [hI20]
  field_simp

theorem integral_trial_pow (A k : ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (n : ℕ) :
    ∫ x, ‖trial A a b k x‖ ^ n = |A| ^ n * ((a * ∫ s, g s ^ n) * (b * ∫ t, g t ^ n)) := by
  simp_rw [norm_trial, mul_pow]
  rw [integral_const_mul, integral_scaled_prod (f := fun s => g s ^ n) (h := fun t => g t ^ n) ha hb]

theorem integral_trial_sq (A k : ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ x, ‖trial A a b k x‖ ^ 2 = A ^ 2 * (a * b) * I0 ^ 2 := by
  rw [integral_trial_pow A k ha hb 2, sq_abs, I0]
  ring

theorem integral_trial_four (A k : ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ x, ‖trial A a b k x‖ ^ 4 = A ^ 4 * (a * b) * I4 ^ 2 := by
  rw [integral_trial_pow A k ha hb 4, I4,
    show |A| ^ 4 = A ^ 4 by rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, sq_abs, ← pow_mul]]
  ring

theorem integral_trial_six (A k : ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ x, ‖trial A a b k x‖ ^ 6 = A ^ 6 * (a * b) * I6 ^ 2 := by
  rw [integral_trial_pow A k ha hb 6, I6,
    show |A| ^ 6 = A ^ 6 by rw [show (6 : ℕ) = 2 * 3 by rfl, pow_mul, sq_abs, ← pow_mul]]
  ring

theorem g_eq_zero_of_two_lt {s : ℝ} (hs : 2 < |s|) : g s = 0 :=
  bump1.zero_of_le_dist (by simp [bump1]; linarith)

theorem hasCompactSupport_trial (A k : ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    HasCompactSupport (trial A a b k) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : R2) (2 * a + 2 * b)) fun x hx => ?_
  rw [Metric.mem_closedBall, dist_zero_right, not_le] at hx
  have hnorm : ‖x‖ ≤ |x 0| + |x 1| := by
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
    rw [Real.sqrt_le_left (by positivity)]
    simp only [Real.norm_eq_abs, sq_abs]
    nlinarith [mul_nonneg (abs_nonneg (x 0)) (abs_nonneg (x 1)), sq_abs (x 0), sq_abs (x 1)]
  by_cases h0 : 2 * a < |x 0|
  · have : g (x 0 / a) = 0 := g_eq_zero_of_two_lt (by
      rw [abs_div, abs_of_pos ha, lt_div_iff₀ ha]
      linarith)
    simp [trial, Gc, this]
  · have h1 : 2 * b < |x 1| := by
      push_neg at h0
      linarith
    have : g (x 1 / b) = 0 := g_eq_zero_of_two_lt (by
      rw [abs_div, abs_of_pos hb, lt_div_iff₀ hb]
      linarith)
    simp [trial, this]

/-- The trial as a Schwartz function. -/
noncomputable def trialS (A a b k : ℝ) (ha : 0 < a) (hb : 0 < b) : SchwartzMap R2 ℂ :=
  Sobolev.schwartzOfCompact (trial A a b k) (contDiff_trial A a b k)
    (hasCompactSupport_trial A k ha hb)

/-- The trial as an element of `H²(ℝ²)`. -/
noncomputable def trialH (A a b k : ℝ) (ha : 0 < a) (hb : 0 < b) : Sobolev.H2 2 :=
  Sobolev.H2.ofSchwartz (trialS A a b k ha hb)

end NegativeEnergy

end ReyesMath

namespace ReyesMath

namespace Sobolev

namespace H2

/-- `M(u) = ∫ |u|²`. -/
theorem M_eq_integral {d : ℕ} (U : H2 d) : M U = ∫ x, ‖U.val x‖ ^ 2 := by
  rw [M, @norm_sq_eq_re_inner ℂ, L2.inner_def]
  simp_rw [inner_self_complex]
  rw [integral_complex_ofReal]
  simp

/-- The fourth-order cubic–quintic energy
`H(u) = ‖(Δ + k²)u‖² − (β/2)‖u‖⁴_{L⁴} + (γ/3)‖u‖⁶_{L⁶}` on `H²(ℝ²; ℂ)`. -/
noncomputable def energy (β γ k : ℝ) (U : H2 2) : ℝ :=
  ‖U.lap + ((k ^ 2 : ℝ) : ℂ) • U.val‖ ^ 2 - β / 2 * Q U + γ / 3 * S U

/-- `I(m) = inf {H(u) : u ∈ H²(ℝ²; ℂ), ‖u‖²₂ = m}`. -/
noncomputable def Imin (β γ k m : ℝ) : ℝ := sInf (energy β γ k '' {U | M U = m})

/-- The pointwise square completion
`−(β/2)r² + (γ/3)r³ = (γ/3) r (r − 3β/(4γ))² − (3β²/(16γ)) r`. -/
theorem square_completion {β γ : ℝ} (hγ : 0 < γ) (r : ℝ) :
    -β / 2 * r ^ 2 + γ / 3 * r ^ 3 = γ / 3 * r * (r - 3 * β / (4 * γ)) ^ 2 - 3 * β ^ 2 / (16 * γ) * r := by
  field_simp
  ring

/-- **Coercive lower bound:** `H(u) ≥ ‖(Δ+k²)u‖² − (3β²/(16γ)) M(u)`. -/
theorem energy_ge (β γ k : ℝ) (hγ : 0 < γ) (U : H2 2) :
    ‖U.lap + ((k ^ 2 : ℝ) : ℂ) • U.val‖ ^ 2 - 3 * β ^ 2 / (16 * γ) * M U ≤ energy β γ k U := by
  have hQ := integrable_Q U
  have hS := integrable_S U
  have h2 := integrable_sq_val U
  have hpt : ∀ x : EuclideanSpace ℝ (Fin 2), -(3 * β ^ 2 / (16 * γ)) * ‖U.val x‖ ^ 2 ≤
      -β / 2 * ‖U.val x‖ ^ 4 + γ / 3 * ‖U.val x‖ ^ 6 := by
    intro x
    have h := square_completion (β := β) hγ (‖U.val x‖ ^ 2)
    rw [show ‖U.val x‖ ^ 4 = (‖U.val x‖ ^ 2) ^ 2 by ring,
      show ‖U.val x‖ ^ 6 = (‖U.val x‖ ^ 2) ^ 3 by ring, h]
    have : 0 ≤ γ / 3 * ‖U.val x‖ ^ 2 * (‖U.val x‖ ^ 2 - 3 * β / (4 * γ)) ^ 2 := by positivity
    linarith
  have hQS : Integrable fun x => -β / 2 * ‖U.val x‖ ^ 4 + γ / 3 * ‖U.val x‖ ^ 6 :=
    (hQ.const_mul (-β / 2)).add (hS.const_mul (γ / 3))
  have hint := integral_mono (h2.const_mul _) hQS hpt
  rw [integral_const_mul, integral_add (hQ.const_mul _) (hS.const_mul _), integral_const_mul,
    integral_const_mul, ← M_eq_integral] at hint
  unfold energy Q S
  linarith

theorem energy_ge_mass (β γ k : ℝ) (hγ : 0 < γ) (U : H2 2) :
    -(3 * β ^ 2 / (16 * γ)) * M U ≤ energy β γ k U := by
  have := energy_ge β γ k hγ U
  have h0 : 0 ≤ ‖U.lap + ((k ^ 2 : ℝ) : ℂ) • U.val‖ ^ 2 := sq_nonneg _
  linarith

end H2

end Sobolev

end ReyesMath

namespace ReyesMath

namespace NegativeEnergy

open Sobolev Sobolev.H2

local notation "R2" => EuclideanSpace ℝ (Fin 2)

theorem coe_trialS (A a b k : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ⇑(trialS A a b k ha hb) = trial A a b k := rfl

theorem integral_val_pow (A a b k : ℝ) (ha : 0 < a) (hb : 0 < b) (n : ℕ) :
    ∫ x, ‖(trialH A a b k ha hb).val x‖ ^ n = ∫ x, ‖trial A a b k x‖ ^ n := by
  refine integral_congr_ae ?_
  filter_upwards [coeFn_toL2 (trialS A a b k ha hb)] with x hx
  simp only [trialH, ofSchwartz]
  rw [hx, coe_trialS]

theorem M_trialH (A a b k : ℝ) (ha : 0 < a) (hb : 0 < b) :
    M (trialH A a b k ha hb) = A ^ 2 * (a * b) * I0 ^ 2 := by
  rw [M_eq_integral, integral_val_pow, integral_trial_sq A k ha hb]

theorem kinetic_trialH (A a b k : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ‖(trialH A a b k ha hb).lap + ((k ^ 2 : ℝ) : ℂ) • (trialH A a b k ha hb).val‖ ^ 2 =
      A ^ 2 * (a * b) * (I2 * I0 / a ^ 4 + 2 * I20 ^ 2 / (a ^ 2 * b ^ 2) + I0 * I2 / b ^ 4 +
        4 * k ^ 2 * I1 * I0 / a ^ 2) := by
  simp only [trialH, ofSchwartz]
  rw [← map_smul, ← map_add, norm_toL2_sq, ← integral_shift_trial A k ha hb]
  congr 1
  funext x
  rw [SchwartzMap.add_apply, SchwartzMap.smul_apply, lapS_apply, coe_trialS, smul_eq_mul]

theorem energy_trialH (β γ A a b k : ℝ) (ha : 0 < a) (hb : 0 < b) :
    energy β γ k (trialH A a b k ha hb) =
      A ^ 2 * (a * b) * (I2 * I0 / a ^ 4 + 2 * I20 ^ 2 / (a ^ 2 * b ^ 2) + I0 * I2 / b ^ 4 +
        4 * k ^ 2 * I1 * I0 / a ^ 2) - β / 2 * (A ^ 4 * (a * b) * I4 ^ 2) +
        γ / 3 * (A ^ 6 * (a * b) * I6 ^ 2) := by
  rw [energy, kinetic_trialH, Q, S, integral_val_pow, integral_val_pow,
    integral_trial_four A k ha hb, integral_trial_six A k ha hb]

/-- **Strict negativity at every positive mass.**  For `β > 0` and every `m > 0` there is an
anisotropic carrier trial `u ∈ H²(ℝ²; ℂ)` with `‖u‖²₂ = m` and `H(u) < 0`. -/
theorem exists_negative {β γ k m : ℝ} (hβ : 0 < β) (hm : 0 < m) :
    ∃ U : H2 2, M U = m ∧ energy β γ k U < 0 := by
  have hI0 := I0_pos
  have hI4 := I4_pos
  have hI1 := I1_nonneg
  have hI0ne : I0 ≠ 0 := hI0.ne'
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = 8 * k ^ 2 * I1 * I0 ^ 3 / (β * m * I4 ^ 2) + 1 := ⟨_, rfl⟩
  have hLpos : 0 < L := by
    have : 0 ≤ 8 * k ^ 2 * I1 * I0 ^ 3 / (β * m * I4 ^ 2) := by positivity
    linarith
  have hLne : L ≠ 0 := hLpos.ne'
  obtain ⟨c2, hc2⟩ : ∃ c2 : ℝ,
      c2 = 4 * k ^ 2 * m * I1 / (I0 * L ^ 2) - β / 2 * m ^ 2 * I4 ^ 2 / (L * I0 ^ 4) := ⟨_, rfl⟩
  obtain ⟨c4, hc4⟩ : ∃ c4 : ℝ, c4 = m / I0 ^ 2 * (I2 * I0 / L ^ 4 + 2 * I20 ^ 2 / L ^ 2 + I0 * I2) +
      γ / 3 * m ^ 3 * I6 ^ 2 / (L ^ 2 * I0 ^ 6) := ⟨_, rfl⟩
  have hc2neg : c2 < 0 := by
    have hlt : 8 * k ^ 2 * I1 * I0 ^ 3 / (β * m * I4 ^ 2) < L := by linarith
    rw [div_lt_iff₀ (by positivity)] at hlt
    have : c2 = m / (L * I0 ^ 4) * (4 * k ^ 2 * I1 * I0 ^ 3 / L - β / 2 * m * I4 ^ 2) := by
      rw [hc2]
      field_simp
    rw [this]
    apply mul_neg_of_pos_of_neg (by positivity)
    rw [sub_neg, div_lt_iff₀ hLpos]
    nlinarith
  have hnc2 : 0 < -c2 := by linarith
  have hq : 0 ≤ 2 * |c4| / (-c2) := div_nonneg (by positivity) hnc2.le
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = Real.sqrt (2 * |c4| / (-c2) + 1) := ⟨_, rfl⟩
  have hRpos : 0 < R := by rw [hR]; exact Real.sqrt_pos.2 (by linarith)
  have hRne : R ≠ 0 := hRpos.ne'
  have hR2 : R ^ 2 = 2 * |c4| / (-c2) + 1 := by rw [hR]; exact Real.sq_sqrt (by linarith)
  have hapos : 0 < L * R := mul_pos hLpos hRpos
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = m / (L * R * R * I0 ^ 2) := ⟨_, rfl⟩
  have hXpos : 0 < X := by rw [hX]; positivity
  have hA2 : Real.sqrt X ^ 2 = X := Real.sq_sqrt hXpos.le
  refine ⟨trialH (Real.sqrt X) (L * R) R k hapos hRpos, ?_, ?_⟩
  · rw [M_trialH, hA2, hX]
    field_simp
  · rw [energy_trialH]
    have hA4 : Real.sqrt X ^ 4 = X ^ 2 := by rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, hA2]
    have hA6 : Real.sqrt X ^ 6 = X ^ 3 := by rw [show (6 : ℕ) = 2 * 3 by rfl, pow_mul, hA2]
    rw [hA2, hA4, hA6]
    have hE : X * (L * R * R) * (I2 * I0 / (L * R) ^ 4 + 2 * I20 ^ 2 / ((L * R) ^ 2 * R ^ 2) +
        I0 * I2 / R ^ 4 + 4 * k ^ 2 * I1 * I0 / (L * R) ^ 2) -
        β / 2 * (X ^ 2 * (L * R * R) * I4 ^ 2) + γ / 3 * (X ^ 3 * (L * R * R) * I6 ^ 2) =
        c2 / R ^ 2 + c4 / R ^ 4 := by
      rw [hX, hc2, hc4]
      field_simp
      ring
    rw [hE]
    have hc4R : c4 / R ^ 2 ≤ -c2 / 2 := by
      have h1 : c4 ≤ |c4| := le_abs_self c4
      have h2 : 2 * |c4| / (-c2) ≤ R ^ 2 := by rw [hR2]; linarith
      rw [div_le_iff₀ hnc2] at h2
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    have : c2 / R ^ 2 + c4 / R ^ 4 = (c2 + c4 / R ^ 2) / R ^ 2 := by
      field_simp
    rw [this]
    apply div_neg_of_neg_of_pos _ (by positivity)
    linarith

/-- **Theorem (negative constrained energy at every positive mass).**  For `β, γ > 0`, every
`k`, and every `m > 0`,
`−(3β²/(16γ)) m ≤ I(m) < 0`, where `I(m) = inf {H(u) : u ∈ H²(ℝ²; ℂ), ‖u‖²₂ = m}`. -/
theorem negative_constrained_energy {β γ k m : ℝ} (hβ : 0 < β) (hγ : 0 < γ) (hm : 0 < m) :
    -(3 * β ^ 2 / (16 * γ)) * m ≤ Imin β γ k m ∧ Imin β γ k m < 0 := by
  obtain ⟨U, hUm, hUneg⟩ := exists_negative (β := β) (γ := γ) (k := k) hβ hm
  have hne : (energy β γ k '' {U | M U = m}).Nonempty := ⟨_, U, hUm, rfl⟩
  have hbdd : BddBelow (energy β γ k '' {U | M U = m}) := by
    refine ⟨-(3 * β ^ 2 / (16 * γ)) * m, ?_⟩
    rintro _ ⟨V, hV, rfl⟩
    have := energy_ge_mass β γ k hγ V
    rw [hV] at this
    exact this
  constructor
  · apply le_csInf hne
    rintro _ ⟨V, hV, rfl⟩
    have := energy_ge_mass β γ k hγ V
    rw [hV] at this
    exact this
  · exact lt_of_le_of_lt (csInf_le hbdd ⟨U, hUm, rfl⟩) hUneg

end NegativeEnergy

end ReyesMath
