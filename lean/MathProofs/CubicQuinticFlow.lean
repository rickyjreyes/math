import Mathlib
import MathProofs.H2Algebra

/-!
# Global `H²(ℝ²)` well-posedness and conservation for the cubic–quintic flow (F01/T3, part 3)

The Cauchy problem `i ∂ₜu = (Δ + k²)²u − β|u|²u + γ|u|⁴u`, `u(0) = u₀ ∈ H²(ℝ²)`, for the
proposition "global well-posedness and conservation" of
`papers/orbital-stability-fourth-order-cubic-quintic/main.tex`.

* Interaction picture `w(t) = U(−t)u(t)` with `w' = G(t, w) = −i U(−t) F(U(t)w)`
  (`Sobolev.Gfield`), and the product rule against the weak generator
  (`Sobolev.hasDerivAt_inner_Usp`).
* Conservation laws in infinitesimal form: `Sobolev.hasDerivAt_mass` and `Sobolev.hasDerivAt_Esp`
  (`d/dt H(U(t)w(t)) = 0`, using `Sobolev.Nsp_taylor` for the potential).
* Truncation by the radial retraction (`Sobolev.retr`, `2`-Lipschitz) and Picard–Lindelöf on every
  `[−T, T]` (`Sobolev.exists_global_tr`); the a priori bound `Sobolev.norm_toSp_sq_le` from
  coercivity; global existence by a clopen argument with conservation (`Sobolev.exists_global`);
  uniqueness `Sobolev.ode_unique`; the Gronwall estimate `Sobolev.ode_dist_le`.
* Solutions of the PDE, `Sobolev.IsSolution`: `u ∈ C(ℝ; H²)` and the equation in the sense of
  distributions against every Schwartz test function; they are exactly the interaction-picture
  solutions (`Sobolev.isSolution_of_ode`, `Sobolev.ode_of_isSolution`).
* `Sobolev.global_wellposed` (unique global solution for every datum, `γ > 0`),
  `Sobolev.continuous_dependence` (uniformly on `[−T, T]`) and `Sobolev.conservation`
  (`M(u(t)) = M(u₀)`, `H(u(t)) = H(u₀)`).
-/

open Filter Topology Complex InnerProductSpace MeasureTheory Set
open scoped ContDiff FourierTransform

namespace ReyesMath

namespace Sobolev

local notation "R2" => EuclideanSpace ℝ (Fin 2)

variable {β γ k : ℝ}

/-- The interaction-picture vector field `G(t, w) = −i U(−t) F(U(t) w)`. -/
noncomputable def Gfield (β γ k : ℝ) (t : ℝ) (e : Hsp 2) : Hsp 2 :=
  (-Complex.I) • Usp k (-t) (Fnl β γ (Usp k t e))

/-- `u ↦ u ∈ L²` as a continuous linear map. -/
noncomputable def vlL : Hsp 2 →L[ℂ] L2 2 where
  toFun := vl
  map_add' := vl_add
  map_smul' := vl_smul
  cont := continuous_vl

/-- `u ↦ (Δ + k²)u ∈ L²` as a continuous linear map. -/
noncomputable def AspL (k : ℝ) : Hsp 2 →L[ℂ] L2 2 where
  toFun := Asp k
  map_add' := Asp_add k
  map_smul' := Asp_smul k
  cont := continuous_Asp k

theorem hasDerivAt_vl {w : ℝ → Hsp 2} {w' : Hsp 2} {t : ℝ} (hw : HasDerivAt w w' t) :
    HasDerivAt (fun s => vl (w s)) (vl w') t :=
  (vlL.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hw

theorem hasDerivAt_Asp {w : ℝ → Hsp 2} {w' : Hsp 2} {t : ℝ} (hw : HasDerivAt w w' t) :
    HasDerivAt (fun s => Asp k (w s)) (Asp k w') t :=
  ((AspL k).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hw

theorem vl_Gfield (t : ℝ) (e : Hsp 2) :
    vl (Gfield β γ k t e) = (-Complex.I) • U2 k (-t) (vl (Fnl β γ (Usp k t e))) := by
  rw [Gfield, vl_smul, vl_Usp]

theorem Asp_Gfield (t : ℝ) (e : Hsp 2) :
    Asp k (Gfield β γ k t e) = (-Complex.I) • U2 k (-t) (Asp k (Fnl β γ (Usp k t e))) := by
  rw [Gfield, Asp_smul, Asp_Usp]

theorem re_neg_I_mul (z : ℂ) : (-Complex.I * z).re = z.im := by
  simp [Complex.mul_re]

/-- The real inner product of `L²(ℝ²; ℂ)` is the real part of the complex one. -/
theorem real_inner_L2 (f g : L2 2) : (inner ℝ f g : ℝ) = (inner ℂ f g).re := by
  rw [L2.inner_def, L2.inner_def, ← RCLike.re_to_complex, ← integral_re (L2.integrable_inner _ _)]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [Complex.inner, RCLike.inner_apply, RCLike.re_to_complex]

/-- **Conservation of mass** (infinitesimal form). -/
theorem hasDerivAt_mass {w : ℝ → Hsp 2} {t : ℝ} (hw : HasDerivAt w (Gfield β γ k t (w t)) t) :
    HasDerivAt (fun s => ‖vl (w s)‖ ^ 2) 0 t := by
  have h := (hasDerivAt_vl hw).norm_sq
  convert h using 1
  rw [real_inner_L2, vl_Gfield, inner_smul_right, ← inner_U2, ← vl_Usp, re_neg_I_mul,
    inner_vl_Fnl_im, mul_zero]

/-- The derivative of the kinetic term `‖A w(t)‖²`. -/
theorem hasDerivAt_kin {w : ℝ → Hsp 2} {t : ℝ} (hw : HasDerivAt w (Gfield β γ k t (w t)) t) :
    HasDerivAt (fun s => ‖Asp k (w s)‖ ^ 2)
      (2 * (-Complex.I * inner ℂ (Asp k (Usp k t (w t)))
        (Asp k (Fnl β γ (Usp k t (w t))))).re) t := by
  have h := (hasDerivAt_Asp (k := k) hw).norm_sq
  convert h using 1
  rw [real_inner_L2, Asp_Gfield, inner_smul_right, ← inner_U2, ← Asp_Usp]

end Sobolev

end ReyesMath

open Filter Topology Complex InnerProductSpace MeasureTheory Set
open scoped ContDiff FourierTransform

namespace ReyesMath

namespace Sobolev

local notation "R2" => EuclideanSpace ℝ (Fin 2)

variable {β γ k : ℝ}

/-- `U(t+h)w(t+h) − U(t)w(t) = U(t+h)(w(t+h) − w(t)) + (U(h)u(t) − u(t))`. -/
theorem vl_Usp_split (k t h : ℝ) (w : ℝ → Hsp 2) :
    vl (Usp k (t + h) (w (t + h))) - vl (Usp k t (w t)) =
      vl (Usp k (t + h) (w (t + h) - w t)) +
        (vl (Usp k h (Usp k t (w t))) - vl (Usp k t (w t))) := by
  rw [map_sub, vl_sub, ← Usp_add, add_comm h t]
  abel

theorem tendsto_add_nhdsNE (t : ℝ) : Tendsto (fun h : ℝ => t + h) (𝓝[≠] 0) (𝓝 t) := by
  have h : Tendsto (fun h : ℝ => t + h) (𝓝 0) (𝓝 (t + 0)) := tendsto_const_nhds.add tendsto_id
  rw [add_zero] at h
  exact h.mono_left nhdsWithin_le_nhds

/-- The difference quotient of `w`, with the real scalar written as a complex one. -/
theorem tendsto_slope_complex {w : ℝ → Hsp 2} {w' : Hsp 2} {t : ℝ} (hw : HasDerivAt w w' t) :
    Tendsto (fun h : ℝ => ((h⁻¹ : ℝ) : ℂ) • (w (t + h) - w t)) (𝓝[≠] 0) (𝓝 w') :=
  hasDerivAt_iff_tendsto_slope_zero.1 hw

/-- Difference quotients of `w`, transported by `U(t + h)`. -/
theorem tendsto_Usp_slope {w : ℝ → Hsp 2} {w' : Hsp 2} {t : ℝ} (hw : HasDerivAt w w' t) :
    Tendsto (fun h : ℝ => Usp k (t + h) (((h⁻¹ : ℝ) : ℂ) • (w (t + h) - w t))) (𝓝[≠] 0)
      (𝓝 (Usp k t w')) := by
  have h1 := tendsto_slope_complex hw
  have h2 := (tendsto_add_nhdsNE t).prodMk_nhds h1
  have h3 := ((continuous_Usp_uncurry (d := 2) k).tendsto (t, w')).comp h2
  exact h3

theorem slope_inner_Usp (k : ℝ) (f : Hsp 2) (w : ℝ → Hsp 2) (t h : ℝ) :
    h⁻¹ • (inner ℂ (vl f) (vl (Usp k (t + h) (w (t + h)))) -
        inner ℂ (vl f) (vl (Usp k t (w t)))) =
      inner ℂ (vl f) (vl (Usp k (t + h) (((h⁻¹ : ℝ) : ℂ) • (w (t + h) - w t)))) +
        Qh k h f (Usp k t (w t)) := by
  rw [← inner_sub_right, vl_Usp_split, inner_add_right, smul_add, Qh, map_smul, vl_smul,
    inner_smul_right, Complex.real_smul, Complex.real_smul, Complex.ofReal_inv]

/-- **Product rule** for `s ↦ ⟪f, U(s) w(s)⟫_{L²}`. -/
theorem hasDerivAt_inner_Usp (f : Hsp 2) {w : ℝ → Hsp 2} {w' : Hsp 2} {t : ℝ}
    (hw : HasDerivAt w w' t) :
    HasDerivAt (fun s => inner ℂ (vl f) (vl (Usp k s (w s))))
      (inner ℂ (vl f) (vl (Usp k t w')) + Lw k f (Usp k t (w t))) t := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  have hA : Tendsto (fun h : ℝ =>
      inner ℂ (vl f) (vl (Usp k (t + h) (((h⁻¹ : ℝ) : ℂ) • (w (t + h) - w t)))))
      (𝓝[≠] 0) (𝓝 (inner ℂ (vl f) (vl (Usp k t w')))) :=
    tendsto_const_nhds.inner ((continuous_vl.tendsto _).comp (tendsto_Usp_slope hw))
  refine (hA.add (tendsto_Qh k f (Usp k t (w t)))).congr fun h => ?_
  exact (slope_inner_Usp k f w t h).symm

theorem sq_div_arith {x a b c h : ℝ} (hh : 0 < h) (hx : 0 ≤ x) (ha : 0 ≤ a)
    (hxab : x ≤ a + b) (hac : a ≤ c) :
    x ^ 2 / h ≤ 2 * (h * (c / h) ^ 2) + 2 * (b ^ 2 / h) := by
  have h1 : x ^ 2 ≤ 2 * c ^ 2 + 2 * b ^ 2 := by
    have e1 : x ^ 2 ≤ (a + b) ^ 2 := pow_le_pow_left₀ hx hxab 2
    have e2 : a ^ 2 ≤ c ^ 2 := pow_le_pow_left₀ ha hac 2
    nlinarith [sq_nonneg (a - b)]
  have h2 : 2 * (h * (c / h) ^ 2) + 2 * (b ^ 2 / h) = (2 * c ^ 2 + 2 * b ^ 2) / h := by
    field_simp
  rw [h2]
  exact div_le_div_of_nonneg_right h1 hh.le

/-- `‖u(t+h) − u(t)‖²_{L²} = o(h)` for `u(s) = U(s) w(s)` with `w` differentiable. -/
theorem tendsto_norm_vl_sq_div {w : ℝ → Hsp 2} {w' : Hsp 2} {t : ℝ} (hw : HasDerivAt w w' t) :
    Tendsto (fun h : ℝ => ‖vl (Usp k (t + h) (w (t + h))) - vl (Usp k t (w t))‖ ^ 2 / |h|)
      (𝓝[≠] 0) (𝓝 0) := by
  have h1 := tendsto_slope_complex hw
  have habs : Tendsto (fun h : ℝ => |h|) (𝓝[≠] 0) (𝓝 0) := by
    have h := continuous_abs.tendsto (0 : ℝ)
    rw [abs_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun h : ℝ => |h| * ‖((h⁻¹ : ℝ) : ℂ) • (w (t + h) - w t)‖ ^ 2) (𝓝[≠] 0)
      (𝓝 (0 * ‖w'‖ ^ 2)) := habs.mul (h1.norm.pow 2)
  rw [zero_mul] at h2
  have h3 := tendsto_norm_vl_Usp_sub_sq_div k (Usp k t (w t))
  have h4 := (h2.const_mul 2).add (h3.const_mul 2)
  rw [mul_zero, add_zero] at h4
  refine squeeze_zero' (Eventually.of_forall fun h => by positivity) ?_ h4
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh' : 0 < |h| := abs_pos.2 hh
  have hn : ‖((h⁻¹ : ℝ) : ℂ) • (w (t + h) - w t)‖ = ‖w (t + h) - w t‖ / |h| := by
    rw [norm_smul, Complex.norm_real, norm_inv, Real.norm_eq_abs, inv_mul_eq_div]
  have ha : ‖vl (Usp k (t + h) (w (t + h) - w t))‖ ≤ ‖w (t + h) - w t‖ :=
    calc ‖vl (Usp k (t + h) (w (t + h) - w t))‖ ≤ ‖Usp k (t + h) (w (t + h) - w t)‖ :=
          norm_vl_le _
      _ = ‖w (t + h) - w t‖ := norm_Usp _ _ _
  rw [hn, vl_Usp_split]
  exact sq_div_arith hh' (norm_nonneg _) (norm_nonneg _) (norm_add_le _ _) ha

/-- The derivative of the potential term `N(U(s) w(s))` along a differentiable `w`. -/
theorem hasDerivAt_Nsp_Usp {w : ℝ → Hsp 2} {w' : Hsp 2} {t : ℝ} (hw : HasDerivAt w w' t) :
    HasDerivAt (fun s => Nsp β γ (Usp k s (w s)))
      (2 * (inner ℂ (vl (Fnl β γ (Usp k t (w t)))) (vl (Usp k t w')) +
        Lw k (Fnl β γ (Usp k t (w t))) (Usp k t (w t))).re) t := by
  obtain ⟨u, hu⟩ : ∃ u, u = Usp k t (w t) := ⟨_, rfl⟩
  obtain ⟨f, hf⟩ : ∃ f, f = Fnl β γ u := ⟨_, rfl⟩
  rw [← hu, ← hf]
  have hL := hasDerivAt_inner_Usp (k := k) f hw
  rw [← hu] at hL
  have hL' : HasDerivAt (fun s => 2 * (inner ℂ (vl f) (vl (Usp k s (w s)))).re)
      (2 * (inner ℂ (vl f) (vl (Usp k t w')) + Lw k f u).re) t :=
    (Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hL).const_mul 2
  -- the remainder is `o(h)`
  obtain ⟨R, hR⟩ : ∃ R, R = ‖w t‖ + 1 := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C, C = 3 * |β| * R ^ 2 + 5 * |γ| * R ^ 4 := ⟨_, rfl⟩
  have hev : ∀ᶠ h in 𝓝[≠] (0 : ℝ), ‖w (t + h)‖ < R := by
    rw [hR]
    exact (hw.continuousAt.tendsto.comp (tendsto_add_nhdsNE t)).norm.eventually
      (gt_mem_nhds (lt_add_one _))
  have hrem : HasDerivAt (fun s => Nsp β γ (Usp k s (w s)) -
      2 * (inner ℂ (vl f) (vl (Usp k s (w s)))).re) 0 t := by
    rw [hasDerivAt_iff_tendsto_slope_zero]
    have hlim := (tendsto_norm_vl_sq_div (k := k) hw).const_mul C
    rw [mul_zero] at hlim
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [hev, self_mem_nhdsWithin] with h hh hh0
    have hh' : 0 < |h| := abs_pos.2 hh0
    have hu0 : ‖u‖ ≤ R := by rw [hu, norm_Usp, hR]; linarith
    have hu1 : ‖Usp k (t + h) (w (t + h))‖ ≤ R := by rw [norm_Usp]; exact hh.le
    have hT := Nsp_taylor β γ hu0 hu1
    rw [← hf, ← hC] at hT
    rw [hu] at hT
    have heq : Nsp β γ (Usp k (t + h) (w (t + h))) -
          2 * (inner ℂ (vl f) (vl (Usp k (t + h) (w (t + h))))).re -
          (Nsp β γ (Usp k t (w t)) - 2 * (inner ℂ (vl f) (vl (Usp k t (w t)))).re) =
        Nsp β γ (Usp k (t + h) (w (t + h))) - Nsp β γ (Usp k t (w t)) -
          2 * (inner ℂ (vl f) (vl (Usp k (t + h) (w (t + h))) - vl (Usp k t (w t)))).re := by
      rw [inner_sub_right, Complex.sub_re]
      ring
    beta_reduce
    rw [heq, norm_smul, norm_inv, Real.norm_eq_abs, Real.norm_eq_abs, inv_mul_eq_div,
      mul_div_assoc']
    exact div_le_div_of_nonneg_right hT hh'.le
  have h := hrem.add hL'
  rw [zero_add] at h
  refine h.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
  exact (sub_add_cancel _ _).symm

theorem re_inner_neg_I_smul_self (x : L2 2) : (inner ℂ x ((-Complex.I) • x)).re = 0 := by
  rw [inner_smul_right, re_neg_I_mul, ← RCLike.im_to_complex, inner_self_im]

theorem Usp_Gfield (t : ℝ) (e : Hsp 2) :
    Usp k t (Gfield β γ k t e) = (-Complex.I) • Fnl β γ (Usp k t e) := by
  rw [Gfield, map_smul, Usp_Usp_neg]

/-- The derivative of the potential term along the interaction-picture flow. -/
theorem hasDerivAt_pot {w : ℝ → Hsp 2} {t : ℝ} (hw : HasDerivAt w (Gfield β γ k t (w t)) t) :
    HasDerivAt (fun s => Nsp β γ (Usp k s (w s)))
      (2 * (Lw k (Fnl β γ (Usp k t (w t))) (Usp k t (w t))).re) t := by
  have h := hasDerivAt_Nsp_Usp (β := β) (γ := γ) (k := k) hw
  rw [Complex.add_re, Usp_Gfield, vl_smul, re_inner_neg_I_smul_self, zero_add] at h
  exact h

/-- The energy `H = ‖Au‖² + N(u)` on the state space. -/
noncomputable def Esp (β γ k : ℝ) (e : Hsp 2) : ℝ := ‖Asp k e‖ ^ 2 + Nsp β γ e

/-- **Conservation of energy** (infinitesimal form). -/
theorem hasDerivAt_Esp {w : ℝ → Hsp 2} {t : ℝ} (hw : HasDerivAt w (Gfield β γ k t (w t)) t) :
    HasDerivAt (fun s => Esp β γ k (Usp k s (w s))) 0 t := by
  have h := (hasDerivAt_kin hw).add (hasDerivAt_pot hw)
  have heq : (fun s => Esp β γ k (Usp k s (w s))) =
      fun s => ‖Asp k (w s)‖ ^ 2 + Nsp β γ (Usp k s (w s)) := by
    funext s
    rw [Esp, norm_Asp_Usp]
  rw [heq]
  convert h using 1
  have hc := inner_conj_symm (𝕜 := ℂ) (Asp k (Fnl β γ (Usp k t (w t)))) (Asp k (Usp k t (w t)))
  rw [Lw, re_neg_I_mul, re_neg_I_mul, ← hc, Complex.conj_im]
  ring

end Sobolev

end ReyesMath

open Filter Topology Complex InnerProductSpace MeasureTheory Set
open scoped ContDiff FourierTransform NNReal

namespace ReyesMath

namespace Sobolev

variable {β γ k : ℝ}

attribute [local irreducible] Usp

/-! ### The interaction-picture vector field -/

theorem Gfield_zero (t : ℝ) : Gfield β γ k t 0 = 0 := by
  rw [Gfield, map_zero, Fnl_zero, map_zero, smul_zero]

theorem norm_Gfield_sub_le {R : ℝ} (t : ℝ) {a b : Hsp 2} (ha : ‖a‖ ≤ R) (hb : ‖b‖ ≤ R) :
    ‖Gfield β γ k t a - Gfield β γ k t b‖ ≤ LF β γ R * ‖a - b‖ := by
  have h := norm_Fnl_sub_le β γ (u := Usp k t a) (v := Usp k t b) (R := R)
    (by rwa [norm_Usp]) (by rwa [norm_Usp])
  rw [← map_sub, norm_Usp] at h
  rw [Gfield, Gfield, ← smul_sub, ← map_sub, norm_smul, norm_neg, Complex.norm_I, one_mul,
    norm_Usp]
  exact h

theorem norm_Gfield_le {R : ℝ} (hR : 0 ≤ R) (t : ℝ) {a : Hsp 2} (ha : ‖a‖ ≤ R) :
    ‖Gfield β γ k t a‖ ≤ LF β γ R * R := by
  have h0 : ‖(0 : Hsp 2)‖ ≤ R := by rw [norm_zero]; exact hR
  have h := norm_Gfield_sub_le (β := β) (γ := γ) (k := k) t ha h0
  rw [Gfield_zero, sub_zero, sub_zero] at h
  exact h.trans (mul_le_mul_of_nonneg_left ha (LF_nonneg β γ))

theorem continuous_Gfield : Continuous fun p : ℝ × Hsp 2 => Gfield β γ k p.1 p.2 := by
  have h1 : Continuous fun p : ℝ × Hsp 2 => Fnl β γ (Usp k p.1 p.2) :=
    (continuous_Fnl β γ).comp (continuous_Usp_uncurry (d := 2) k)
  have h1' : Continuous fun p : ℝ × Hsp 2 => (-p.1, Fnl β γ (Usp k p.1 p.2)) :=
    continuous_fst.neg.prodMk h1
  have h2 : Continuous fun p : ℝ × Hsp 2 => Usp k (-p.1) (Fnl β γ (Usp k p.1 p.2)) :=
    (continuous_Usp_uncurry (d := 2) k).comp h1'
  have h3 : Continuous fun p : ℝ × Hsp 2 =>
      (-Complex.I) • Usp k (-p.1) (Fnl β γ (Usp k p.1 p.2)) := h2.const_smul (-Complex.I)
  exact h3

theorem lipschitzOnWith_Gfield {R : ℝ} (t : ℝ) :
    LipschitzOnWith ⟨LF β γ R, LF_nonneg β γ⟩ (Gfield β γ k t) (Metric.closedBall 0 R) := by
  refine LipschitzOnWith.of_dist_le_mul fun a ha b hb => ?_
  rw [Metric.mem_closedBall, dist_zero_right] at ha hb
  rw [dist_eq_norm, dist_eq_norm]
  exact norm_Gfield_sub_le t ha hb

/-! ### Radial retraction onto a ball -/

/-- The radial retraction onto the closed ball of radius `R`. -/
noncomputable def retr (R : ℝ) (x : Hsp 2) : Hsp 2 :=
  if ‖x‖ ≤ R then x else ((R / ‖x‖ : ℝ) : ℂ) • x

theorem retr_of_le {R : ℝ} {x : Hsp 2} (h : ‖x‖ ≤ R) : retr R x = x := if_pos h

theorem retr_of_lt {R : ℝ} {x : Hsp 2} (h : R < ‖x‖) :
    retr R x = ((R / ‖x‖ : ℝ) : ℂ) • x := if_neg (not_le.2 h)

theorem norm_ofReal_smul {c : ℝ} (hc : 0 ≤ c) (x : Hsp 2) : ‖((c : ℝ) : ℂ) • x‖ = c * ‖x‖ := by
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]

theorem norm_retr_le {R : ℝ} (hR : 0 ≤ R) (x : Hsp 2) : ‖retr R x‖ ≤ R := by
  rcases le_or_gt ‖x‖ R with h | h
  · rw [retr_of_le h]
    exact h
  · have hx : 0 < ‖x‖ := lt_of_le_of_lt hR h
    rw [retr_of_lt h, norm_ofReal_smul (div_nonneg hR hx.le), div_mul_cancel₀ _ hx.ne']

theorem norm_retr_sub_aux {R : ℝ} (hR : 0 ≤ R) {x y : Hsp 2} (hx : ‖x‖ ≤ R) (hy : R < ‖y‖) :
    ‖x - ((R / ‖y‖ : ℝ) : ℂ) • y‖ ≤ 2 * ‖x - y‖ := by
  have hy0 : 0 < ‖y‖ := lt_of_le_of_lt hR hy
  have hc : R / ‖y‖ ≤ 1 := (div_le_one hy0).2 hy.le
  have e : y - ((R / ‖y‖ : ℝ) : ℂ) • y = ((1 - R / ‖y‖ : ℝ) : ℂ) • y := by
    rw [Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul]
  have h1 : ‖y - ((R / ‖y‖ : ℝ) : ℂ) • y‖ = ‖y‖ - R := by
    rw [e, norm_ofReal_smul (by linarith), sub_mul, one_mul, div_mul_cancel₀ _ hy0.ne']
  have h2 : ‖y‖ - ‖x‖ ≤ ‖x - y‖ := by
    rw [norm_sub_rev]
    exact norm_sub_norm_le y x
  calc ‖x - ((R / ‖y‖ : ℝ) : ℂ) • y‖ ≤ ‖x - y‖ + ‖y - ((R / ‖y‖ : ℝ) : ℂ) • y‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 2 * ‖x - y‖ := by rw [h1]; linarith

theorem retr_arith {R a b d : ℝ} (hR : 0 ≤ R) (ha : R < a) (hb : R < b) (hd : |a - b| ≤ d) :
    R / a * d + |R / a - R / b| * b ≤ 2 * d := by
  have ha0 : 0 < a := lt_of_le_of_lt hR ha
  have hb0 : 0 < b := lt_of_le_of_lt hR hb
  have hc : 0 ≤ R / a := div_nonneg hR ha0.le
  have hc1 : R / a ≤ 1 := (div_le_one ha0).2 ha.le
  have hd0 : 0 ≤ d := le_trans (abs_nonneg _) hd
  have e1 : |R / a - R / b| * b = |(R / a - R / b) * b| := by rw [abs_mul, abs_of_pos hb0]
  have e2 : (R / a - R / b) * b = R / a * (b - a) := by
    field_simp
  have h1 : |R / a - R / b| * b = R / a * |a - b| := by
    rw [e1, e2, abs_mul, abs_of_nonneg hc, abs_sub_comm]
  rw [h1]
  calc R / a * d + R / a * |a - b| ≤ R / a * d + R / a * d := by gcongr
    _ = R / a * (2 * d) := by ring
    _ ≤ 1 * (2 * d) := by gcongr
    _ = 2 * d := one_mul _

/-- The retraction is `2`-Lipschitz. -/
theorem norm_retr_sub_le {R : ℝ} (hR : 0 ≤ R) (x y : Hsp 2) :
    ‖retr R x - retr R y‖ ≤ 2 * ‖x - y‖ := by
  rcases le_or_gt ‖x‖ R with hx | hx <;> rcases le_or_gt ‖y‖ R with hy | hy
  · rw [retr_of_le hx, retr_of_le hy]
    linarith [norm_nonneg (x - y)]
  · rw [retr_of_le hx, retr_of_lt hy]
    exact norm_retr_sub_aux hR hx hy
  · rw [retr_of_lt hx, retr_of_le hy, norm_sub_rev, norm_sub_rev x y]
    exact norm_retr_sub_aux hR hy hx
  · rw [retr_of_lt hx, retr_of_lt hy]
    have hx0 : 0 < ‖x‖ := lt_of_le_of_lt hR hx
    have e : ((R / ‖x‖ : ℝ) : ℂ) • x - ((R / ‖y‖ : ℝ) : ℂ) • y =
        ((R / ‖x‖ : ℝ) : ℂ) • (x - y) + ((R / ‖x‖ - R / ‖y‖ : ℝ) : ℂ) • y := by
      rw [smul_sub, Complex.ofReal_sub, sub_smul]
      abel
    rw [e]
    calc _ ≤ ‖((R / ‖x‖ : ℝ) : ℂ) • (x - y)‖ + ‖((R / ‖x‖ - R / ‖y‖ : ℝ) : ℂ) • y‖ :=
          norm_add_le _ _
      _ = R / ‖x‖ * ‖x - y‖ + |R / ‖x‖ - R / ‖y‖| * ‖y‖ := by
          rw [norm_ofReal_smul (div_nonneg hR hx0.le), norm_smul, Complex.norm_real,
            Real.norm_eq_abs]
      _ ≤ 2 * ‖x - y‖ := retr_arith hR hx hy (abs_norm_sub_norm_le x y)

/-! ### The truncated equation -/

/-- The truncated field `G(t, π_R w)`. -/
noncomputable def Gtr (β γ k R : ℝ) (t : ℝ) (a : Hsp 2) : Hsp 2 := Gfield β γ k t (retr R a)

theorem Gtr_of_le {R : ℝ} (t : ℝ) {a : Hsp 2} (ha : ‖a‖ ≤ R) :
    Gtr β γ k R t a = Gfield β γ k t a := by
  rw [Gtr, retr_of_le ha]

theorem lipschitzWith_Gtr {R : ℝ} (hR : 0 ≤ R) (t : ℝ) :
    LipschitzWith ⟨2 * LF β γ R, mul_nonneg zero_le_two (LF_nonneg β γ)⟩ (Gtr β γ k R t) := by
  refine LipschitzWith.of_dist_le_mul fun a b => ?_
  rw [dist_eq_norm, dist_eq_norm, Gtr, Gtr, NNReal.coe_mk]
  calc _ ≤ LF β γ R * ‖retr R a - retr R b‖ :=
        norm_Gfield_sub_le t (norm_retr_le hR a) (norm_retr_le hR b)
    _ ≤ LF β γ R * (2 * ‖a - b‖) :=
        mul_le_mul_of_nonneg_left (norm_retr_sub_le hR a b) (LF_nonneg β γ)
    _ = 2 * LF β γ R * ‖a - b‖ := by ring

theorem norm_Gtr_le {R : ℝ} (hR : 0 ≤ R) (t : ℝ) (a : Hsp 2) :
    ‖Gtr β γ k R t a‖ ≤ LF β γ R * R :=
  norm_Gfield_le hR t (norm_retr_le hR a)

theorem continuous_Gtr_time (R : ℝ) (a : Hsp 2) : Continuous fun t => Gtr β γ k R t a := by
  have h1 : Continuous fun t : ℝ => (t, retr R a) := continuous_id.prodMk continuous_const
  have h2 : Continuous fun t : ℝ => Gfield β γ k t (retr R a) :=
    (continuous_Gfield (β := β) (γ := γ) (k := k)).comp h1
  exact h2

/-- Local existence on `[-T, T]` for the truncated equation (Picard–Lindelöf). -/
theorem exists_local_tr {R : ℝ} (hR : 0 ≤ R) (u₀ : Hsp 2) {T : ℝ} (hT : 0 ≤ T) :
    ∃ α : ℝ → Hsp 2, α 0 = u₀ ∧ ∀ t ∈ Icc (-T) T,
      HasDerivWithinAt α (Gtr β γ k R t (α t)) (Icc (-T) T) t := by
  have h0 : (0 : ℝ) ∈ Icc (-T) T := ⟨by linarith, hT⟩
  obtain ⟨B, hB⟩ : ∃ B, B = LF β γ R * R := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by rw [hB]; exact mul_nonneg (LF_nonneg β γ) hR
  have hPL : IsPicardLindelof (Gtr β γ k R) (tmin := -T) (tmax := T) ⟨0, h0⟩ u₀
      ⟨B * T, mul_nonneg hB0 hT⟩ 0 ⟨B, hB0⟩
      ⟨2 * LF β γ R, mul_nonneg zero_le_two (LF_nonneg β γ)⟩ := by
    refine ⟨fun t _ => (lipschitzWith_Gtr hR t).lipschitzOnWith, fun x _ => ?_,
      fun t _ x _ => ?_, ?_⟩
    · exact (continuous_Gtr_time R x).continuousOn
    · rw [NNReal.coe_mk, hB]
      exact norm_Gtr_le hR t x
    · simp only [NNReal.coe_mk, NNReal.coe_zero, sub_zero, zero_sub, neg_neg, max_self]
      exact le_refl _
  obtain ⟨α, hα0, hα⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨α, hα0, hα⟩

/-- Global existence for the truncated equation. -/
theorem exists_global_tr {R : ℝ} (hR : 0 ≤ R) (u₀ : Hsp 2) :
    ∃ W : ℝ → Hsp 2, W 0 = u₀ ∧ ∀ t, HasDerivAt W (Gtr β γ k R t (W t)) t := by
  have hloc : ∀ n : ℕ, ∃ α : ℝ → Hsp 2, α 0 = u₀ ∧ ∀ t ∈ Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1),
      HasDerivWithinAt α (Gtr β γ k R t (α t)) (Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1)) t :=
    fun n => exists_local_tr hR u₀ (by positivity)
  choose α hα0 hα using hloc
  have hder : ∀ (n : ℕ) (t : ℝ), |t| < (n : ℝ) + 1 → HasDerivAt (α n) (Gtr β γ k R t (α n t)) t := by
    intro n t ht
    have h1 := neg_abs_le t
    have h2 := le_abs_self t
    exact (hα n t ⟨by linarith, by linarith⟩).hasDerivAt (Icc_mem_nhds (by linarith) (by linarith))
  have hcons : ∀ (m n : ℕ) (t : ℝ), |t| < (m : ℝ) + 1 → |t| < (n : ℝ) + 1 → α m t = α n t := by
    intro m n t hm hn
    obtain ⟨T, hT⟩ : ∃ T, T = min ((m : ℝ) + 1) ((n : ℝ) + 1) := ⟨_, rfl⟩
    have hTm : T ≤ (m : ℝ) + 1 := hT ▸ min_le_left _ _
    have hTn : T ≤ (n : ℝ) + 1 := hT ▸ min_le_right _ _
    have htT : |t| < T := hT ▸ lt_min hm hn
    have hT0 : 0 < T := lt_of_le_of_lt (abs_nonneg t) htT
    have key := ODE_solution_unique_of_mem_Ioo (v := Gtr β γ k R) (s := fun _ => univ)
      (fun s _ => (lipschitzWith_Gtr hR s).lipschitzOnWith)
      (show (0 : ℝ) ∈ Ioo (-T) T from ⟨by linarith, hT0⟩)
      (fun s hs => ⟨hder m s (abs_lt.2 ⟨by linarith [hs.1], by linarith [hs.2]⟩), trivial⟩)
      (fun s hs => ⟨hder n s (abs_lt.2 ⟨by linarith [hs.1], by linarith [hs.2]⟩), trivial⟩)
      ((hα0 m).trans (hα0 n).symm)
    exact key ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
  refine ⟨fun t => α ⌈|t|⌉₊ t, hα0 _, fun t => ?_⟩
  have hn : |t| < (⌈|t|⌉₊ : ℝ) + 1 := lt_of_le_of_lt (Nat.le_ceil _) (lt_add_one _)
  refine (hder _ t hn).congr_of_eventuallyEq ?_
  filter_upwards [(continuous_abs.tendsto t).eventually (gt_mem_nhds hn)] with s hs
  exact hcons _ _ s (lt_of_le_of_lt (Nat.le_ceil _) (lt_add_one _)) hs

end Sobolev

end ReyesMath

open Filter Topology Complex InnerProductSpace MeasureTheory Set
open scoped ContDiff FourierTransform NNReal

namespace ReyesMath

namespace Sobolev

variable {β γ k : ℝ}

attribute [local irreducible] Usp

/-! ### Continuity of the energy -/

theorem continuous_Nsp (β γ : ℝ) : Continuous (Nsp β γ) := by
  rw [continuous_iff_continuousAt]
  intro e
  obtain ⟨R, hR⟩ : ∃ R, R = ‖e‖ + 1 := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C, C = 3 * |β| * R ^ 2 + 5 * |γ| * R ^ 4 := ⟨_, rfl⟩
  have hev : ∀ᶠ f in 𝓝 e, ‖f‖ < R := by
    rw [hR]
    exact (continuous_norm.tendsto e).eventually (gt_mem_nhds (lt_add_one _))
  have hv : Tendsto (fun f => ‖vl f - vl e‖) (𝓝 e) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1 ((continuous_vl (d := 2)).tendsto e)
  have hlim : Tendsto (fun f => C * ‖vl f - vl e‖ ^ 2 + 2 * ‖vl (Fnl β γ e)‖ * ‖vl f - vl e‖)
      (𝓝 e) (𝓝 0) := by
    have h := ((hv.pow 2).const_mul C).add (hv.const_mul (2 * ‖vl (Fnl β γ e)‖))
    rwa [zero_pow two_ne_zero, mul_zero, mul_zero, add_zero] at h
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun f => norm_nonneg _) ?_ hlim
  filter_upwards [hev] with f hf
  have he : ‖e‖ ≤ R := by rw [hR]; linarith
  have hT := Nsp_taylor β γ he hf.le
  rw [← hC] at hT
  have hin : |2 * (inner ℂ (vl (Fnl β γ e)) (vl f - vl e)).re| ≤
      2 * ‖vl (Fnl β γ e)‖ * ‖vl f - vl e‖ := by
    rw [abs_mul, abs_two, mul_assoc]
    exact mul_le_mul_of_nonneg_left
      ((Complex.abs_re_le_norm _).trans (norm_inner_le_norm _ _)) zero_le_two
  rw [Real.norm_eq_abs]
  have h1 := abs_le.1 hT
  have h2 := abs_le.1 hin
  rw [abs_le]
  constructor <;> linarith

theorem continuous_Esp (β γ k : ℝ) : Continuous (Esp β γ k) :=
  ((continuous_norm.comp (continuous_Asp (d := 2) k)).pow 2).add (continuous_Nsp β γ)

/-! ### Mass, energy and the `H²` norm -/

theorem M_ofSp (e : Hsp 2) : H2.M (H2.ofSp e) = ‖vl e‖ ^ 2 := rfl

theorem T_ofSp (e : Hsp 2) : H2.T k (H2.ofSp e) = ‖Asp k e‖ ^ 2 := rfl

theorem energy_ofSp (e : Hsp 2) : H2.energy β γ k (H2.ofSp e) = Esp β γ k e := by
  rw [H2.energy_eq, Esp, Nsp_eq, T_ofSp]
  ring

theorem M_eq_vl (U : H2 2) : H2.M U = ‖vl (H2.toSp U)‖ ^ 2 := rfl

theorem energy_eq_Esp (U : H2 2) : H2.energy β γ k U = Esp β γ k (H2.toSp U) := by
  rw [← energy_ofSp, H2.ofSp_toSp]

/-- The bound `‖u‖²_{H²} ≤ 3 (H(u) + (3β²/(16γ)) M(u)) + (2 + 3k⁴) M(u)`. -/
noncomputable def Bd (β γ k m E : ℝ) : ℝ := 3 * (E + 3 * β ^ 2 / (16 * γ) * m) + (2 + 3 * k ^ 4) * m

theorem apriori_arith {a b c K n2 E C₀ q : ℝ} (ha : 0 ≤ a)
    (hac : a ≤ c + q * b) (hK : K ≤ b * a) (hn : n2 = b ^ 2 + a ^ 2 + K)
    (hE : c ^ 2 - C₀ * b ^ 2 ≤ E) :
    n2 ≤ 3 * (E + C₀ * b ^ 2) + (2 + 3 * q ^ 2) * b ^ 2 := by
  have h1 : a ^ 2 ≤ (c + q * b) ^ 2 := pow_le_pow_left₀ ha hac 2
  nlinarith [sq_nonneg (a - b), sq_nonneg (c - q * b)]

/-- **A priori bound:** the `H²` norm is controlled by the mass and the energy. -/
theorem norm_toSp_sq_le (hγ : 0 < γ) (U : H2 2) :
    ‖H2.toSp U‖ ^ 2 ≤ Bd β γ k (H2.M U) (H2.energy β γ k U) := by
  have hE := H2.energy_ge β γ k hγ U
  have hl : ‖U.lap‖ ≤ ‖U.lap + ((k ^ 2 : ℝ) : ℂ) • U.val‖ + k ^ 2 * ‖U.val‖ := by
    calc ‖U.lap‖ = ‖(U.lap + ((k ^ 2 : ℝ) : ℂ) • U.val) - ((k ^ 2 : ℝ) : ℂ) • U.val‖ := by
          rw [add_sub_cancel_right]
      _ ≤ ‖U.lap + ((k ^ 2 : ℝ) : ℂ) • U.val‖ + ‖((k ^ 2 : ℝ) : ℂ) • U.val‖ := norm_sub_le _ _
      _ = _ := by rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h := apriori_arith (norm_nonneg U.lap) hl (H2.K_le U)
    (H2.norm_toSp_sq U) hE
  rw [Bd, H2.M]
  have e : (k ^ 2) ^ 2 = k ^ 4 := by ring
  rw [e] at h
  exact h

theorem norm_sq_le_Bd (hγ : 0 < γ) (e : Hsp 2) :
    ‖e‖ ^ 2 ≤ Bd β γ k (‖vl e‖ ^ 2) (Esp β γ k e) := by
  have h := norm_toSp_sq_le (β := β) (k := k) hγ (H2.ofSp e)
  rwa [H2.toSp_ofSp, M_ofSp, energy_ofSp] at h

/-! ### Global solutions of the interaction-picture equation -/

/-- Conservation of mass and energy along any solution of `w' = G(t, w)`. -/
theorem conserved {W : ℝ → Hsp 2} (hW : ∀ t, HasDerivAt W (Gfield β γ k t (W t)) t) (t : ℝ) :
    ‖vl (W t)‖ ^ 2 = ‖vl (W 0)‖ ^ 2 ∧ Esp β γ k (Usp k t (W t)) = Esp β γ k (W 0) := by
  constructor
  · exact is_const_of_deriv_eq_zero (f := fun s => ‖vl (W s)‖ ^ 2)
      (fun s => (hasDerivAt_mass (hW s)).differentiableAt) (fun s => (hasDerivAt_mass (hW s)).deriv)
      t 0
  · have h : Esp β γ k (Usp k t (W t)) = Esp β γ k (Usp k 0 (W 0)) :=
      is_const_of_deriv_eq_zero (f := fun s => Esp β γ k (Usp k s (W s)))
        (fun s => (hasDerivAt_Esp (hW s)).differentiableAt)
        (fun s => (hasDerivAt_Esp (hW s)).deriv) t 0
    rw [Usp_zero] at h
    exact h

theorem continuous_Usp_path {W : ℝ → Hsp 2} (hW : Continuous W) :
    Continuous fun s => Usp k s (W s) := by
  have h1 : Continuous fun s : ℝ => (s, W s) := continuous_id.prodMk hW
  have h2 : Continuous fun s : ℝ => Usp k s (W s) := (continuous_Usp_uncurry (d := 2) k).comp h1
  exact h2

/-- **Global existence** for `w' = G(t, w)`: the truncated solution never leaves the ball on
which the truncation is inactive, by conservation of mass and energy. -/
theorem exists_global (hγ : 0 < γ) (u₀ : Hsp 2) :
    ∃ W : ℝ → Hsp 2, W 0 = u₀ ∧ ∀ t, HasDerivAt W (Gfield β γ k t (W t)) t := by
  obtain ⟨C₀, hC₀⟩ : ∃ C₀, C₀ = Real.sqrt (Bd β γ k (‖vl u₀‖ ^ 2) (Esp β γ k u₀)) := ⟨_, rfl⟩
  have hbd : ∀ e : Hsp 2, ‖vl e‖ ^ 2 = ‖vl u₀‖ ^ 2 → Esp β γ k e = Esp β γ k u₀ → ‖e‖ ≤ C₀ := by
    intro e h1 h2
    have h := norm_sq_le_Bd (β := β) (k := k) hγ e
    rw [h1, h2] at h
    rw [hC₀]
    exact Real.le_sqrt_of_sq_le h
  have hC₀0 : 0 ≤ C₀ := hC₀ ▸ Real.sqrt_nonneg _
  obtain ⟨R, hR⟩ : ∃ R, R = C₀ + 1 := ⟨_, rfl⟩
  have hR0 : 0 ≤ R := by rw [hR]; linarith
  obtain ⟨W, hW0, hW⟩ := exists_global_tr (β := β) (γ := γ) (k := k) hR0 u₀
  have hWc : Continuous W := continuous_iff_continuousAt.2 fun t => (hW t).continuousAt
  have hinner : ∀ s, ‖W s‖ ≤ R → HasDerivAt W (Gfield β γ k s (W s)) s := fun s hs => by
    have h := hW s
    rwa [Gtr_of_le s hs] at h
  obtain ⟨S, hS⟩ : ∃ S : Set ℝ, S = {t | ‖vl (W t)‖ ^ 2 = ‖vl u₀‖ ^ 2 ∧
      Esp β γ k (Usp k t (W t)) = Esp β γ k u₀} := ⟨_, rfl⟩
  have hSb : ∀ t ∈ S, ‖W t‖ ≤ C₀ := by
    intro t ht
    rw [hS] at ht
    have h := hbd (Usp k t (W t)) (by rw [norm_vl_Usp]; exact ht.1) ht.2
    rwa [norm_Usp] at h
  have hm : Continuous fun t => ‖vl (W t)‖ ^ 2 :=
    (continuous_norm.comp ((continuous_vl (d := 2)).comp hWc)).pow 2
  have hE : Continuous fun t => Esp β γ k (Usp k t (W t)) :=
    (continuous_Esp β γ k).comp (continuous_Usp_path hWc)
  have hclosed : IsClosed S := by
    rw [hS]
    exact (isClosed_eq hm continuous_const).inter (isClosed_eq hE continuous_const)
  have hopen : IsOpen S := by
    rw [Metric.isOpen_iff]
    intro t ht
    have htR : ‖W t‖ < R := by rw [hR]; linarith [hSb t ht]
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1
      ((continuous_norm.comp hWc).continuousAt.preimage_mem_nhds (gt_mem_nhds htR))
    refine ⟨ε, hε, fun s hs => ?_⟩
    have hder : ∀ x ∈ Metric.ball t ε, HasDerivAt W (Gfield β γ k x (W x)) x :=
      fun x hx => hinner x (hball hx).le
    have hpre : IsPreconnected (Metric.ball t ε) := (convex_ball t ε).isPreconnected
    have h1 : ‖vl (W s)‖ ^ 2 = ‖vl (W t)‖ ^ 2 :=
      Metric.isOpen_ball.is_const_of_deriv_eq_zero (f := fun x => ‖vl (W x)‖ ^ 2) hpre
        (fun x hx => (hasDerivAt_mass (hder x hx)).differentiableAt.differentiableWithinAt)
        (fun x hx => (hasDerivAt_mass (hder x hx)).deriv) hs (Metric.mem_ball_self hε)
    have h2 : Esp β γ k (Usp k s (W s)) = Esp β γ k (Usp k t (W t)) :=
      Metric.isOpen_ball.is_const_of_deriv_eq_zero (f := fun x => Esp β γ k (Usp k x (W x))) hpre
        (fun x hx => (hasDerivAt_Esp (hder x hx)).differentiableAt.differentiableWithinAt)
        (fun x hx => (hasDerivAt_Esp (hder x hx)).deriv) hs (Metric.mem_ball_self hε)
    rw [hS] at ht ⊢
    exact ⟨h1.trans ht.1, h2.trans ht.2⟩
  have h0S : (0 : ℝ) ∈ S := by
    rw [hS]
    refine ⟨by rw [hW0], ?_⟩
    rw [Usp_zero, hW0]
  have hSu : S = univ := IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨0, h0S⟩
  refine ⟨W, hW0, fun t => hinner t ?_⟩
  have ht : t ∈ S := by rw [hSu]; exact mem_univ t
  rw [hR]
  linarith [hSb t ht]

/-- **Uniqueness** for `w' = G(t, w)`. -/
theorem ode_unique {W₁ W₂ : ℝ → Hsp 2} (h₁ : ∀ t, HasDerivAt W₁ (Gfield β γ k t (W₁ t)) t)
    (h₂ : ∀ t, HasDerivAt W₂ (Gfield β γ k t (W₂ t)) t) (h0 : W₁ 0 = W₂ 0) : W₁ = W₂ := by
  funext t
  obtain ⟨T, hT⟩ : ∃ T, T = |t| + 1 := ⟨_, rfl⟩
  have hc₁ : ContinuousOn W₁ (Icc (-T) T) :=
    (continuous_iff_continuousAt.2 fun s => (h₁ s).continuousAt).continuousOn
  have hc₂ : ContinuousOn W₂ (Icc (-T) T) :=
    (continuous_iff_continuousAt.2 fun s => (h₂ s).continuousAt).continuousOn
  obtain ⟨R₁, hR₁⟩ := isCompact_Icc.exists_bound_of_continuousOn hc₁
  obtain ⟨R₂, hR₂⟩ := isCompact_Icc.exists_bound_of_continuousOn hc₂
  obtain ⟨R, hR⟩ : ∃ R, R = max R₁ R₂ := ⟨_, rfl⟩
  have ht0 := abs_nonneg t
  have key := ODE_solution_unique_of_mem_Ioo (v := Gfield β γ k)
    (s := fun _ => Metric.closedBall (0 : Hsp 2) R) (K := ⟨LF β γ R, LF_nonneg β γ⟩)
    (fun s _ => lipschitzOnWith_Gfield s)
    (show (0 : ℝ) ∈ Ioo (-T) T from ⟨by linarith, by linarith⟩)
    (fun s hs => ⟨h₁ s, by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact (hR₁ s (Ioo_subset_Icc_self hs)).trans (hR ▸ le_max_left _ _)⟩)
    (fun s hs => ⟨h₂ s, by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact (hR₂ s (Ioo_subset_Icc_self hs)).trans (hR ▸ le_max_right _ _)⟩) h0
  exact key ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩

end Sobolev

end ReyesMath

open Filter Topology Complex InnerProductSpace MeasureTheory Set
open scoped ContDiff FourierTransform NNReal

namespace ReyesMath

namespace Sobolev

local notation "R2" => EuclideanSpace ℝ (Fin 2)

variable {β γ k : ℝ}

attribute [local irreducible] Usp

/-! ### Pairings with Schwartz test functions -/

theorem integral_conj_mul_eq_inner (φ : SchwartzMap R2 ℂ) (f : L2 2) :
    ∫ x, (starRingEnd ℂ) (φ x) * f x = inner ℂ (toL2 φ) f := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_toL2 φ] with x hx
  rw [hx, RCLike.inner_apply, mul_comm]

theorem integral_conj_fnl (φ : SchwartzMap R2 ℂ) (e : Hsp 2) :
    ∫ x, (starRingEnd ℂ) (φ x) * fnl β γ ((H2.ofSp e).val x) =
      inner ℂ (toL2 φ) (vl (Fnl β γ e)) := by
  rw [← integral_conj_mul_eq_inner]
  refine integral_congr_ae ?_
  filter_upwards [vl_Fnl_ae β γ e] with x hx
  rw [hx]
  rfl

/-- Integration by parts: `⟪(Δ + k²)ψ, u⟫ = ⟪ψ, (Δ + k²)u⟫` for `u ∈ H²`. -/
theorem inner_AS_vl (ψ : SchwartzMap R2 ℂ) (e : Hsp 2) :
    inner ℂ (toL2 (AS k ψ)) (vl e) = inner ℂ (toL2 ψ) (Asp k e) := by
  have h := H2.inner_lap_eq (H2.ofSp e) ψ
  change inner ℂ (toL2 (AS k ψ)) (H2.ofSp e).val =
    inner ℂ (toL2 ψ) ((H2.ofSp e).lap + ((k ^ 2 : ℝ) : ℂ) • (H2.ofSp e).val)
  rw [AS, map_add, map_smul, inner_add_left, inner_smul_left, Complex.conj_ofReal,
    inner_add_right, inner_smul_right, h]

theorem ofSp_val' (e : Hsp 2) : (H2.ofSp e).val = vl e := rfl

/-! ### Solutions -/

/-- `u : ℝ → H²(ℝ²; ℂ)` is a **solution** of `i ∂ₜu = (Δ + k²)²u − β|u|²u + γ|u|⁴u`:
`u ∈ C(ℝ; H²)` (continuity for the `H²` distance), and the equation holds in the sense of
distributions in space: for every Schwartz test function `φ`, `t ↦ ⟪φ, u(t)⟫_{L²}` is
differentiable with `i ∂ₜ⟪φ, u(t)⟫ = ⟪(Δ + k²)²φ, u(t)⟫ + ⟪φ, −β|u|²u + γ|u|⁴u⟫`. -/
def IsSolution (β γ k : ℝ) (u : ℝ → H2 2) : Prop :=
  (∀ t, Tendsto (fun s => H2.distH2 (u s) (u t)) (𝓝 t) (𝓝 0)) ∧
  ∀ (φ : SchwartzMap R2 ℂ) (t : ℝ),
    HasDerivAt (fun s => ∫ x, (starRingEnd ℂ) (φ x) * (u s).val x)
      (-Complex.I * ((∫ x, (starRingEnd ℂ) (AS k (AS k φ) x) * (u t).val x) +
        ∫ x, (starRingEnd ℂ) (φ x) * fnl β γ ((u t).val x))) t

/-- Interaction-picture solutions give solutions. -/
theorem isSolution_of_ode {W : ℝ → Hsp 2} (hW : ∀ t, HasDerivAt W (Gfield β γ k t (W t)) t) :
    IsSolution β γ k fun t => H2.ofSp (Usp k t (W t)) := by
  have hWc : Continuous W := continuous_iff_continuousAt.2 fun t => (hW t).continuousAt
  have hc := continuous_Usp_path (k := k) hWc
  refine ⟨fun t => ?_, fun φ t => ?_⟩
  · have h1 : Tendsto (fun s => ‖Usp k s (W s) - Usp k t (W t)‖) (𝓝 t) (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.1 (hc.tendsto t)
    have h2 := h1.const_mul (((2 : ℕ) : ℝ) + 2)
    rw [mul_zero] at h2
    refine squeeze_zero (fun s => H2.distH2_nonneg _ _) (fun s => ?_) h2
    have h := H2.distH2_le (H2.ofSp (Usp k s (W s))) (H2.ofSp (Usp k t (W t)))
    rwa [H2.toSp_ofSp, H2.toSp_ofSp] at h
  · have h := hasDerivAt_inner_Usp (k := k) (ιS φ) (hW t)
    have hfun : (fun s => ∫ x, (starRingEnd ℂ) (φ x) * (H2.ofSp (Usp k s (W s))).val x) =
        fun s => inner ℂ (vl (ιS φ)) (vl (Usp k s (W s))) := by
      funext s
      rw [integral_conj_mul_eq_inner, vl_ιS]
      rfl
    rw [hfun]
    convert h using 1
    rw [integral_conj_fnl, integral_conj_mul_eq_inner, ofSp_val', inner_AS_vl, ← Asp_ιS,
      Usp_Gfield, vl_smul, inner_smul_right, Lw, vl_ιS]
    ring

theorem toSp_continuous {u : ℝ → H2 2} (hu : IsSolution β γ k u) :
    Continuous fun t => H2.toSp (u t) := by
  rw [continuous_iff_continuousAt]
  intro t
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun s => norm_nonneg _) (fun s => H2.norm_le_distH2 _ _) (hu.1 t)

theorem inner_vl_W (φ : SchwartzMap R2 ℂ) (e : Hsp 2) (s : ℝ) :
    inner ℂ (toL2 φ) (vl (Usp k (-s) e)) = inner ℂ (vl (Usp k s (ιS φ))) (vl e) := by
  rw [vl_Usp, vl_Usp, vl_ιS, inner_U2]

theorem slope_arith (h : ℝ) (a b c c₀ : L2 2) :
    (starRingEnd ℂ) ((h : ℂ)⁻¹ * inner ℂ c (a - b)) + h⁻¹ • (inner ℂ b c - inner ℂ b c₀) =
      h⁻¹ • (inner ℂ a c - inner ℂ b c₀) := by
  rw [map_mul, map_inv₀, Complex.conj_ofReal, inner_conj_symm, inner_sub_left, Complex.real_smul,
    Complex.real_smul, Complex.ofReal_inv]
  ring

/-- Along a solution, `w(t) = U(−t)u(t)` is weakly differentiable with derivative `G(t, w(t))`. -/
theorem hasDerivAt_inner_W {u : ℝ → H2 2} (hu : IsSolution β γ k u) (φ : SchwartzMap R2 ℂ)
    (t : ℝ) :
    HasDerivAt (fun s => inner ℂ (toL2 φ) (vl (Usp k (-s) (H2.toSp (u s)))))
      (inner ℂ (toL2 φ) (vl (Gfield β γ k t (Usp k (-t) (H2.toSp (u t)))))) t := by
  have hec : Continuous fun s => H2.toSp (u s) := toSp_continuous hu
  obtain ⟨ψ, hψ⟩ : ∃ ψ, ψ = US k t φ := ⟨_, rfl⟩
  have hfun : (fun s => inner ℂ (toL2 φ) (vl (Usp k (-s) (H2.toSp (u s))))) =
      fun s => inner ℂ (vl (Usp k s (ιS φ))) (vl (H2.toSp (u s))) := by
    funext s
    exact inner_vl_W φ _ s
  have e1 : (∫ x, (starRingEnd ℂ) (AS k (AS k ψ) x) * (u t).val x) =
      inner ℂ (Asp k (ιS ψ)) (Asp k (H2.toSp (u t))) := by
    rw [integral_conj_mul_eq_inner, Asp_ιS]
    exact inner_AS_vl (AS k ψ) (H2.toSp (u t))
  have e2 : (∫ x, (starRingEnd ℂ) (ψ x) * fnl β γ ((u t).val x)) =
      inner ℂ (toL2 ψ) (vl (Fnl β γ (H2.toSp (u t)))) := by
    have h := integral_conj_fnl (β := β) (γ := γ) ψ (H2.toSp (u t))
    rwa [H2.ofSp_toSp] at h
  have e3 : inner ℂ (toL2 φ) (vl (Gfield β γ k t (Usp k (-t) (H2.toSp (u t))))) =
      -Complex.I * inner ℂ (toL2 ψ) (vl (Fnl β γ (H2.toSp (u t)))) := by
    rw [Gfield, Usp_Usp_neg, vl_smul, inner_smul_right, vl_Usp, ← inner_U2, U2_toL2, ← hψ]
  have hval : (starRingEnd ℂ) (Lw k (H2.toSp (u t)) (ιS ψ)) +
      -Complex.I * ((∫ x, (starRingEnd ℂ) (AS k (AS k ψ) x) * (u t).val x) +
        ∫ x, (starRingEnd ℂ) (ψ x) * fnl β γ ((u t).val x)) =
      inner ℂ (toL2 φ) (vl (Gfield β γ k t (Usp k (-t) (H2.toSp (u t))))) := by
    rw [e1, e2, e3, Lw, map_mul, map_neg, Complex.conj_I, inner_conj_symm]
    ring
  rw [hfun, hasDerivAt_iff_tendsto_slope_zero, ← hval]
  have hd : Tendsto (fun h : ℝ => ‖H2.toSp (u (t + h)) - H2.toSp (u t)‖) (𝓝[≠] 0) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1 ((hec.tendsto t).comp (tendsto_add_nhdsNE t))
  have hQ : Tendsto (fun h : ℝ => Qh k h (H2.toSp (u (t + h))) (ιS ψ)) (𝓝[≠] 0)
      (𝓝 (Lw k (H2.toSp (u t)) (ιS ψ))) := by
    have h1 := tendsto_Qh k (H2.toSp (u t)) (ιS ψ)
    have h2 : Tendsto (fun h : ℝ => Qh k h (H2.toSp (u (t + h)) - H2.toSp (u t)) (ιS ψ))
        (𝓝[≠] 0) (𝓝 0) := by
      have h3 := hd.mul_const ((1 + k ^ 2) * ‖Asp k (ιS ψ)‖)
      rw [zero_mul] at h3
      refine squeeze_zero_norm' ?_ h3
      filter_upwards [self_mem_nhdsWithin] with h hh
      calc ‖Qh k h (H2.toSp (u (t + h)) - H2.toSp (u t)) (ιS ψ)‖
          ≤ ‖Asp k (H2.toSp (u (t + h)) - H2.toSp (u t))‖ * ‖Asp k (ιS ψ)‖ :=
            norm_Qh_le k h hh _ _
        _ ≤ (1 + k ^ 2) * ‖H2.toSp (u (t + h)) - H2.toSp (u t)‖ * ‖Asp k (ιS ψ)‖ :=
            mul_le_mul_of_nonneg_right (norm_Asp_le k _) (norm_nonneg _)
        _ = _ := by ring
    have h4 := h1.add h2
    rw [add_zero] at h4
    refine h4.congr fun h => ?_
    rw [Qh_sub_left, add_sub_cancel]
  have hconj : Tendsto (fun h : ℝ => (starRingEnd ℂ) (Qh k h (H2.toSp (u (t + h))) (ιS ψ)))
      (𝓝[≠] 0) (𝓝 ((starRingEnd ℂ) (Lw k (H2.toSp (u t)) (ιS ψ)))) :=
    (Complex.continuous_conj.tendsto _).comp hQ
  have hweak := hasDerivAt_iff_tendsto_slope_zero.1 (hu.2 ψ t)
  refine (hconj.add hweak).congr fun h => ?_
  have hP1 : vl (Usp k (t + h) (ιS φ)) = vl (Usp k h (ιS ψ)) := by
    rw [add_comm t h, Usp_add, Usp_ιS, ← hψ]
  have hP0 : vl (Usp k t (ιS φ)) = toL2 ψ := by rw [Usp_ιS, ← hψ, vl_ιS]
  have hΦ : ∀ s, (∫ x, (starRingEnd ℂ) (ψ x) * (u s).val x) =
      inner ℂ (toL2 ψ) (vl (H2.toSp (u s))) := fun s => integral_conj_mul_eq_inner ψ (u s).val
  have hQh : Qh k h (H2.toSp (u (t + h))) (ιS ψ) = (h : ℂ)⁻¹ *
      inner ℂ (vl (H2.toSp (u (t + h)))) (vl (Usp k h (ιS ψ)) - toL2 ψ) := by
    rw [Qh, vl_ιS]
  show (starRingEnd ℂ) (Qh k h (H2.toSp (u (t + h))) (ιS ψ)) +
      h⁻¹ • ((∫ x, (starRingEnd ℂ) (ψ x) * (u (t + h)).val x) -
        ∫ x, (starRingEnd ℂ) (ψ x) * (u t).val x) =
    h⁻¹ • (inner ℂ (vl (Usp k (t + h) (ιS φ))) (vl (H2.toSp (u (t + h)))) -
      inner ℂ (vl (Usp k t (ιS φ))) (vl (H2.toSp (u t))))
  rw [hP1, hP0, hΦ, hΦ, hQh]
  exact slope_arith h _ _ _ _

theorem vl_injective : Function.Injective (vl (d := 2)) := by
  intro e f h
  have h' := congrArg H2.toSp (H2.ext_of_val (U := H2.ofSp e) (V := H2.ofSp f) h)
  rwa [H2.toSp_ofSp, H2.toSp_ofSp] at h'

/-- Solutions give interaction-picture solutions `w(t) = U(−t)u(t)`. -/
theorem ode_of_isSolution {u : ℝ → H2 2} (hu : IsSolution β γ k u) {W : ℝ → Hsp 2}
    (hW : ∀ s, W s = Usp k (-s) (H2.toSp (u s))) (t : ℝ) :
    HasDerivAt W (Gfield β γ k t (W t)) t := by
  have hWc : Continuous W := by
    have h1 : Continuous fun s : ℝ => (-s, H2.toSp (u s)) :=
      continuous_neg.prodMk (toSp_continuous hu)
    have h2 : Continuous fun s : ℝ => Usp k (-s) (H2.toSp (u s)) :=
      (continuous_Usp_uncurry (d := 2) k).comp h1
    have h3 : W = fun s => Usp k (-s) (H2.toSp (u s)) := funext hW
    rw [h3]
    exact h2
  have hΓc : Continuous fun s => Gfield β γ k s (W s) := by
    have h1 : Continuous fun s : ℝ => (s, W s) := continuous_id.prodMk hWc
    have h2 : Continuous fun s : ℝ => Gfield β γ k s (W s) :=
      (continuous_Gfield (β := β) (γ := γ) (k := k)).comp h1
    exact h2
  have hint : ∀ r, W r = W 0 + ∫ s in (0 : ℝ)..r, Gfield β γ k s (W s) := by
    intro r
    have hzero : vl (W r - W 0 - ∫ s in (0 : ℝ)..r, Gfield β γ k s (W s)) = 0 := by
      refine eq_zero_of_inner_schwartz fun φ => ?_
      have hder : ∀ s, HasDerivAt (fun q => inner ℂ (toL2 φ) (vl (W q)))
          (inner ℂ (toL2 φ) (vl (Gfield β γ k s (W s)))) s := by
        intro s
        have h := hasDerivAt_inner_W hu φ s
        rw [← hW s] at h
        refine h.congr_of_eventuallyEq (Eventually.of_forall fun q => ?_)
        beta_reduce
        rw [hW q]
      have hcont : Continuous fun s => inner ℂ (toL2 φ) (vl (Gfield β γ k s (W s))) :=
        continuous_const.inner ((continuous_vl (d := 2)).comp hΓc)
      have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hder s)
        (hcont.intervalIntegrable 0 r)
      have hcomm : ∫ s in (0 : ℝ)..r, inner ℂ (toL2 φ) (vl (Gfield β γ k s (W s))) =
          inner ℂ (toL2 φ) (vl (∫ s in (0 : ℝ)..r, Gfield β γ k s (W s))) :=
        ((innerSL ℂ (toL2 φ)).comp vlL).intervalIntegral_comp_comm (hΓc.intervalIntegrable _ _)
      rw [vl_sub, vl_sub, inner_sub_right, inner_sub_right, ← hcomm, hFTC]
      ring
    have hz : vl (0 : Hsp 2) = 0 := rfl
    have h := vl_injective (hzero.trans hz.symm)
    rw [sub_sub, sub_eq_zero] at h
    exact h
  have hF := (hΓc.integral_hasStrictDerivAt 0 t).hasDerivAt.const_add (W 0)
  exact hF.congr_of_eventuallyEq (Eventually.of_forall hint)

/-- **Global well-posedness in `H²(ℝ²)`.** -/
theorem global_wellposed (hγ : 0 < γ) (u₀ : H2 2) :
    ∃! u : ℝ → H2 2, IsSolution β γ k u ∧ u 0 = u₀ := by
  obtain ⟨W, hW0, hW⟩ := exists_global (β := β) (γ := γ) (k := k) hγ (H2.toSp u₀)
  refine ⟨fun t => H2.ofSp (Usp k t (W t)), ⟨isSolution_of_ode hW, ?_⟩, ?_⟩
  · show H2.ofSp (Usp k 0 (W 0)) = u₀
    rw [Usp_zero, hW0, H2.ofSp_toSp]
  · rintro v ⟨hv, hv0⟩
    obtain ⟨W', hW'⟩ : ∃ W' : ℝ → Hsp 2, ∀ s, W' s = Usp k (-s) (H2.toSp (v s)) :=
      ⟨_, fun _ => rfl⟩
    have hode := ode_of_isSolution hv hW'
    have h0 : W' 0 = W 0 := by rw [hW' 0, neg_zero, Usp_zero, hv0, hW0]
    have heq := ode_unique hode hW h0
    funext t
    have h1 : H2.toSp (v t) = Usp k t (W' t) := by rw [hW' t, Usp_Usp_neg]
    rw [← heq, ← h1, H2.ofSp_toSp]

/-- **Conservation of mass and energy** along every solution. -/
theorem conservation {u : ℝ → H2 2} (hu : IsSolution β γ k u) (t : ℝ) :
    H2.M (u t) = H2.M (u 0) ∧ H2.energy β γ k (u t) = H2.energy β γ k (u 0) := by
  obtain ⟨W, hW⟩ : ∃ W : ℝ → Hsp 2, ∀ s, W s = Usp k (-s) (H2.toSp (u s)) :=
    ⟨_, fun _ => rfl⟩
  have hode := ode_of_isSolution hu hW
  obtain ⟨h1, h2⟩ := conserved hode t
  have hWt : Usp k t (W t) = H2.toSp (u t) := by rw [hW t, Usp_Usp_neg]
  have hW0 : W 0 = H2.toSp (u 0) := by rw [hW 0, neg_zero, Usp_zero]
  rw [hW0, hWt] at h2
  rw [hW t, hW0, norm_vl_Usp] at h1
  rw [M_eq_vl, M_eq_vl, energy_eq_Esp, energy_eq_Esp]
  exact ⟨h1, h2⟩

end Sobolev

end ReyesMath

open Filter Topology Complex InnerProductSpace MeasureTheory Set
open scoped ContDiff FourierTransform NNReal

namespace ReyesMath

namespace Sobolev

local notation "R2" => EuclideanSpace ℝ (Fin 2)

variable {β γ k : ℝ}

attribute [local irreducible] Usp

/-! ### Local Lipschitz bounds for mass and energy -/

theorem sq_sub_sq_abs_le {x y d R : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hxR : x ≤ R) (hyR : y ≤ R)
    (hd : |x - y| ≤ d) : |x ^ 2 - y ^ 2| ≤ 2 * R * d := by
  have e : x ^ 2 - y ^ 2 = (x - y) * (x + y) := by ring
  rw [e, abs_mul, abs_of_nonneg (add_nonneg hx hy)]
  have hd0 : 0 ≤ d := le_trans (abs_nonneg _) hd
  calc |x - y| * (x + y) ≤ d * (2 * R) := mul_le_mul hd (by linarith) (add_nonneg hx hy) hd0
    _ = 2 * R * d := by ring

theorem mass_lip {R : ℝ} {a b : Hsp 2} (ha : ‖a‖ ≤ R) (hb : ‖b‖ ≤ R) :
    |‖vl a‖ ^ 2 - ‖vl b‖ ^ 2| ≤ 2 * R * ‖a - b‖ := by
  have h1 : |‖vl a‖ - ‖vl b‖| ≤ ‖a - b‖ := by
    refine (abs_norm_sub_norm_le _ _).trans ?_
    rw [← vl_sub]
    exact norm_vl_le _
  exact sq_sub_sq_abs_le (norm_nonneg _) (norm_nonneg _) ((norm_vl_le a).trans ha)
    ((norm_vl_le b).trans hb) h1

/-- The local Lipschitz constant of the energy. -/
noncomputable def Lam (β γ k R : ℝ) : ℝ :=
  2 * ((1 + k ^ 2) * R) * (1 + k ^ 2) + 2 * (LF β γ R * R) +
    (3 * |β| * R ^ 2 + 5 * |γ| * R ^ 4) * (2 * R)

theorem Esp_lip (β γ k : ℝ) {R : ℝ} (hR : 0 ≤ R) {a b : Hsp 2} (ha : ‖a‖ ≤ R) (hb : ‖b‖ ≤ R) :
    |Esp β γ k a - Esp β γ k b| ≤ Lam β γ k R * ‖a - b‖ := by
  have hk : 0 ≤ 1 + k ^ 2 := by positivity
  have hab : ‖a - b‖ ≤ 2 * R := by
    calc ‖a - b‖ ≤ ‖a‖ + ‖b‖ := norm_sub_le _ _
      _ ≤ 2 * R := by linarith
  have hvab : ‖vl a - vl b‖ ≤ ‖a - b‖ := by rw [← vl_sub]; exact norm_vl_le _
  -- kinetic part
  have hkin : |‖Asp k a‖ ^ 2 - ‖Asp k b‖ ^ 2| ≤ 2 * ((1 + k ^ 2) * R) * ((1 + k ^ 2) * ‖a - b‖) := by
    refine sq_sub_sq_abs_le (norm_nonneg _) (norm_nonneg _)
      ((norm_Asp_le k a).trans (mul_le_mul_of_nonneg_left ha hk))
      ((norm_Asp_le k b).trans (mul_le_mul_of_nonneg_left hb hk)) ?_
    refine (abs_norm_sub_norm_le _ _).trans ?_
    rw [← Asp_sub]
    exact norm_Asp_le k _
  -- potential part
  have hT := Nsp_taylor β γ hb ha
  have hFb : ‖vl (Fnl β γ b)‖ ≤ LF β γ R * R := by
    have h0 : ‖(0 : Hsp 2)‖ ≤ R := by rw [norm_zero]; exact hR
    have h := norm_Fnl_sub_le β γ hb h0
    rw [Fnl_zero, sub_zero, sub_zero] at h
    exact (norm_vl_le _).trans (h.trans (mul_le_mul_of_nonneg_left hb (LF_nonneg β γ)))
  have hin : |2 * (inner ℂ (vl (Fnl β γ b)) (vl a - vl b)).re| ≤
      2 * (LF β γ R * R) * ‖a - b‖ := by
    rw [abs_mul, abs_two, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ zero_le_two
    calc |(inner ℂ (vl (Fnl β γ b)) (vl a - vl b)).re|
        ≤ ‖vl (Fnl β γ b)‖ * ‖vl a - vl b‖ :=
          (Complex.abs_re_le_norm _).trans (norm_inner_le_norm _ _)
      _ ≤ LF β γ R * R * ‖a - b‖ :=
          mul_le_mul hFb hvab (norm_nonneg _) (mul_nonneg (LF_nonneg β γ) hR)
  have hsq : ‖vl a - vl b‖ ^ 2 ≤ 2 * R * ‖a - b‖ := by
    have h0 := norm_nonneg (vl a - vl b)
    nlinarith [norm_nonneg (a - b)]
  have hC : 0 ≤ 3 * |β| * R ^ 2 + 5 * |γ| * R ^ 4 := by positivity
  have hT' := hT.trans (mul_le_mul_of_nonneg_left hsq hC)
  have h1 := abs_le.1 hkin
  have h2 := abs_le.1 hT'
  have h3 := abs_le.1 hin
  rw [Esp, Esp, abs_le, Lam]
  constructor <;> nlinarith [norm_nonneg (a - b)]

/-! ### `H²`-level facts -/

theorem toSp_smul (c : ℂ) (U : H2 2) : H2.toSp (H2.smul c U) = c • H2.toSp U := by
  apply Hsp.ext
  rw [Hsp.val_smul]
  refine PiLp.ext fun o => ?_
  rw [PiLp.smul_apply]
  rcases o with _ | _ | i <;> rfl

theorem distH2_comm (U V : H2 2) : H2.distH2 U V = H2.distH2 V U := by
  unfold H2.distH2
  have h : ∑ i, ‖U.grad i - V.grad i‖ = ∑ i, ‖V.grad i - U.grad i‖ :=
    Finset.sum_congr rfl fun i _ => norm_sub_rev _ _
  rw [h, norm_sub_rev U.val, norm_sub_rev U.lap]

theorem distH2_triangle (U V W : H2 2) : H2.distH2 U W ≤ H2.distH2 U V + H2.distH2 V W := by
  unfold H2.distH2
  have h1 := norm_sub_le_norm_sub_add_norm_sub U.val V.val W.val
  have h2 := norm_sub_le_norm_sub_add_norm_sub U.lap V.lap W.lap
  have h3 : ∑ i, ‖U.grad i - W.grad i‖ ≤
      ∑ i, ‖U.grad i - V.grad i‖ + ∑ i, ‖V.grad i - W.grad i‖ := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ => norm_sub_le_norm_sub_add_norm_sub _ _ _
  linarith

theorem distH2_translate (y : R2) (U V : H2 2) :
    H2.distH2 (H2.translate y U) (H2.translate y V) = H2.distH2 U V := by
  simp only [H2.distH2, H2.translate, ← map_sub, LinearIsometry.norm_map]

theorem transL2_transL2_neg (y : R2) (f : L2 2) : transL2 y (transL2 (-y) f) = f := by
  apply Lp.ext
  have h1 := coeFn_transL2 y (transL2 (-y) f)
  have h2 := (mp_add_right y).quasiMeasurePreserving.ae_eq_comp (coeFn_transL2 (-y) f)
  filter_upwards [h1, h2] with x hx1 hx2
  rw [hx1]
  simp only [Function.comp_apply] at hx2
  rw [hx2, add_neg_cancel_right]

theorem translate_translate_neg (y : R2) (U : H2 2) :
    H2.translate y (H2.translate (-y) U) = U :=
  H2.ext_of_val (transL2_transL2_neg y U.val)

theorem distH2_le_four (U V : H2 2) : H2.distH2 U V ≤ 4 * ‖H2.toSp U - H2.toSp V‖ := by
  have h := H2.distH2_le U V
  norm_num at h
  linarith

end Sobolev

end ReyesMath

open Filter Topology Complex InnerProductSpace MeasureTheory Set
open scoped ContDiff FourierTransform NNReal

namespace ReyesMath

namespace Sobolev

variable {β γ k : ℝ}

attribute [local irreducible] Usp

/-! ### Continuous dependence on the data -/

theorem lipschitzOnWith_Gfield_rev {R : ℝ} (s : ℝ) :
    LipschitzOnWith ⟨LF β γ R, LF_nonneg β γ⟩ (fun x => -Gfield β γ k (-s) x)
      (Metric.closedBall 0 R) := by
  refine LipschitzOnWith.of_dist_le_mul fun a ha b hb => ?_
  have h := (lipschitzOnWith_Gfield (β := β) (γ := γ) (k := k) (R := R) (-s)).dist_le_mul a ha b hb
  show dist (-Gfield β γ k (-s) a) (-Gfield β γ k (-s) b) ≤ _
  rw [dist_neg_neg]
  exact h

theorem hasDerivAt_rev {W : ℝ → Hsp 2} (hW : ∀ t, HasDerivAt W (Gfield β γ k t (W t)) t)
    (s : ℝ) : HasDerivAt (fun r => W (-r)) (-Gfield β γ k (-s) (W (-s))) s := by
  have h := (hW (-s)).scomp s (hasDerivAt_neg s)
  rw [neg_one_smul] at h
  exact h

/-- **Gronwall estimate** for `w' = G(t, w)` on `[-T, T]`, along trajectories in a ball. -/
theorem ode_dist_le {W₁ W₂ : ℝ → Hsp 2} (h₁ : ∀ t, HasDerivAt W₁ (Gfield β γ k t (W₁ t)) t)
    (h₂ : ∀ t, HasDerivAt W₂ (Gfield β γ k t (W₂ t)) t) {R : ℝ}
    (hR₁ : ∀ t, ‖W₁ t‖ ≤ R) (hR₂ : ∀ t, ‖W₂ t‖ ≤ R) {T t : ℝ} (ht : t ∈ Icc (-T) T) :
    ‖W₁ t - W₂ t‖ ≤ ‖W₁ 0 - W₂ 0‖ * Real.exp (LF β γ R * T) := by
  have hK := LF_nonneg β γ (R := R)
  have hc₁ : Continuous W₁ := continuous_iff_continuousAt.2 fun s => (h₁ s).continuousAt
  have hc₂ : Continuous W₂ := continuous_iff_continuousAt.2 fun s => (h₂ s).continuousAt
  have hm₁ : ∀ s, W₁ s ∈ Metric.closedBall (0 : Hsp 2) R := fun s => by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hR₁ s
  have hm₂ : ∀ s, W₂ s ∈ Metric.closedBall (0 : Hsp 2) R := fun s => by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hR₂ s
  rcases le_total 0 t with h0 | h0
  · have key := dist_le_of_trajectories_ODE_of_mem (v := Gfield β γ k)
      (s := fun _ => Metric.closedBall (0 : Hsp 2) R) (K := ⟨LF β γ R, hK⟩) (a := 0) (b := T)
      (fun s _ => lipschitzOnWith_Gfield s) hc₁.continuousOn
      (fun s _ => (h₁ s).hasDerivWithinAt) (fun s _ => hm₁ s) hc₂.continuousOn
      (fun s _ => (h₂ s).hasDerivWithinAt) (fun s _ => hm₂ s) (le_refl _) t ⟨h0, ht.2⟩
    rw [dist_eq_norm, dist_eq_norm, NNReal.coe_mk, sub_zero] at key
    exact key.trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ht.2 hK)) (norm_nonneg _))
  · have hc₁' : Continuous fun r => W₁ (-r) := hc₁.comp continuous_neg
    have hc₂' : Continuous fun r => W₂ (-r) := hc₂.comp continuous_neg
    have key := dist_le_of_trajectories_ODE_of_mem (v := fun s x => -Gfield β γ k (-s) x)
      (s := fun _ => Metric.closedBall (0 : Hsp 2) R) (K := ⟨LF β γ R, hK⟩) (a := 0) (b := T)
      (f := fun r => W₁ (-r)) (g := fun r => W₂ (-r))
      (fun s _ => lipschitzOnWith_Gfield_rev s) hc₁'.continuousOn
      (fun s _ => (hasDerivAt_rev h₁ s).hasDerivWithinAt) (fun s _ => hm₁ (-s)) hc₂'.continuousOn
      (fun s _ => (hasDerivAt_rev h₂ s).hasDerivWithinAt) (fun s _ => hm₂ (-s)) (le_refl _) (-t)
      ⟨by linarith, by linarith [ht.1]⟩
    simp only [neg_neg, neg_zero] at key
    rw [dist_eq_norm, dist_eq_norm, NNReal.coe_mk, sub_zero] at key
    exact key.trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (by linarith [ht.1]) hK)) (norm_nonneg _))

theorem dep_arith {x δ e ε : ℝ} (hx0 : 0 ≤ x) (hx : x < δ) (he : 0 < e)
    (hδ : δ * (4 * e + 1) ≤ ε) : 4 * (x * e) < ε := by
  nlinarith [mul_lt_mul_of_pos_right hx he]

theorem Lam_nonneg (β γ k : ℝ) {R : ℝ} (hR : 0 ≤ R) : 0 ≤ Lam β γ k R := by
  unfold Lam
  have := LF_nonneg β γ (R := R)
  positivity

/-- **Continuous dependence on the data** on bounded time intervals. -/
theorem continuous_dependence (hγ : 0 < γ) {u : ℝ → H2 2} (hu : IsSolution β γ k u) (T : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ v : ℝ → H2 2, IsSolution β γ k v → H2.distH2 (v 0) (u 0) < δ →
      ∀ t ∈ Icc (-T) T, H2.distH2 (v t) (u t) < ε := by
  obtain ⟨B₀, hB₀⟩ : ∃ B₀, B₀ = Bd β γ k (H2.M (u 0)) (H2.energy β γ k (u 0)) := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R, R = Real.sqrt (B₀ + 1) := ⟨_, rfl⟩
  have hbound : ∀ w : ℝ → H2 2, IsSolution β γ k w →
      Bd β γ k (H2.M (w 0)) (H2.energy β γ k (w 0)) ≤ B₀ + 1 → ∀ t, ‖H2.toSp (w t)‖ ≤ R := by
    intro w hw hB t
    have h := norm_toSp_sq_le (β := β) (k := k) hγ (w t)
    rw [(conservation hw t).1, (conservation hw t).2] at h
    rw [hR]
    exact Real.le_sqrt_of_sq_le (h.trans hB)
  obtain ⟨R₀, hR₀⟩ : ∃ R₀, R₀ = ‖H2.toSp (u 0)‖ + 1 := ⟨_, rfl⟩
  have hR₀0 : 0 ≤ R₀ := by rw [hR₀]; positivity
  obtain ⟨cM, hcM⟩ : ∃ cM, cM = 3 * (3 * β ^ 2 / (16 * γ)) + (2 + 3 * k ^ 4) := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L, L = 3 * Lam β γ k R₀ + |cM| * (2 * R₀) := ⟨_, rfl⟩
  have hL0 : 0 ≤ L := by rw [hL]; have := Lam_nonneg β γ k hR₀0; positivity
  have hBd_lip : ∀ w₀ : H2 2, ‖H2.toSp w₀ - H2.toSp (u 0)‖ ≤ 1 →
      |Bd β γ k (H2.M w₀) (H2.energy β γ k w₀) - B₀| ≤ L * ‖H2.toSp w₀ - H2.toSp (u 0)‖ := by
    intro w₀ hw₀
    have hn : ‖H2.toSp w₀‖ ≤ R₀ := by
      have := norm_le_norm_add_norm_sub' (H2.toSp w₀) (H2.toSp (u 0))
      rw [hR₀]
      linarith
    have hn0 : ‖H2.toSp (u 0)‖ ≤ R₀ := by rw [hR₀]; linarith
    have hE := Esp_lip β γ k hR₀0 hn hn0
    have hM := mass_lip hn hn0
    rw [← energy_eq_Esp, ← energy_eq_Esp] at hE
    rw [← M_eq_vl, ← M_eq_vl] at hM
    have e : Bd β γ k (H2.M w₀) (H2.energy β γ k w₀) - B₀ =
        3 * (H2.energy β γ k w₀ - H2.energy β γ k (u 0)) + cM * (H2.M w₀ - H2.M (u 0)) := by
      rw [hB₀, hcM]
      unfold Bd
      ring
    have h1 := abs_le.1 hE
    have h2 := abs_le.1 hM
    have h3 : |cM * (H2.M w₀ - H2.M (u 0))| ≤ |cM| * (2 * R₀ * ‖H2.toSp w₀ - H2.toSp (u 0)‖) := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hM (abs_nonneg _)
    have h4 := abs_le.1 h3
    rw [e, hL, abs_le]
    constructor <;> nlinarith [norm_nonneg (H2.toSp w₀ - H2.toSp (u 0))]
  obtain ⟨e, he⟩ : ∃ e, e = Real.exp (LF β γ R * T) := ⟨_, rfl⟩
  have he0 : 0 < e := he ▸ Real.exp_pos _
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = min 1 (min (1 / (L + 1)) (ε / (4 * e + 1))) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have hδ1 : δ ≤ 1 := hδ ▸ min_le_left _ _
  have hδL : δ ≤ 1 / (L + 1) := hδ ▸ (min_le_right _ _).trans (min_le_left _ _)
  have hδε : δ * (4 * e + 1) ≤ ε := by
    have h : δ ≤ ε / (4 * e + 1) := hδ ▸ (min_le_right _ _).trans (min_le_right _ _)
    exact (le_div_iff₀ (by positivity)).1 h
  refine ⟨δ, hδ0, fun v hv hv0 t ht => ?_⟩
  have hΔ : ‖H2.toSp (v 0) - H2.toSp (u 0)‖ < δ := lt_of_le_of_lt (H2.norm_le_distH2 _ _) hv0
  have hBv : Bd β γ k (H2.M (v 0)) (H2.energy β γ k (v 0)) ≤ B₀ + 1 := by
    have h := hBd_lip (v 0) (hΔ.le.trans hδ1)
    have hLδ : L * ‖H2.toSp (v 0) - H2.toSp (u 0)‖ ≤ 1 := by
      calc L * ‖H2.toSp (v 0) - H2.toSp (u 0)‖ ≤ L * (1 / (L + 1)) :=
            mul_le_mul_of_nonneg_left (hΔ.le.trans hδL) hL0
        _ ≤ 1 := by rw [mul_one_div, div_le_one (by linarith)]; linarith
    linarith [(abs_le.1 h).2]
  have hBu : Bd β γ k (H2.M (u 0)) (H2.energy β γ k (u 0)) ≤ B₀ + 1 := by rw [hB₀]; linarith
  obtain ⟨Wu, hWu⟩ : ∃ W : ℝ → Hsp 2, ∀ s, W s = Usp k (-s) (H2.toSp (u s)) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨Wv, hWv⟩ : ∃ W : ℝ → Hsp 2, ∀ s, W s = Usp k (-s) (H2.toSp (v s)) :=
    ⟨_, fun _ => rfl⟩
  have hRu : ∀ s, ‖Wu s‖ ≤ R := fun s => by rw [hWu s, norm_Usp]; exact hbound u hu hBu s
  have hRv : ∀ s, ‖Wv s‖ ≤ R := fun s => by rw [hWv s, norm_Usp]; exact hbound v hv hBv s
  have key := ode_dist_le (ode_of_isSolution hv hWv) (ode_of_isSolution hu hWu) hRv hRu ht
  have h0 : Wv 0 - Wu 0 = H2.toSp (v 0) - H2.toSp (u 0) := by
    rw [hWv 0, hWu 0, neg_zero, Usp_zero, Usp_zero]
  have ht' : H2.toSp (v t) - H2.toSp (u t) = Usp k t (Wv t - Wu t) := by
    rw [map_sub, hWv t, hWu t, Usp_Usp_neg, Usp_Usp_neg]
  rw [h0, ← he] at key
  have hfin : ‖H2.toSp (v t) - H2.toSp (u t)‖ ≤ ‖H2.toSp (v 0) - H2.toSp (u 0)‖ * e := by
    rw [ht', norm_Usp]
    exact key
  calc H2.distH2 (v t) (u t) ≤ 4 * ‖H2.toSp (v t) - H2.toSp (u t)‖ := distH2_le_four _ _
    _ ≤ 4 * (‖H2.toSp (v 0) - H2.toSp (u 0)‖ * e) := by linarith
    _ < ε := dep_arith (norm_nonneg _) hΔ he0 hδε

end Sobolev

end ReyesMath
