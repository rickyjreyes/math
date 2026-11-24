import MathProofs.V18Identifiability

/-!
# GC26: exact global fibers of the actual v18 observation map

The quark correction coordinates are absent from the observed dispatch.
The Higgs amplitude and offset occur only in one combination.
These identities do not differentiate any floor or clipping branch.
-/

set_option maxHeartbeats 1000000

noncomputable section
namespace ReyesMath.V18Forward
open Filter
open scoped Topology

theorem observed_update_quarkAmp (p : Params) (t : ℝ) :
    observed (Function.update p (16 : Fin 31) t) = observed p := by
  funext i
  fin_cases i <;>
    norm_num [observed, light, lightRaw, middle, middleRaw, heavy,
      heavyCorrection, Function.update]

theorem observed_update_quarkPower (p : Params) (t : ℝ) :
    observed (Function.update p (18 : Fin 31) t) = observed p := by
  funext i
  fin_cases i <;>
    norm_num [observed, light, lightRaw, middle, middleRaw, heavy,
      heavyCorrection, Function.update]

def shiftHiggs (p : Params) (t : ℝ) : Params :=
  Function.update (Function.update p (27 : Fin 31) (p 27 + t))
    (28 : Fin 31) (p 28 - (123 / 124 : ℝ) * t)

private theorem shiftHiggs_light (p : Params) (t : ℝ) (n : ℕ) :
    light (shiftHiggs p t) n = light p n := by
  norm_num [shiftHiggs, light, lightRaw, Function.update]

private theorem shiftHiggs_middle (p : Params) (t : ℝ) (n : ℕ) :
    middle (shiftHiggs p t) n = middle p n := by
  norm_num [shiftHiggs, middle, middleRaw, Function.update]

private theorem shiftHiggs_heavyCorrection (p : Params) (t : ℝ) (n : Fin 3) :
    heavyCorrection (shiftHiggs p t) (![95, 96, 123] n) =
      heavyCorrection p (![95, 96, 123] n) := by
  fin_cases n <;>
    norm_num [shiftHiggs, heavyCorrection, Function.update] <;> ring

theorem observed_shiftHiggs (p : Params) (t : ℝ) :
    observed (shiftHiggs p t) = observed p := by
  have h0 := shiftHiggs_heavyCorrection p t (0 : Fin 3)
  have h1 := shiftHiggs_heavyCorrection p t (1 : Fin 3)
  have h2 := shiftHiggs_heavyCorrection p t (2 : Fin 3)
  norm_num at h0 h1 h2
  funext i
  fin_cases i <;>
    simp [observed, heavy, shiftHiggs_light, shiftHiggs_middle, h0, h1, h2]

/-- Three independent free scalars give an exact global family of equal outputs. -/
def invisibleFamily (p : Params) (a b c : ℝ) : Params :=
  shiftHiggs (Function.update (Function.update p (16 : Fin 31) a)
    (18 : Fin 31) b) c

theorem observed_invisibleFamily (p : Params) (a b c : ℝ) :
    observed (invisibleFamily p a b c) = observed p := by
  simp only [invisibleFamily, observed_shiftHiggs,
    observed_update_quarkPower, observed_update_quarkAmp]

theorem invisibleFamily_injective (p : Params) :
    Function.Injective (fun t : ℝ × ℝ × ℝ =>
      invisibleFamily p t.1 t.2.1 t.2.2) := by
  rintro ⟨a,b,c⟩ ⟨d,e,f⟩ h
  have h16 := congrFun h (16 : Fin 31)
  have h18 := congrFun h (18 : Fin 31)
  have h27 := congrFun h (27 : Fin 31)
  norm_num [invisibleFamily, shiftHiggs, Function.update] at h16 h18 h27
  have hc : c = f := by linarith
  exact Prod.ext h16 (Prod.ext h18 hc)

/-- At every ambient point, even at a nonsmooth floor or clip, every
neighborhood contains a distinct point on the exact same fiber. -/
theorem observed_all_points_nonisolated (p : Params) (U : Set Params)
    (hU : U ∈ 𝓝 p) : ∃ q ∈ U, q ≠ p ∧ observed q = observed p := by
  let path : ℝ → Params := fun t => Function.update p (16 : Fin 31) t
  have hc : Continuous path := by
    apply continuous_pi
    intro i
    by_cases hi : i = (16 : Fin 31)
    · subst i
      simpa [path] using (continuous_id : Continuous (fun t : ℝ => t))
    · simpa [path, Function.update, hi] using
        (continuous_const : Continuous (fun _ : ℝ => p i))
  have hp : path (p 16) = p := by
    funext i
    by_cases hi : i = (16 : Fin 31)
    · subst i
      simp [path]
    · simp [path, Function.update, hi]
  have ht : Tendsto path (𝓝 (p 16)) (𝓝 p) := by
    simpa only [ContinuousAt, hp] using (hc.continuousAt (x := p 16))
  have hnear : ∀ᶠ t in 𝓝 (p 16), path t ∈ U := ht hU
  have hne : ∀ᶠ t in 𝓝[≠] (p 16), t ≠ p 16 := self_mem_nhdsWithin
  obtain ⟨t, hu, htne⟩ := ((hnear.filter_mono nhdsWithin_le_nhds).and hne).exists
  refine ⟨path t, hu, ?_, observed_update_quarkAmp p t⟩
  intro he
  apply htne
  simpa [path] using congrFun he (16 : Fin 31)

/-- A relative domain inherits non-isolation whenever it permits arbitrarily
small changes of the unused quark amplitude. The hypothesis is explicit;
a fixed-coordinate prior is not automatically covered. -/
theorem observed_relative_nonisolated (p : Params) (S : Set Params)
    (h : ∀ U : Set Params, U ∈ 𝓝 p →
      ∃ t : ℝ, t ≠ p 16 ∧ Function.update p (16 : Fin 31) t ∈ U ∩ S)
    (U : Set Params) (hU : U ∈ 𝓝 p) :
    ∃ q ∈ U ∩ S, q ≠ p ∧ observed q = observed p := by
  obtain ⟨t, ht, hmem⟩ := h U hU
  refine ⟨_, hmem, ?_, observed_update_quarkAmp p t⟩
  intro he
  apply ht
  simpa using congrFun he (16 : Fin 31)

theorem observed_not_injective : ¬ Function.Injective observed := by
  intro h
  let p : Params := fun _ => 0
  have he := h (observed_update_quarkAmp p 1)
  have hn := congrFun he (16 : Fin 31)
  norm_num [p] at hn

/-- Exact scalar floor-fiber test, including equality at the clipping boundary. -/
theorem floor_eq_iff (x c y : ℝ) :
    max x c = y ↔ x ≤ y ∧ c ≤ y ∧ (x = y ∨ c = y) := by
  constructor
  · intro h
    refine ⟨h ▸ le_max_left x c, h ▸ le_max_right x c, ?_⟩
    rcases le_total x c with hx | hx
    · exact Or.inr ((max_eq_right hx).symm.trans h)
    · exact Or.inl ((max_eq_left hx).symm.trans h)
  · rintro ⟨hx, hc, h | h⟩
    · rw [h, max_eq_left hc]
    · rw [h, max_eq_right hx]

/-- Exact nested floor-fiber test: applies to heavy outputs at every point. -/
theorem nested_floor_eq_iff (x d c y : ℝ) :
    max (max x c + d) c = y ↔
      x + d ≤ y ∧ c + d ≤ y ∧ c ≤ y ∧
      (x + d = y ∨ c + d = y ∨ c = y) := by
  have h : max x c + d = max (x + d) (c + d) := by
    rcases le_total x c with hx | hx
    · rw [max_eq_right hx, max_eq_right (add_le_add_right hx d)]
    · rw [max_eq_left hx, max_eq_left (add_le_add_right hx d)]
  rw [h, floor_eq_iff, max_le_iff, floor_eq_iff]
  tauto

/-- A polynomial with generically nonzero derivative need not be globally injective. -/
theorem generic_rank_counterexample :
    (∀ x : ℝ, x ≠ 0 → HasDerivAt (fun t : ℝ => t ^ 2) (2 * x) x ∧
      2 * x ≠ 0) ∧ ¬ Function.Injective (fun t : ℝ => t ^ 2) := by
  constructor
  · intro x hx
    exact ⟨by simpa using (hasDerivAt_pow 2 x), mul_ne_zero (by norm_num) hx⟩
  · intro h
    have hn : (1 : ℝ) = -1 := h (by norm_num)
    norm_num at hn

/-- Any differentiable augmented observation with fewer than 31 output
coordinates has a nontrivial derivative kernel. This is a rank obstruction,
not by itself an obstruction to a singular isolated fiber. -/
theorem augmented_rank_obstruction (N : ℕ) (hN : N < 31)
    (J : Params →L[ℝ] (Fin N → ℝ)) :
    0 < Module.finrank ℝ (LinearMap.ker J.toLinearMap) := by
  have hr : Module.finrank ℝ (LinearMap.range J.toLinearMap) ≤ N := by
    simpa using (Submodule.finrank_le (LinearMap.range J.toLinearMap))
  have hsum := LinearMap.finrank_range_add_finrank_ker J.toLinearMap
  have hdim : Module.finrank ℝ Params = 31 := by simp [Params]
  omega

/-- Strict separation by a positive inner-product pairing is sufficient
for injectivity, independently of the Jacobian. -/
theorem injective_of_strict_pairing {X Y : Type*} (f : X → Y)
    (pairing : X → X → Y → Y → ℝ)
    (h : ∀ x z, x ≠ z → 0 < pairing x z (f x) (f z))
    (hdiag : ∀ x z y, pairing x z y y = 0) :
    Function.Injective f := by
  intro x z hz
  by_contra hne
  have hp := h x z hne
  rw [hz, hdiag] at hp
  exact (lt_irrefl 0 hp)

/-! Historical two-coordinate slice, with all 29 stored coefficients fixed. -/

def historicalNumerator (n : ℕ) : ℝ :=
  frozenLightBase n * (if n = 3 then (0.0048 : ℝ) else 1)

theorem historical_lightRaw (a e : ℝ) (n : ℕ) :
    lightRaw (frozen a e) n =
      historicalNumerator n * (1 + Real.exp (a * ((n : ℝ) - e)))⁻¹ := by
  simp only [lightRaw, frozen, frozenLightBase, historicalNumerator, Matrix.cons_val]
  split_ifs <;> simp_all <;> ring

/-- Two equal, strictly unfloored logistic outputs with a common numerator
force their logit arguments to agree. No approximation of exp is used. -/
theorem logistic_floor_logit_eq (A x z : ℝ)
    (hx : (1e-12 : ℝ) < max (A * (1 + Real.exp x)⁻¹) 1e-12)
    (h : max (A * (1 + Real.exp x)⁻¹) 1e-12 =
      max (A * (1 + Real.exp z)⁻¹) 1e-12) : x = z := by
  have hx' : (1e-12 : ℝ) < A * (1 + Real.exp x)⁻¹ := by
    by_contra! hh
    rw [max_eq_right hh] at hx
    exact (lt_irrefl _ hx)
  have hz : (1e-12 : ℝ) < A * (1 + Real.exp z)⁻¹ := by
    rw [h] at hx
    by_contra! hh
    rw [max_eq_right hh] at hx
    exact (lt_irrefl _ hx)
  have hA : A ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hx'
    norm_num at hx'
  have hv : A * (1 + Real.exp x)⁻¹ = A * (1 + Real.exp z)⁻¹ := by
    simpa only [max_eq_left hx'.le, max_eq_left hz.le] using h
  have hi := mul_left_cancel₀ hA hv
  have hd : 1 + Real.exp x = 1 + Real.exp z := by
    simpa only [inv_inv] using congrArg (fun v : ℝ => v⁻¹) hi
  exact Real.exp_injective (add_left_cancel hd)

/-- Global uniqueness on the historical two-parameter slice whenever
alpha is positive and the first two observed light rows are unfloored.
The competing parameter pair need not be nearby or inside the optimizer box. -/
theorem historical_two_active_unique (a e b f : ℝ) (ha : 0 < a)
    (h0 : (1e-12 : ℝ) < observed (frozen a e) 0)
    (h1 : (1e-12 : ℝ) < observed (frozen a e) 1)
    (h : observed (frozen a e) = observed (frozen b f)) :
    a = b ∧ e = f := by
  have h0' := congrFun h (0 : Fin 11)
  have h1' := congrFun h (1 : Fin 11)
  change (1e-12 : ℝ) < light (frozen a e) 1 at h0
  change (1e-12 : ℝ) < light (frozen a e) 2 at h1
  change light (frozen a e) 1 = light (frozen b f) 1 at h0'
  change light (frozen a e) 2 = light (frozen b f) 2 at h1'
  simp only [light, historical_lightRaw, Nat.cast_one, Nat.cast_ofNat] at h0 h1 h0' h1'
  have he0 := logistic_floor_logit_eq (historicalNumerator 1) _ _ h0 h0'
  have he1 := logistic_floor_logit_eq (historicalNumerator 2) _ _ h1 h1'
  have hab : a = b := by nlinarith only [he0, he1]
  subst b
  have hp : a * e = a * f := by nlinarith only [he0]
  exact ⟨rfl, mul_left_cancel₀ (ne_of_gt ha) hp⟩

/-- At alpha zero the historical epsilon coordinate is exactly invisible. -/
theorem historical_zero_alpha (e f : ℝ) :
    observed (frozen 0 e) = observed (frozen 0 f) := by
  funext i
  fin_cases i <;>
    norm_num [observed, light, lightRaw, middle, middleRaw, heavy,
      heavyCorrection, frozen, Matrix.cons_val]

/-! The exact geometry of the transformed rectangle, separated from
the source-specific transcendental threshold enclosures. -/

theorem historical_active_prefix (a t h1 h2 h3 : ℝ)
    (ha : 0 ≤ a) (ht : t ≤ a) (h12 : h2 < 2 * h1)
    (h32 : h3 < h2) :
    (h1 ≤ t → h2 ≤ a + t) ∧
    (h2 ≤ a + t → h3 ≤ 2 * a + t) := by
  constructor <;> intro h <;> linarith

/-- The first-row-only fiber, after the logit fixes t, is an exact interval.
This includes the triangle constraints and all remaining floor inequalities. -/
theorem historical_one_active_interval (a t h2 h3 : ℝ)
    (h32 : h3 ≤ h2) :
    (0 ≤ a ∧ a ≤ 50 ∧ 0 ≤ a - t ∧ a - t ≤ 5 * a ∧
      h2 ≤ a + t ∧ h3 ≤ 2 * a + t) ↔
    max 0 (max t (max (-t / 4) (h2 - t))) ≤ a ∧ a ≤ 50 := by
  simp only [max_le_iff]
  constructor
  · rintro ⟨ha, hu, hz, hza, h2a, _⟩
    exact ⟨⟨ha, by linarith, by linarith, by linarith⟩, hu⟩
  · rintro ⟨⟨ha, ht, hneg, hh⟩, hu⟩
    exact ⟨ha, hu, by linarith, by linarith, by linarith, by linarith⟩

/-- In the one-active region the lower endpoint reaches the upper bound
exactly at the exceptional clipping-edge point. -/
theorem historical_exceptional_endpoint (t h1 h2 : ℝ)
    (ht : t < h1) (h12 : h1 < h2) (hupper : h2 < 40)
    (hp : 0 < h2) (hfeas : h2 - 50 ≤ t) :
    max 0 (max t (max (-t / 4) (h2 - t))) = 50 ↔ t = h2 - 50 := by
  have ht50 : t < 50 := by linarith
  have hneg50 : -t / 4 < 50 := by linarith
  constructor
  · intro h
    have hmax := (floor_eq_iff (0 : ℝ) (max t (max (-t / 4) (h2 - t))) 50).mp h
    have hh : max t (max (-t / 4) (h2 - t)) = 50 := by
      rcases hmax.2.2 with h0 | h0
      · norm_num at h0
      · exact h0
    have hmax2 := (floor_eq_iff t (max (-t / 4) (h2 - t)) 50).mp hh
    have hh2 : max (-t / 4) (h2 - t) = 50 := by
      rcases hmax2.2.2 with h0 | h0
      · linarith
      · exact h0
    have hmax3 := (floor_eq_iff (-t / 4) (h2 - t) 50).mp hh2
    rcases hmax3.2.2 with h0 | h0 <;> linarith
  · intro he
    have hh : h2 - t = 50 := by linarith
    rw [hh, max_eq_right hneg50.le, max_eq_right ht50.le]
    norm_num

/-! A source-model plateau, not an assumed constant map. -/

def plateauCenter : Params := fun i =>
  if i = 7 ∨ i = 14 ∨ i = 17 ∨ i = 28 then -1
  else if i = 8 then 1 else 0

/-- Every observed coordinate is exactly at the floor on an ambient
neighborhood of an explicit 31-vector. This supports the stronger
topological lower bound on global observation augmentation. -/
theorem observed_constant_near_plateau :
    ∀ᶠ q in 𝓝 plateauCenter, observed q = fun _ => (1e-12 : ℝ) := by
  have hl (i : Fin 3) :
      (fun q => light q (i.val + 1)) =ᶠ[𝓝 plateauCenter]
        (fun _ => (1e-12 : ℝ)) := by
    apply eventually_max_right (continuous_lightRaw (i.val + 1)).continuousAt
    fin_cases i <;> norm_num [plateauCenter, lightRaw, clip, topo]
  have hm (i : Fin 5) :
      (fun q => middle q (middleN i)) =ᶠ[𝓝 plateauCenter]
        (fun _ => (1e-12 : ℝ)) := by
    apply eventually_max_right (contDiff_middleRaw (middleN i)).continuous.continuousAt
    fin_cases i <;> norm_num [plateauCenter, middleN, middleRaw, Matrix.cons_val]
  have hh (i : Fin 3) :
      (fun q => heavy q (heavyN i)) =ᶠ[𝓝 plateauCenter]
        (fun _ => (1e-12 : ℝ)) := by
    apply eventually_max_right
      ((continuous_light (heavyN i)).add (continuous_heavyCorrection (heavyN i))).continuousAt
    fin_cases i <;>
      norm_num [plateauCenter, heavyN, light, lightRaw, heavyCorrection,
        clip, topo, Matrix.cons_val, Real.rpow_zero]
  filter_upwards [hl 0, hl 1, hl 2, hm 0, hm 1, hm 2, hm 3, hm 4,
    hh 0, hh 1, hh 2] with q l0 l1 l2 m0 m1 m2 m3 m4 h0 h1 h2
  funext i
  fin_cases i <;> first | exact l0 | exact l1 | exact l2 |
    exact m0 | exact m1 | exact m2 | exact m3 | exact m4 |
    exact h0 | exact h1 | exact h2

/-- A canonical representative for the three affine invisible directions.
This does not quotient the other, nonlinear observation aliases. -/
def canonicalInvisible (p : Params) : Params :=
  invisibleFamily p 0 0 (-(p 27))

theorem observed_canonicalInvisible (p : Params) :
    observed (canonicalInvisible p) = observed p :=
  observed_invisibleFamily p 0 0 (-(p 27))

theorem canonicalInvisible_zero_coords (p : Params) :
    canonicalInvisible p 16 = 0 ∧ canonicalInvisible p 18 = 0 ∧
      canonicalInvisible p 27 = 0 := by
  norm_num [canonicalInvisible, invisibleFamily, shiftHiggs, Function.update]

/-! Exact historical thresholds. -/
def historicalThreshold (n : ℕ) : ℝ :=
  Real.log (historicalNumerator n / (1e-12 : ℝ) - 1)

theorem historical_numerator_bounds :
    (0.4 : ℝ) < historicalNumerator 1 ∧ historicalNumerator 1 < 1 ∧
    2 < historicalNumerator 2 ∧ historicalNumerator 2 < 12 ∧
    (1e-12 : ℝ) < historicalNumerator 3 ∧ historicalNumerator 3 < 0.1 := by
  have h1 := frozenLightBase_one
  have h2 := frozenLightBase_two
  have h3 := frozenLightBase_three
  have u1 := frozenLightBase_one_upper
  have u2 := frozenLightBase_two_upper
  have u3 := frozenLightBase_three_upper
  norm_num [historicalNumerator]
  exact ⟨h1, u1, h2, u2, by linarith, by linarith⟩

private theorem exp_twenty_lt : Real.exp 20 < (3 : ℝ)^20 := by
  have h : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  calc
    Real.exp 20 = Real.exp 1 ^ (20 : ℕ) := by
      rw [← Real.exp_nat_mul] <;> norm_num
    _ < _ := pow_lt_pow_left₀ h (Real.exp_pos _).le (by decide)

private theorem exp_forty_gt : (2.5 : ℝ)^40 < Real.exp 40 := by
  have h : (2.5 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  calc
    (2.5 : ℝ)^40 < Real.exp 1 ^ (40 : ℕ) :=
      pow_lt_pow_left₀ h (by norm_num) (by decide)
    _ = Real.exp 40 := by rw [← Real.exp_nat_mul] <;> norm_num

theorem historical_threshold_bounds :
    0 < historicalThreshold 3 ∧ historicalThreshold 3 < historicalThreshold 1 ∧
    historicalThreshold 1 < historicalThreshold 2 ∧
    20 < historicalThreshold 1 ∧ historicalThreshold 2 < 40 := by
  obtain ⟨h1,u1,h2,u2,h3,u3⟩ := historical_numerator_bounds
  have h3' : 0.00002 < historicalNumerator 3 := by
    have h := frozenLightBase_three
    norm_num [historicalNumerator]
    linarith
  have q1 : 0 < historicalNumerator 1 / (1e-12 : ℝ) - 1 := by linarith
  have q2 : 0 < historicalNumerator 2 / (1e-12 : ℝ) - 1 := by linarith
  have q3 : 1 < historicalNumerator 3 / (1e-12 : ℝ) - 1 := by linarith
  unfold historicalThreshold
  refine ⟨Real.log_pos q3, Real.log_lt_log (by linarith) (by linarith),
    Real.log_lt_log q1 (by linarith), ?_, ?_⟩
  · apply (Real.lt_log_iff_exp_lt q1).2
    have h := exp_twenty_lt
    norm_num at h
    linarith
  · apply (Real.log_lt_iff_lt_exp q2).2
    have h := exp_forty_gt
    norm_num at h
    linarith

/-- The exact (unrounded) threshold test, valid for any historical row
whose fixed numerator exceeds twice the floor. -/
theorem historical_light_active_iff (a e : ℝ) (n : ℕ)
    (hA : (2e-12 : ℝ) < historicalNumerator n) :
    (1e-12 : ℝ) < light (frozen a e) n ↔
      a * ((n : ℝ) - e) < historicalThreshold n := by
  have hd : 0 < 1 + Real.exp (a * ((n : ℝ) - e)) := by positivity
  have hq : 0 < historicalNumerator n / (1e-12 : ℝ) - 1 := by linarith
  rw [light, historical_lightRaw, ← div_eq_mul_inv, lt_max_iff, or_iff_left (lt_irrefl _),
    historicalThreshold, Real.lt_log_iff_exp_lt hq, lt_div_iff₀ hd]
  constructor <;> intro h <;> linarith

/-- Exact reconstruction from the canonical quotient representative
and the three eliminated coordinates. -/
theorem invisible_reconstruct (p : Params) :
    invisibleFamily (canonicalInvisible p) (p 16) (p 18) (p 27) = p := by
  funext i
  fin_cases i <;>
    norm_num [canonicalInvisible, invisibleFamily, shiftHiggs, Function.update] <;> ring

/-- An arbitrarily large change in an unused coordinate is completely
invisible to the actual spectral observations. -/
theorem observed_unbounded_coordinate_fiber (p : Params) (R : ℝ) :
    ∃ q : Params, R < q 16 ∧ observed q = observed p := by
  refine ⟨Function.update p (16 : Fin 31) (R + 1), ?_,
    observed_update_quarkAmp p (R + 1)⟩
  simp

/-- Historical heavy rows remain constant for all real alpha and epsilon,
not only at the previously frozen epsilon=5. -/
theorem historical_heavy_light_floor (a e : ℝ) (i : Fin 3) :
    light (frozen a e) (heavyN i) = (1e-12 : ℝ) := by
  have hn : heavyN i ≠ 3 := by fin_cases i <;> decide
  rw [light, historical_lightRaw, historicalNumerator, if_neg hn, mul_one]
  apply max_eq_right
  have h := mul_neg_of_neg_of_pos (frozenLightBase_heavy_neg i)
    (show 0 < (1 + Real.exp (a * ((heavyN i : ℝ) - e)))⁻¹ by positivity)
  linarith

theorem historical_heavy_constant (a e b f : ℝ) (i : Fin 3) :
    heavy (frozen a e) (heavyN i) = heavy (frozen b f) (heavyN i) := by
  rw [heavy, heavy, historical_heavy_light_floor, historical_heavy_light_floor]
  fin_cases i <;> norm_num [heavyN, heavyCorrection, frozen, Matrix.cons_val]

/-- On the historical slice the complete eleven-output fiber is exactly
the fiber of the three light rows. -/
theorem historical_equal_iff_light (a e b f : ℝ) :
    observed (frozen a e) = observed (frozen b f) ↔
      ∀ i : Fin 3, light (frozen a e) (i.val + 1) =
        light (frozen b f) (i.val + 1) := by
  constructor
  · intro h i
    fin_cases i
    · exact congrFun h (0 : Fin 11)
    · exact congrFun h (1 : Fin 11)
    · exact congrFun h (2 : Fin 11)
  · intro h
    funext i
    fin_cases i
    · exact h 0
    · exact h 1
    · exact h 2
    · norm_num [observed, middle, middleRaw, frozen, Matrix.cons_val]
    · norm_num [observed, middle, middleRaw, frozen, Matrix.cons_val]
    · norm_num [observed, middle, middleRaw, frozen, Matrix.cons_val]
    · norm_num [observed, middle, middleRaw, frozen, Matrix.cons_val]
    · norm_num [observed, middle, middleRaw, frozen, Matrix.cons_val]
    · exact historical_heavy_constant a e b f 0
    · exact historical_heavy_constant a e b f 1
    · exact historical_heavy_constant a e b f 2

/-- All actual outputs obey the positive source floor. -/
theorem observed_floor_le (p : Params) (i : Fin 11) :
    (1e-12 : ℝ) ≤ observed p i := by
  fin_cases i <;> exact le_max_right _ _

/-- A square real observation block with nonzero determinant attains every
right hand side. Used in the analytical full-range proof. -/
theorem square_system_solvable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (h : A.det ≠ 0) (y : Fin n → ℝ) :
    ∃ x : Fin n → ℝ, A.mulVec x = y := by
  have hu : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).mpr
    (isUnit_iff_ne_zero.mpr h)
  have hr := Matrix.rank_of_isUnit A hu
  have hs : Function.Surjective A.mulVecLin := by
    apply LinearMap.range_eq_top.mp
    apply Submodule.eq_top_of_finrank_eq
    change Module.finrank ℝ (LinearMap.range A.mulVecLin) =
      Module.finrank ℝ (Fin n → ℝ)
    simpa [Matrix.rank] using hr
  exact hs y

end ReyesMath.V18Forward
