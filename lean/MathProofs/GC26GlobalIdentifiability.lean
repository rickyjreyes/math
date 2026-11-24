import MathProofs.V18Identifiability

/-!
# GC26: exact global fibers of the actual v18 observation map

The quark correction coordinates are absent from the observed dispatch.
The Higgs amplitude and offset occur only in one combination.
These identities do not differentiate any floor or clipping branch.
-/

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

end ReyesMath.V18Forward
