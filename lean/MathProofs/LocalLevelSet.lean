import MathProofs.LocalIdentifiability

/-!
# C¹ local coordinates for a regular level set

This is the coordinate formulation of a C¹ embedded submanifold: an ambient
C¹ chart with C¹ inverse sends the level set to a vertical linear slice.
Unlike a merely topological implicit-function chart, both maps below are
proved C¹ on their open source and target.
-/

noncomputable section
namespace ReyesMath
open Filter
open scoped Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] [FiniteDimensional ℝ F]

/-- A surjective C¹ derivative gives local ambient C¹ coordinates in which
the original function is exactly the first projection. -/
theorem exists_c1_level_set_chart (f : E → F) (a : E) (J : E →L[ℝ] F)
    (hf : ContDiffAt ℝ 1 f a) (hd : HasFDerivAt f J a) (hs : Function.Surjective J) :
    ∃ e : PartialHomeomorph E (F × LinearMap.ker J.toLinearMap),
      a ∈ e.source ∧ e a = (f a, 0) ∧
      ContDiffOn ℝ 1 e e.source ∧ ContDiffOn ℝ 1 e.symm e.target ∧
      ∀ x, (e x).1 = f x := by
  have hstrict := hf.hasStrictFDerivAt' hd (by norm_num)
  have hr : LinearMap.range J.toLinearMap = ⊤ := LinearMap.range_eq_top.mpr hs
  have hk := J.ker_closedComplemented_of_finiteDimensional_range
  let data := hstrict.implicitFunctionDataOfComplemented f J hr hk
  let e := data.toPartialHomeomorph
  have ha : a ∈ e.source := data.pt_mem_toPartialHomeomorph_source
  have he : e a = (f a, 0) := by
    change (f a, Classical.choose hk (a - a)) = _
    simp
  have hc : ContDiffAt ℝ 1 e a := by
    change ContDiffAt ℝ 1 (fun x => (f x, Classical.choose hk (x - a))) a
    exact hf.prodMk ((Classical.choose hk).contDiff.contDiffAt.comp a
      (contDiffAt_id.sub contDiffAt_const))
  have hd' := data.hasStrictFDerivAt.hasFDerivAt
  have hi : ContDiffAt ℝ 1 e.symm (e a) := by
    apply e.contDiffAt_symm (e.map_source ha)
    · simpa only [e.left_inv ha] using hd'
    · simpa only [e.left_inv ha] using hc
  obtain ⟨U, hU, hUo, haU⟩ := eventually_nhds_iff.mp (hc.eventually (by norm_num))
  obtain ⟨V, hV, hVo, haV⟩ := eventually_nhds_iff.mp (hi.eventually (by norm_num))
  let e' := ((e.restrOpen U hUo).symm.restrOpen V hVo).symm
  refine ⟨e', ?_, he, ?_, ?_, ?_⟩
  · exact ⟨⟨ha, haU⟩, haV⟩
  · intro x hx
    exact (hU x hx.1.2).contDiffWithinAt
  · intro y hy
    exact (hV y hy.2).contDiffWithinAt
  · intro x
    rfl

/-- The manuscript's conditional proposition, for an arbitrary 31-to-11 C¹
map on an open neighborhood. The chart exhibits a twenty-dimensional
embedded level set by fixing its first eleven coordinates. -/
theorem conditional_local_level_set
    (f : (Fin 31 → ℝ) → (Fin 11 → ℝ)) (a : Fin 31 → ℝ)
    (J : (Fin 31 → ℝ) →L[ℝ] (Fin 11 → ℝ))
    (U : Set (Fin 31 → ℝ)) (hU : IsOpen U) (ha : a ∈ U)
    (hc : ContDiffOn ℝ 1 f U) (hd : HasFDerivAt f J a)
    (hr : Module.finrank ℝ (LinearMap.range J.toLinearMap) = 11) :
    Module.finrank ℝ (LinearMap.ker J.toLinearMap) = 20 ∧
    ∃ e : PartialHomeomorph (Fin 31 → ℝ)
        ((Fin 11 → ℝ) × LinearMap.ker J.toLinearMap),
      a ∈ e.source ∧ e a = (f a, 0) ∧
      ContDiffOn ℝ 1 e e.source ∧ ContDiffOn ℝ 1 e.symm e.target ∧
      (∀ x, (e x).1 = f x) ∧
      (∀ x ∈ e.source, f x = f a ↔ (e x).1 = f a) := by
  have hs : Function.Surjective J := by
    apply LinearMap.range_eq_top.mp
    apply Submodule.eq_top_of_finrank_eq
    simpa using hr
  have hn := LinearMap.finrank_range_add_finrank_ker J.toLinearMap
  have hdim : Module.finrank ℝ (Fin 31 → ℝ) = 31 := by simp
  refine ⟨by omega, ?_⟩
  obtain ⟨e, he, he0, hce, hci, hef⟩ :=
    exists_c1_level_set_chart f a J (hc.contDiffAt (hU.mem_nhds ha)) hd hs
  exact ⟨e, he, he0, hce, hci, hef, fun x _ => by rw [hef]⟩

/-- The chart sends the entire local level set onto a vertical slice. -/
theorem level_set_chart_image {G : Type*} [TopologicalSpace G]
    (f : E → F) (a : E) (e : PartialHomeomorph E (F × G))
    (hf : ∀ x, (e x).1 = f x) :
    e '' {x | x ∈ e.source ∧ f x = f a} =
      {y | y ∈ e.target ∧ y.1 = f a} := by
  ext y
  constructor
  · rintro ⟨x, ⟨hx, hfx⟩, rfl⟩
    exact ⟨e.map_source hx, (hf x).trans hfx⟩
  · rintro ⟨hy, hyf⟩
    refine ⟨e.symm y, ⟨e.map_target hy, ?_⟩, e.right_inv hy⟩
    rw [← hf (e.symm y), e.right_inv hy]
    exact hyf

/-- A positive-dimensional local fiber has a different equal-output point
in every ambient neighborhood. No classification of distant fibers is made. -/
theorem level_set_not_isolated {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [Nontrivial G]
    (f : E → F) (a : E) (e : PartialHomeomorph E (F × G))
    (ha : a ∈ e.source) (he : e a = (f a, 0)) (hf : ∀ x, (e x).1 = f x)
    (U : Set E) (hU : U ∈ 𝓝 a) :
    ∃ x ∈ U, x ≠ a ∧ f x = f a := by
  obtain ⟨v, hv⟩ := exists_ne (0 : G)
  let path := fun t : ℝ => (f a, t • v)
  have hp : Continuous path := continuous_const.prodMk (continuous_id.smul continuous_const)
  have ht : Tendsto path (𝓝 0) (𝓝 (e a)) := by
    simpa [ContinuousAt, path, he] using hp.continuousAt (x := 0)
  have htarget : ∀ᶠ t in 𝓝 (0 : ℝ), path t ∈ e.target :=
    ht (e.open_target.mem_nhds (e.map_source ha))
  have hnear : ∀ᶠ t in 𝓝 (0 : ℝ), e.symm (path t) ∈ U :=
    ((e.tendsto_symm ha).comp ht) hU
  have hne : ∀ᶠ t in 𝓝[≠] (0 : ℝ), t ≠ 0 := self_mem_nhdsWithin
  obtain ⟨t, ⟨hu, htar⟩, ht0⟩ :=
    (((hnear.and htarget).filter_mono nhdsWithin_le_nhds).and hne).exists
  refine ⟨e.symm (path t), hu, ?_, ?_⟩
  · intro hx
    have hz : t • v = 0 := by
      have h := congrArg (fun x => (e x).2) hx
      simpa only [e.right_inv htar, he] using h
    exact (smul_ne_zero ht0 hv) hz
  · have h := congrArg Prod.fst (e.right_inv htar)
    simpa only [hf] using h

end ReyesMath
