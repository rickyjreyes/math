import Mathlib

/-!
# GC08: constructive smooth Hadamard factorization

This module isolates the general analytic step of the polar and global
invariant-coordinate normal forms. It does not assume smoothness of the
integral coefficient: that follows from parameter differentiation on a
compact integration interval. Candidate proof for the pinned Mathlib.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval
namespace ReyesMath.GC08

universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem compact_parameter_bound [ProperSpace E]
    {G : Type u} [NormedAddCommGroup G]
    (F : E × ℝ → G) (hF : Continuous F) (x : E) :
    ∃ M : ℝ, ∀ y ∈ Metric.closedBall x 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖F (y,t)‖ ≤ M := by
  have hc : IsCompact (Metric.closedBall x 1 ×ˢ Icc (0 : ℝ) 1) :=
    (isCompact_closedBall x 1).prod isCompact_Icc
  obtain ⟨M,hM⟩ := hc.bddAbove_image hF.norm.continuousOn
  exact ⟨M,fun y hy t ht => hM ⟨(y,t),⟨hy,ht⟩,rfl⟩⟩

/-- Continuous parameter integration over the fixed interval [0,1].
The local domination is obtained from the actual compact product. -/
theorem continuous_parameter_integral [ProperSpace E]
    {G : Type u} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (F : E × ℝ → G) (hF : Continuous F) :
    Continuous (fun x => ∫ t in (0 : ℝ)..1, F (x,t)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  obtain ⟨M,hM⟩ := compact_parameter_bound F hF x
  apply intervalIntegral.continuousAt_of_dominated_interval (bound := fun _ => M)
  · exact Eventually.of_forall fun y =>
      (hF.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds x (by norm_num : (0 : ℝ)<1)] with y hy
    exact Eventually.of_forall fun t ht => hM y (Metric.ball_subset_closedBall hy) t
      (by
        have ht' : t ∈ Ioc (0 : ℝ) 1 := by simpa [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
        exact ⟨ht'.1.le,ht'.2⟩)
  · exact intervalIntegrable_const
  · exact Eventually.of_forall fun t _ =>
      (hF.comp (continuous_id.prodMk continuous_const)).continuousAt

/-- The derivative in the parameter coordinate. -/
def parameterDerivative {G : Type u} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (F : E × ℝ → G) (p : E × ℝ) : E →L[ℝ] G :=
  (fderiv ℝ F p).comp (ContinuousLinearMap.inl ℝ E ℝ)

theorem hasFDerivAt_parameter_integral [ProperSpace E]
    {G : Type u} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (F : E × ℝ → G) (hF : ContDiff ℝ 1 F) (x : E) :
    HasFDerivAt (fun y => ∫ t in (0 : ℝ)..1, F (y,t))
      (∫ t in (0 : ℝ)..1, parameterDerivative F (x,t)) x := by
  have hD : Continuous (parameterDerivative F) := by
    unfold parameterDerivative
    exact ((hF.fderiv_right (m := 0) (by norm_num)).clm_comp
      contDiff_const).continuous
  obtain ⟨M,hM⟩ := compact_parameter_bound (parameterDerivative F) hD x
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le''
    (F := fun y t => F (y,t))
    (F' := fun y t => parameterDerivative F (y,t))
    (μ := volume) (a := 0) (b := 1)
    (bound := fun _ => M) (ε := 1) (by norm_num)
  · exact Eventually.of_forall fun y =>
      (hF.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact (hF.continuous.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
  · have hDc : Continuous (fun t : ℝ => parameterDerivative F (x,t)) :=
      hD.comp (continuous_const.prodMk continuous_id)
    letI : SecondCountableTopologyEither ℝ (E →L[ℝ] G) :=
      ⟨Or.inl (inferInstance : SecondCountableTopology ℝ)⟩
    exact hDc.stronglyMeasurable.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    intro y hy
    have ht' : t ∈ Ioc (0 : ℝ) 1 := by simpa [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
    exact hM y (Metric.ball_subset_closedBall hy) t ⟨ht'.1.le,ht'.2⟩
  · exact intervalIntegrable_const
  · exact Eventually.of_forall fun t y _ =>
      ((hF.differentiable_one (y,t)).hasFDerivAt.comp y
        (hasFDerivAt_prodMk_left y t))

/-- Integration in a compact dummy variable preserves arbitrary finite
orders of continuous differentiability. The induction quantifies over the
target space, allowing the derivative to take values in continuous maps. -/
theorem parameter_integral_contDiff [ProperSpace E] (n : ℕ) :
    ∀ {G : Type u} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
      (F : E × ℝ → G), ContDiff ℝ n F →
        ContDiff ℝ n (fun x => ∫ t in (0 : ℝ)..1, F (x,t)) := by
  induction n with
  | zero =>
    intro G _ _ _ F hF
    exact contDiff_zero.mpr (continuous_parameter_integral F hF.continuous)
  | succ n ih =>
    intro G _ _ _ F hF
    have h1 : ContDiff ℝ 1 F := hF.of_le (by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n)))
    have hD : ContDiff ℝ n (parameterDerivative F) := by
      unfold parameterDerivative
      exact (hF.fderiv_right (m := n) (by simp [Nat.cast_succ])).clm_comp contDiff_const
    have hIntD := ih (parameterDerivative F) hD
    have hd := fun x => hasFDerivAt_parameter_integral F h1 x
    have heq : fderiv ℝ (fun x => ∫ t in (0 : ℝ)..1, F (x,t)) =
        fun x => ∫ t in (0 : ℝ)..1, parameterDerivative F (x,t) := by
      funext x
      exact (hd x).fderiv
    rw [Nat.cast_succ,contDiff_succ_iff_fderiv]
    refine ⟨fun x => (hd x).differentiableAt, ?_, ?_⟩
    · simp
    · rw [heq]
      exact hIntD

theorem parameter_integral_smooth [ProperSpace E]
    {G : Type u} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (F : E × ℝ → G) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun x => ∫ t in (0 : ℝ)..1, F (x,t)) := by
  apply contDiff_infty.mpr
  intro n
  exact parameter_integral_contDiff n F ((contDiff_infty.mp hF) n)

/-- The integrated derivative on a segment, with no division by x-y. -/
def segmentCoefficient (f : E → ℝ) (x y : E) : E →L[ℝ] ℝ :=
  ∫ t in (0 : ℝ)..1, fderiv ℝ f (x+t • (y-x))

theorem segment_difference (f : E → ℝ) (hf : ContDiff ℝ 1 f) (x y : E) :
    f y-f x = segmentCoefficient f x y (y-x) := by
  have hline : Continuous (fun t : ℝ => x+t • (y-x)) := by fun_prop
  have hc : Continuous (fun t : ℝ => fderiv ℝ f (x+t • (y-x))) :=
    (hf.continuous_fderiv le_rfl).comp hline
  have ha : Continuous (fun t : ℝ => fderiv ℝ f (x+t • (y-x)) (y-x)) := by
    exact (hf.continuous_fderiv_apply le_rfl).comp (hline.prodMk continuous_const)
  have hd : ∀ t : ℝ, HasDerivAt (fun s : ℝ => f (x+s • (y-x)))
      (fderiv ℝ f (x+t • (y-x)) (y-x)) t := by
    intro t
    have hl : HasDerivAt (fun s : ℝ => x+s • (y-x)) (y-x) t := by
      have h := (hasDerivAt_const t x).add ((hasDerivAt_id t).smul_const (y-x))
      change HasDerivAt (fun s : ℝ => x+s • (y-x)) (0+1 • (y-x)) t at h
      simpa only [zero_add, one_smul] using h
    exact (hf.differentiable_one _).hasFDerivAt.comp_hasDerivAt t hl
  unfold segmentCoefficient
  rw [ContinuousLinearMap.intervalIntegral_apply (hc.intervalIntegrable _ _)]
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 1)
    (fun t _ => hd t) (ha.intervalIntegrable 0 1)
  simpa using h.symm

/-- The coefficient is jointly smooth even on the diagonal x=y. -/
theorem segmentCoefficient_smooth [ProperSpace E] (f : E → ℝ)
    (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun p : E × E => segmentCoefficient f p.1 p.2) := by
  have hline : ContDiff ℝ ∞
      (fun p : (E × E) × ℝ => p.1.1+p.2 • (p.1.2-p.1.1)) := by fun_prop
  have hd : ContDiff ℝ ∞ (fderiv ℝ f) :=
    hf.fderiv_right (by simp)
  exact parameter_integral_smooth _ (hd.comp hline)

/-- Smooth factorization relative to an arbitrary smooth base graph.
This is the analytic Hadamard step used after invariant-coordinate
factorization, not an assumed Schwarz theorem. -/
theorem smooth_graph_factorization [ProperSpace E]
    (f : E → ℝ) (hf : ContDiff ℝ ∞ f) (p : E → E)
    (hp : ContDiff ℝ ∞ p) :
    ∃ A : E → E →L[ℝ] ℝ, ContDiff ℝ ∞ A ∧
      ∀ x, f x-f (p x)=A x (x-p x) := by
  refine ⟨fun x => segmentCoefficient f (p x) x, ?_, ?_⟩
  · exact (segmentCoefficient_smooth f hf).comp (hp.prodMk contDiff_id)
  · intro x
    exact segment_difference f (hf.of_le (by simp)) (p x) x

/-- Differentiating an exact linear symmetry gives the equivariance law
for the derivative, without assuming invertibility of the symmetry. -/
theorem fderiv_linear_symmetry (f : E → ℝ) (hf : ContDiff ℝ 1 f)
    (T : E →L[ℝ] E) (hT : ∀ x, f (T x)=f x) (x v : E) :
    fderiv ℝ f (T x) (T v)=fderiv ℝ f x v := by
  have he : (fun y => f (T y))=f := funext hT
  have hd := (hf.differentiable_one (T x)).hasFDerivAt.comp x T.hasFDerivAt
  change HasFDerivAt (fun y => f (T y)) ((fderiv ℝ f (T x)).comp T) x at hd
  rw [he] at hd
  have h := congrArg (fun L : E →L[ℝ] ℝ => L v) hd.fderiv
  exact h.symm

theorem segmentCoefficient_equivariant (f : E → ℝ) (hf : ContDiff ℝ 1 f)
    (T : E →L[ℝ] E) (hT : ∀ x, f (T x)=f x) (x y v : E) :
    segmentCoefficient f (T x) (T y) (T v)=segmentCoefficient f x y v := by
  have hci (a b : E) : IntervalIntegrable
      (fun t : ℝ => fderiv ℝ f (a+t • (b-a))) volume 0 1 :=
    ((hf.continuous_fderiv le_rfl).comp (by fun_prop)).intervalIntegrable _ _
  unfold segmentCoefficient
  rw [ContinuousLinearMap.intervalIntegral_apply (hci _ _),
    ContinuousLinearMap.intervalIntegral_apply (hci _ _)]
  apply intervalIntegral.integral_congr
  intro t _
  change fderiv ℝ f (T x+t • (T y-T x)) (T v) =
    fderiv ℝ f (x+t • (y-x)) v
  rw [show T x+t • (T y-T x)=T (x+t • (y-x)) by
    simp]
  exact fderiv_linear_symmetry f hf T hT _ v

/-- Full equivariant graph factorization: the same canonical smooth
coefficient works simultaneously for all linear symmetries commuting
with the base graph. The vanishing condition is only on the base graph. -/
theorem equivariant_graph_factorization [ProperSpace E]
    (f : E → ℝ) (hf : ContDiff ℝ ∞ f) (p : E → E)
    (hp : ContDiff ℝ ∞ p) (hz : ∀ x, f (p x)=0) :
    ∃ A : E → E →L[ℝ] ℝ, ContDiff ℝ ∞ A ∧
      (∀ x, f x=A x (x-p x)) ∧
      (∀ T : E →L[ℝ] E, (∀ x, f (T x)=f x) →
        (∀ x, p (T x)=T (p x)) → ∀ x v, A (T x) (T v)=A x v) := by
  refine ⟨fun x => segmentCoefficient f (p x) x, ?_, ?_, ?_⟩
  · exact (segmentCoefficient_smooth f hf).comp (hp.prodMk contDiff_id)
  · intro x
    have h := segment_difference f (hf.of_le (by simp)) (p x) x
    simpa only [hz x,sub_zero] using h
  · intro T hT hP x v
    change segmentCoefficient f (p (T x)) (T x) (T v)=segmentCoefficient f (p x) x v
    rw [hP x]
    exact segmentCoefficient_equivariant f (hf.of_le (by simp)) T hT _ _ v

end ReyesMath.GC08

#print axioms ReyesMath.GC08.parameter_integral_smooth
#print axioms ReyesMath.GC08.segment_difference
#print axioms ReyesMath.GC08.smooth_graph_factorization

#print axioms ReyesMath.GC08.equivariant_graph_factorization
