import Mathlib

/-!
# E68: radial integration on `ℝⁿ`

Polar coordinates for radial functions, from Mathlib's measure-preserving identification
`ℝⁿ ∖ {0} ≅ Sⁿ⁻¹ × (0, ∞)` (`Measure.measurePreserving_homeomorphUnitSphereProd`) and the
radial integral formula `integral_fun_norm_addHaar`.

* `integrable_fun_norm_of_integrableOn`: `f(|x|)` is integrable on `ℝⁿ` as soon as
  `y^{n-1} f(y)` is integrable on `(0, ∞)`.
* `integrable_indicator_closedBall_rpow`: `|x|^t 1_{|x| ≤ R}` is integrable for `t > -n`.
* `setIntegral_ball_rpow`: `∫_{B_R} |x|^t dx = n ω_n R^{n+t} / (n+t)` for `t > -n`, where
  `ω_n = |B_1|`; `sphereArea_eq`: `n ω_n = σ_{n-1}` is the surface measure of the unit sphere.
-/

noncomputable section

open MeasureTheory Set Metric Filter

namespace ReyesMath.E68

section General

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Radial integrability.** If `y ↦ y^{n-1} f(y)` is integrable on `(0, ∞)`, then `x ↦ f(|x|)`
is integrable for every additive Haar measure. -/
theorem integrable_fun_norm_of_integrableOn (μ : Measure E) [μ.IsAddHaarMeasure] {f : ℝ → F}
    (hf : IntegrableOn (fun y => y ^ (Module.finrank ℝ E - 1) • f y) (Ioi 0)) :
    Integrable (fun x => f ‖x‖) μ := by
  rw [← MeasureTheory.restrict_compl_singleton (μ := μ) (0 : E)]
  rw [← IntegrableOn, integrableOn_iff_comap_subtypeVal (measurableSet_singleton _).compl]
  have hmp := μ.measurePreserving_homeomorphUnitSphereProd
  have key : Integrable (fun p : sphere (0 : E) 1 × Ioi (0 : ℝ) => f p.2.1)
      (μ.toSphere.prod (Measure.volumeIoiPow (Module.finrank ℝ E - 1))) := by
    have h1 : Integrable (fun r : Ioi (0 : ℝ) => f r.1)
        (Measure.volumeIoiPow (Module.finrank ℝ E - 1)) := by
      rw [Measure.volumeIoiPow, integrable_withDensity_iff_integrable_smul']
      · have h2 := (integrableOn_iff_comap_subtypeVal measurableSet_Ioi).1 hf
        refine h2.congr (Filter.Eventually.of_forall fun x => ?_)
        simp only [Function.comp_apply]
        rw [ENNReal.toReal_ofReal (pow_nonneg x.2.out.le _)]
      · exact (measurable_subtype_coe.pow_const _).ennreal_ofReal
      · exact Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
    exact h1.comp_snd _
  have := (hmp.integrable_comp_emb (Homeomorph.measurableEmbedding _)).2 key
  convert this using 1

omit [Nontrivial E] in
/-- `σ_{n-1} = n ω_n`: the surface measure of the unit sphere. -/
theorem sphereArea_eq (μ : Measure E) [μ.IsAddHaarMeasure] :
    μ.toSphere.real univ = Module.finrank ℝ E * μ.real (ball 0 1) :=
  μ.toSphere_real_apply_univ

end General

variable {n : ℕ}

theorem finrank_euclidean (n : ℕ) : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by
  simp

/-- `|x|^t 1_{|x| ≤ R}` is integrable on `ℝⁿ` for `t > -n`. -/
theorem integrable_indicator_closedBall_rpow (hn : 1 ≤ n) {t : ℝ} (ht : -(n : ℝ) < t) (R : ℝ) :
    Integrable ((closedBall (0 : EuclideanSpace ℝ (Fin n)) R).indicator fun x => ‖x‖ ^ t)
      volume := by
  haveI : Nontrivial (EuclideanSpace ℝ (Fin n)) := by
    have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    infer_instance
  have hrad : ((closedBall (0 : EuclideanSpace ℝ (Fin n)) R).indicator fun x => ‖x‖ ^ t) =
      fun x => (Iic R).indicator (fun y : ℝ => y ^ t) ‖x‖ := by
    funext x
    by_cases hx : ‖x‖ ≤ R
    · rw [indicator_of_mem (mem_closedBall_zero_iff.2 hx), indicator_of_mem (mem_Iic.2 hx)]
    · rw [indicator_of_notMem (fun h => hx (mem_closedBall_zero_iff.1 h)),
        indicator_of_notMem (fun h => hx (mem_Iic.1 h))]
  rw [hrad]
  apply integrable_fun_norm_of_integrableOn
  rw [finrank_euclidean]
  have hg : IntegrableOn (fun y : ℝ => y ^ (n - 1) • (Iic R).indicator (fun y : ℝ => y ^ t) y)
      (Ioc 0 R) := by
    rcases le_or_gt R 0 with hR | hR
    · rw [Ioc_eq_empty (not_lt.2 hR)]
      exact integrableOn_empty
    · have h1 := (intervalIntegrable_iff_integrableOn_Ioc_of_le hR.le).1
        (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := R) (r := (n : ℝ) - 1 + t)
          (by linarith))
      refine h1.congr_fun (fun y hy => ?_) measurableSet_Ioc
      rw [indicator_of_mem (mem_Iic.2 hy.2), smul_eq_mul, ← Real.rpow_natCast,
        ← Real.rpow_add hy.1, Nat.cast_sub hn, Nat.cast_one]
  exact hg.of_forall_diff_eq_zero measurableSet_Ioi fun y hy => by
    rw [indicator_of_notMem, smul_zero]
    exact fun h => hy.2 ⟨hy.1, mem_Iic.1 h⟩

theorem nontrivial_euclidean (hn : 1 ≤ n) : Nontrivial (EuclideanSpace ℝ (Fin n)) := by
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  infer_instance

/-- **Exact radial integral.** For `t > -n` and `R > 0`,
`∫_{B_R} |x|^t dx = n ω_n R^{n+t} / (n+t)`, with `ω_n = |B_1|`. -/
theorem setIntegral_ball_rpow (hn : 1 ≤ n) {t : ℝ} (ht : -(n : ℝ) < t) {R : ℝ} (hR : 0 < R) :
    (∫ x in ball (0 : EuclideanSpace ℝ (Fin n)) R, ‖x‖ ^ t) =
      n * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1) *
        (R ^ ((n : ℝ) + t) / ((n : ℝ) + t)) := by
  haveI := nontrivial_euclidean hn
  have hrad : (∫ x in ball (0 : EuclideanSpace ℝ (Fin n)) R, ‖x‖ ^ t) =
      ∫ x : EuclideanSpace ℝ (Fin n), (Iio R).indicator (fun y : ℝ => y ^ t) ‖x‖ := by
    rw [← integral_indicator measurableSet_ball]
    congr 1
    funext x
    by_cases hx : ‖x‖ < R
    · rw [indicator_of_mem (mem_ball_zero_iff.2 hx), indicator_of_mem (mem_Iio.2 hx)]
    · rw [indicator_of_notMem (fun h => hx (mem_ball_zero_iff.1 h)),
        indicator_of_notMem (fun h => hx (mem_Iio.1 h))]
  rw [hrad, integral_fun_norm_addHaar, finrank_euclidean]
  have h1 : (∫ y in Ioi (0 : ℝ), y ^ (n - 1) • (Iio R).indicator (fun y : ℝ => y ^ t) y) =
      ∫ y in (0 : ℝ)..R, y ^ ((n : ℝ) - 1 + t) := by
    have heq : EqOn (fun y : ℝ => y ^ (n - 1) • (Iio R).indicator (fun y : ℝ => y ^ t) y)
        ((Iio R).indicator fun y : ℝ => y ^ ((n : ℝ) - 1 + t)) (Ioi 0) := by
      intro y hy
      dsimp only
      by_cases hyR : y < R
      · rw [indicator_of_mem (mem_Iio.2 hyR), indicator_of_mem (mem_Iio.2 hyR), smul_eq_mul,
          ← Real.rpow_natCast, ← Real.rpow_add hy, Nat.cast_sub hn, Nat.cast_one]
      · rw [indicator_of_notMem (fun h => hyR (mem_Iio.1 h)),
          indicator_of_notMem (fun h => hyR (mem_Iio.1 h)), smul_zero]
    rw [setIntegral_congr_fun measurableSet_Ioi heq, integral_indicator measurableSet_Iio,
      Measure.restrict_restrict measurableSet_Iio, Iio_inter_Ioi,
      intervalIntegral.integral_of_le hR.le, integral_Ioc_eq_integral_Ioo]
  rw [h1, integral_rpow (Or.inl (by linarith))]
  have hpos : 0 < (n : ℝ) - 1 + t + 1 := by linarith
  rw [Real.zero_rpow hpos.ne', show (n : ℝ) - 1 + t + 1 = (n : ℝ) + t by ring, nsmul_eq_mul,
    smul_eq_mul]
  ring

end ReyesMath.E68
