import MathProofs.V18BranchBounds

/-!
# Smooth local branches of the actual 31-parameter observation map

The analytic expressions below retain every active parameter. They are used
only after proving equality with `observed` on a neighborhood of the frozen
vector; the observation map itself is not redefined.
-/

noncomputable section
namespace ReyesMath.V18Forward
open Filter
open scoped Topology
set_option maxHeartbeats 1000000

def lightSmooth (p : Params) (n : ℕ) : ℝ :=
  let x : ℝ := n
  let ratio := if n = 0 then 0 else x / (x + 1)
  let chirality := if n = 0 then (1 : ℝ) else x^2
  let base := p 0 * ratio + p 1 * topo n + p 2 * Real.log (1 + x) +
    p 3 * x^2 + p 4 * x^3 + p 5 * Real.exp (p 6 * x) + p 7 / chirality
  let preliminary := base * (1 + Real.exp (p 29 * (x - p 30)))⁻¹
  if n = 3 then preliminary * p 8 else preliminary

def bosonSmooth (p : Params) (n : ℕ) : ℝ :=
  let x : ℝ := n
  p 17 * (x / 100) ^ (p 19) + p 20 * (x / 100) ^ (p 21) +
    p 22 * (x / 100) ^ (p 23) +
    (if n = 95 ∨ n = 96 then p 24 * Real.sin (p 25 * x + p 26) else 0) +
    (if n = 123 then p 27 * (x / (x + 1)) + p 28 else 0)

def heavySmooth (p : Params) (n : ℕ) : ℝ := (1e-12 : ℝ) + bosonSmooth p n

def middleN : Fin 5 → ℕ := ![12, 19, 53, 73, 91]

def observedSmooth (p : Params) : Fin 11 → ℝ :=
  ![lightSmooth p 1, lightSmooth p 2, lightSmooth p 3,
    middleRaw p 12, middleRaw p 19, middleRaw p 53, middleRaw p 73, middleRaw p 91,
    heavySmooth p 95, heavySmooth p 96, heavySmooth p 123]

theorem continuous_lightRaw (n : ℕ) : Continuous (fun p : Params => lightRaw p n) := by
  unfold lightRaw clip
  dsimp
  split_ifs <;> fun_prop (disch := (intro p; positivity))

theorem continuous_light (n : ℕ) : Continuous (fun p : Params => light p n) :=
  (continuous_lightRaw n).max continuous_const

theorem contDiff_middleRaw (n : ℕ) : ContDiff ℝ 1 (fun p : Params => middleRaw p n) := by
  unfold middleRaw
  fun_prop

theorem continuous_heavyCorrection (n : ℕ) :
    Continuous (fun p : Params => heavyCorrection p n) := by
  unfold heavyCorrection clip
  dsimp
  split_ifs <;> fun_prop (disch := (intro p; positivity))

theorem contDiff_lightSmooth (n : ℕ) : ContDiff ℝ 1 (fun p : Params => lightSmooth p n) := by
  unfold lightSmooth
  dsimp
  split_ifs <;> fun_prop (disch := (intro p; positivity))

theorem contDiff_heavySmooth (n : ℕ) (hn : 0 < n) :
    ContDiff ℝ 1 (fun p : Params => heavySmooth p n) := by
  unfold heavySmooth bosonSmooth
  dsimp
  split_ifs <;> fun_prop (disch := (intro p; positivity))

theorem eventually_clip_eq {p : Params} {g : Params → ℝ} {lo hi : ℝ}
    (hg : ContinuousAt g p) (hlo : lo < g p) (hhi : g p < hi) :
    (fun q => clip lo hi (g q)) =ᶠ[𝓝 p] g := by
  have h := hg.eventually_mem (isOpen_Ioo.mem_nhds ⟨hlo, hhi⟩)
  filter_upwards [h] with q hq
  exact (show max lo (min hi (g q)) = g q by
    rw [min_eq_right hq.2.le, max_eq_right hq.1.le])

theorem eventually_max_left {p : Params} {g : Params → ℝ} {c : ℝ}
    (hg : ContinuousAt g p) (hc : c < g p) :
    (fun q => max (g q) c) =ᶠ[𝓝 p] g := by
  have h := hg.eventually_mem (isOpen_Ioi.mem_nhds hc)
  exact h.mono fun q hq => max_eq_left hq.le

theorem eventually_max_right {p : Params} {g : Params → ℝ} {c : ℝ}
    (hg : ContinuousAt g p) (hc : g p < c) :
    (fun q => max (g q) c) =ᶠ[𝓝 p] (fun _ => c) := by
  have h := hg.eventually_mem (isOpen_Iio.mem_nhds hc)
  exact h.mono fun q hq => max_eq_right hq.le

theorem light_eq_smooth_near_frozen (alpha : ℝ) (ha : 0 ≤ alpha) (i : Fin 3) :
    (fun q => light q (i.val + 1)) =ᶠ[𝓝 (frozen alpha 5)]
      (fun q => lightSmooth q (i.val + 1)) := by
  have hf := eventually_max_left (continuous_lightRaw (i.val + 1)).continuousAt
    (frozen_light_floor_lt alpha ha i)
  have hc := eventually_clip_eq
    ((continuous_apply (6 : Fin 31)).mul
      (continuous_const : Continuous (fun _ : Params => ((i.val + 1 : ℕ) : ℝ)))).continuousAt
    (frozen_light_exp_clip alpha i).1 (frozen_light_exp_clip alpha i).2
  filter_upwards [hf, hc] with q hq hclip
  change light q (i.val + 1) = lightSmooth q (i.val + 1)
  change light q (i.val + 1) = lightRaw q (i.val + 1) at hq
  rw [hq]
  simp only [lightRaw, lightSmooth, hclip]

theorem middle_eq_raw_near_frozen (alpha : ℝ) (i : Fin 5) :
    (fun q => middle q (middleN i)) =ᶠ[𝓝 (frozen alpha 5)]
      (fun q => middleRaw q (middleN i)) := by
  exact eventually_max_left (contDiff_middleRaw (middleN i)).continuous.continuousAt
    (V18MiddleFloor.every_middle_observable_unclipped alpha 5 i)

theorem heavyCorrection_eq_smooth_near_frozen (alpha : ℝ) (i : Fin 3) :
    (fun q => heavyCorrection q (heavyN i)) =ᶠ[𝓝 (frozen alpha 5)]
      (fun q => bosonSmooth q (heavyN i)) := by
  have hc := eventually_clip_eq
    (continuous_apply (19 : Fin 31)).continuousAt
    (frozen_boson_power_clip alpha).1 (frozen_boson_power_clip alpha).2
  filter_upwards [hc] with q hq
  change max (-10) (min 10 (q 19)) = q 19 at hq
  fin_cases i
  · change heavyCorrection q 95 = bosonSmooth q 95
    norm_num [heavyCorrection, bosonSmooth, hq, clip]
  · change heavyCorrection q 96 = bosonSmooth q 96
    norm_num [heavyCorrection, bosonSmooth, hq, clip]
  · change heavyCorrection q 123 = bosonSmooth q 123
    norm_num [heavyCorrection, bosonSmooth, hq, clip]

theorem heavy_eq_smooth_near_frozen (alpha : ℝ) (i : Fin 3) :
    (fun q => heavy q (heavyN i)) =ᶠ[𝓝 (frozen alpha 5)]
      (fun q => heavySmooth q (heavyN i)) := by
  have hi := eventually_max_right (continuous_lightRaw (heavyN i)).continuousAt
    (frozen_heavy_light_floor alpha i)
  have ho := eventually_max_left
    ((continuous_light (heavyN i)).add (continuous_heavyCorrection (heavyN i))).continuousAt
    (frozen_heavy_floor_lt alpha i)
  have hc := heavyCorrection_eq_smooth_near_frozen alpha i
  filter_upwards [hi, ho, hc] with q hqi hqo hqc
  change light q (heavyN i) = (1e-12 : ℝ) at hqi
  change heavy q (heavyN i) = light q (heavyN i) + heavyCorrection q (heavyN i) at hqo
  rw [hqo, hqi, hqc]
  rfl

theorem observed_eq_smooth_near_frozen (alpha : ℝ) (ha : 0 ≤ alpha) :
    observed =ᶠ[𝓝 (frozen alpha 5)] observedSmooth := by
  have hl := Filter.eventually_all.mpr (light_eq_smooth_near_frozen alpha ha)
  have hm := Filter.eventually_all.mpr (middle_eq_raw_near_frozen alpha)
  have hh := Filter.eventually_all.mpr (heavy_eq_smooth_near_frozen alpha)
  filter_upwards [hl, hm, hh] with q hqL hqM hqH
  ext i
  fin_cases i
  · exact hqL 0
  · exact hqL 1
  · exact hqL 2
  · exact hqM 0
  · exact hqM 1
  · exact hqM 2
  · exact hqM 3
  · exact hqM 4
  · exact hqH 0
  · exact hqH 1
  · exact hqH 2

theorem contDiff_observedSmooth : ContDiff ℝ 1 observedSmooth := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact contDiff_lightSmooth 1
  · exact contDiff_lightSmooth 2
  · exact contDiff_lightSmooth 3
  · exact contDiff_middleRaw 12
  · exact contDiff_middleRaw 19
  · exact contDiff_middleRaw 53
  · exact contDiff_middleRaw 73
  · exact contDiff_middleRaw 91
  · exact contDiff_heavySmooth 95 (by norm_num)
  · exact contDiff_heavySmooth 96 (by norm_num)
  · exact contDiff_heavySmooth 123 (by norm_num)

/-- C¹ regularity of the actual clipped observation map at each specified
frozen point. Every parameter remains free in the neighborhood. -/
theorem contDiffAt_observed_frozen (alpha : ℝ) (ha : 0 ≤ alpha) :
    ContDiffAt ℝ 1 observed (frozen alpha 5) :=
  contDiff_observedSmooth.contDiffAt.congr_of_eventuallyEq
    (observed_eq_smooth_near_frozen alpha ha)

/-- An open ambient neighborhood on which the actual map is C¹. -/
theorem observed_regular_neighborhood (alpha : ℝ) (ha : 0 ≤ alpha) :
    ∃ U : Set Params, IsOpen U ∧ frozen alpha 5 ∈ U ∧ ContDiffOn ℝ 1 observed U := by
  obtain ⟨U, hU, ho, hp⟩ := eventually_nhds_iff.mp
    (observed_eq_smooth_near_frozen alpha ha)
  exact ⟨U, ho, hp, contDiff_observedSmooth.contDiffOn.congr hU⟩

theorem observed_regular_on_alpha_interval (alpha : ℝ)
    (ha : alpha ∈ Set.Icc (5.172 : ℝ) 5.173) :
    ∃ U : Set Params, IsOpen U ∧ frozen alpha 5 ∈ U ∧ ContDiffOn ℝ 1 observed U :=
  observed_regular_neighborhood alpha (le_trans (by norm_num) ha.1)

end ReyesMath.V18Forward
