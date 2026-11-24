import MathProofs.GC26GlobalIdentifiability

/-! Exact historical optimizer rectangle: global singleton fibers, isolated
fiber points, and relative neighborhood injectivity are distinguished. -/

noncomputable section
namespace ReyesMath.V18Forward
open Filter
open scoped Topology

set_option maxHeartbeats 3000000

def historicalRectangle : Set (ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ p.1 ≤ 50 ∧ 0 ≤ p.2 ∧ p.2 ≤ 5}

def historicalObserved (p : ℝ × ℝ) : Fin 11 → ℝ :=
  observed (frozen p.1 p.2)

def historicalT (p : ℝ × ℝ) : ℝ := p.1 * (1 - p.2)

def HistoricalSingleton (p : ℝ × ℝ) : Prop :=
  ∀ q ∈ historicalRectangle, historicalObserved q = historicalObserved p → q = p

def HistoricalIsolated (p : ℝ × ℝ) : Prop :=
  ∃ U : Set (ℝ × ℝ), U ∈ 𝓝 p ∧
    ∀ q ∈ U ∩ historicalRectangle, historicalObserved q = historicalObserved p → q = p

def HistoricalNeighborhoodInjective (p : ℝ × ℝ) : Prop :=
  ∃ U : Set (ℝ × ℝ), IsOpen U ∧ p ∈ U ∧
    Set.InjOn historicalObserved (U ∩ historicalRectangle)

def HistoricalGood (p : ℝ × ℝ) : Prop :=
  0 < p.1 ∧ p.1 + historicalT p < historicalThreshold 2

def historicalExceptional : ℝ × ℝ :=
  (50, 2 - historicalThreshold 2 / 50)

local notation "h₁" => historicalThreshold 1
local notation "h₂" => historicalThreshold 2
local notation "h₃" => historicalThreshold 3
local notation "c" => (1e-12 : ℝ)

private def row (p : ℝ × ℝ) (n : ℕ) : ℝ :=
  light (frozen p.1 p.2) n

private theorem numerator_gt (n : Fin 3) :
    (2e-12 : ℝ) < historicalNumerator (n.val + 1) := by
  obtain ⟨h1, _, h2, _, _, _⟩ := historical_numerator_bounds
  fin_cases n
  · norm_num at h1 ⊢ <;> linarith
  · norm_num at h2 ⊢ <;> linarith
  · have h := frozenLightBase_three
    norm_num [historicalNumerator] <;> linarith

private theorem active1 (p : ℝ × ℝ) : c < row p 1 ↔ historicalT p < h₁ := by
  simpa [row, historicalT] using
    historical_light_active_iff p.1 p.2 1 (numerator_gt 0)

private theorem active2 (p : ℝ × ℝ) : c < row p 2 ↔ p.1 + historicalT p < h₂ := by
  have h := historical_light_active_iff p.1 p.2 2 (numerator_gt 1)
  simp only [Nat.cast_ofNat] at h
  rw [show p.1 * (2 - p.2) = p.1 + historicalT p by unfold historicalT; ring] at h
  simpa [row] using h

private theorem active3 (p : ℝ × ℝ) : c < row p 3 ↔ 2 * p.1 + historicalT p < h₃ := by
  have h := historical_light_active_iff p.1 p.2 3 (numerator_gt 2)
  simp only [Nat.cast_ofNat] at h
  rw [show p.1 * (3 - p.2) = 2 * p.1 + historicalT p by unfold historicalT; ring] at h
  simpa [row] using h

private theorem row_floor (p : ℝ × ℝ) (n : ℕ) : c ≤ row p n :=
  le_max_right _ _

private theorem floor1 (p : ℝ × ℝ) : row p 1 = c ↔ h₁ ≤ historicalT p := by
  have h := active1 p
  constructor
  · intro he
    by_contra! ht
    have := h.mpr ht
    linarith
  · intro ht
    apply le_antisymm _ (row_floor p 1)
    by_contra! hh
    have := h.mp hh
    linarith

private theorem floor2 (p : ℝ × ℝ) : row p 2 = c ↔ h₂ ≤ p.1 + historicalT p := by
  have h := active2 p
  constructor
  · intro he
    by_contra! ht
    have := h.mpr ht
    linarith
  · intro ht
    apply le_antisymm _ (row_floor p 2)
    by_contra! hh
    have := h.mp hh
    linarith

private theorem floor3 (p : ℝ × ℝ) : row p 3 = c ↔ h₃ ≤ 2 * p.1 + historicalT p := by
  have h := active3 p
  constructor
  · intro he
    by_contra! ht
    have := h.mpr ht
    linarith
  · intro ht
    apply le_antisymm _ (row_floor p 3)
    by_contra! hh
    have := h.mp hh
    linarith

private theorem t_bounds {p : ℝ × ℝ} (hp : p ∈ historicalRectangle) :
    -4 * p.1 ≤ historicalT p ∧ historicalT p ≤ p.1 := by
  rcases hp with ⟨ha, _, he, he'⟩
  have h0 := mul_nonneg ha he
  have h5 := mul_nonneg ha (sub_nonneg.mpr he')
  unfold historicalT
  constructor <;> nlinarith only [h0, h5]

private theorem active_prefix_rect {p : ℝ × ℝ} (hp : p ∈ historicalRectangle) :
    (h₁ ≤ historicalT p → h₂ ≤ p.1 + historicalT p) ∧
    (h₂ ≤ p.1 + historicalT p → h₃ ≤ 2 * p.1 + historicalT p) := by
  obtain ⟨_, h31, h12, h20, h40⟩ := historical_threshold_bounds
  exact historical_active_prefix _ _ _ _ _ hp.1 (t_bounds hp).2 (by linarith) (by linarith)

private theorem eq_rows (p q : ℝ × ℝ) :
    historicalObserved p = historicalObserved q ↔
      row p 1 = row q 1 ∧ row p 2 = row q 2 ∧ row p 3 = row q 3 := by
  change observed (frozen p.1 p.2) = observed (frozen q.1 q.2) ↔ _
  rw [historical_equal_iff_light]
  constructor
  · intro h
    exact ⟨h 0, h 1, h 2⟩
  · rintro ⟨h1, h2, h3⟩ i
    fin_cases i
    · exact h1
    · exact h2
    · exact h3

private theorem row1_same {p q : ℝ × ℝ} (ht : historicalT p = historicalT q) :
    row p 1 = row q 1 := by
  simp only [row, light, historical_lightRaw, Nat.cast_one]
  change max (historicalNumerator 1 * (1 + Real.exp (historicalT p))⁻¹) c =
    max (historicalNumerator 1 * (1 + Real.exp (historicalT q))⁻¹) c
  rw [ht]

private theorem t_of_row1 {p q : ℝ × ℝ} (ha : historicalT p < h₁)
    (he : row p 1 = row q 1) : historicalT p = historicalT q := by
  have hx := (active1 p).mpr ha
  simp only [row, light, historical_lightRaw, Nat.cast_one] at hx he
  exact logistic_floor_logit_eq _ _ _ hx he

private theorem coords_eq {p q : ℝ × ℝ} (ha : 0 < p.1)
    (hab : p.1 = q.1) (ht : historicalT p = historicalT q) : p = q := by
  apply Prod.ext hab
  unfold historicalT at ht
  rw [← hab] at ht
  have hm : p.1 * (p.2 - q.2) = 0 := by nlinarith only [ht]
  rcases mul_eq_zero.mp hm with hz | hz
  · linarith
  · linarith

/-- Exact one-active-row fiber; includes threshold equality. -/
theorem historical_one_active_fiber_iff {p q : ℝ × ℝ}
    (hp : p ∈ historicalRectangle) (hq : q ∈ historicalRectangle)
    (ht : historicalT p < h₁) (h2 : h₂ ≤ p.1 + historicalT p) :
    historicalObserved q = historicalObserved p ↔
      historicalT q = historicalT p ∧ h₂ ≤ q.1 + historicalT q := by
  constructor
  · intro he
    obtain ⟨e1, e2, _⟩ := (eq_rows q p).mp he
    have ht' := (t_of_row1 ht e1.symm).symm
    have hf := (floor2 p).mpr h2
    exact ⟨ht', (floor2 q).mp (e2.trans hf)⟩
  · rintro ⟨ht', h2'⟩
    apply (eq_rows q p).mpr
    exact ⟨row1_same ht',
      ((floor2 q).mpr h2').trans ((floor2 p).mpr h2).symm,
      ((floor3 q).mpr ((active_prefix_rect hq).2 h2')).trans
        ((floor3 p).mpr ((active_prefix_rect hp).2 h2)).symm⟩

/-- Exact all-floor fiber, including the boundary of the plateau. -/
theorem historical_plateau_fiber_iff {p q : ℝ × ℝ}
    (hp : p ∈ historicalRectangle) (hq : q ∈ historicalRectangle)
    (ht : h₁ ≤ historicalT p) :
    historicalObserved q = historicalObserved p ↔ h₁ ≤ historicalT q := by
  constructor
  · intro he
    exact (floor1 q).mp (((eq_rows q p).mp he).1.trans ((floor1 p).mpr ht))
  · intro ht'
    have h2 := (active_prefix_rect hp).1 ht
    have h2' := (active_prefix_rect hq).1 ht'
    apply (eq_rows q p).mpr
    exact ⟨((floor1 q).mpr ht').trans ((floor1 p).mpr ht).symm,
      ((floor2 q).mpr h2').trans ((floor2 p).mpr h2).symm,
      ((floor3 q).mpr ((active_prefix_rect hq).2 h2')).trans
        ((floor3 p).mpr ((active_prefix_rect hp).2 h2)).symm⟩

theorem historical_good_singleton {p : ℝ × ℝ} (hp : p ∈ historicalRectangle)
    (hg : HistoricalGood p) : HistoricalSingleton p := by
  intro q _ he
  have ht : historicalT p < h₁ := by
    by_contra! hh
    have := (active_prefix_rect hp).1 hh
    linarith [hg.2]
  have h0 : c < observed (frozen p.1 p.2) 0 := (active1 p).mpr ht
  have h1 : c < observed (frozen p.1 p.2) 1 := (active2 p).mpr hg.2
  obtain ⟨ha, hb⟩ := historical_two_active_unique _ _ _ _ hg.1 h0 h1 he.symm
  exact (Prod.ext ha hb).symm

theorem historical_zero_fiber_iff {p q : ℝ × ℝ}
    (hp : p ∈ historicalRectangle) (hq : q ∈ historicalRectangle) (hz : p.1 = 0) :
    historicalObserved q = historicalObserved p ↔ q.1 = 0 := by
  constructor
  · intro he
    by_contra hn
    have hqpos : 0 < q.1 := lt_of_le_of_ne hq.1 (Ne.symm hn)
    obtain ⟨h3p, h31, h12, _, _⟩ := historical_threshold_bounds
    have ht : historicalT p = 0 := by simp [historicalT, hz]
    have h0 : c < row p 1 := (active1 p).mpr (by linarith)
    have h1 : c < row p 2 := (active2 p).mpr (by linarith)
    obtain ⟨e0, e1, _⟩ := (eq_rows q p).mp he
    have h0' : c < observed (frozen q.1 q.2) 0 := by
      change c < row q 1
      rw [e0]
      exact h0
    have h1' : c < observed (frozen q.1 q.2) 1 := by
      change c < row q 2
      rw [e1]
      exact h1
    have hh := (historical_two_active_unique _ _ _ _ hqpos h0' h1' he).1
    exact hn (hh.trans hz)
  · intro hqz
    simpa only [historicalObserved, hz, hqz] using historical_zero_alpha q.2 p.2

private def lift (a t : ℝ) : ℝ × ℝ := (a, 1 - t / a)

private theorem lift_t {a t : ℝ} (ha : 0 < a) : historicalT (lift a t) = t := by
  change a * (1 - (1 - t / a)) = t
  field_simp [ha.ne'] <;> ring

private theorem lift_mem {a t : ℝ} (ha : 0 < a) (ha50 : a ≤ 50)
    (htl : -4 * a ≤ t) (htu : t ≤ a) : lift a t ∈ historicalRectangle := by
  change 0 ≤ a ∧ a ≤ 50 ∧ 0 ≤ 1 - t / a ∧ 1 - t / a ≤ 5
  have h1 : t / a ≤ 1 := (div_le_iff₀ ha).mpr (by linarith)
  have h2 : -4 ≤ t / a := (le_div_iff₀ ha).mpr htl
  exact ⟨ha.le, ha50, by linarith, by linarith⟩

private def lower (t : ℝ) : ℝ := max 0 (max t (max (-t / 4) (h₂ - t)))

private theorem lower_le {p : ℝ × ℝ} (hp : p ∈ historicalRectangle)
    (hh : h₂ ≤ p.1 + historicalT p) : lower (historicalT p) ≤ p.1 := by
  obtain ⟨htl, htu⟩ := t_bounds hp
  simp only [lower, max_le_iff]
  exact ⟨hp.1, htu, by linarith, by linarith⟩

private theorem lower_pos {t : ℝ} (ht : t < h₁) : 0 < lower t := by
  obtain ⟨_, _, h12, _, _⟩ := historical_threshold_bounds
  have hh : 0 < h₂ - t := by linarith
  exact lt_of_lt_of_le hh (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))

private theorem lift_one_active {p : ℝ × ℝ} (hp : p ∈ historicalRectangle)
    (ht : historicalT p < h₁) (hh : h₂ ≤ p.1 + historicalT p)
    {a : ℝ} (hl : lower (historicalT p) ≤ a) (hu : a ≤ 50) :
    lift a (historicalT p) ∈ historicalRectangle ∧
      historicalObserved (lift a (historicalT p)) = historicalObserved p := by
  have ha : 0 < a := lt_of_lt_of_le (lower_pos ht) hl
  have hbounds := hl
  simp only [lower, max_le_iff] at hbounds
  have hq := lift_mem ha hu (by linarith [hbounds.2.2.1]) hbounds.2.1
  refine ⟨hq, (historical_one_active_fiber_iff hp hq ht hh).mpr ?_⟩
  change historicalT (lift a (historicalT p)) = historicalT p ∧
    h₂ ≤ a + historicalT (lift a (historicalT p))
  rw [lift_t ha]
  exact ⟨rfl, by linarith [hbounds.2.2.2]⟩

private theorem lower_endpoint {p : ℝ × ℝ} (hp : p ∈ historicalRectangle)
    (ht : historicalT p < h₁) (hh : h₂ ≤ p.1 + historicalT p) :
    lower (historicalT p) = 50 ↔ historicalT p = h₂ - 50 := by
  obtain ⟨h3, h31, h12, _, h40⟩ := historical_threshold_bounds
  exact historical_exceptional_endpoint _ _ _ ht h12 h40 (by linarith)
    (by linarith [hp.2.1])

/-- The only one-active singleton is the exceptional boundary point. -/
theorem historical_one_active_singleton_iff {p : ℝ × ℝ}
    (hp : p ∈ historicalRectangle) (ht : historicalT p < h₁)
    (hh : h₂ ≤ p.1 + historicalT p) :
    HistoricalSingleton p ↔ p = historicalExceptional := by
  constructor
  · intro hs
    have hl := lower_le hp hh
    obtain ⟨h50m, h50e⟩ := lift_one_active hp ht hh (le_trans hl hp.2.1) le_rfl
    obtain ⟨hlm, hle⟩ := lift_one_active hp ht hh le_rfl (le_trans hl hp.2.1)
    have ha : p.1 = 50 := (congrArg Prod.fst (hs _ h50m h50e)).symm
    have hlow : lower (historicalT p) = p.1 := congrArg Prod.fst (hs _ hlm hle)
    have hte := (lower_endpoint hp ht hh).mp (hlow.trans ha)
    apply Prod.ext ha
    change p.2 = 2 - h₂ / 50
    unfold historicalT at hte
    rw [ha] at hte
    linarith
  · intro he q hq hobs
    have ⟨htq, hq2⟩ := (historical_one_active_fiber_iff hp hq ht hh).mp hobs
    have hap : p.1 = 50 := congrArg Prod.fst he
    have htp : historicalT p = h₂ - 50 := by
      rw [he]
      unfold historicalT historicalExceptional
      norm_num <;> ring
    have haq : q.1 = 50 := by linarith [hq.2.1]
    exact coords_eq (show 0 < q.1 by linarith) (haq.trans hap.symm) htq

theorem historical_exceptional_mem : historicalExceptional ∈ historicalRectangle := by
  obtain ⟨h3, h31, h12, _, h40⟩ := historical_threshold_bounds
  change 0 ≤ (50 : ℝ) ∧ 50 ≤ (50 : ℝ) ∧ 0 ≤ 2 - h₂ / 50 ∧ 2 - h₂ / 50 ≤ 5
  constructor
  · norm_num
  · exact ⟨le_rfl, by linarith, by linarith⟩

private theorem exceptional_t : historicalT historicalExceptional = h₂ - 50 := by
  unfold historicalT historicalExceptional
  norm_num <;> ring

theorem historical_exceptional_singleton : HistoricalSingleton historicalExceptional := by
  obtain ⟨h3, h31, h12, h20, h40⟩ := historical_threshold_bounds
  apply (historical_one_active_singleton_iff historical_exceptional_mem ?_ ?_).mpr rfl
  · rw [exceptional_t]
    linarith
  · change h₂ ≤ 50 + historicalT historicalExceptional
    rw [exceptional_t]
    linarith

/-! The following segment argument is in the original Euclidean rectangle,
not a rank surrogate. The lift is continuous at the starting point whenever
its alpha coordinate is positive. -/

private def blend (x y s : ℝ) : ℝ := (1-s)*x + s*y

private theorem blend_le {x y u v s : ℝ} (hx : x ≤ u) (hy : y ≤ v)
    (hs : 0 ≤ s) (hs' : s ≤ 1) : blend x y s ≤ blend u v s :=
  add_le_add (mul_le_mul_of_nonneg_left hx (sub_nonneg.mpr hs'))
    (mul_le_mul_of_nonneg_left hy hs)

private theorem blend_self (x s : ℝ) : blend x x s = x := by unfold blend; ring

private def segment (p q : ℝ × ℝ) (s : ℝ) : ℝ × ℝ :=
  lift (blend p.1 q.1 s) (blend (historicalT p) (historicalT q) s)

private theorem blend_pos {x y s : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hs : 0 ≤ s) (hs' : s < 1) : 0 < blend x y s := by
  unfold blend
  exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr hs') hx) (mul_nonneg hs hy.le)

private theorem segment_mem {p q : ℝ × ℝ}
    (hp : p ∈ historicalRectangle) (hq : q ∈ historicalRectangle)
    (ha : 0 < p.1) (hb : 0 < q.1) {s : ℝ} (hs : 0 ≤ s) (hs' : s < 1) :
    segment p q s ∈ historicalRectangle := by
  have hpos := blend_pos ha hb hs hs'
  have h50 := blend_le hp.2.1 hq.2.1 hs hs'.le
  rw [blend_self] at h50
  obtain ⟨pl, pu⟩ := t_bounds hp
  obtain ⟨ql, qu⟩ := t_bounds hq
  have hl := blend_le pl ql hs hs'.le
  have hu := blend_le pu qu hs hs'.le
  apply lift_mem hpos h50 _ hu
  unfold blend at hl ⊢
  linarith

private theorem segment_t {p q : ℝ × ℝ} (ha : 0 < p.1) (hb : 0 < q.1)
    {s : ℝ} (hs : 0 ≤ s) (hs' : s < 1) :
    historicalT (segment p q s) = blend (historicalT p) (historicalT q) s :=
  lift_t (blend_pos ha hb hs hs')

private theorem segment_zero {p q : ℝ × ℝ} (ha : 0 < p.1) : segment p q 0 = p := by
  have he : (segment p q 0).1 = p.1 := by simp [segment, lift, blend]
  apply coords_eq (by rwa [he]) he
  unfold segment
  rw [lift_t (by simpa [blend] using ha)]
  simp [blend]

private theorem segment_continuousAt {p q : ℝ × ℝ} (ha : 0 < p.1) :
    ContinuousAt (segment p q) 0 := by
  have hA : Continuous (fun s : ℝ => blend p.1 q.1 s) := by unfold blend; fun_prop
  have hT : Continuous (fun s : ℝ => blend (historicalT p) (historicalT q) s) := by
    unfold blend
    fun_prop
  have hn : blend p.1 q.1 0 ≠ 0 := by simpa [blend] using ha.ne'
  change ContinuousAt (fun s : ℝ => (blend p.1 q.1 s,
    1 - blend (historicalT p) (historicalT q) s / blend p.1 q.1 s)) 0
  exact hA.continuousAt.prodMk
    (continuousAt_const.sub (hT.continuousAt.div hA.continuousAt hn))

private theorem segment_ne {p q : ℝ × ℝ} (ha : 0 < p.1) (hb : 0 < q.1)
    (hne : q ≠ p) {s : ℝ} (hs : 0 < s) (hs' : s < 1) : segment p q s ≠ p := by
  intro he
  have ea := congrArg Prod.fst he
  change blend p.1 q.1 s = p.1 at ea
  have et := congrArg historicalT he
  rw [segment_t ha hb hs.le hs'] at et
  have em : s * (q.1-p.1) = 0 := by unfold blend at ea; nlinarith only [ea]
  have en : s * (historicalT q-historicalT p) = 0 := by
    unfold blend at et
    nlinarith only [et]
  apply hne
  exact coords_eq hb (by
    rcases mul_eq_zero.mp em with h | h
    · linarith
    · linarith) (by
    rcases mul_eq_zero.mp en with h | h
    · linarith
    · linarith)

private theorem path_hits {X : Type*} [TopologicalSpace X] {p : X}
    (f : ℝ → X) (hf : ContinuousAt f 0) (h0 : f 0 = p)
    {U : Set X} (hU : U ∈ 𝓝 p) :
    ∃ s : ℝ, 0 < s ∧ s < 1 ∧ f s ∈ U := by
  have hu' : U ∈ 𝓝 (f 0) := by rw [h0]; exact hU
  have hpre : f ⁻¹' U ∈ 𝓝 (0 : ℝ) := hf hu'
  obtain ⟨d, hd, hdU⟩ := Metric.mem_nhds_iff.mp hpre
  let s := min (d / 2) (1 / 2 : ℝ)
  have hs : 0 < s := lt_min (by linarith) (by norm_num)
  have hsd : s < d := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hs1 : s < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  refine ⟨s, hs, hs1, hdU ?_⟩
  change dist s 0 < d
  rwa [Real.dist_eq, sub_zero, abs_of_pos hs]

private theorem one_active_segment_eq {p q : ℝ × ℝ}
    (hp : p ∈ historicalRectangle) (hq : q ∈ historicalRectangle)
    (ha : 0 < p.1) (hb : 0 < q.1)
    (ht : historicalT p < h₁) (hh : h₂ ≤ p.1 + historicalT p)
    (he : historicalObserved q = historicalObserved p) {s : ℝ} (hs : 0 ≤ s) (hs' : s < 1) :
    historicalObserved (segment p q s) = historicalObserved p := by
  obtain ⟨htq, hq2⟩ := (historical_one_active_fiber_iff hp hq ht hh).mp he
  have hmem := segment_mem hp hq ha hb hs hs'
  apply (historical_one_active_fiber_iff hp hmem ht hh).mpr
  have hst := segment_t ha hb hs hs'
  rw [htq, blend_self] at hst
  refine ⟨hst, ?_⟩
  change h₂ ≤ blend p.1 q.1 s + historicalT (segment p q s)
  rw [hst]
  have hq2' : h₂ - historicalT p ≤ q.1 := by linarith
  have h := blend_le (show h₂ - historicalT p ≤ p.1 by linarith) hq2' hs hs'.le
  rw [blend_self] at h
  linarith

private theorem plateau_segment_eq {p q : ℝ × ℝ}
    (hp : p ∈ historicalRectangle) (hq : q ∈ historicalRectangle)
    (ha : 0 < p.1) (hb : 0 < q.1)
    (ht : h₁ ≤ historicalT p) (htq : h₁ ≤ historicalT q)
    {s : ℝ} (hs : 0 ≤ s) (hs' : s < 1) :
    historicalObserved (segment p q s) = historicalObserved p := by
  apply (historical_plateau_fiber_iff hp (segment_mem hp hq ha hb hs hs') ht).mpr
  rw [segment_t ha hb hs hs']
  have h := blend_le ht htq hs hs'.le
  rwa [blend_self] at h

private theorem zero_nonisolated {p : ℝ × ℝ} (hp : p ∈ historicalRectangle)
    (hz : p.1 = 0) : ¬ HistoricalIsolated p := by
  rintro ⟨U, hU, hi⟩
  let e : ℝ := if p.2 = 0 then 5 else 0
  have he : 0 ≤ e ∧ e ≤ 5 := by unfold e; split_ifs <;> norm_num
  have hne : e ≠ p.2 := by
    unfold e
    split_ifs with hz'
    · rw [hz']
      norm_num
    · exact Ne.symm hz'
  let f : ℝ → ℝ × ℝ := fun s => (0, blend p.2 e s)
  have hc : Continuous f := by unfold f blend; fun_prop
  have h0 : f 0 = p := by apply Prod.ext <;> simp [f, blend, hz]
  obtain ⟨s, hs, hs', hu⟩ := path_hits f hc.continuousAt h0 hU
  have hh := blend_le hp.2.2.2 he.2 hs.le hs'.le
  -- The lower bound uses the blend of two zeros.
  have hl' := blend_le hp.2.2.1 he.1 hs.le hs'.le
  rw [blend_self] at hl' hh
  have hm : f s ∈ historicalRectangle := by
    change 0 ≤ (0 : ℝ) ∧ 0 ≤ (50 : ℝ) ∧ 0 ≤ blend p.2 e s ∧ blend p.2 e s ≤ 5
    exact ⟨le_rfl, by norm_num, hl', hh⟩
  have heq := (historical_zero_fiber_iff hp hm hz).mpr rfl
  have hsame := congrArg Prod.snd (hi _ ⟨hu, hm⟩ heq)
  change blend p.2 e s = p.2 at hsame
  have hm0 : s * (e - p.2) = 0 := by unfold blend at hsame; nlinarith only [hsame]
  rcases mul_eq_zero.mp hm0 with h | h
  · linarith
  · exact hne (by linarith)

private theorem one_active_nonisolated {p : ℝ × ℝ} (hp : p ∈ historicalRectangle)
    (ht : historicalT p < h₁) (hh : h₂ ≤ p.1 + historicalT p)
    (hne : p ≠ historicalExceptional) : ¬ HistoricalIsolated p := by
  have hns : ¬ HistoricalSingleton p := fun h =>
    hne ((historical_one_active_singleton_iff hp ht hh).mp h)
  unfold HistoricalSingleton at hns
  push_neg at hns
  obtain ⟨q, hq, he, hqp⟩ := hns
  obtain ⟨_, _, h12, _, _⟩ := historical_threshold_bounds
  have ha : 0 < p.1 := by linarith
  have hq2 := ((historical_one_active_fiber_iff hp hq ht hh).mp he)
  have hb : 0 < q.1 := by linarith [hq2.1, hq2.2]
  rintro ⟨U, hU, hi⟩
  obtain ⟨s, hs, hs', hu⟩ := path_hits (segment p q)
    (segment_continuousAt ha) (segment_zero ha) hU
  have hm := segment_mem hp hq ha hb hs.le hs'
  exact segment_ne ha hb hqp hs hs'
    (hi _ ⟨hu, hm⟩ (one_active_segment_eq hp hq ha hb ht hh he hs.le hs'))

private theorem plateau_nonisolated {p : ℝ × ℝ} (hp : p ∈ historicalRectangle)
    (ht : h₁ ≤ historicalT p) : ¬ HistoricalIsolated p := by
  obtain ⟨_, _, h12, h20, h40⟩ := historical_threshold_bounds
  have ha : 0 < p.1 := by linarith [(t_bounds hp).2]
  let q : ℝ × ℝ := if p = (50, 0) then (49, 0) else (50, 0)
  have hq : q ∈ historicalRectangle := by unfold q historicalRectangle; split_ifs <;> norm_num
  have hb : 0 < q.1 := by unfold q; split_ifs <;> norm_num
  have htq : h₁ ≤ historicalT q := by
    unfold q
    split_ifs <;> norm_num [historicalT] <;> linarith
  have hqp : q ≠ p := by
    unfold q
    split_ifs with he
    · rw [he]
      norm_num
    · exact Ne.symm he
  rintro ⟨U, hU, hi⟩
  obtain ⟨s, hs, hs', hu⟩ := path_hits (segment p q)
    (segment_continuousAt ha) (segment_zero ha) hU
  have hm := segment_mem hp hq ha hb hs.le hs'
  exact segment_ne ha hb hqp hs hs'
    (hi _ ⟨hu, hm⟩ (plateau_segment_eq hp hq ha hb ht htq hs.le hs'))

/-- Global singleton and local isolated-point identifiability coincide for
this exact historical domain, and have one exceptional endpoint. -/
theorem historical_isolated_iff {p : ℝ × ℝ} (hp : p ∈ historicalRectangle) :
    HistoricalIsolated p ↔ HistoricalGood p ∨ p = historicalExceptional := by
  constructor
  · intro hi
    by_cases hg : HistoricalGood p
    · exact Or.inl hg
    · right
      by_contra he
      by_cases hz : p.1 = 0
      · exact zero_nonisolated hp hz hi
      · have ha : 0 < p.1 := lt_of_le_of_ne hp.1 (Ne.symm hz)
        have hh : h₂ ≤ p.1 + historicalT p := le_of_not_gt (fun hh => hg ⟨ha, hh⟩)
        by_cases ht : historicalT p < h₁
        · exact one_active_nonisolated hp ht hh he hi
        · exact plateau_nonisolated hp (le_of_not_gt ht) hi
  · intro h
    have hs : HistoricalSingleton p := by
      rcases h with hg | he
      · exact historical_good_singleton hp hg
      · rw [he]
        exact historical_exceptional_singleton
    exact ⟨Set.univ, univ_mem, fun q hq he => hs q hq.2 he⟩

theorem historical_singleton_iff {p : ℝ × ℝ} (hp : p ∈ historicalRectangle) :
    HistoricalSingleton p ↔ HistoricalGood p ∨ p = historicalExceptional := by
  constructor
  · intro hs
    exact (historical_isolated_iff hp).mp
      ⟨Set.univ, univ_mem, fun q hq he => hs q hq.2 he⟩
  · rintro (hg | he)
    · exact historical_good_singleton hp hg
    · rw [he]
      exact historical_exceptional_singleton

private theorem neighborhood_implies_isolated {p : ℝ × ℝ}
    (hp : p ∈ historicalRectangle) (hn : HistoricalNeighborhoodInjective p) :
    HistoricalIsolated p := by
  obtain ⟨U, ho, hu, hi⟩ := hn
  exact ⟨U, ho.mem_nhds hu, fun q hq he => hi hq ⟨hu, hp⟩ he⟩

theorem historical_exceptional_not_neighborhood_injective :
    ¬ HistoricalNeighborhoodInjective historicalExceptional := by
  rintro ⟨U, hopen, hpU, hi⟩
  let q : ℝ × ℝ := (49, 1)
  have hq : q ∈ historicalRectangle := by norm_num [q, historicalRectangle]
  have ha : 0 < historicalExceptional.1 := by norm_num [historicalExceptional]
  have hb : 0 < q.1 := by norm_num [q]
  obtain ⟨s, hs, hs', hu⟩ := path_hits (segment historicalExceptional q)
    (segment_continuousAt ha) (segment_zero ha) (hopen.mem_nhds hpU)
  let w := segment historicalExceptional q s
  have hw : w ∈ historicalRectangle := segment_mem historical_exceptional_mem hq ha hb hs.le hs'
  have hwt : historicalT w = blend (h₂ - 50) 0 s := by
    change historicalT (segment historicalExceptional q s) = _
    rw [segment_t ha hb hs.le hs', exceptional_t]
    norm_num [q, historicalT]
  have hwa : w.1 = blend 50 49 s := rfl
  obtain ⟨h3, h31, h12, h20, h40⟩ := historical_threshold_bounds
  have ht : historicalT w < h₁ := by
    rw [hwt]
    have h := blend_le (show h₂ - 50 ≤ 0 by linarith) (le_refl (0 : ℝ)) hs.le hs'.le
    rw [blend_self] at h
    linarith
  have hh : h₂ ≤ w.1 + historicalT w := by
    rw [hwa, hwt]
    unfold blend
    have hm := mul_nonneg hs.le (show 0 ≤ 49 - h₂ by linarith)
    nlinarith only [hm]
  have hne : w ≠ historicalExceptional := by
    intro he
    have e := congrArg Prod.fst he
    change w.1 = 50 at e
    rw [hwa] at e
    unfold blend at e
    nlinarith only [e, hs]
  have hiw : HistoricalIsolated w :=
    ⟨U, hopen.mem_nhds hu, fun z hz he => hi hz ⟨hu, hw⟩ he⟩
  exact one_active_nonisolated hw ht hh hne hiw

/-- Necessary and sufficient relative neighborhood injectivity, including
all four edges of the actual historical rectangle. -/
theorem historical_neighborhood_injective_iff {p : ℝ × ℝ}
    (hp : p ∈ historicalRectangle) :
    HistoricalNeighborhoodInjective p ↔ HistoricalGood p := by
  constructor
  · intro hn
    rcases (historical_isolated_iff hp).mp (neighborhood_implies_isolated hp hn) with hg | he
    · exact hg
    · rw [he] at hn
      exact False.elim (historical_exceptional_not_neighborhood_injective hn)
  · intro hg
    let U : Set (ℝ × ℝ) := {q | HistoricalGood q}
    have ht : Continuous historicalT := by unfold historicalT; fun_prop
    have ho : IsOpen U := by
      change IsOpen ({q : ℝ × ℝ | 0 < q.1 ∧ q.1 + historicalT q < h₂})
      exact (isOpen_lt continuous_const continuous_fst).inter
        (isOpen_lt (continuous_fst.add ht) continuous_const)
    refine ⟨U, ho, hg, ?_⟩
    intro x hx y hy he
    exact (historical_good_singleton hx.2 hx.1 y hy.2 he.symm).symm

/-- Integrated classification for the exact historical model and actual
closed parameter rectangle. No assumptions on additional sensors. -/
theorem historical_complete_classification {p : ℝ × ℝ}
    (hp : p ∈ historicalRectangle) :
    (HistoricalSingleton p ↔
      (0 < p.1 ∧ p.1 * (2 - p.2) < historicalThreshold 2) ∨
      p = historicalExceptional) ∧
    (HistoricalIsolated p ↔
      (0 < p.1 ∧ p.1 * (2 - p.2) < historicalThreshold 2) ∨
      p = historicalExceptional) ∧
    (HistoricalNeighborhoodInjective p ↔
      0 < p.1 ∧ p.1 * (2 - p.2) < historicalThreshold 2) := by
  have he : p.1 + historicalT p = p.1 * (2 - p.2) := by
    unfold historicalT
    ring
  refine ⟨?_, ?_, ?_⟩
  · simpa only [HistoricalGood, he] using historical_singleton_iff hp
  · simpa only [HistoricalGood, he] using historical_isolated_iff hp
  · simpa only [HistoricalGood, he] using historical_neighborhood_injective_iff hp

end ReyesMath.V18Forward
