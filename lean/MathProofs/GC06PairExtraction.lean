import MathProofs.GC06SpectralMerging
import MathProofs.GC01ExpandedOrbits

/-! GC06/GC16: direct two-profile extraction without a finite cluster induction.
Candidate implementation, pending pinned build. Ordinary subadditivity and
the spectral exclusion of attained equality pairs are distinguished explicitly. -/

open Filter Topology Complex InnerProductSpace MeasureTheory Set
open scoped Topology

namespace ReyesMath.GC06PairExtraction
open Sobolev Sobolev.H2 StrictBinding WholeSpace
local notation "R2" => EuclideanSpace ℝ (Fin 2)
variable {β γ k : ℝ}

def SubadditiveEnergy (β γ k : ℝ) : Prop :=
  ∀ a b : ℝ, 0 < a → 0 < b →
    Imin β γ k (a + b) ≤ Imin β γ k a + Imin β γ k b

/-! Weak translation limit in the exact L² space, using compact-support
approximation, not an assumed Fourier asymptotic. -/

private theorem approximate_L2 (f : L2 2) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : R2 → ℂ, ∃ hg : MemLp g 2 volume, HasCompactSupport g ∧
      ‖f - hg.toLp g‖ ≤ ε := by
  obtain ⟨g, hgc, herr, _, hg⟩ :=
    (Lp.memLp f).exists_hasCompactSupport_eLpNorm_sub_le
      (by norm_num : (2 : ENNReal) ≠ ⊤)
      (ENNReal.ofReal_ne_zero_iff.mpr hε)
  refine ⟨g, hg, hgc, ?_⟩
  rw [Lp.norm_def]
  have hae : (⇑(f - hg.toLp g) : R2 → ℂ) =ᵐ[volume] (fun x => f x - g x) := by
    filter_upwards [Lp.coeFn_sub f (hg.toLp g), hg.coeFn_toLp] with x hx hy
    rw [hx, Pi.sub_apply, hy]
  rw [eLpNorm_congr_ae hae]
  simpa [ENNReal.toReal_ofReal hε.le] using
    ENNReal.toReal_mono (ENNReal.ofReal_ne_top : ENNReal.ofReal ε ≠ ⊤) herr

private theorem compact_inner_translate_zero
    (f g : R2 → ℂ) (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) :
    ∃ R : ℝ, ∀ y : R2, R < ‖y‖ →
      inner ℂ (hf.toLp f) (transL2 y (hg.toLp g)) = 0 := by
  obtain ⟨A, hA⟩ := hfc.isBounded.subset_closedBall (0 : R2)
  obtain ⟨B, hB⟩ := hgc.isBounded.subset_closedBall (0 : R2)
  refine ⟨A+B, fun y hy => ?_⟩
  have hpoint (x : R2) : f x = 0 ∨ g (x+y) = 0 := by
    by_contra! h
    have hx : ‖x‖ ≤ A := by
      have hm := hA (subset_closure (show x ∈ Function.support f from h.1))
      simpa [Metric.mem_closedBall, dist_zero_right] using hm
    have hxy : ‖x+y‖ ≤ B := by
      have hm := hB (subset_closure (show x+y ∈ Function.support g from h.2))
      simpa [Metric.mem_closedBall, dist_zero_right] using hm
    have ht := norm_sub_le (x+y) x
    rw [add_sub_cancel_left] at ht
    linarith
  have hshift : (transL2 y (hg.toLp g) : R2 → ℂ) =ᵐ[volume] fun x => g (x+y) := by
    have hm := (mp_add_right y).quasiMeasurePreserving
    exact (coeFn_transL2 y (hg.toLp g)).trans (hm.ae_eq_comp hg.coeFn_toLp)
  rw [L2.inner_def]
  calc
    _ = ∫ _x : R2, (0 : ℂ) := by
      apply integral_congr_ae
      filter_upwards [hf.coeFn_toLp, hshift] with x hx hy'
      rw [hx, hy']
      rcases hpoint x with h | h
      · simp [h]
      · simp [h]
    _ = 0 := integral_zero _ _

/-- Translation to infinity is weakly zero for arbitrary L² fields. -/
theorem weak_translate_zero (f z : L2 2) (y : ℕ → R2)
    (hy : Tendsto (fun n => ‖y n‖) atTop atTop) :
    Tendsto (fun n => inner ℂ z (transL2 (y n) f)) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  let d := min 1 (ε / (3 * (‖f‖ + ‖z‖ + 1)))
  have hd : 0 < d := lt_min one_pos (by positivity)
  have hd1 : d ≤ 1 := min_le_left _ _
  have hdε : d * (‖f‖ + ‖z‖ + 1) ≤ ε / 3 := by
    have hh := mul_le_mul_of_nonneg_right
      (min_le_right (1 : ℝ) (ε / (3 * (‖f‖ + ‖z‖ + 1))))
      (show 0 ≤ ‖f‖ + ‖z‖ + 1 by positivity)
    change d * (‖f‖ + ‖z‖ + 1) ≤ _ at hh
    have he : ε / (3 * (‖f‖ + ‖z‖ + 1)) * (‖f‖ + ‖z‖ + 1) = ε / 3 := by
      field_simp
    linarith only [hh, he]
  obtain ⟨f', hf', hfc, hferr⟩ := approximate_L2 f hd
  obtain ⟨z', hz', hzc, hzerr⟩ := approximate_L2 z hd
  let F := hf'.toLp f'
  let Z := hz'.toLp z'
  have hF : ‖F‖ ≤ ‖f‖ + 1 := by
    have h := norm_sub_norm_le F f
    rw [norm_sub_rev] at h
    linarith only [h, hferr, hd1]
  obtain ⟨R, hR⟩ := compact_inner_translate_zero z' f' hz' hf' hzc hfc
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hy.eventually (eventually_gt_atTop R))
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_zero_right]
  have hzero : inner ℂ Z (transL2 (y n) F) = 0 := hR _ (hN n hn)
  have he : inner ℂ z (transL2 (y n) f) =
      inner ℂ (z-Z) (transL2 (y n) F) +
      inner ℂ z (transL2 (y n) (f-F)) := by
    simp only [map_sub, inner_sub_left, inner_sub_right]
    rw [hzero]
    abel
  rw [he]
  calc
    _ ≤ ‖inner ℂ (z-Z) (transL2 (y n) F)‖ +
        ‖inner ℂ z (transL2 (y n) (f-F))‖ := norm_add_le _ _
    _ ≤ d * (‖f‖+1) + ‖z‖ * d := by
      have h1 := norm_inner_le_norm (z-Z) (transL2 (y n) F)
      have h2 := norm_inner_le_norm z (transL2 (y n) (f-F))
      simp only [LinearIsometry.norm_map] at h1 h2
      have h3 := mul_le_mul hzerr hF (norm_nonneg _) (by positivity : 0 ≤ d)
      have h4 := mul_le_mul_of_nonneg_left hferr (norm_nonneg z)
      linarith only [h1, h2, h3, h4]
    _ = d * (‖f‖ + ‖z‖ + 1) := by ring
    _ < ε := hdε.trans_lt (by linarith)

/-- A fixed sequence of translates works for every val and lap component. -/
theorem exists_weak_translates (V : H2 2) :
    ∃ y : ℕ → R2,
      (∀ z, Tendsto (fun n => inner ℂ z (translate (y n) V).val) atTop (𝓝 0)) ∧
      (∀ z, Tendsto (fun n => inner ℂ z (translate (y n) V).lap) atTop (𝓝 0)) := by
  let y : ℕ → R2 := fun n => EuclideanSpace.single (0 : Fin 2) (n : ℝ)
  have hy : Tendsto (fun n => ‖y n‖) atTop atTop := by
    simpa [y, EuclideanSpace.norm_single, Real.norm_eq_abs] using
      (tendsto_natCast_atTop_atTop (R := ℝ))
  exact ⟨y, fun z => weak_translate_zero V.val z y hy,
    fun z => weak_translate_zero V.lap z y hy⟩

/-- Approximate splitting of a fixed pair into spatially separated trials.
The weak-translation limit, rather than a fictitious exact disjointness of
arbitrary H² fields, is the precise remaining input to this lemma. -/
theorem pair_upper_of_weak_translates (hγ : 0 < γ) (U V : H2 2)
    (ha : 0 < M U) (hb : 0 < M V) (y : ℕ → R2)
    (h0 : ∀ z, Tendsto (fun n => inner ℂ z (translate (y n) V).val) atTop (𝓝 0))
    (h2 : ∀ z, Tendsto (fun n => inner ℂ z (translate (y n) V).lap) atTop (𝓝 0)) :
    Imin β γ k (M U + M V) ≤ energy β γ k U + energy β γ k V := by
  let W : ℕ → H2 2 := fun n => H2.add U (translate (y n) V)
  have hsub : ∀ n, H2.sub (W n) U = translate (y n) V := by
    intro n
    apply ext_of_val
    simp [W, H2.sub, H2.add, add_comm U.val]
  have hw0 : ∀ z, Tendsto (fun n => inner ℂ z (W n).val) atTop (𝓝 (inner ℂ z U.val)) := by
    intro z
    have h := (h0 z).const_add (inner ℂ z U.val)
    simpa [W, H2.add, inner_add_right] using h
  have hw2 : ∀ z, Tendsto (fun n => inner ℂ z (W n).lap) atTop (𝓝 (inner ℂ z U.lap)) := by
    intro z
    have h := (h2 z).const_add (inner ℂ z U.lap)
    simpa [W, H2.add, inner_add_right] using h
  let B := (‖U.val‖ + ‖V.val‖)^2 + (‖U.lap‖ + ‖V.lap‖)^2
  have hB : ∀ n, D (W n) + M (W n) ≤ B := by
    intro n
    have hv : ‖(W n).val‖ ≤ ‖U.val‖ + ‖V.val‖ := by
      change ‖U.val + transL2 (y n) V.val‖ ≤ _
      simpa only [LinearIsometry.norm_map] using
        norm_add_le U.val (transL2 (y n) V.val)
    have hl : ‖(W n).lap‖ ≤ ‖U.lap‖ + ‖V.lap‖ := by
      change ‖U.lap + transL2 (y n) V.lap‖ ≤ _
      simpa only [LinearIsometry.norm_map] using
        norm_add_le U.lap (transL2 (y n) V.lap)
    unfold B D M
    linarith only [pow_le_pow_left₀ (norm_nonneg _) hv 2,
      pow_le_pow_left₀ (norm_nonneg _) hl 2]
  have hsM := tendsto_M_split W U hw0
  simp_rw [hsub, M_translate] at hsM
  have hM : Tendsto (fun n => M (W n)) atTop (𝓝 (M U + M V)) := by
    have h := hsM.const_add (M U + M V)
    rw [add_zero] at h
    exact h.congr fun n => by ring
  have hsE := tendsto_energy_split β γ k W U hB hw0 hw2
  simp_rw [hsub, energy_translate] at hsE
  have hE : Tendsto (fun n => energy β γ k (W n)) atTop
      (𝓝 (energy β γ k U + energy β γ k V)) := by
    have h := hsE.const_add (energy β γ k U + energy β γ k V)
    rw [add_zero] at h
    exact h.congr fun n => by ring
  obtain ⟨e, he, hcorr⟩ := exists_energy_ge_Imin β γ k hγ W
    (add_pos ha hb) hM hB
  have hlim := hE.add he
  rw [add_zero] at hlim
  exact ge_of_tendsto hlim hcorr

/-- Ordinary subadditivity from the standard weak-translation lemma. -/
theorem subadditive_of_weak_translates (hβ : 0 < β) (hγ : 0 < γ)
    (htrans : ∀ V : H2 2, ∃ y : ℕ → R2,
      (∀ z, Tendsto (fun n => inner ℂ z (translate (y n) V).val) atTop (𝓝 0)) ∧
      (∀ z, Tendsto (fun n => inner ℂ z (translate (y n) V).lap) atTop (𝓝 0))) :
    SubadditiveEnergy β γ k := by
  intro a b ha hb
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨U, hU, hUE⟩ := exists_energy_lt (β := β) (γ := γ) (k := k) hβ ha
    (ε := ε / 3) (by positivity)
  obtain ⟨V, hV, hVE⟩ := exists_energy_lt (β := β) (γ := γ) (k := k) hβ hb
    (ε := ε / 3) (by positivity)
  obtain ⟨y, h0, h2⟩ := htrans V
  have hi := pair_upper_of_weak_translates (β := β) (k := k) hγ U V
    (by rw [hU]; exact ha) (by rw [hV]; exact hb) y h0 h2
  rw [hU, hV] at hi
  linarith only [hi, hUE, hVE, hε]

/-- Ordinary subadditivity of the original continuum constrained infimum. -/
theorem ordinary_subadditive (hβ : 0 < β) (hγ : 0 < γ) :
    SubadditiveEnergy β γ k :=
  subadditive_of_weak_translates hβ hγ exists_weak_translates

/-- Every nonzero weak profile of a minimizing sequence is itself an attained
minimizer at its own mass. If its mass is smaller, the complementary infima
saturate ordinary subadditivity. No strict-binding hypothesis is used. -/
theorem attained_profile_of_weak (hγ : 0 < γ)
    (hsub : SubadditiveEnergy β γ k) {m C : ℝ} (hm : 0 < m)
    {W : ℕ → H2 2} (hM : ∀ n, M (W n) = m)
    (hD : ∀ n, D (W n) ≤ C)
    (hE : Tendsto (fun n => energy β γ k (W n)) atTop (𝓝 (Imin β γ k m)))
    {U : H2 2} (hU : 0 < M U)
    (h0 : ∀ z, Tendsto (fun n => inner ℂ z (W n).val) atTop (𝓝 (inner ℂ z U.val)))
    (h2 : ∀ z, Tendsto (fun n => inner ℂ z (W n).lap) atTop (𝓝 (inner ℂ z U.lap))) :
    M U ≤ m ∧ energy β γ k U = Imin β γ k (M U) ∧
      (M U < m → Imin β γ k m = Imin β γ k (M U) + Imin β γ k (m - M U)) := by
  set B := C + m
  have hbd : ∀ n, D (W n) + M (W n) ≤ B := fun n => by rw [hM n]; linarith [hD n]
  set V : ℕ → H2 2 := fun n => sub (W n) U with hV
  set B₂ := 2 * B + 2 * (D U + M U)
  have hbd₂ : ∀ n, D (V n) + M (V n) ≤ B₂ := fun n =>
    (DM_sub_le (W n) U).trans (by linarith [hbd n])
  have hMV : Tendsto (fun n => M (V n)) atTop (𝓝 (m - M U)) := by
    have h := (tendsto_M_split W U h0).neg.const_add (m - M U)
    simp only [neg_zero, add_zero] at h
    refine h.congr fun n => ?_
    simp only [hV, hM n]
    ring
  have hEsplit := tendsto_energy_split β γ k W U hbd h0 h2
  have hle : M U ≤ m := by
    have h := ge_of_tendsto' hMV fun n => M_nonneg (V n)
    linarith
  have hIa := Imin_le_energy (β := β) (k := k) hγ (rfl : M U = M U)
  refine ⟨hle, ?_⟩
  rcases lt_or_eq_of_le hle with hlt | heq
  · have hμ : 0 < m - M U := by linarith
    obtain ⟨e, he, hev⟩ := exists_energy_ge_Imin β γ k hγ V hμ hMV hbd₂
    have hF : Tendsto (fun n => energy β γ k (W n) -
        (energy β γ k (W n) - energy β γ k U - energy β γ k (V n)) + e n) atTop
        (𝓝 (Imin β γ k m - 0 + 0)) := (hE.sub hEsplit).add he
    rw [sub_zero, add_zero] at hF
    have hge : energy β γ k U + Imin β γ k (m - M U) ≤ Imin β γ k m := by
      refine ge_of_tendsto hF ?_
      filter_upwards [hev] with n hn
      linarith
    have hupper := hsub (M U) (m - M U) hU hμ
    rw [show M U + (m - M U) = m by ring] at hupper
    exact ⟨by linarith only [hIa, hge, hupper], fun _ => by linarith only [hIa, hge, hupper]⟩
  · have hMV0 : Tendsto (fun n => M (V n)) atTop (𝓝 0) := by rwa [heq, sub_self] at hMV
    have hQ0 : Tendsto (fun n => Q (V n)) atTop (𝓝 0) := by
      have h := hMV0.const_mul (B₂ / 4)
      rw [mul_zero] at h
      exact squeeze_zero (fun n => Q_nonneg _) (fun n => Q_le_of_bound (hbd₂ n)) h
    have hS0 : Tendsto (fun n => S (V n)) atTop (𝓝 0) := by
      have h := hMV0.const_mul ((B₂ / 4) ^ 2)
      rw [mul_zero] at h
      exact squeeze_zero (fun n => S_nonneg _) (fun n => S_le_of_bound (hbd₂ n)) h
    have hTV : Tendsto (fun n => T k (V n)) atTop (𝓝 (Imin β γ k m - energy β γ k U)) := by
      have h := ((hE.sub_const (energy β γ k U)).sub hEsplit).add
        ((hQ0.const_mul (β / 2)).sub (hS0.const_mul (γ / 3)))
      simp only [mul_zero, sub_zero, add_zero] at h
      refine h.congr fun n => ?_
      rw [energy_eq β γ k (V n)]
      ring
    have hL0 : 0 ≤ Imin β γ k m - energy β γ k U := ge_of_tendsto' hTV fun n => T_nonneg k _
    rw [heq] at hIa ⊢
    exact ⟨by linarith only [hIa, hL0], fun hh => (lt_irrefl m hh).elim⟩

/-- Extract one attained profile from each positive mass, without requiring
that the full mass is attained or that a cluster decomposition terminates. -/
theorem exists_attained_submass (hβ : 0 < β) (hγ : 0 < γ)
    (hsub : SubadditiveEnergy β γ k) {m : ℝ} (hm : 0 < m) :
    ∃ U : H2 2, 0 < M U ∧ M U ≤ m ∧ energy β γ k U = Imin β γ k (M U) ∧
      (M U < m → Imin β γ k m = Imin β γ k (M U) + Imin β γ k (m - M U)) := by
  have htrial : ∀ n : ℕ, ∃ U : H2 2, M U = m ∧ energy β γ k U < Imin β γ k m + 1 / ((n : ℝ) + 1) :=
    fun n => StrictBinding.exists_energy_lt hβ hm (by positivity)
  choose u hM hult using htrial
  have hlim : Tendsto (fun n : ℕ => Imin β γ k m + 1 / ((n : ℝ) + 1)) atTop
      (𝓝 (Imin β γ k m)) := by
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_add (Imin β γ k m)
  have hE : Tendsto (fun n => energy β γ k (u n)) atTop (𝓝 (Imin β γ k m)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun n => StrictBinding.Imin_le_energy hγ (hM n)) (fun n => (hult n).le)
  have hI := (NegativeEnergy.negative_constrained_energy (k := k) hβ hγ hm).2
  obtain ⟨N₀, hN₀⟩ := eventually_bounds hβ hγ hI hM hE
  set C := (Real.sqrt (0 + 3 * β ^ 2 / (16 * γ) * m) + k ^ 2 * Real.sqrt m) ^ 2 with hC
  set q₀ := -Imin β γ k m / β with hq₀
  have hq : 0 < q₀ := div_pos (by linarith) hβ
  set u' : ℕ → H2 2 := fun n => u (n + N₀) with hu'
  have hM' : ∀ n, M (u' n) = m := fun n => hM _
  have hQ' : ∀ n, q₀ ≤ Q (u' n) := fun n => (hN₀ (n + N₀) (Nat.le_add_left _ _)).1
  have hD' : ∀ n, D (u' n) ≤ C := fun n => (hN₀ (n + N₀) (Nat.le_add_left _ _)).2
  obtain ⟨r, -, c₀, hc₀, y, hy⟩ := exists_translations hm hq hM' hQ' hD'
  set w : ℕ → H2 2 := fun n => translate (y n) (u' n) with hw
  have hMw : ∀ n, M (w n) = m := fun n => by rw [hw, M_translate, hM']
  have hDw : ∀ n, D (w n) ≤ C := fun n => by rw [hw, D_translate]; exact hD' n
  obtain ⟨φ, hφ, U, hU, h0, -, h2⟩ := exists_profile hc₀ hMw hDw hy
  have hφN : Tendsto (fun n => φ n + N₀) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_add_right _ _) hφ.tendsto_atTop
  have hEW : Tendsto (fun n => energy β γ k (w (φ n))) atTop (𝓝 (Imin β γ k m)) := by
    refine (hE.comp hφN).congr fun n => ?_
    simp only [Function.comp_apply, hw, hu', energy_translate]
  exact ⟨U, hU, attained_profile_of_weak hγ hsub hm
    (fun n => hMw (φ n)) (fun n => hDw (φ n)) hEW hU h0 h2⟩

/-- If a split saturates subadditivity, any attained subprofile from each side
also saturates it. This replaces the finite-cluster induction in the binding
proof; all residual masses are accounted for, including zero residuals. -/
theorem equality_of_subprofiles (hsub : SubadditiveEnergy β γ k)
    {a b x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hxa : x ≤ a) (hyb : y ≤ b)
    (heq : Imin β γ k (a+b) = Imin β γ k a + Imin β γ k b)
    (ha : x < a → Imin β γ k a = Imin β γ k x + Imin β γ k (a-x))
    (hb : y < b → Imin β γ k b = Imin β γ k y + Imin β γ k (b-y)) :
    Imin β γ k (x+y) = Imin β γ k x + Imin β γ k y := by
  have hxy := hsub x y hx hy
  have hpos : 0 < x+y := add_pos hx hy
  rcases lt_or_eq_of_le hxa with hxa' | hxa'
  · have hr : 0 < a-x := sub_pos.mpr hxa'
    have h1 := hsub (x+y) (a-x) hpos hr
    rw [show x+y+(a-x)=a+y by ring] at h1
    rcases lt_or_eq_of_le hyb with hyb' | hyb'
    · have hs : 0 < b-y := sub_pos.mpr hyb'
      have h2 := hsub (a+y) (b-y) (by linarith) hs
      rw [show a+y+(b-y)=a+b by ring] at h2
      linarith only [heq, ha hxa', hb hyb', hxy, h1, h2]
    · rw [hyb'] at h1 hxy ⊢
      linarith only [heq, ha hxa', hxy, h1]
  · rcases lt_or_eq_of_le hyb with hyb' | hyb'
    · have hs : 0 < b-y := sub_pos.mpr hyb'
      have h1 := hsub (x+y) (b-y) hpos hs
      rw [show x+y+(b-y)=x+b by ring, hxa'] at h1
      rw [hxa'] at hxy ⊢
      linarith only [heq, hb hyb', hxy, h1]
    · simpa only [hxa', hyb'] using heq

/-- A failed split produces a pair of attained equality profiles using just
two extractions. The spectral merging proof no longer needs a full finite
profile decomposition in order to establish universal binding. -/
theorem pair_of_failed_split (hβ : 0 < β) (hγ : 0 < γ)
    (hsub : SubadditiveEnergy β γ k)
    {m a : ℝ} (hm : 0 < m) (ha : 0 < a) (ham : a < m)
    (hfail : ¬ Imin β γ k m < Imin β γ k a + Imin β γ k (m-a)) :
    ∃ U V : H2 2, 0 < M U ∧ 0 < M V ∧
      energy β γ k U = Imin β γ k (M U) ∧
      energy β γ k V = Imin β γ k (M V) ∧
      Imin β γ k (M U + M V) = Imin β γ k (M U) + Imin β γ k (M V) := by
  have hb : 0 < m-a := sub_pos.mpr ham
  have hle := hsub a (m-a) ha hb
  rw [show a+(m-a)=m by ring] at hle
  have heq : Imin β γ k (a+(m-a)) = Imin β γ k a + Imin β γ k (m-a) := by
    rw [show a+(m-a)=m by ring]
    exact le_antisymm hle (le_of_not_gt hfail)
  obtain ⟨U, hU, hUa, hUE, hUr⟩ := exists_attained_submass hβ hγ hsub ha
  obtain ⟨V, hV, hVb, hVE, hVr⟩ := exists_attained_submass hβ hγ hsub hb
  exact ⟨U, V, hU, hV, hUE, hVE,
    equality_of_subprofiles hsub hU hV hUa hVb heq hUr hVr⟩

/-- The only remaining substantive binding input after subadditivity is
the actual spectral exclusion of attained equality pairs. -/
theorem binding_of_spectral_exclusion (hβ : 0 < β) (hγ : 0 < γ)
    (hsub : SubadditiveEnergy β γ k)
    (hmerge : ∀ U V : H2 2, 0 < M U → 0 < M V →
      energy β γ k U = Imin β γ k (M U) →
      energy β γ k V = Imin β γ k (M V) →
      Imin β γ k (M U + M V) ≠ Imin β γ k (M U) + Imin β γ k (M V))
    {m a : ℝ} (hm : 0 < m) (ha : 0 < a) (ham : a < m) :
    Imin β γ k m < Imin β γ k a + Imin β γ k (m-a) := by
  by_contra hn
  obtain ⟨U, V, hU, hV, hUE, hVE, heq⟩ := pair_of_failed_split hβ hγ hsub hm ha ham hn
  exact hmerge U V hU hV hUE hVE heq

theorem confinement_of_spectral_exclusion (hβ : 0 < β) (hγ : 0 < γ)
    (hsub : SubadditiveEnergy β γ k)
    (hmerge : ∀ U V : H2 2, 0 < M U → 0 < M V →
      energy β γ k U = Imin β γ k (M U) →
      energy β γ k V = Imin β γ k (M V) →
      Imin β γ k (M U + M V) ≠ Imin β γ k (M U) + Imin β γ k (M V))
    {m : ℝ} (hm : 0 < m) :
    ∃ U : H2 2, M U = m ∧ energy β γ k U = Imin β γ k m :=
  exists_minimizer_of_binding hβ hγ hm
    (fun a ha ham => binding_of_spectral_exclusion hβ hγ hsub hmerge hm ha ham)

theorem compactness_of_spectral_exclusion (hβ : 0 < β) (hγ : 0 < γ)
    (hsub : SubadditiveEnergy β γ k)
    (hmerge : ∀ U V : H2 2, 0 < M U → 0 < M V →
      energy β γ k U = Imin β γ k (M U) →
      energy β γ k V = Imin β γ k (M V) →
      Imin β γ k (M U + M V) ≠ Imin β γ k (M U) + Imin β γ k (M V))
    {m : ℝ} (hm : 0 < m) {u : ℕ → H2 2} (hM : ∀ n, M (u n) = m)
    (hE : Tendsto (fun n => energy β γ k (u n)) atTop (𝓝 (Imin β γ k m))) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ y : ℕ → R2, ∃ U : H2 2, M U = m ∧
      energy β γ k U = Imin β γ k m ∧
      Tendsto (fun n => distH2 (translate (y n) (u (φ n))) U) atTop (𝓝 0) :=
  compactness_of_binding hβ hγ hm
    (fun a ha ham => binding_of_spectral_exclusion hβ hγ hsub hmerge hm ha ham) hM hE

open OrbitalStability

theorem stability_of_spectral_exclusion (hβ : 0 < β) (hγ : 0 < γ)
    (hsub : SubadditiveEnergy β γ k)
    (hmerge : ∀ U V : H2 2, 0 < M U → 0 < M V →
      energy β γ k U = Imin β γ k (M U) →
      energy β γ k V = Imin β γ k (M V) →
      Imin β γ k (M U + M V) ≠ Imin β γ k (M U) + Imin β γ k (M V))
    {m ε : ℝ} (hm : 0 < m) (hε : 0 < ε) :
    ∃ δ > 0, ∀ u : ℝ → H2 2, IsSolution β γ k u →
      distX (u 0) (Gset β γ k m) < δ →
      BddAbove (Set.range fun t => distX (u t) (Gset β γ k m)) ∧
      ⨆ t, distX (u t) (Gset β γ k m) < ε :=
  orbital_stability_of_binding hβ hγ hm
    (fun a ha ham => binding_of_spectral_exclusion hβ hγ hsub hmerge hm ha ham) hε

end ReyesMath.GC06PairExtraction
