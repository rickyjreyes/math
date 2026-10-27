import Mathlib

/-!
# Exact positive-wavenumber dispersion minimum (F06)

Complete formalization of the main theorem, both corollaries and the
wavenumber remark of `papers/exact-positive-wavenumber-minimum/main.tex`.

For the quadratic dispersion relation
`K z² − (1 + a q) z + m² + q + (K + G + T) q² = 0`, `a = 2K + G`, under
`K, T, B > 0`, `0 < 4Km² < 1` (`Base`) and the strict finite-scale condition
`G(1 − s)/(2K) > s` (`FiniteScale`):

* `exact_positive_wavenumber_minimum`: `G, a > 0`; the branches `z±` are exactly
  the real roots; real roots exist for `q ≥ 0` iff `q ≤ q_coll`; the explicit `q*`
  satisfies `0 < q* < G/B < q_coll` and is the unique global minimizer of `z₋`
  on `[0, q_coll]`; the actual second derivative is `(Bs² + G²)/(2K d^{3/2}) > 0`;
  both branches are strictly positive on `[0, q_coll]`.
* `exact_minimum_frequency`: `z₋(q*) = (B + aG − √((a² + B)(G² + Bs²)))/(2KB) > 0`.
* `sharp_initial_slope_criterion`, `min_at_zero_of_not_finiteScale`: for arbitrary
  real `G` an interior minimizer exists iff the finite-scale condition holds;
  otherwise `z₋` is strictly increasing with minimum at `q = 0`.
* `omegaMinus_unique_min`, `wavenumber_minimum`, `wavenumber_second_deriv`:
  the same minimizer for `ω₋ = √z₋` and for `k = √q`, with
  `d²/dk² z₋(k²)|_{k*} = 4 k*² z₋''(q*) > 0`.

Existence of the stationary point is established by the explicit formula
(Step 5) rather than by the intermediate value theorem; uniqueness follows
from an exact supporting-tangent identity.
-/

open Set Filter Topology

namespace ReyesMath

namespace Dispersion

/-- `a = 2K + G`. -/
def a (K G : ℝ) : ℝ := 2 * K + G
/-- `B = 4KT − G²`. -/
def B (K G T : ℝ) : ℝ := 4 * K * T - G ^ 2
/-- `s = √(1 − 4Km²)`. -/
noncomputable def s (K m : ℝ) : ℝ := Real.sqrt (1 - 4 * K * m ^ 2)
/-- The discriminant `d(q) = s² + 2Gq − Bq²`. -/
noncomputable def d (K G T m q : ℝ) : ℝ := s K m ^ 2 + 2 * G * q - B K G T * q ^ 2
/-- The quadratic dispersion polynomial in `z = ω²`. -/
def poly (K G T m q z : ℝ) : ℝ :=
  K * z ^ 2 - (1 + a K G * q) * z + m ^ 2 + q + (K + G + T) * q ^ 2
/-- Upper squared-frequency branch. -/
noncomputable def zPlus (K G T m q : ℝ) : ℝ :=
  (1 + a K G * q + Real.sqrt (d K G T m q)) / (2 * K)
/-- Lower squared-frequency branch. -/
noncomputable def zMinus (K G T m q : ℝ) : ℝ :=
  (1 + a K G * q - Real.sqrt (d K G T m q)) / (2 * K)
/-- The collision wavenumber `q_coll = (G + √(G² + Bs²)) / B`. -/
noncomputable def qColl (K G T m : ℝ) : ℝ :=
  (G + Real.sqrt (G ^ 2 + B K G T * s K m ^ 2)) / B K G T
/-- The explicit minimizer `q* = (G − a √((G² + Bs²)/(a² + B))) / B`. -/
noncomputable def qStar (K G T m : ℝ) : ℝ :=
  (G - a K G * Real.sqrt ((G ^ 2 + B K G T * s K m ^ 2) / (a K G ^ 2 + B K G T))) / B K G T
/-- The explicit minimum squared frequency. -/
noncomputable def zMin (K G T m : ℝ) : ℝ :=
  (B K G T + a K G * G -
      Real.sqrt ((a K G ^ 2 + B K G T) * (G ^ 2 + B K G T * s K m ^ 2))) /
    (2 * K * B K G T)

/-- The baseline hypotheses `K > 0`, `T > 0`, `B > 0`, `0 < 4Km² < 1`. -/
structure Base (K G T m : ℝ) : Prop where
  K_pos : 0 < K
  T_pos : 0 < T
  B_pos : 0 < B K G T
  mass_pos : 0 < 4 * K * m ^ 2
  mass_lt : 4 * K * m ^ 2 < 1

variable {K G T m : ℝ}

theorem Base.s_sq (h : Base K G T m) : s K m ^ 2 = 1 - 4 * K * m ^ 2 :=
  Real.sq_sqrt (by linarith [h.mass_lt])

theorem Base.s_pos (h : Base K G T m) : 0 < s K m :=
  Real.sqrt_pos.2 (by linarith [h.mass_lt])

theorem Base.s_lt_one (h : Base K G T m) : s K m < 1 := by
  rw [s, Real.sqrt_lt' one_pos]
  linarith [h.mass_pos]

/-- Step 1: the discriminant of the dispersion polynomial is exactly `d(q)`. -/
theorem discriminant_eq (h : Base K G T m) (q : ℝ) :
    (1 + a K G * q) ^ 2 - 4 * K * (m ^ 2 + q + (K + G + T) * q ^ 2) = d K G T m q := by
  rw [d, h.s_sq, a, B]
  ring

/-- Factorization of the polynomial when the discriminant is nonnegative. -/
theorem poly_factor (h : Base K G T m) {q : ℝ} (hd : 0 ≤ d K G T m q) (z : ℝ) :
    poly K G T m q z = K * (z - zPlus K G T m q) * (z - zMinus K G T m q) := by
  have hK := h.K_pos.ne'
  have hsq := Real.sq_sqrt hd
  have hdisc := discriminant_eq h q
  unfold poly zPlus zMinus
  field_simp
  rw [← sub_eq_zero]
  have : (Real.sqrt (d K G T m q)) ^ 2 = (1 + a K G * q) ^ 2 -
      4 * K * (m ^ 2 + q + (K + G + T) * q ^ 2) := by rw [hsq, hdisc]
  nlinarith [this]

/-- The branches `z±` are exactly the real roots when `d(q) ≥ 0`. -/
theorem poly_eq_zero_iff (h : Base K G T m) {q : ℝ} (hd : 0 ≤ d K G T m q) (z : ℝ) :
    poly K G T m q z = 0 ↔ z = zPlus K G T m q ∨ z = zMinus K G T m q := by
  rw [poly_factor h hd, mul_assoc, mul_eq_zero, or_iff_right h.K_pos.ne', mul_eq_zero,
    sub_eq_zero, sub_eq_zero]

/-- No real root exists when `d(q) < 0`. -/
theorem poly_ne_zero_of_neg (h : Base K G T m) {q : ℝ} (hd : d K G T m q < 0) (z : ℝ) :
    poly K G T m q z ≠ 0 := by
  have hK := h.K_pos
  have hdisc := discriminant_eq h q
  have key : 4 * K * poly K G T m q z =
      (2 * K * z - (1 + a K G * q)) ^ 2 - d K G T m q := by
    rw [← hdisc]
    unfold poly
    ring
  intro h0
  rw [h0, mul_zero] at key
  nlinarith [sq_nonneg (2 * K * z - (1 + a K G * q))]

theorem sqrt_disc_gt_abs (h : Base K G T m) :
    |G| < Real.sqrt (G ^ 2 + B K G T * s K m ^ 2) := by
  rw [← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_lt_sqrt (sq_nonneg _)
  have := mul_pos h.B_pos (pow_pos h.s_pos 2)
  linarith

/-- `d(q) = −B (q − q₊)(q − q₋)`. -/
theorem d_factor (h : Base K G T m) (q : ℝ) :
    d K G T m q = -B K G T * (q - qColl K G T m) *
      (q - (G - Real.sqrt (G ^ 2 + B K G T * s K m ^ 2)) / B K G T) := by
  have hB := h.B_pos.ne'
  have hr : Real.sqrt (G ^ 2 + B K G T * s K m ^ 2) ^ 2 = G ^ 2 + B K G T * s K m ^ 2 :=
    Real.sq_sqrt (by have := h.B_pos; positivity)
  unfold d qColl
  set r := Real.sqrt (G ^ 2 + B K G T * s K m ^ 2)
  set b := B K G T
  field_simp
  linear_combination (-1 : ℝ) * hr

theorem qColl_pos (h : Base K G T m) : 0 < qColl K G T m := by
  have := sqrt_disc_gt_abs h
  have hG := neg_abs_le G
  unfold qColl
  exact div_pos (by linarith) h.B_pos

/-- Step 2: for `q ≥ 0`, the branches are real precisely on `[0, q_coll]`. -/
theorem d_nonneg_iff (h : Base K G T m) {q : ℝ} (hq : 0 ≤ q) :
    0 ≤ d K G T m q ↔ q ≤ qColl K G T m := by
  have hr := sqrt_disc_gt_abs h
  have hneg : (G - Real.sqrt (G ^ 2 + B K G T * s K m ^ 2)) / B K G T < 0 :=
    div_neg_of_neg_of_pos (by linarith [le_abs_self G]) h.B_pos
  rw [d_factor h q]
  have hpos : 0 < q - (G - Real.sqrt (G ^ 2 + B K G T * s K m ^ 2)) / B K G T := by linarith
  constructor
  · intro hd
    by_contra hlt
    push_neg at hlt
    have : 0 < -B K G T * (q - qColl K G T m) *
        (q - (G - Real.sqrt (G ^ 2 + B K G T * s K m ^ 2)) / B K G T) * (-1) := by
      have h1 : 0 < B K G T * (q - qColl K G T m) := mul_pos h.B_pos (by linarith)
      have := mul_pos h1 hpos
      linarith
    linarith
  · intro hle
    have h1 : 0 ≤ -B K G T * (q - qColl K G T m) := by
      have := h.B_pos
      nlinarith
    exact mul_nonneg h1 hpos.le

theorem d_pos_of_lt (h : Base K G T m) {q : ℝ} (hq : 0 ≤ q) (hlt : q < qColl K G T m) :
    0 < d K G T m q := by
  have hr := sqrt_disc_gt_abs h
  have hneg : (G - Real.sqrt (G ^ 2 + B K G T * s K m ^ 2)) / B K G T < 0 :=
    div_neg_of_neg_of_pos (by linarith [le_abs_self G]) h.B_pos
  rw [d_factor h q]
  have hpos : 0 < q - (G - Real.sqrt (G ^ 2 + B K G T * s K m ^ 2)) / B K G T := by linarith
  have h1 : 0 < -B K G T * (q - qColl K G T m) := by
    have := h.B_pos
    nlinarith
  exact mul_pos h1 hpos

theorem d_qColl (h : Base K G T m) : d K G T m (qColl K G T m) = 0 := by
  rw [d_factor h, sub_self, mul_zero, zero_mul]

theorem real_root_iff (h : Base K G T m) {q : ℝ} (hq : 0 ≤ q) :
    (∃ z : ℝ, poly K G T m q z = 0) ↔ q ≤ qColl K G T m := by
  constructor
  · rintro ⟨z, hz⟩
    by_contra hlt
    push_neg at hlt
    have hd : d K G T m q < 0 := by
      by_contra hd
      push_neg at hd
      exact absurd ((d_nonneg_iff h hq).1 hd) (not_le.2 hlt)
    exact poly_ne_zero_of_neg h hd z hz
  · intro hle
    exact ⟨_, (poly_eq_zero_iff h ((d_nonneg_iff h hq).2 hle) _).2 (Or.inl rfl)⟩

/-- The strict finite-scale condition `G(1 − s)/(2K) > s`. -/
def FiniteScale (K G m : ℝ) : Prop := G * (1 - s K m) / (2 * K) > s K m

theorem G_pos (h : Base K G T m) (hc : FiniteScale K G m) : 0 < G := by
  have hs := h.s_pos
  have hs1 := h.s_lt_one
  have hK := h.K_pos
  unfold FiniteScale at hc
  have h1 : 0 < G * (1 - s K m) / (2 * K) := lt_trans hs hc
  have h2 : 0 < G * (1 - s K m) := by
    have := (div_pos_iff.1 h1)
    rcases this with ⟨h3, _⟩ | ⟨_, h4⟩
    · exact h3
    · linarith
  by_contra hG
  push_neg at hG
  nlinarith

theorem a_pos (h : Base K G T m) (hc : FiniteScale K G m) : 0 < a K G := by
  have := G_pos h hc
  have := h.K_pos
  unfold a
  linarith

/-- The finite-scale condition is equivalent to `G > a s`. -/
theorem finiteScale_iff (h : Base K G T m) : FiniteScale K G m ↔ a K G * s K m < G := by
  have hK := h.K_pos
  unfold FiniteScale a
  rw [gt_iff_lt, lt_div_iff₀ (by positivity)]
  constructor <;> intro h' <;> nlinarith

/-- The auxiliary root `t = √((G² + Bs²)/(a² + B))`. -/
noncomputable def t (K G T m : ℝ) : ℝ :=
  Real.sqrt ((G ^ 2 + B K G T * s K m ^ 2) / (a K G ^ 2 + B K G T))

theorem t_nonneg : 0 ≤ t K G T m := Real.sqrt_nonneg _

theorem t_sq (h : Base K G T m) :
    t K G T m ^ 2 = (G ^ 2 + B K G T * s K m ^ 2) / (a K G ^ 2 + B K G T) := by
  have := h.B_pos
  exact Real.sq_sqrt (by positivity)

theorem qStar_eq : qStar K G T m = (G - a K G * t K G T m) / B K G T := rfl

theorem d_qStar (h : Base K G T m) : d K G T m (qStar K G T m) = t K G T m ^ 2 := by
  have hB := h.B_pos.ne'
  have hAB : a K G ^ 2 + B K G T ≠ 0 := by have := h.B_pos; positivity
  have key : (a K G ^ 2 + B K G T) * t K G T m ^ 2 = G ^ 2 + B K G T * s K m ^ 2 := by
    rw [t_sq h]
    field_simp
  rw [qStar_eq, d]
  set tt := t K G T m
  set b := B K G T
  set aa := a K G
  field_simp
  linear_combination (-1 : ℝ) * key

theorem sqrt_d_qStar (h : Base K G T m) :
    Real.sqrt (d K G T m (qStar K G T m)) = t K G T m := by
  rw [d_qStar h, Real.sqrt_sq t_nonneg]

/-- The stationary-point equation `a √(d(q*)) = G − B q*` holds without extraneous roots. -/
theorem stationary (h : Base K G T m) :
    G - B K G T * qStar K G T m = a K G * Real.sqrt (d K G T m (qStar K G T m)) := by
  rw [sqrt_d_qStar h, qStar_eq]
  field_simp [h.B_pos.ne']
  ring

theorem qStar_pos (h : Base K G T m) (hc : FiniteScale K G m) : 0 < qStar K G T m := by
  have hG := G_pos h hc
  have ha := a_pos h hc
  have hB := h.B_pos
  have hs := h.s_pos
  have hgas := (finiteScale_iff h).1 hc
  rw [qStar_eq]
  apply div_pos _ hB
  rw [sub_pos]
  -- `a t < G` ⇔ `a² t² < G²`
  have hAB : 0 < a K G ^ 2 + B K G T := by positivity
  have hsq : (a K G * t K G T m) ^ 2 < G ^ 2 := by
    rw [mul_pow, t_sq h, mul_div_assoc', div_lt_iff₀ hAB]
    have : a K G ^ 2 * s K m ^ 2 < G ^ 2 := by
      have := mul_lt_mul_of_pos_left hgas ha
      nlinarith [mul_pos ha hs]
    nlinarith
  have h1 : 0 ≤ a K G * t K G T m := mul_nonneg ha.le t_nonneg
  nlinarith

theorem t_pos (h : Base K G T m) : 0 < t K G T m := by
  have hB := h.B_pos
  have hs := h.s_pos
  unfold t
  apply Real.sqrt_pos.2
  positivity

theorem qStar_lt (h : Base K G T m) (hc : FiniteScale K G m) :
    qStar K G T m < G / B K G T := by
  rw [qStar_eq]
  apply div_lt_div_of_pos_right _ h.B_pos
  have := mul_pos (a_pos h hc) (t_pos h)
  linarith

theorem G_div_B_lt_qColl (h : Base K G T m) : G / B K G T < qColl K G T m := by
  unfold qColl
  apply div_lt_div_of_pos_right _ h.B_pos
  have := sqrt_disc_gt_abs h
  linarith [abs_nonneg G]

/-- `a q* ≤ t`, so the supporting tangent is nonnegative on `q ≥ 0`. -/
theorem tangent_nonneg (h : Base K G T m) (hc : FiniteScale K G m) {q : ℝ} (hq : 0 ≤ q) :
    0 ≤ Real.sqrt (d K G T m (qStar K G T m)) + a K G * (q - qStar K G T m) := by
  rw [sqrt_d_qStar h]
  have ha := a_pos h hc
  have hB := h.B_pos
  have hG := G_pos h hc
  have hAB : 0 < a K G ^ 2 + B K G T := by positivity
  have ht := t_nonneg (K := K) (G := G) (T := T) (m := m)
  -- `(a² + B) t ≥ a G`
  have key : a K G * G ≤ (a K G ^ 2 + B K G T) * t K G T m := by
    have h1 : ((a K G ^ 2 + B K G T) * t K G T m) ^ 2 =
        (a K G ^ 2 + B K G T) * (G ^ 2 + B K G T * s K m ^ 2) := by
      rw [mul_pow, t_sq h]
      field_simp
    have h2 : (a K G * G) ^ 2 ≤ ((a K G ^ 2 + B K G T) * t K G T m) ^ 2 := by
      rw [h1]
      have := h.s_pos
      nlinarith [mul_pos hB (pow_pos this 2), sq_nonneg (a K G), sq_nonneg G]
    have h3 : 0 ≤ (a K G ^ 2 + B K G T) * t K G T m := by positivity
    have h4 : 0 ≤ a K G * G := by positivity
    nlinarith
  have hq' : a K G * qStar K G T m ≤ t K G T m := by
    rw [qStar_eq, mul_div_assoc', div_le_iff₀ hB]
    nlinarith
  nlinarith

/-- Exact supporting-tangent identity at the stationary point. -/
theorem tangent_square_identity (h : Base K G T m) {q : ℝ} (hq : 0 ≤ d K G T m q) :
    (Real.sqrt (d K G T m (qStar K G T m)) + a K G * (q - qStar K G T m)) ^ 2 -
        Real.sqrt (d K G T m q) ^ 2 = (a K G ^ 2 + B K G T) * (q - qStar K G T m) ^ 2 := by
  have hs0 := Real.sq_sqrt (d_qStar h ▸ sq_nonneg (t K G T m))
  have hsq := Real.sq_sqrt hq
  have hstat := stationary h
  rw [add_sq, hs0, hsq]
  unfold d at *
  linear_combination (-(2 : ℝ)) * (q - qStar K G T m) * hstat

/-- Steps 4–5: `q*` is the unique global minimizer of `z₋` on `[0, q_coll]`. -/
theorem zMinus_unique_min (h : Base K G T m) (hc : FiniteScale K G m) {q : ℝ}
    (hq : 0 ≤ q) (hd : 0 ≤ d K G T m q) (hne : q ≠ qStar K G T m) :
    zMinus K G T m (qStar K G T m) < zMinus K G T m q := by
  have hK := h.K_pos
  have hsquare : 0 < (q - qStar K G T m) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.2 hne)
  have hcoeff : 0 < a K G ^ 2 + B K G T := by have := h.B_pos; positivity
  have hid := tangent_square_identity h hd
  have htan := tangent_nonneg h hc hq
  have hsq0 := Real.sqrt_nonneg (d K G T m q)
  have hbound : Real.sqrt (d K G T m q) <
      Real.sqrt (d K G T m (qStar K G T m)) + a K G * (q - qStar K G T m) := by
    nlinarith [mul_pos hcoeff hsquare]
  unfold zMinus
  apply div_lt_div_of_pos_right _ (by positivity)
  nlinarith

/-- Corollary 1: the exact minimum squared frequency. -/
theorem zMinus_qStar (h : Base K G T m) :
    zMinus K G T m (qStar K G T m) = zMin K G T m := by
  have hB := h.B_pos
  have hK := h.K_pos
  have hAB : 0 < a K G ^ 2 + B K G T := by positivity
  have hrt : Real.sqrt ((a K G ^ 2 + B K G T) * (G ^ 2 + B K G T * s K m ^ 2)) =
      (a K G ^ 2 + B K G T) * t K G T m := by
    have : (a K G ^ 2 + B K G T) * (G ^ 2 + B K G T * s K m ^ 2) =
        ((a K G ^ 2 + B K G T) * t K G T m) ^ 2 := by
      rw [mul_pow, t_sq h]
      field_simp
    rw [this, Real.sqrt_sq (mul_nonneg hAB.le t_nonneg)]
  rw [zMinus, zMin, sqrt_d_qStar h, hrt, qStar_eq]
  field_simp
  ring

/-- Step 6: both squared frequencies are strictly positive on the real-pole interval. -/
theorem branches_pos (h : Base K G T m) (hc : FiniteScale K G m) {q : ℝ} (hq : 0 ≤ q)
    (_hd : 0 ≤ d K G T m q) : 0 < zMinus K G T m q ∧ 0 < zPlus K G T m q := by
  have hK := h.K_pos
  have hT := h.T_pos
  have hG := G_pos h hc
  have ha := a_pos h hc
  have hm : 0 < m ^ 2 := by
    have := h.mass_pos
    nlinarith
  have h1 : 0 < 1 + a K G * q := by positivity
  have hdisc := discriminant_eq h q
  have hlt : Real.sqrt (d K G T m q) < 1 + a K G * q := by
    rw [Real.sqrt_lt' h1, ← hdisc]
    have : 0 < 4 * K * (m ^ 2 + q + (K + G + T) * q ^ 2) := by positivity
    linarith
  constructor
  · unfold zMinus
    apply div_pos (by linarith) (by positivity)
  · unfold zPlus
    apply div_pos (by linarith [Real.sqrt_nonneg (d K G T m q)]) (by positivity)

/-- The first derivative of the lower branch on the region `d > 0`. -/
noncomputable def zMinusDeriv (K G T m q : ℝ) : ℝ :=
  (a K G - (G - B K G T * q) / Real.sqrt (d K G T m q)) / (2 * K)

theorem hasDerivAt_d (q : ℝ) : HasDerivAt (d K G T m) (2 * G - 2 * B K G T * q) q := by
  have := (((hasDerivAt_id q).const_mul (2 * G)).const_add (s K m ^ 2)).sub
    ((hasDerivAt_pow 2 q).const_mul (B K G T))
  convert this using 1
  ring

theorem continuous_d : Continuous (d K G T m) := by
  unfold d
  fun_prop

theorem continuous_zMinus : Continuous (zMinus K G T m) := by
  unfold zMinus
  have := (continuous_d (K := K) (G := G) (T := T) (m := m)).sqrt
  fun_prop

theorem hasDerivAt_zMinus (h : Base K G T m) {q : ℝ} (hd : 0 < d K G T m q) :
    HasDerivAt (zMinus K G T m) (zMinusDeriv K G T m q) q := by
  have hK := h.K_pos
  have hsq := (hasDerivAt_d (K := K) (G := G) (T := T) (m := m) q).sqrt hd.ne'
  have := ((((hasDerivAt_id q).const_mul (a K G)).const_add 1).sub hsq).div_const (2 * K)
  convert this using 1
  have hs : 0 < Real.sqrt (d K G T m q) := Real.sqrt_pos.2 hd
  unfold zMinusDeriv
  field_simp

/-- The second derivative `z₋'' = (Bs² + G²)/(2K d^{3/2})`. -/
theorem hasDerivAt_zMinusDeriv (h : Base K G T m) {q : ℝ} (hd : 0 < d K G T m q) :
    HasDerivAt (zMinusDeriv K G T m)
      ((B K G T * s K m ^ 2 + G ^ 2) / (2 * K * Real.sqrt (d K G T m q) ^ 3)) q := by
  have hK := h.K_pos
  have hs : 0 < Real.sqrt (d K G T m q) := Real.sqrt_pos.2 hd
  have hsq := (hasDerivAt_d (K := K) (G := G) (T := T) (m := m) q).sqrt hd.ne'
  have hnum : HasDerivAt (fun q => G - B K G T * q) (-B K G T) q := by
    simpa using ((hasDerivAt_id q).const_mul (B K G T)).const_sub G
  have := ((hnum.div hsq hs.ne').const_sub (a K G)).div_const (2 * K)
  convert this using 1
  have hsq2 : Real.sqrt (d K G T m q) ^ 2 = d K G T m q := Real.sq_sqrt hd.le
  have hd_def : d K G T m q = s K m ^ 2 + 2 * G * q - B K G T * q ^ 2 := rfl
  field_simp
  rw [hsq2, hd_def]
  ring

theorem deriv_zMinus_eventually (h : Base K G T m) {q : ℝ} (hd : 0 < d K G T m q) :
    deriv (zMinus K G T m) =ᶠ[𝓝 q] zMinusDeriv K G T m := by
  have hopen : IsOpen {y | 0 < d K G T m y} := isOpen_lt continuous_const continuous_d
  filter_upwards [hopen.mem_nhds hd] with y hy
  exact (hasDerivAt_zMinus h hy).deriv

/-- Strict convexity in squared wavenumber: the actual second derivative. -/
theorem zMinus_second_deriv (h : Base K G T m) {q : ℝ} (hd : 0 < d K G T m q) :
    deriv (deriv (zMinus K G T m)) q =
      (B K G T * s K m ^ 2 + G ^ 2) / (2 * K * Real.sqrt (d K G T m q) ^ 3) := by
  rw [(deriv_zMinus_eventually h hd).deriv_eq]
  exact (hasDerivAt_zMinusDeriv h hd).deriv

theorem second_deriv_value_pos (h : Base K G T m) {q : ℝ} (hd : 0 < d K G T m q) :
    0 < (B K G T * s K m ^ 2 + G ^ 2) / (2 * K * Real.sqrt (d K G T m q) ^ 3) := by
  have hK := h.K_pos
  have hB := h.B_pos
  have hs := h.s_pos
  have : 0 < Real.sqrt (d K G T m q) := Real.sqrt_pos.2 hd
  positivity

theorem zMinusDeriv_strictMonoOn (h : Base K G T m) :
    StrictMonoOn (zMinusDeriv K G T m) (Ico 0 (qColl K G T m)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ico 0 (qColl K G T m))
  · intro x hx
    exact (hasDerivAt_zMinusDeriv h (d_pos_of_lt h hx.1 hx.2)).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ico] at hx
    have hd := d_pos_of_lt h hx.1.le hx.2
    rw [(hasDerivAt_zMinusDeriv h hd).deriv]
    exact second_deriv_value_pos h hd

theorem zMinusDeriv_zero (h : Base K G T m) :
    zMinusDeriv K G T m 0 = (a K G - G / s K m) / (2 * K) := by
  have hd0 : d K G T m 0 = s K m ^ 2 := by simp [d]
  rw [zMinusDeriv, hd0, Real.sqrt_sq h.s_pos.le]
  simp

/-- The initial slope is negative exactly under the finite-scale condition. -/
theorem zMinusDeriv_zero_neg_iff (h : Base K G T m) :
    zMinusDeriv K G T m 0 < 0 ↔ FiniteScale K G m := by
  have hK := h.K_pos
  have hs := h.s_pos
  rw [zMinusDeriv_zero h, div_neg_iff, finiteScale_iff h]
  constructor
  · rintro (⟨_, h2⟩ | ⟨h1, _⟩)
    · linarith
    · rw [sub_neg, lt_div_iff₀ hs] at h1
      exact h1
  · intro h1
    refine Or.inr ⟨?_, by positivity⟩
    rw [sub_neg, lt_div_iff₀ hs]
    exact h1

/-- **Corollary 2 (sharp initial-slope criterion)**, with no sign assumption on `G`:
an interior minimizer exists if and only if the finite-scale condition holds. -/
theorem sharp_initial_slope_criterion (h : Base K G T m) :
    (∃ q₀ ∈ Ioo 0 (qColl K G T m), IsMinOn (zMinus K G T m) (Icc 0 (qColl K G T m)) q₀) ↔
      FiniteScale K G m := by
  constructor
  · rintro ⟨q₀, hq₀, hmin⟩
    have hd := d_pos_of_lt h hq₀.1.le hq₀.2
    have hloc : IsLocalMin (zMinus K G T m) q₀ :=
      hmin.isLocalMin (Icc_mem_nhds hq₀.1 hq₀.2)
    have hzero := hloc.hasDerivAt_eq_zero (hasDerivAt_zMinus h hd)
    rw [← zMinusDeriv_zero_neg_iff h]
    calc zMinusDeriv K G T m 0 < zMinusDeriv K G T m q₀ :=
          zMinusDeriv_strictMonoOn h ⟨le_rfl, qColl_pos h⟩ ⟨hq₀.1.le, hq₀.2⟩ hq₀.1
      _ = 0 := hzero
  · intro hc
    have hpos := qStar_pos h hc
    have hlt := (qStar_lt h hc).trans (G_div_B_lt_qColl h)
    refine ⟨qStar K G T m, ⟨hpos, hlt⟩, fun q hq => ?_⟩
    by_cases hne : q = qStar K G T m
    · subst hne
      simp
    · exact (zMinus_unique_min h hc hq.1 ((d_nonneg_iff h hq.1).2 hq.2) hne).le

/-- Otherwise the lower branch is strictly increasing and minimized at `q = 0`. -/
theorem min_at_zero_of_not_finiteScale (h : Base K G T m) (hc : ¬ FiniteScale K G m) :
    StrictMonoOn (zMinus K G T m) (Icc 0 (qColl K G T m)) ∧
      IsMinOn (zMinus K G T m) (Icc 0 (qColl K G T m)) 0 := by
  have h0 : 0 ≤ zMinusDeriv K G T m 0 := by
    by_contra hneg
    exact hc ((zMinusDeriv_zero_neg_iff h).1 (not_le.1 hneg))
  have hmono : StrictMonoOn (zMinus K G T m) (Icc 0 (qColl K G T m)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 (qColl K G T m))
      continuous_zMinus.continuousOn
    intro x hx
    rw [interior_Icc] at hx
    have hd := d_pos_of_lt h hx.1.le hx.2
    rw [(hasDerivAt_zMinus h hd).deriv]
    exact lt_of_le_of_lt h0
      (zMinusDeriv_strictMonoOn h ⟨le_rfl, qColl_pos h⟩ ⟨hx.1.le, hx.2⟩ hx.1)
  refine ⟨hmono, fun q hq => ?_⟩
  rcases eq_or_lt_of_le hq.1 with h' | h'
  · subst h'
    simp
  · exact (hmono ⟨le_rfl, (qColl_pos h).le⟩ hq h').le

/-- **Theorem (exact positive-wavenumber minimum).**  Under the baseline hypotheses and
the strict finite-scale condition: `G, a > 0`; `z±` are exactly the real roots; for
`q ≥ 0` real roots exist exactly on `[0, q_coll]`; the explicit `q*` satisfies
`0 < q* < G/B < q_coll` and is the unique global minimizer of `z₋` on `[0, q_coll]`;
`z₋'' = (Bs² + G²)/(2K d^{3/2}) > 0` on the open interval; and both branches are
strictly positive on the whole real-pole interval. -/
theorem exact_positive_wavenumber_minimum (h : Base K G T m) (hc : FiniteScale K G m) :
    0 < G ∧ 0 < a K G ∧
    (∀ q z, 0 ≤ d K G T m q →
      (poly K G T m q z = 0 ↔ z = zPlus K G T m q ∨ z = zMinus K G T m q)) ∧
    (∀ q, 0 ≤ q → ((∃ z : ℝ, poly K G T m q z = 0) ↔ q ≤ qColl K G T m)) ∧
    (0 < qStar K G T m ∧ qStar K G T m < G / B K G T ∧ G / B K G T < qColl K G T m) ∧
    (∀ q ∈ Icc 0 (qColl K G T m), q ≠ qStar K G T m →
      zMinus K G T m (qStar K G T m) < zMinus K G T m q) ∧
    (∀ q ∈ Ioo 0 (qColl K G T m),
      deriv (deriv (zMinus K G T m)) q =
          (B K G T * s K m ^ 2 + G ^ 2) / (2 * K * Real.sqrt (d K G T m q) ^ 3) ∧
        0 < deriv (deriv (zMinus K G T m)) q) ∧
    (∀ q ∈ Icc 0 (qColl K G T m), 0 < zMinus K G T m q ∧ 0 < zPlus K G T m q) := by
  refine ⟨G_pos h hc, a_pos h hc, fun q z hd => poly_eq_zero_iff h hd z,
    fun q hq => real_root_iff h hq, ⟨qStar_pos h hc, qStar_lt h hc, G_div_B_lt_qColl h⟩,
    fun q hq hne => zMinus_unique_min h hc hq.1 ((d_nonneg_iff h hq.1).2 hq.2) hne,
    fun q hq => ?_, fun q hq => branches_pos h hc hq.1 ((d_nonneg_iff h hq.1).2 hq.2)⟩
  have hd := d_pos_of_lt h hq.1.le hq.2
  rw [zMinus_second_deriv h hd]
  exact ⟨rfl, second_deriv_value_pos h hd⟩

/-- **Corollary (exact minimum squared frequency).** -/
theorem exact_minimum_frequency (h : Base K G T m) (hc : FiniteScale K G m) :
    zMinus K G T m (qStar K G T m) = zMin K G T m ∧ 0 < zMin K G T m := by
  refine ⟨zMinus_qStar h, ?_⟩
  rw [← zMinus_qStar h]
  exact (branches_pos h hc (qStar_pos h hc).le (d_qStar h ▸ sq_nonneg _)).1

/-- The positive frequency `ω₋ = √z₋` has the same unique minimizer. -/
theorem omegaMinus_unique_min (h : Base K G T m) (hc : FiniteScale K G m) :
    ∀ q ∈ Icc 0 (qColl K G T m), q ≠ qStar K G T m →
      Real.sqrt (zMinus K G T m (qStar K G T m)) < Real.sqrt (zMinus K G T m q) := by
  intro q hq hne
  have hpos := (branches_pos h hc (qStar_pos h hc).le (d_qStar h ▸ sq_nonneg _)).1
  exact Real.sqrt_lt_sqrt hpos.le
    (zMinus_unique_min h hc hq.1 ((d_nonneg_iff h hq.1).2 hq.2) hne)

/-- In terms of the wavenumber `k = |𝐤| ≥ 0`, the unique minimizer is `k* = √q* > 0`. -/
theorem wavenumber_minimum (h : Base K G T m) (hc : FiniteScale K G m) :
    0 < Real.sqrt (qStar K G T m) ∧
      ∀ k : ℝ, 0 ≤ k → k ^ 2 ≤ qColl K G T m → k ≠ Real.sqrt (qStar K G T m) →
        zMinus K G T m (Real.sqrt (qStar K G T m) ^ 2) < zMinus K G T m (k ^ 2) := by
  have hq := qStar_pos h hc
  refine ⟨Real.sqrt_pos.2 hq, fun k hk hkq hne => ?_⟩
  rw [Real.sq_sqrt hq.le]
  refine zMinus_unique_min h hc (sq_nonneg k) ((d_nonneg_iff h (sq_nonneg k)).2 hkq) ?_
  intro heq
  apply hne
  rw [← heq, Real.sqrt_sq hk]

theorem zMinusDeriv_qStar (h : Base K G T m) : zMinusDeriv K G T m (qStar K G T m) = 0 := by
  have ht : 0 < Real.sqrt (d K G T m (qStar K G T m)) := by
    rw [sqrt_d_qStar h]
    exact t_pos h
  rw [zMinusDeriv, stationary h, mul_div_assoc, div_self ht.ne', mul_one, sub_self, zero_div]

/-- Remark: in the variable `k`, `d²/dk² z₋(k²)` at `k* = √q*` equals `4 k*² z₋''(q*) > 0`. -/
theorem wavenumber_second_deriv (h : Base K G T m) (hc : FiniteScale K G m) :
    deriv (deriv fun k => zMinus K G T m (k ^ 2)) (Real.sqrt (qStar K G T m)) =
        4 * Real.sqrt (qStar K G T m) ^ 2 * deriv (deriv (zMinus K G T m)) (qStar K G T m) ∧
      0 < deriv (deriv fun k => zMinus K G T m (k ^ 2)) (Real.sqrt (qStar K G T m)) := by
  have hq := qStar_pos h hc
  set k₀ := Real.sqrt (qStar K G T m) with hk₀
  have hk₀sq : k₀ ^ 2 = qStar K G T m := Real.sq_sqrt hq.le
  have hd₀ : 0 < d K G T m (qStar K G T m) := by
    rw [d_qStar h]
    exact pow_pos (t_pos h) 2
  have hopen : IsOpen {k : ℝ | 0 < d K G T m (k ^ 2)} :=
    isOpen_lt continuous_const (continuous_d.comp (continuous_pow 2))
  have hmem : k₀ ∈ {k : ℝ | 0 < d K G T m (k ^ 2)} := by
    show 0 < d K G T m (k₀ ^ 2)
    rw [hk₀sq]
    exact hd₀
  have hev : deriv (fun k => zMinus K G T m (k ^ 2)) =ᶠ[𝓝 k₀]
      fun k => zMinusDeriv K G T m (k ^ 2) * (2 * k) := by
    filter_upwards [hopen.mem_nhds hmem] with k hk
    have hk' : 0 < d K G T m (k ^ 2) := hk
    have := HasDerivAt.comp (h := fun x : ℝ => x ^ 2) k (hasDerivAt_zMinus h hk')
      (hasDerivAt_pow 2 k)
    rw [show (fun k => zMinus K G T m (k ^ 2)) = (zMinus K G T m ∘ fun x => x ^ 2) from rfl,
      this.deriv]
    simp
  have hD : HasDerivAt (fun k => zMinusDeriv K G T m (k ^ 2) * (2 * k))
      ((B K G T * s K m ^ 2 + G ^ 2) / (2 * K * Real.sqrt (d K G T m (k₀ ^ 2)) ^ 3) *
          (2 * k₀) * (2 * k₀) + zMinusDeriv K G T m (k₀ ^ 2) * 2) k₀ := by
    have hmem' : 0 < d K G T m (k₀ ^ 2) := hmem
    have h1 := HasDerivAt.comp (h := fun x : ℝ => x ^ 2) k₀ (hasDerivAt_zMinusDeriv h hmem')
      (hasDerivAt_pow 2 k₀)
    have h2 : HasDerivAt (fun k : ℝ => 2 * k) 2 k₀ := by
      simpa using (hasDerivAt_id k₀).const_mul (2 : ℝ)
    have := h1.mul h2
    convert this using 1
    simp
  rw [hev.deriv_eq, hD.deriv, hk₀sq, zMinusDeriv_qStar h, zMinus_second_deriv h hd₀]
  constructor
  · linear_combination (4 * ((B K G T * s K m ^ 2 + G ^ 2) /
      (2 * K * Real.sqrt (d K G T m (qStar K G T m)) ^ 3))) * hk₀sq
  · have := second_deriv_value_pos h hd₀
    have hk : 0 < k₀ := Real.sqrt_pos.2 hq
    nlinarith [mul_pos hk hk]

end Dispersion

end ReyesMath
