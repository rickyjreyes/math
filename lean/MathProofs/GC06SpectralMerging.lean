import MathProofs.GC16InterfaceBinding

/-! GC06 unrestricted spectral merging: exact amplitude/infimum algebra and
the low-density Hessian sign. The analytic spectral and profile-decomposition
hypotheses are explicit; this file does not certify the all-mass theorem. -/

open Filter Topology Set MeasureTheory
namespace ReyesMath.GC06SpectralMerging
open Sobolev Sobolev.H2 StrictBinding
variable {β γ k : ℝ}

/-- Exact mass-amplitude polynomial in the original F01 model. -/
noncomputable def amp (β γ k : ℝ) (U : H2 2) (t : ℝ) : ℝ :=
  t * T k U - β / 2 * (t ^ 2 * Q U) + γ / 3 * (t ^ 3 * S U)

/-- The amplitude derivative divided by the original mass. For a weak
Euler-Lagrange solution, testing its equation with U identifies this scalar
with the Lagrange multiplier. That PDE correspondence is not proved here. -/
noncomputable def multiplier (β γ k : ℝ) (U : H2 2) : ℝ :=
  (T k U - β * Q U + γ * S U) / M U

theorem amp_one (U : H2 2) : amp β γ k U 1 = energy β γ k U := by
  rw [energy_eq]
  unfold amp
  ring

/-- Ordinary subadditivity is an explicit continuum obligation. -/
theorem mass_deletion_comparison (hβ : 0 < β) (hγ : 0 < γ) (U : H2 2)
    (hM : 0 < M U) (hU : energy β γ k U = Imin β γ k (M U))
    (hsub : ∀ a b : ℝ, 0 < a → 0 < b →
      Imin β γ k (a + b) ≤ Imin β γ k a + Imin β γ k b)
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    amp β γ k U 1 < amp β γ k U t := by
  have ha := mul_pos ht hM
  have hb := mul_pos (sub_pos.mpr ht1) hM
  have hsum : t * M U + (1 - t) * M U = M U := by ring
  have hs := hsub _ _ ha hb
  rw [hsum] at hs
  have hn := (NegativeEnergy.negative_constrained_energy (k := k) hβ hγ hb).2
  obtain ⟨V, hVm, hVe⟩ := exists_scaled (β := β) (γ := γ) (k := k) U ht.le
  have hi := Imin_le_energy (β := β) (k := k) hγ hVm
  change energy β γ k V = amp β γ k U t at hVe
  rw [amp_one, hU]
  linarith only [hs, hn, hi, hVe]

/-- Any two attained profiles saturating ordinary subadditivity minimize the
exact mass-transfer polynomial at zero. -/
theorem mass_exchange_comparison (hγ : 0 < γ) (U V : H2 2)
    (hMu : 0 < M U) (hMv : 0 < M V)
    (hU : energy β γ k U = Imin β γ k (M U))
    (hV : energy β γ k V = Imin β γ k (M V))
    (heq : Imin β γ k (M U + M V) =
      Imin β γ k (M U) + Imin β γ k (M V))
    (hsub : ∀ a b : ℝ, 0 < a → 0 < b →
      Imin β γ k (a + b) ≤ Imin β γ k a + Imin β γ k b)
    {h : ℝ} (hlo : -M U < h) (hhi : h < M V) :
    amp β γ k U 1 + amp β γ k V 1 ≤
      amp β γ k U (1 + h / M U) + amp β γ k V (1 - h / M V) := by
  have ha : 0 < M U + h := by linarith
  have hb : 0 < M V - h := by linarith
  have ht : 0 < 1 + h / M U := by
    rw [show 1 + h / M U = (M U + h) / M U by field_simp [hMu.ne'] <;> ring]
    exact div_pos ha hMu
  have hs : 0 < 1 - h / M V := by
    rw [show 1 - h / M V = (M V - h) / M V by field_simp [hMv.ne'] <;> ring]
    exact div_pos hb hMv
  obtain ⟨W, hWm, hWe⟩ := exists_scaled (β := β) (γ := γ) (k := k) U ht.le
  obtain ⟨Z, hZm, hZe⟩ := exists_scaled (β := β) (γ := γ) (k := k) V hs.le
  have hWm' : M W = M U + h := by
    rw [hWm]
    field_simp [hMu.ne'] <;> ring
  have hZm' : M Z = M V - h := by
    rw [hZm]
    field_simp [hMv.ne'] <;> ring
  have hw := Imin_le_energy (β := β) (k := k) hγ hWm'
  have hz := Imin_le_energy (β := β) (k := k) hγ hZm'
  have hi := hsub _ _ ha hb
  rw [show M U + h + (M V - h) = M U + M V by ring, heq] at hi
  change energy β γ k W = amp β γ k U (1 + h / M U) at hWe
  change energy β γ k Z = amp β γ k V (1 - h / M V) at hZe
  rw [amp_one U, amp_one V, hU, hV]
  linarith only [hw, hz, hi, hWe, hZe]

/-- A cubic nonnegative on a right neighborhood has nonnegative linear
coefficient. Elementary proof, avoiding differentiability of the infimum. -/
theorem cubic_linear_nonneg {δ d c e : ℝ} (hδ : 0 < δ)
    (h : ∀ x : ℝ, 0 < x → x < δ → 0 ≤ x * (d + c * x + e * x ^ 2)) :
    0 ≤ d := by
  by_contra! hn
  let B := |c| + |e| + 1
  have hB : 0 < B := by dsimp [B]; positivity
  let x := min (δ / 2) (min 1 ((-d) / (2 * B)))
  have hx : 0 < x := by
    dsimp only [x]
    exact lt_min (by positivity) (lt_min (by norm_num) (div_pos (by linarith) (by positivity)))
  have hxδ : x < δ := by
    have hh : x ≤ δ / 2 := min_le_left _ _
    linarith only [hh, hδ]
  have hx1 : x ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hxD : x ≤ (-d) / (2 * B) := (min_le_right _ _).trans (min_le_right _ _)
  have hBx := (le_div_iff₀ (by positivity : 0 < 2 * B)).mp hxD
  have hxx : x ^ 2 ≤ x := by
    nlinarith only [mul_nonneg hx.le (sub_nonneg.mpr hx1)]
  have hc := mul_le_mul_of_nonneg_right (le_abs_self c) hx.le
  have he := mul_le_mul_of_nonneg_right (le_abs_self e) (sq_nonneg x)
  have he' := mul_le_mul_of_nonneg_left hxx (abs_nonneg e)
  have hsum : c * x + e * x ^ 2 ≤ B * x := by
    dsimp only [B]
    nlinarith only [hc, he, he', hx.le]
  have hnon : 0 ≤ d + c * x + e * x ^ 2 := by
    by_contra! hh
    exact (not_lt_of_ge (h x hx hxδ)) (mul_neg_of_pos_of_neg hx hh)
  nlinarith only [hBx, hsum, hn, hnon]

/-- A genuine minimizer has nonpositive amplitude multiplier, conditional
only on ordinary subadditivity. Strict negativity requires the continuum
angular Helmholtz Hessian argument. -/
theorem multiplier_nonpos (hβ : 0 < β) (hγ : 0 < γ) (U : H2 2)
    (hM : 0 < M U) (hU : energy β γ k U = Imin β γ k (M U))
    (hsub : ∀ a b : ℝ, 0 < a → 0 < b →
      Imin β γ k (a + b) ≤ Imin β γ k a + Imin β γ k b) :
    multiplier β γ k U ≤ 0 := by
  let D0 := T k U - β * Q U + γ * S U
  have hD : 0 ≤ -D0 := by
    apply cubic_linear_nonneg (δ := 1) (c := -β / 2 * Q U + γ * S U)
      (e := -γ / 3 * S U) (by norm_num)
    intro x hx hx1
    have hcmp := mass_deletion_comparison hβ hγ U hM hU hsub
      (t := 1 - x) (by linarith) (by linarith)
    have hp : amp β γ k U (1 - x) - amp β γ k U 1 =
        x * (-D0 + (-β / 2 * Q U + γ * S U) * x +
          (-γ / 3 * S U) * x ^ 2) := by
      unfold amp
      dsimp only [D0]
      ring
    linarith only [hcmp, hp]
  unfold multiplier
  exact div_nonpos_of_nonpos_of_nonneg (by dsimp only [D0] at hD; linarith only [hD]) hM.le

/-- Exact scalar multiplier agreement at a split equality, with the
ordinary subadditivity input explicit. -/
theorem common_multiplier_of_equality (hγ : 0 < γ) (U V : H2 2)
    (hMu : 0 < M U) (hMv : 0 < M V)
    (hU : energy β γ k U = Imin β γ k (M U))
    (hV : energy β γ k V = Imin β γ k (M V))
    (heq : Imin β γ k (M U + M V) =
      Imin β γ k (M U) + Imin β γ k (M V))
    (hsub : ∀ a b : ℝ, 0 < a → 0 < b →
      Imin β γ k (a + b) ≤ Imin β γ k a + Imin β γ k b) :
    multiplier β γ k U = multiplier β γ k V := by
  let d := multiplier β γ k U - multiplier β γ k V
  let c := (-β / 2 * Q U + γ * S U) / (M U) ^ 2 +
    (-β / 2 * Q V + γ * S V) / (M V) ^ 2
  let e := (γ / 3 * S U) / (M U) ^ 3 - (γ / 3 * S V) / (M V) ^ 3
  have hp (x : ℝ) :
      amp β γ k U (1 + x / M U) + amp β γ k V (1 - x / M V) -
        (amp β γ k U 1 + amp β γ k V 1) =
        x * (d + c * x + e * x ^ 2) := by
    dsimp only [d, c, e, amp, multiplier]
    field_simp [hMu.ne', hMv.ne'] <;> ring
  have hδ : 0 < min (M U) (M V) := lt_min hMu hMv
  have hpos : 0 ≤ d := by
    apply cubic_linear_nonneg (c := c) (e := e) hδ
    intro x hx hxδ
    have hhi : x < M V := hxδ.trans_le (min_le_right _ _)
    have hlo : -M U < x := by linarith
    have hc := mass_exchange_comparison hγ U V hMu hMv hU hV heq hsub hlo hhi
    linarith only [hc, hp x]
  have hneg : 0 ≤ -d := by
    apply cubic_linear_nonneg (c := c) (e := -e) hδ
    intro x hx hxδ
    have hxU : x < M U := hxδ.trans_le (min_le_left _ _)
    have hlo : -M U < -x := by linarith
    have hhi : -x < M V := by linarith
    have hc := mass_exchange_comparison hγ U V hMu hMv hU hV heq hsub hlo hhi
    have hh := hp (-x)
    rw [show (-x) * (d + c * (-x) + e * (-x) ^ 2) =
      x * (-d + c * x + (-e) * x ^ 2) by ring] at hh
    linarith only [hc, hh]
  dsimp only [d] at hpos hneg
  linarith only [hpos, hneg]

/-- Scalar sign needed for the angular Helmholtz threshold test. The variables
are density, squared perturbation norm, and real overlap, respectively. -/
theorem low_density_hessian (hβ : 0 < β) (hγ : 0 < γ)
    {ρ z p : ℝ} (hρ : 0 ≤ ρ) (hz : 0 ≤ z) (hd : ρ ≤ β / (4 * γ)) :
    (-β * ρ + γ * ρ ^ 2) * z + (-2 * β + 4 * γ * ρ) * p ^ 2
      ≤ -(3 * β / 4) * ρ * z := by
  have h4' := (le_div_iff₀ (by positivity : 0 < 4 * γ)).mp hd
  have h4 : 4 * γ * ρ ≤ β := by nlinarith only [h4']
  have hcoef : -2 * β + 4 * γ * ρ ≤ 0 := by linarith
  have hcoef' : -β * ρ + γ * ρ ^ 2 ≤ -(3 * β / 4) * ρ := by
    nlinarith only [mul_le_mul_of_nonneg_right h4 hρ]
  have h1 := mul_le_mul_of_nonneg_right hcoef' hz
  have h2 := mul_nonpos_of_nonpos_of_nonneg hcoef (sq_nonneg p)
  nlinarith only [h1, h2]

/-- Exact obstruction reduction: the analytical finite-cluster extraction
must supply a pair of attained profiles saturating ordinary subadditivity
whenever some split fails. The analytical spectral merging must exclude such
a pair. Neither continuum input is disguised as an axiom. -/
theorem all_binding_of_pair_exclusion
    (hcluster : ∀ m a : ℝ, 0 < m → 0 < a → a < m →
      ¬ Imin β γ k m < Imin β γ k a + Imin β γ k (m - a) →
      ∃ U V : H2 2, 0 < M U ∧ 0 < M V ∧
        energy β γ k U = Imin β γ k (M U) ∧
        energy β γ k V = Imin β γ k (M V) ∧
        Imin β γ k (M U + M V) = Imin β γ k (M U) + Imin β γ k (M V))
    (hmerge : ∀ U V : H2 2, 0 < M U → 0 < M V →
      energy β γ k U = Imin β γ k (M U) →
      energy β γ k V = Imin β γ k (M V) →
      Imin β γ k (M U + M V) ≠ Imin β γ k (M U) + Imin β γ k (M V))
    {m a : ℝ} (hm : 0 < m) (ha : 0 < a) (ham : a < m) :
    Imin β γ k m < Imin β γ k a + Imin β γ k (m - a) := by
  by_contra hn
  obtain ⟨U, V, hMu, hMv, hU, hV, heq⟩ := hcluster m a hm ha ham hn
  exact hmerge U V hMu hMv hU hV heq

end ReyesMath.GC06SpectralMerging
